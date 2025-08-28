#![warn(missing_docs)]

//! `slice-rc` provides a variant of the `std`'s [`Rc`](std::rc::Rc) type, and more generally the contents of the module [`std::rc`].
//! 
//! If you are not familiar with those, you should read their documentation before trying to use this crate.
//! 
//! * [`Src<T>`] (which, as the crate name suggests, stands for 'Slice Reference Counted') is a variant of [`std::rc::Rc<T>`]
//! * [`WeakSrc<T>`] is a variant of [`std::rc::Weak<T>`]
//! * [`UniqueSrc<T>`] is a variant of the currently-unstable [`std::rc::UniqueRc<T>`]
//! * [`UninitSrc<T>`] is a variant of the as-yet-only-hypothetical `std::rc::UninitRc<T>`
//! 
//! ### How do this crate's types differ from the [`std::rc`] ones?
//! 
//! Notably, <code>[Rc](std::rc::Rc)\<[\[T\]](prim@slice)></code> is already a valid, usable type; why do we need a special slice [`Rc`](std::rc::Rc) when [`Rc`](std::rc::Rc) already supports slices?
//! 
//! The answer can be found in one method (well, two: one on [`Src`](Src::slice), and its analog on [`WeakSrc`](WeakSrc::slice)):
//! [`Src::slice`] allows us to acquire a sub-slice of the contents of the [`Src`] which still uses the reference-counting mechanism rather than using lifetime-style references;
//! e.g.:
//! 
//! ```rust
//! use slice_rc::Src;
//! 
//! let whole: Src<str> = Src::new("Hello World!");
//! let world: Src<str> = whole.slice(6..=10);
//! assert_eq!(&*world, "World");
//! ```
//! 
//! This is useful because:
//! * <code>[Src]\<T>: \'static where T: \'static</code>, and therefore this is useful where lifetimes are difficult or impossible to accomodate.
//! * Via [`WeakSrc`] and constructor functions like [`Src::cyclic_from_fn`], it allows constructing collections of self-referential objects,
//!   and unlike e.g. <code>[Vec]\<[Rc](std::rc::Rc)\<T>></code>, in a <code>[Src]\<[\[T\]](prim@slice)></code>, the actual `T`'s are contiguous, which makes it possible to obtain a [`&[T]`](prim@slice).
//! 
//! ### Root
//! 
//! Many methods in this crate refer to a "root" pointer (e.g., root `Src`).
//! This refers to any `Src`-family pointer that refers to the whole allocation;
//! its [`len`](Src::len) is the number of elements in the whole allocation,
//! and every non-root pointer to the allocation references either an element or a subslice of if.
//! 
//! Note that it is not just the "original" `Src` that can be root:
//! 
//! ```rust
//! # use slice_rc::Src;
//! let root = Src::from_array([1, 2, 3]);
//! 
//! assert!(Src::is_root(&root));
//! 
//! let slice = root.slice(1..);
//! 
//! assert!(!Src::is_root(&slice));
//! 
//! let also_root = Src::root(&slice);
//! 
//! assert!(Src::is_root(&also_root));
//! ```

mod inner;
mod strong;
mod uninit;
mod unique;
mod weak;

use std::{ops::{Bound, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive}, slice, usize};

use inner::*;
pub use strong::*;
pub use uninit::*;
pub use unique::*;
pub use weak::*;

/// A helper trait for [`Src::slice`] and [`WeakSrc::slice`].
/// Analagous to [`SliceIndex`](std::slice::SliceIndex).
pub trait SrcIndex<T: SrcSlice + ?Sized> {
  
  /// The output type returned by methods.
  type Output: SrcTarget + ?Sized;
  
  /// Returns an [`Src`] pointer to the output at this location, panicking if out of bounds.
  fn get(self, slice: Src<T>) -> Src<Self::Output>;
  
  /// Returns a [`WeakSrc`] pointer to the output at this location, panicking if out of bounds.
  fn get_weak(self, slice: WeakSrc<T>) -> WeakSrc<Self::Output>;
  
}

impl<T> SrcIndex<[T]> for usize {
  
  type Output = T;
  
  #[inline]
  fn get(self, slice: Src<[T]>) -> Src<Self::Output> {
    Src::into_item(slice, self)
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<[T]>) -> WeakSrc<Self::Output> {
    WeakSrc::into_item(slice, self)
  }
  
}

impl<T> SrcIndex<[T]> for (Bound<usize>, Bound<usize>) {
  
  type Output = [T];
  
  #[inline]
  fn get(self, slice: Src<[T]>) -> Src<Self::Output> {
    let (start, end) = self;
    Src::into_slice_from_bounds(slice, start, end)
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<[T]>) -> WeakSrc<Self::Output> {
    let (start, end) = self;
    WeakSrc::into_slice_from_bounds(slice, start, end)
  }
  
}

impl<T> SrcIndex<[T]> for Range<usize> {
  
  type Output = [T];
  
  #[inline]
  fn get(self, slice: Src<[T]>) -> Src<Self::Output> {
    let Range { start, end } = self;
    Src::into_slice_from_bounds(slice, Bound::Included(start), Bound::Excluded(end))
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<[T]>) -> WeakSrc<Self::Output> {
    let Range { start, end } = self;
    WeakSrc::into_slice_from_bounds(slice, Bound::Included(start), Bound::Excluded(end))
  }
  
}

impl<T> SrcIndex<[T]> for RangeFrom<usize> {
  
  type Output = [T];
  
  #[inline]
  fn get(self, slice: Src<[T]>) -> Src<Self::Output> {
    let RangeFrom { start } = self;
    Src::into_slice_from_bounds(slice, Bound::Included(start), Bound::Unbounded)
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<[T]>) -> WeakSrc<Self::Output> {
    let RangeFrom { start } = self;
    WeakSrc::into_slice_from_bounds(slice, Bound::Included(start), Bound::Unbounded)
  }
  
}

impl<T> SrcIndex<[T]> for RangeFull {
  
  type Output = [T];
  
  #[inline]
  fn get(self, slice: Src<[T]>) -> Src<Self::Output> {
    let RangeFull = self;
    Src::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Unbounded)
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<[T]>) -> WeakSrc<Self::Output> {
    let RangeFull = self;
    WeakSrc::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Unbounded)
  }
  
}

impl<T> SrcIndex<[T]> for RangeInclusive<usize> {
  
  type Output = [T];
  
  #[inline]
  fn get(self, slice: Src<[T]>) -> Src<Self::Output> {
    let (start, end) = self.into_inner();
    Src::into_slice_from_bounds(slice, Bound::Included(start), Bound::Included(end))
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<[T]>) -> WeakSrc<Self::Output> {
    let (start, end) = self.into_inner();
    WeakSrc::into_slice_from_bounds(slice, Bound::Included(start), Bound::Included(end))
  }
  
}

impl<T> SrcIndex<[T]> for RangeTo<usize> {
  
  type Output = [T];
  
  #[inline]
  fn get(self, slice: Src<[T]>) -> Src<Self::Output> {
    let RangeTo { end } = self;
    Src::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Excluded(end))
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<[T]>) -> WeakSrc<Self::Output> {
    let RangeTo { end } = self;
    WeakSrc::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Excluded(end))
  }
  
}

impl<T> SrcIndex<[T]> for RangeToInclusive<usize> {
  
  type Output = [T];
  
  #[inline]
  fn get(self, slice: Src<[T]>) -> Src<Self::Output> {
    let RangeToInclusive { end } = self;
    Src::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Included(end))
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<[T]>) -> WeakSrc<Self::Output> {
    let RangeToInclusive { end } = self;
    WeakSrc::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Included(end))
  }
  
}

impl SrcIndex<str> for (Bound<usize>, Bound<usize>) {
  
  type Output = str;
  
  #[inline]
  fn get(self, slice: Src<str>) -> Src<Self::Output> {
    let (start, end) = self;
    Src::into_slice_from_bounds(slice, start, end)
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<str>) -> WeakSrc<Self::Output> {
    let (start, end) = self;
    WeakSrc::into_slice_from_bounds(slice, start, end)
  }
  
}

impl SrcIndex<str> for Range<usize> {
  
  type Output = str;
  
  #[inline]
  fn get(self, slice: Src<str>) -> Src<Self::Output> {
    let Range { start, end } = self;
    Src::into_slice_from_bounds(slice, Bound::Included(start), Bound::Excluded(end))
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<str>) -> WeakSrc<Self::Output> {
    let Range { start, end } = self;
    WeakSrc::into_slice_from_bounds(slice, Bound::Included(start), Bound::Excluded(end))
  }
  
}

impl SrcIndex<str> for RangeFrom<usize> {
  
  type Output = str;
  
  #[inline]
  fn get(self, slice: Src<str>) -> Src<Self::Output> {
    let RangeFrom { start } = self;
    Src::into_slice_from_bounds(slice, Bound::Included(start), Bound::Unbounded)
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<str>) -> WeakSrc<Self::Output> {
    let RangeFrom { start } = self;
    WeakSrc::into_slice_from_bounds(slice, Bound::Included(start), Bound::Unbounded)
  }
  
}

impl SrcIndex<str> for RangeFull {
  
  type Output = str;
  
  #[inline]
  fn get(self, slice: Src<str>) -> Src<Self::Output> {
    let RangeFull = self;
    Src::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Unbounded)
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<str>) -> WeakSrc<Self::Output> {
    let RangeFull = self;
    WeakSrc::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Unbounded)
  }
  
}

impl SrcIndex<str> for RangeInclusive<usize> {
  
  type Output = str;
  
  #[inline]
  fn get(self, slice: Src<str>) -> Src<Self::Output> {
    let (start, end) = self.into_inner();
    Src::into_slice_from_bounds(slice, Bound::Included(start), Bound::Included(end))
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<str>) -> WeakSrc<Self::Output> {
    let (start, end) = self.into_inner();
    WeakSrc::into_slice_from_bounds(slice, Bound::Included(start), Bound::Included(end))
  }
  
}

impl SrcIndex<str> for RangeTo<usize> {
  
  type Output = str;
  
  #[inline]
  fn get(self, slice: Src<str>) -> Src<Self::Output> {
    let RangeTo { end } = self;
    Src::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Excluded(end))
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<str>) -> WeakSrc<Self::Output> {
    let RangeTo { end } = self;
    WeakSrc::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Excluded(end))
  }
  
}

impl SrcIndex<str> for RangeToInclusive<usize> {
  
  type Output = str;
  
  #[inline]
  fn get(self, slice: Src<str>) -> Src<Self::Output> {
    let RangeToInclusive { end } = self;
    Src::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Included(end))
  }
  
  #[inline]
  fn get_weak(self, slice: WeakSrc<str>) -> WeakSrc<Self::Output> {
    let RangeToInclusive { end } = self;
    WeakSrc::into_slice_from_bounds(slice, Bound::Unbounded, Bound::Included(end))
  }
  
}

/// A sealed trait to encode types that can can be used in the `Src`-family of pointers.
/// 
/// Either <code>Self: [Sized]</code> or <code>Self: [SrcSlice]</code>.
pub trait SrcTarget: private::SealedSrcTarget {
  
  /// The type of each element of a <code>[Src]\<Self></code>.
  /// * Where <code>Self: [Sized]</code>: `Self::Item = Self`
  /// * Where <code>Self = [\[T\]](prim@slice)</code>: `Self::Item = T`
  /// * Where <code>Self = [str]</code>: <code>Self::Item = [u8]</code>
  ///   (because a [`str`] is just a [`[u8]`](prim@slice) which must be UTF-8)
  type Item: Sized;
  
}

#[diagnostic::do_not_recommend]
impl<T> SrcTarget for T {
  
  type Item = T;
  
}

#[diagnostic::do_not_recommend]
impl<T> private::SealedSrcTarget for T {
  
  type Len = ();
  
  #[inline]
  fn len_as_usize((): Self::Len) -> usize {
    1
  }
  
  fn get(rc: &Src<Self>) -> &Self {
    // SAFETY:
    // all constructor fns of Src guarantee initialization of all elements
    unsafe { rc.start.as_ref() }
  }
  
  fn get_unique(rc: &UniqueSrc<Self>) -> &Self {
    // SAFETY:
    // all constructor fns of UniqueSrc guarantee initialization of all elements
    unsafe { rc.start.as_ref() }
  }
  
  fn get_unique_mut(rc: &mut UniqueSrc<Self>) -> &mut Self {
    // SAFETY:
    // all constructor fns of UniqueSrc guarantee initialization of all elements
    unsafe { rc.start.as_mut() }
  }
  
  #[inline]
  fn new_unique_from_clone(&self) -> UniqueSrc<Self> where <Self as SrcTarget>::Item: Clone {
    UniqueSrc::single(T::clone(self))
  }
  
}

impl<T> SrcTarget for [T] {
  
  type Item = T;
  
}

impl<T> private::SealedSrcTarget for [T] {
  
  type Len = usize;
  
  #[inline]
  fn len_as_usize(len: Self::Len) -> usize {
    len
  }
  
  fn get(rc: &Src<Self>) -> &Self {
    let start = rc.start.as_ptr().cast_const();
    let len = rc.len;
    // SAFETY:
    // * all constructor fns of Src guarantee initialization of all elements; if this is a sliced clone, Src::clone_from_bounds guarantees that start and len will still be valid
    unsafe { slice::from_raw_parts(start, len) }
  }
  
  fn get_unique(rc: &UniqueSrc<Self>) -> &Self {
    let start = rc.start.as_ptr().cast_const();
    let len = rc.len;
    // SAFETY:
    // * all constructor fns of Src guarantee initialization of all elements; if this is a sliced clone, Src::clone_from_bounds guarantees that start and len will still be valid
    unsafe { slice::from_raw_parts(start, len) }
  }
  
  fn get_unique_mut(rc: &mut UniqueSrc<Self>) -> &mut Self {
    let start = rc.start.as_ptr();
    let len = rc.len;
    // SAFETY:
    // * all constructor fns of Src guarantee initialization of all elements; if this is a sliced clone, Src::clone_from_bounds guarantees that start and len will still be valid
    unsafe { slice::from_raw_parts_mut(start, len) }
  }
  
  #[inline]
  fn new_unique_from_clone(&self) -> UniqueSrc<Self> where <Self as SrcTarget>::Item: Clone {
    UniqueSrc::cloned(self)
  }
  
}

impl SrcTarget for str {
  
  type Item = u8;
  
}

impl private::SealedSrcTarget for str {
  
  type Len = usize;
  
  #[inline]
  fn len_as_usize(len: Self::Len) -> usize {
    len
  }
  
  fn get(rc: &Src<Self>) -> &Self {
    let start = rc.start.as_ptr().cast_const();
    let len = rc.len;
    // SAFETY: all constructor fns of Src guarantee initialization of all elements (well, one of them unsafely passes that requirement on to the caller); if this is a sliced clone, Src::clone_from_bounds guarantees that start and len will still be valid
    let slice: &[u8] = unsafe { slice::from_raw_parts(start, len) };
    // SAFETY: all constructor fns of Src<str> guarantee the contents are UTF8
    unsafe { str::from_utf8_unchecked(slice) }
  }
  
  fn get_unique(rc: &UniqueSrc<Self>) -> &Self {
    let start = rc.start.as_ptr().cast_const();
    let len = rc.len;
    // SAFETY: all constructor fns of Src guarantee initialization of all elements (well, one of them unsafely passes that requirement on to the caller); if this is a sliced clone, Src::clone_from_bounds guarantees that start and len will still be valid
    let slice: &[u8] = unsafe { slice::from_raw_parts(start, len) };
    // SAFETY: all constructor fns of Src<str> guarantee the contents are UTF8
    unsafe { str::from_utf8_unchecked(slice) }
  }
  
  fn get_unique_mut(rc: &mut UniqueSrc<Self>) -> &mut Self {
    let start = rc.start.as_ptr();
    let len = rc.len;
    // SAFETY: all constructor fns of Src guarantee initialization of all elements (well, one of them unsafely passes that requirement on to the caller); if this is a sliced clone, Src::clone_from_bounds guarantees that start and len will still be valid
    let slice: &mut [u8] = unsafe { slice::from_raw_parts_mut(start, len) };
    // SAFETY: all constructor fns of Src<str> guarantee the contents are UTF8
    unsafe { str::from_utf8_unchecked_mut(slice) }
  }
  
  #[inline]
  fn new_unique_from_clone(&self) -> UniqueSrc<Self> {
    UniqueSrc::new(self)
  }
  
}

/// A sealed trait to encode the subset of [`SrcTarget`] that can contain multiple elements.
/// 
/// Either <code>Self = [\[T\]](prim@slice)</code> or <code>Self = [str]</code>.
pub trait SrcSlice: SrcTarget + private::SealedSrcSlice {}

impl<T> SrcSlice for [T] {}

impl<T> private::SealedSrcSlice for [T] {
  
  #[inline]
  fn validate_range(_this: &Src<Self>, _range: Range<usize>) {}
  
  #[inline]
  unsafe fn validate_range_weak(_this: &WeakSrc<Self>, _range: Range<usize>) {}
  
}

impl SrcSlice for str {}

impl private::SealedSrcSlice for str {
  
  fn validate_range(this: &Src<Self>, range: Range<usize>) {
    let s: &str = &**this;
    let _ = s[range]; // construct the slice just to trigger the appropriate errors if these indices are not at char boundaries
  }
  
  // SAFETY:
  // requires:
  // * that this is not dangling nor dropped
  unsafe fn validate_range_weak(this: &crate::WeakSrc<Self>, range: Range<usize>) where Self: crate::SrcSlice {
    // SAFETY:
    // * safety requirements passed onto the caller
    let s: &[u8] = unsafe { this.get_slice() };
    // SAFETY: all constructor fns of WeakSrc<str> guarantee the contents are UTF-8
    let s: &str = unsafe { str::from_utf8_unchecked(s) };
    let _ = s[range];
  }
  
}

mod private {
  
  use std::ops::Range;
  
  pub trait SealedSrcTarget {
    
    type Len: Copy + Default;
    
    fn len_as_usize(len: Self::Len) -> usize;
    
    fn get(rc: &super::Src<Self>) -> &Self where Self: super::SrcTarget;
    
    fn get_unique(rc: &super::UniqueSrc<Self>) -> &Self where Self: super::SrcTarget;
    
    fn get_unique_mut(rc: &mut super::UniqueSrc<Self>) -> &mut Self where Self: super::SrcTarget;
    
    fn new_unique_from_clone(&self) -> super::UniqueSrc<Self> where Self: super::SrcTarget, Self::Item: Clone;
    
  }
  
  pub trait SealedSrcSlice: SealedSrcTarget<Len = usize> {
    
    fn validate_range(this: &super::Src<Self>, range: Range<usize>) where Self: super::SrcSlice;
    
    // SAFETY:
    // requires:
    // * that this is not dangling nor dropped
    unsafe fn validate_range_weak(this: &super::WeakSrc<Self>, range: Range<usize>) where Self: super::SrcSlice;
    
  }
  
}
