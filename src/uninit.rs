use std::{fmt::{self, Debug, Formatter, Pointer}, marker::PhantomData, mem::forget, ptr::NonNull};

use crate::{inner::AllocUninit, InnerHeader, Src, SrcSlice, SrcTarget, UniqueSrc, WeakSrc};

/// `UninitSrc` is a version of [`Src`] that uniquely owns a new allocation before its body is initialized.
/// This is primarily used to construct self-referential data structures:
/// the [`downgrade`](UninitSrc::downgrade) method allows aquiring [weak references](WeakSrc) to this allocation before its body is initialized.
/// 
/// There are several helper methods for [`Src`] and [`UniqueSrc`] such as [`cyclic_from_fn`](Src::cyclic_from_fn) that may be simpler than `UninitSrc` for specific use cases.
/// 
/// `UninitSrc` pointers are always [root](crate#root)s,
/// because there is (at least at present) no way to track which elements are initialized and which are not,
/// and a non-[root](crate#root) `UninitSrc` would be useless if you couldn't initialize it.
/// 
/// Note that there is no way to construct or initialize an <code>UninitSrc\<[str]></code>;
/// however, as a [`str`] cannot contain a <code>[WeakSrc]\<[str]></code>, this type is useless with [`str`] anyway.
pub struct UninitSrc<T: SrcTarget + ?Sized> {
  
  // SAFETY:
  // requires:
  // * initialized from InnerHeader::new_inner::<T::Item>(_)
  pub(crate) header: NonNull<InnerHeader>,
  // SAFETY:
  // requires when T: SrcSlice:
  // * self.start.add(self.len) <= InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  // requires when T: Sized:
  // * self.start < InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  pub(crate) len: T::Len,
  pub(crate) _phantom: PhantomData<*const T>,
  
}

impl<T: SrcTarget + ?Sized> UninitSrc<T> {
  
  fn header(&self) -> &InnerHeader {
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    unsafe { InnerHeader::get_header(self.header) }
  }
  
  /// Creates a [root](crate#root) [`WeakSrc`] pointer to this allocation.
  /// 
  /// ```rust
  /// use slice_rc::{Src, UninitSrc, WeakSrc};
  /// 
  /// struct S {
  ///   
  ///   me: WeakSrc<S>,
  ///   
  /// }
  /// 
  /// let uninit = UninitSrc::single();
  /// let s = S { me: uninit.downgrade() };
  /// let s = uninit.init(s);
  /// assert!(Src::ptr_eq(&s, &s.me.upgrade().unwrap()));
  /// ```
  pub fn downgrade(&self) -> WeakSrc<T> {
    // safety note: the strong count is 0 until this UninitSrc is initialized into a Src, so the WeakSrc will never read or write from the body during the lifetime of the UninitSrc
    self.header().inc_weak_count();
    // SAFETY:
    // * all constructor fns for UninitSrc<T> initialize self.header from InnerHeader::new_inner::<T>
    // * the header is only accessed from InnerHeader::get_header
    let start = unsafe { InnerHeader::get_body_ptr::<T::Item>(self.header) };
    WeakSrc {
      // SAFETY: the safety invariant for self.header implies that of _.header
      header: self.header,
      // SAFETY: the start we just calculated meets the safety invariant by definition
      start,
      // SAFETY: the safety invariant for self.len implies tha tof _.len
      len: self.len,
      _phantom: PhantomData,
    }
  }
  
}

impl<T: SrcSlice + ?Sized> UninitSrc<T> {
  
  /// Returns the number of (uninitialized) elements in this `UninitSrc`.
  /// Because `UninitSrc` pointers are always [root](crate#root),
  /// this is also the total number of elements in this allocation.
  /// 
  /// ```rust
  /// use slice_rc::UninitSrc;
  /// 
  /// let uninit = UninitSrc::<[i32]>::new(3);
  /// assert_eq!(uninit.len(), 3);
  /// ```
  #[inline]
  pub fn len(&self) -> usize {
    self.len
  }
  
  /// Returns `true` if this `UninitSrc` has a length of `0`.
  /// 
  /// ```rust
  /// use slice_rc::UninitSrc;
  /// 
  /// let a = UninitSrc::<[i32]>::new(3);
  /// assert!(!a.is_empty());
  /// 
  /// let b = UninitSrc::<[i32]>::new(0);
  /// assert!(b.is_empty());
  /// ```
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }
  
}

impl<T: Sized> UninitSrc<T> {
  
  /// Constructs a new `UninitSrc` for a single value.
  /// 
  /// ```rust
  /// use slice_rc::{Src, UninitSrc};
  /// 
  /// let uninit = UninitSrc::<i32>::single();
  /// assert_eq!(uninit.as_slice().len(), 1);
  /// ```
  #[inline]
  pub fn single() -> UninitSrc<T> {
    let this = UninitSrc::<[T]>::new(1);
    debug_assert_eq!(this.len, 1);
    let this2 = UninitSrc {
      // SAFETY: the safety invariant of this.header is the same as this2.header
      header: this.header,
      // SAFETY: the safety invariant of this.len is implies that of this2.len
      len: (),
      _phantom: PhantomData,
    };
    forget(this);
    this2
  }
  
  /// Initializes this `UninitSrc` into an [`Src`] with the given value.
  /// 
  /// ```rust
  /// use slice_rc::{Src, UninitSrc};
  /// 
  /// let uninit = UninitSrc::single();
  /// let s: Src<_> = uninit.init(42);
  /// assert_eq!(*s, 42);
  /// assert_eq!(Src::root(&s).len(), 1);
  /// ```
  #[inline]
  pub fn init(self, value: T) -> Src<T> {
    UniqueSrc::into_shared(self.init_unique(value))
  }
  
  /// Initializes this `UninitSrc` into a [`UniqueSrc`] with the given value.
  /// 
  /// ```rust
  /// use slice_rc::{UninitSrc, UniqueSrc};
  /// 
  /// let uninit = UninitSrc::single();
  /// let s: UniqueSrc<_> = uninit.init_unique(42);
  /// assert_eq!(*s, 42);
  /// ```
  pub fn init_unique(self, value: T) -> UniqueSrc<T> {
    // SAFETY:
    // * all constructor fns for UninitSrc<T> initialize self.header from InnerHeader::new_inner::<T>
    // * the header is only accessed from InnerHeader::get_header
    let start = unsafe { InnerHeader::get_body_ptr::<T>(self.header) };
    // SAFETY: no one else has seen the body of the allocation (because the weaks only look at the header after the strong count has been initialized), so this write is okay
    unsafe { start.write(value); }
    let this = UniqueSrc {
      // SAFETY: the safety invariant of self.header implies that of this.header
      header: self.header,
      // SAFETY: after being initialized by start.write(_), the safety invariant of this.start is fulfilled by definition
      start,
      // SAFETY: the safety invariant of self.len implies that of this.len
      len: self.len,
      _phantom: PhantomData,
    };
    forget(self); // don't drop the weak held by the UninitSrc; it logically transfers to the Src
    this
  }
  
  /// Returns a `UninitSrc` equivalent to this one, but typed as a slice rather than a single element.
  /// The returned slice will have a length of `1`, and its element `0` will be at the same location in memory as `self`'s value.
  /// 
  /// ```rust
  /// use slice_rc::{UninitSrc, WeakSrc};
  /// 
  /// let single = UninitSrc::<i32>::single();
  /// let single_weak: WeakSrc<i32> = single.downgrade();
  /// let slice = single.as_slice();
  /// let slice_weak: WeakSrc<[i32]> = slice.downgrade();
  /// assert!(WeakSrc::ptr_eq(&single_weak, &slice_weak));
  /// ```
  #[inline]
  pub fn as_slice(self) -> UninitSrc<[T]> {
    let this = UninitSrc {
      // SAFETY: the safety invariant of self.header is the same as this.header
      header: self.header,
      // SAFETY: the safety invariant of self.len implies that of this.len
      len: 1,
      _phantom: PhantomData,
    };
    forget(self); // don't modify the weak count because this is logically the same UninitSrc
    this
  }
  
}

impl<T> UninitSrc<[T]> {
  
  /// Constructs a new `UninitSrc` for a slice of `len` values.
  /// 
  /// ```rust
  /// use slice_rc::UninitSrc;
  /// 
  /// let uninit = UninitSrc::<[i32]>::new(3);
  /// assert_eq!(uninit.len(), 3);
  /// ```
  #[inline]
  pub fn new(len: usize) -> UninitSrc<[T]> {
    let header = InnerHeader::new_inner::<T, AllocUninit>(len);
    Self {
      // SAFETY: the safety invariant of _.header is fulfilled by definition
      header,
      // SAFETY: the safety invariant of _.len is fulfilled by definition
      len,
      _phantom: PhantomData,
    }
  }
  
  /// Initializes this `UninitSrc` into an [`Src`] where each element is produced by calling `f` with that element's index while walking forward through the slice.
  /// 
  /// If `len == 0`, this produces an empty [`Src`] without ever calling `f`.
  /// 
  /// ```rust
  /// use slice_rc::UninitSrc;
  /// 
  /// let uninit = UninitSrc::new(5);
  /// let slice = uninit.init_from_fn(|i| i);
  /// assert_eq!(*slice, [0, 1, 2, 3, 4]);
  /// 
  /// let uninit2 = UninitSrc::new(8);
  /// let slice2 = uninit2.init_from_fn(|i| i * 2);
  /// assert_eq!(*slice2, [0, 2, 4, 6, 8, 10, 12, 14]);
  /// 
  /// let bool_uninit = UninitSrc::new(5);
  /// let bool_slice = bool_uninit.init_from_fn(|i| i % 2 == 0);
  /// assert_eq!(*bool_slice, [true, false, true, false, true]);
  /// ```
  /// 
  /// You can also capture things, so you can use closures with mutable state.
  /// The slice is generated in ascending index order, starting from the front and going towards the back.
  /// ```rust
  /// # use slice_rc::UninitSrc;
  /// let uninit = UninitSrc::new(6);
  /// let mut state = 1;
  /// let s = uninit.init_from_fn(|_| { let x = state; state *= 2; x });
  /// assert_eq!(*s, [1, 2, 4, 8, 16, 32]);
  /// ```
  /// 
  /// # Panics
  /// 
  /// Panics if `f` panics; in this event, any elements that have been initialized will be properly dropped.
  /// ```rust
  /// # use slice_rc::UninitSrc;
  /// # use std::cell::Cell;
  /// thread_local! {
  ///   static DROPPED: Cell<usize> = Cell::new(0);
  /// }
  /// 
  /// struct Droppable;
  /// 
  /// impl Drop for Droppable {
  ///   fn drop(&mut self) {
  ///     DROPPED.with(|dropped| dropped.update(|x| x + 1));
  ///   }
  /// }
  /// 
  /// let _ = std::panic::catch_unwind(move || {
  ///   let uninit = UninitSrc::new(10);
  ///   uninit.init_from_fn(|i| {
  ///     if i >= 5 { panic!() }
  ///     Droppable
  ///   })
  /// });
  /// 
  /// assert_eq!(DROPPED.get(), 5);
  /// ```
  #[inline]
  pub fn init_from_fn<F: FnMut(usize) -> T>(self, f: F) -> Src<[T]> {
    UniqueSrc::into_shared(self.init_unique_from_fn(f))
  }
  
  /// Initializes this `UninitSrc` into a [`UniqueSrc`] where each element is produced by calling `f` with that element's index while walking forward through the slice.
  /// 
  /// If `len == 0`, this produces an empty [`UniqueSrc`] without ever calling `f`.
  /// 
  /// ```rust
  /// use slice_rc::UninitSrc;
  /// 
  /// let uninit = UninitSrc::new(5);
  /// let slice = uninit.init_unique_from_fn(|i| i);
  /// assert_eq!(*slice, [0, 1, 2, 3, 4]);
  /// 
  /// let uninit2 = UninitSrc::new(8);
  /// let slice2 = uninit2.init_unique_from_fn(|i| i * 2);
  /// assert_eq!(*slice2, [0, 2, 4, 6, 8, 10, 12, 14]);
  /// 
  /// let bool_uninit = UninitSrc::new(5);
  /// let bool_slice = bool_uninit.init_unique_from_fn(|i| i % 2 == 0);
  /// assert_eq!(*bool_slice, [true, false, true, false, true]);
  /// ```
  /// 
  /// You can also capture things, so you can use closures with mutable state.
  /// The slice is generated in ascending index order, starting from the front and going towards the back.
  /// ```rust
  /// # use slice_rc::UninitSrc;
  /// let uninit = UninitSrc::new(6);
  /// let mut state = 1;
  /// let s = uninit.init_unique_from_fn(|_| { let x = state; state *= 2; x });
  /// assert_eq!(*s, [1, 2, 4, 8, 16, 32]);
  /// ```
  /// 
  /// # Panics
  /// 
  /// Panics if `f` panics; in this event, any elements that have been initialized will be properly dropped.
  /// ```rust
  /// # use slice_rc::UninitSrc;
  /// # use std::cell::Cell;
  /// thread_local! {
  ///   static DROPPED: Cell<usize> = Cell::new(0);
  /// }
  /// 
  /// struct Droppable;
  /// 
  /// impl Drop for Droppable {
  ///   fn drop(&mut self) {
  ///     DROPPED.with(|dropped| dropped.update(|x| x + 1));
  ///   }
  /// }
  /// 
  /// let _ = std::panic::catch_unwind(move || {
  ///   let uninit = UninitSrc::new(10);
  ///   uninit.init_unique_from_fn(|i| {
  ///     if i >= 5 { panic!() }
  ///     Droppable
  ///   })
  /// });
  /// 
  /// assert_eq!(DROPPED.get(), 5);
  /// ```
  pub fn init_unique_from_fn<F: FnMut(usize) -> T>(self, mut f: F) -> UniqueSrc<[T]> {
    let header = self.header();
    // SAFETY:
    // * all constructor fns for UninitSrc<T> initialize self.header from InnerHeader::new_inner::<T>
    // * the header is only accessed from InnerHeader::get_header
    let start = unsafe { InnerHeader::get_body_ptr::<T>(self.header) };
    let mut guard = PartialInitGuard::<T> { header: self.header, initialized: 0, _phantom: PhantomData };
    for i in 0..header.len() {
      // SAFETY:
      // * all constructor fns for UninitSrc<T> initialize self.header from InnerHeader::new_inner::<T>
      // * the header is only accessed from InnerHeader::get_header
      let ptr = unsafe { InnerHeader::get_elem_ptr::<T>(self.header, i) };
      let val = f(i);
      // SAFETY: no one else has seen the body of the allocation (because the weaks only look at the header after the strong count has been initialized), so this write is okay
      unsafe { ptr.write(val) };
      guard.initialized += 1;
    }
    // if all elements are successfully initialized, then forget the drop guard; in other words, the guard only drops the contents if a panic occurs part way through initialization
    forget(guard);
    let this = UniqueSrc {
      // SAFETY: the safety invariant of self.header is the same as this.header
      header: self.header,
      // SAFETY: after a successful initialization, the safety invariant of this.start is fulfilled by definition
      start,
      // SAFETY: the safety invariant of self.len is the same as this.len
      len: self.len,
      _phantom: PhantomData,
    };
    forget(self); // don't drop the weak held by the UninitSrc; it logically transfers to the Src
    this
  }
  
  /// Initializes this `UninitSrc` into an [`Src`] where each element is the type's [default](Default::default).
  /// 
  /// This method is essentially equivalent to <code>self.[init_from_fn](UninitSrc::init_from_fn)(|_| [Default::default]\())</code>.
  #[inline]
  pub fn init_from_default(self) -> Src<[T]> where T: Default {
    self.init_from_fn(|_| T::default())
  }
  
  /// Initializes this `UninitSrc` into a [`UniqueSrc`] where each element is the type's [default](Default::default).
  /// 
  /// This method is essentially equivalent to <code>self.[init_unique_from_fn](UninitSrc::init_unique_from_fn)(|_| [Default::default]\())</code>.
  #[inline]
  pub fn init_unique_from_default(self) -> UniqueSrc<[T]> where T: Default {
    self.init_unique_from_fn(|_| T::default())
  }
  
  /// Initializes this `UninitSrc` into an [`Src`] where each element is a clone of `value`.
  /// 
  /// This method is essentially equivalent to <code>self.[init_from_fn](UninitSrc::init_from_fn)(|_| value.[Clone::clone]\())</code>.
  #[inline]
  pub fn init_filled(self, value: &T) -> Src<[T]> where T: Clone {
    self.init_from_fn(|_| value.clone())
  }
  
  /// Initializes this `UninitSrc` into an [`UniqueSrc`] where each element is a clone of `value`.
  /// 
  /// This method is essentially equivalent to <code>self.[init_unique_from_fn](UninitSrc::init_unique_from_fn)(|_| value.[Clone::clone]\())</code>.
  #[inline]
  pub fn init_unique_filled(self, value: &T) -> UniqueSrc<[T]> where T: Clone {
    self.init_unique_from_fn(|_| value.clone())
  }
  
}

impl<T: SrcTarget + ?Sized> Debug for UninitSrc<T> {
  
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "(UninitSrc)")
  }
  
}

impl<T: SrcTarget + ?Sized> Pointer for UninitSrc<T> {
  
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    // NOTE: the body is not expected to be initialized, but it is also not used
    let start = unsafe { InnerHeader::get_body_ptr::<T::Item>(self.header) };
    Pointer::fmt(&start, f)
  }
  
}

impl<T: SrcTarget + ?Sized> Drop for UninitSrc<T> {
  
  fn drop(&mut self) {
    // SAFETY:
    // * all constructor fns for UninitSrc initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    // NOTE: the UninitSrc logically holds one weak reference
    unsafe { InnerHeader::drop_weak::<T::Item>(self.header); }
  }
  
}

struct PartialInitGuard<T> {
  
  header: NonNull<InnerHeader>,
  initialized: usize,
  _phantom: PhantomData<*const T>,
  
}

impl<T> Drop for PartialInitGuard<T> {
  
  fn drop(&mut self) {
    // SAFETY:
    // * by the contract of this type, self.header is from an initialization fn from UninitSrc; all constructor fns for UninitSrc<T> initialize self.header from InnerHeader::new_inner::<T>
    // * by the contract of this type, the first self.initialized elements have been initialized
    // * the header is only accessed from InnerHeader::get_header
    // * by the contract of this type, self.header is from an initialization fn from UninitSrc that is panicking; therefore, no one else has seen or will see the body
    unsafe { InnerHeader::drop_body_up_to::<T>(self.header, self.initialized); }
  }
  
}

#[cfg(test)]
mod tests {
  
  use std::{cell::Cell, ops::Deref, panic::{catch_unwind, AssertUnwindSafe}};
  use crate::*;
  
  #[test]
  fn downgrade() {
    let u: UninitSrc<[u8]> = UninitSrc::new(3);
    let w: WeakSrc<[u8]> = u.downgrade();
    assert!(w.upgrade().is_none());
    let s1: Src<[u8]> = u.init_from_default();
    let s2: Src<[u8]> = w.upgrade().unwrap();
    assert_eq!(s1, s2);
    assert!(Src::ptr_eq(&s1, &s2));
  }
  
  #[test]
  fn len() {
    let u: UninitSrc<[u8]> = UninitSrc::new(0);
    assert_eq!(u.len(), 0);
    let u: UninitSrc<[u8]> = UninitSrc::new(1);
    assert_eq!(u.len(), 1);
    let u: UninitSrc<[u8]> = UninitSrc::new(17);
    assert_eq!(u.len(), 17);
  }
  
  #[test]
  fn is_empty() {
    let u: UninitSrc<[u8]> = UninitSrc::new(0);
    assert!(u.is_empty());
    let u: UninitSrc<[u8]> = UninitSrc::new(1);
    assert!(!u.is_empty());
    let u: UninitSrc<[u8]> = UninitSrc::new(17);
    assert!(!u.is_empty());
  }
  
  #[test]
  fn single() {
    let u: UninitSrc<u8> = UninitSrc::single();
    let s: Src<u8> = u.init(42);
    assert!(Src::is_root(&s));
    let s: Src<[u8]> = Src::as_slice(&s);
    assert_eq!(s.len(), 1);
  }
  
  #[test]
  fn init() {
    let u: UninitSrc<u8> = UninitSrc::single();
    let s: Src<u8> = u.init(42);
    assert_eq!(*s, 42);
  }
  
  #[test]
  fn init_unique() {
    let u: UninitSrc<u8> = UninitSrc::single();
    let u: UniqueSrc<u8> = u.init_unique(42);
    assert_eq!(*u, 42);
  }
  
  #[test]
  fn as_slice() {
    let u: UninitSrc<u8> = UninitSrc::single();
    let u: UninitSrc<[u8]> = u.as_slice();
    assert_eq!(u.len(), 1);
  }
  
  #[test]
  fn new() {
    let u: UninitSrc<[u8]> = UninitSrc::new(3);
    let s: Src<[u8]> = u.init_from_fn(|i| i as _);
    assert!(Src::is_root(&s));
    assert_eq!(s.len(), 3);
  }
  
  #[test]
  fn init_from_fn() {
    { // normal
      let u: UninitSrc<[u8]> = UninitSrc::new(3);
      let s: Src<[u8]> = u.init_from_fn(|i| i as _);
      assert_eq!(*s, [0, 1, 2]);
    }
    { // panic
      let drop_flags: [_; 6] = std::array::from_fn(|_| AssertUnwindSafe(Cell::new(false)));
      struct DropFlagger<'a>(&'a Cell<bool>);
      impl Drop for DropFlagger<'_> {
        
        fn drop(&mut self) {
          self.0.update(|v| !v)
        }
        
      }
      let _: Result<_, _> = catch_unwind(|| {
        let u: UninitSrc<[DropFlagger<'_>]> = UninitSrc::new(drop_flags.len());
        let _: Src<[DropFlagger<'_>]> = u.init_from_fn(|i| {
          if i >= 3 { panic!() }
          DropFlagger(&drop_flags[i])
        });
      });
      assert!(drop_flags[..3].iter().map(Deref::deref).all(Cell::get));
      assert!(!drop_flags[3..].iter().map(Deref::deref).any(Cell::get));
    }
  }
  
  #[test]
  fn init_unique_from_fn() {
    { // normal
      let u: UninitSrc<[u8]> = UninitSrc::new(3);
      let u: UniqueSrc<[u8]> = u.init_unique_from_fn(|i| i as _);
      assert_eq!(*u, [0, 1, 2]);
    }
    { // panic
      let drop_flags: [_; 6] = std::array::from_fn(|_| AssertUnwindSafe(Cell::new(false)));
      struct DropFlagger<'a>(&'a Cell<bool>);
      impl Drop for DropFlagger<'_> {
        
        fn drop(&mut self) {
          self.0.update(|v| !v)
        }
        
      }
      let _: Result<_, _> = catch_unwind(|| {
        let u: UninitSrc<[DropFlagger<'_>]> = UninitSrc::new(drop_flags.len());
        let _: UniqueSrc<[DropFlagger<'_>]> = u.init_unique_from_fn(|i| {
          if i >= 3 { panic!() }
          DropFlagger(&drop_flags[i])
        });
      });
      assert!(drop_flags[..3].iter().map(Deref::deref).all(Cell::get));
      assert!(!drop_flags[3..].iter().map(Deref::deref).any(Cell::get));
    }
  }
  
  #[test]
  fn init_from_default() {
    let u: UninitSrc<[u8]> = UninitSrc::new(3);
    let s: Src<[u8]> = u.init_from_default();
    assert_eq!(*s, [0, 0, 0]);
  }
  
  #[test]
  fn init_unique_from_default() {
    let u: UninitSrc<[u8]> = UninitSrc::new(3);
    let u: UniqueSrc<[u8]> = u.init_unique_from_default();
    assert_eq!(*u, [0, 0, 0]);
  }
  
  #[test]
  fn init_filled() {
    let u: UninitSrc<[u8]> = UninitSrc::new(3);
    let s: Src<[u8]> = u.init_filled(&42);
    assert_eq!(*s, [42, 42, 42]);
  }
  
  #[test]
  fn init_unique_filled() {
    let u: UninitSrc<[u8]> = UninitSrc::new(3);
    let u: UniqueSrc<[u8]> = u.init_unique_filled(&42);
    assert_eq!(*u, [42, 42, 42]);
  }
  
  #[test]
  fn drop() {
    let u: UninitSrc<[u8]> = UninitSrc::new(3);
    let w: WeakSrc<[u8]> = u.downgrade();
    assert!(w.upgrade().is_none());
    std::mem::drop(u);
    assert!(w.upgrade().is_none());
  }
  
}
