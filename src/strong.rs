use std::{borrow::Borrow, cmp::Ordering, fmt::{self, Debug, Formatter, Pointer}, hash::{Hash, Hasher}, marker::PhantomData, mem::{forget, MaybeUninit}, ops::{Bound, Deref, Index}, ptr::NonNull, str::Utf8Error};

use crate::{InnerHeader, SrcIndex, SrcSlice, SrcTarget, UninitSrc, UniqueSrc, WeakSrc};

/// A single-threaded sliceable reference-counting pointer. 'Src' stands for 'Slice Reference Counted'. 
/// 
/// See [`std::rc`] for details about general reference-counting pointers.
/// 
/// `Src` is a variation on [`Rc`](std::rc::Rc); the functionality that differentiates them can be accessed with the method [`Src::slice`].
/// 
/// Many of the inherent methods of `Src` are associated functions, which means that you have to call them as e.g.,
/// [`Src::downgrade(&value)`](Src::downgrade) instead of `value.downgrade()`;
/// this avoids conflicts with methods of the inner type `T`.
/// However, some methods, e.g. [`Src::slice`], are permitted to remain as methods because the inner type is known not to have a conflicting method,
/// and some, e.g. [`Src::len`], intentionally shadow a known method of the inner type because they use a more efficient computation for the same result.
pub struct Src<T: SrcTarget + ?Sized> {
  
  // SAFETY:
  // requires:
  // * initialized from InnerHeader::new_inner::<T::Item>(_)
  pub(crate) header: NonNull<InnerHeader>,
  // SAFETY:
  // requires:
  // * initialized from either InnerHeader::get_body_ptr::<T::Item>(self.header) or InnerHeader::get_elem_ptr::<T::Item>(self.header, i) where 0 <= i <= InnerHeader::get_header(self.header).len()
  // * all body elements have been properly initialized (e.g., self.start.as_ref() will not cause UB)
  pub(crate) start: NonNull<T::Item>,
  // SAFETY:
  // requires when T: SrcSlice:
  // * self.start.add(self.len) <= InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  // requires when T: Sized:
  // * self.start < InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  pub(crate) len: T::Len,
  pub(crate) _phantom: PhantomData<*const T>,
  
}

impl<T: SrcTarget + ?Sized> Src<T> {
  
  fn header(&self) -> &InnerHeader {
    // SAFETY:
    // * the invariant for self.header guarantees that it is from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    unsafe { InnerHeader::get_header(self.header) }
  }
  
  /// Returns `true` if the two `Src`s point to slices starting at the same location in memory, akin to [`ptr::eq`](std::ptr::eq).
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let slice = Src::from_array([1, 2, 3]);
  /// let same_slice = Src::clone(&slice);
  /// let sub_slice = slice.slice(1..);
  /// let other_slice = Src::from_array([1, 2, 3]);
  /// 
  /// assert!(Src::ptr_eq(&slice, &same_slice));
  /// assert!(!Src::ptr_eq(&slice, &sub_slice));
  /// assert!(!Src::ptr_eq(&slice, &other_slice));
  /// ```
  /// 
  /// If `Src::ptr_eq(&a, &b)` returns true, then <code>Src::[same_root](Src::same_root)(&a, &b)</code> will also be true.
  /// 
  /// The type parameter, `U`, is to allow `Src`s of different types that _could_ be of the same allocation, and therefore, _could_ be equal by pointer, to be compared, e.g.:
  /// ```rust
  /// # use slice_rc::Src;
  /// let single: Src<i32> = Src::single(4);
  /// let slice: Src<[i32]> = Src::as_slice(&single);
  /// 
  /// assert!(Src::ptr_eq(&single, &slice));
  /// ```
  /// 
  /// Note that this method currently ignores the length of the slice:
  /// ```rust
  /// # use slice_rc::Src;
  /// let root = Src::from_array([1, 2, 3]);
  /// let first = root.slice(0);
  /// 
  /// assert!(Src::ptr_eq(&root, &first));
  /// 
  /// let mid_to_end_slice = root.slice(1..);
  /// let mid_slice = root.slice(1..=1);
  /// 
  /// assert!(Src::ptr_eq(&mid_to_end_slice, &mid_slice));
  /// ```
  /// It is undecided whether this behavior is desireable, and as such, it may change;
  /// notably, [`Rc::ptr_eq`](std::rc::Rc::ptr_eq) does ignore metadata for `?Sized` types
  /// (though that's irrelevant for slices because [`Rc`]s can only point to the whole slice, and therefore the length will always be the same for [`Rc`]s that point to the same allocation),
  /// while [`ptr::eq`](std::ptr::eq) does consider the metadata (which causes inconsistent results for trait objects, but that is irrelevant here because `Src`s don't support trait objects).
  /// 
  /// See also [`Src::same_root`].
  /// 
  /// [`Rc`]: std::rc::Rc
  #[inline]
  pub fn ptr_eq<U: SrcTarget<Item = T::Item> + ?Sized>(this: &Src<T>, other: &Src<U>) -> bool {
    this.start == other.start
  }
  
  /// Returns `true` if the two `Src`s share the same [root](crate#root) (i.e., they point to parts of the same allocation).
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let slice = Src::from_array([1, 2, 3]);
  /// let same_slice = Src::clone(&slice);
  /// let other_slice = Src::from_array([1, 2, 3]);
  /// 
  /// assert!(Src::same_root(&slice, &same_slice));
  /// assert!(!Src::same_root(&slice, &other_slice));
  /// ```
  /// 
  /// Notably, neither slice has to be the root, nor do they need to overlap at all:
  /// ```rust
  /// # use slice_rc::Src;
  /// let root = Src::from_array([1, 2, 3]);
  /// let a = root.slice(..1);
  /// let b = root.slice(2..);
  /// 
  /// assert!(Src::same_root(&a, &b));
  /// ```
  /// 
  /// The type parameter, `U`, is to allow `Src`s of different types that _could_ share the same root, to be compared, e.g.:
  /// ```rust
  /// # use slice_rc::Src;
  /// let single: Src<i32> = Src::single(4);
  /// let slice: Src<[i32]> = Src::as_slice(&single);
  /// 
  /// assert!(Src::same_root(&single, &slice));
  /// ```
  /// 
  /// This method ignores the length of the slices in question, but unlike [`Src::ptr_eq`], this will not change,
  /// as the roots remains the same regardless of which parts of it are included in these slices.
  /// 
  /// See also [`Src::ptr_eq`], [`Src::is_root`], and [`Src::root`].
  #[inline]
  pub fn same_root<U: SrcTarget<Item = T::Item> + ?Sized>(this: &Src<T>, other: &Src<U>) -> bool {
    this.header == other.header
  }
  
  /// Returns `true` if this `Src` contains its [root](crate#root) (i.e., it references its entire allocation).
  /// Notably, this `Src` does not have to be the first one that was initialized, it just has to cover the entire allocation.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let root = Src::from_array([1, 2, 3]);
  /// let also_root = root.slice(..);
  /// let slice = root.slice(1..);
  /// 
  /// assert!(Src::is_root(&root));
  /// assert!(Src::is_root(&also_root));
  /// assert!(!Src::is_root(&slice));
  /// ```
  /// 
  /// See also [`Src::same_root`] and [`Src::root`].
  #[inline]
  pub fn is_root(this: &Src<T>) -> bool {
    // SAFETY:
    // * the invariant for this.header guarantees that it is from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    let root_start = unsafe { InnerHeader::get_body_ptr(this.header) };
    this.start == root_start && T::len_as_usize(this.len) == this.header().len()
  }
  
  /// Creates a [`WeakSrc`] pointer to this slice.
  /// The [`WeakSrc`] refers to the same slice as this `Src`, and therefore, refers to the [root](crate#root) if and only if this `Src` does.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let root = Src::from_array([1, 2, 3]);
  /// 
  /// let weak_root = Src::downgrade(&root);
  /// ```
  pub fn downgrade(this: &Src<T>) -> WeakSrc<T> {
    this.header().inc_weak_count();
    WeakSrc {
      // SAFETY: this.header's invariant implies _.header's invariant
      header: this.header,
      // SAFETY: this.header's invariant implies _.header's invariant
      start: this.start,
      // SAFETY: this.header's invariant implies _.header's invariant
      len: this.len,
      _phantom: PhantomData,
    }
  }
  
  /// Gets the number of strong (`Src`) pointers to any part of this allocation.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let root = Src::from_array([1, 2, 3]);
  /// let _slice = root.slice(1..);
  /// 
  /// assert_eq!(2, Src::strong_count(&root));
  /// ```
  pub fn strong_count(this: &Src<T>) -> usize {
    this.header().strong_count()
  }
  
  /// Gets the number of [`WeakSrc`] pointers to any part of this allocation.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let root = Src::from_array([1, 2, 3]);
  /// let slice = root.slice(1..);
  /// let _weak_slice = Src::downgrade(&slice);
  /// 
  /// assert_eq!(1, Src::weak_count(&root));
  /// ```
  pub fn weak_count(this: &Src<T>) -> usize {
    this.header().weak_count() - 1
  }
  
  /// Turns this `Src` into a [`UniqueSrc`], if it has only one strong reference.
  /// 
  /// Otherwise, an [`Err`] is returned withe the same `Src` that was passed in.
  /// 
  /// This will succeed even if there are outstanding weak references,
  /// though those references will not be able to [`upgrade`](WeakSrc::upgrade) while this allocation is managed by a [`UniqueSrc`].
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let x = Src::single(3);
  /// assert_eq!(*Src::into_unique(x).unwrap(), 3);
  /// 
  /// let x = Src::single(4);
  /// let _y = Src::clone(&x);
  /// assert_eq!(*Src::into_unique(x).unwrap_err(), 4);
  /// ```
  /// 
  /// See also [`Src::make_unique`].
  /// 
  /// Note that this method (and [`Src::make_unique`]) can currently be used to construct non-[root](crate#root) [`UniqueSrc`]s;
  /// this behavior has not been thouroghly considered and may be changed or removed in the future.
  /// As it is, the [`UniqueSrc`] will retain unique ownership of the whole allocation, even the parts it doesn't contain.
  /// This means that a [`WeakSrc`] to any part of the allocation will not be able to [`upgrade`](WeakSrc::upgrade),
  /// even if that [`WeakSrc`] does not overlap with the [`UniqueSrc`].
  pub fn into_unique(this: Src<T>) -> Result<UniqueSrc<T>, Src<T>> {
    let header = this.header();
    if header.strong_count() == 1 {
      // decrease the strong count to 0, but don't drop;
      // obviously, the UniqueSrc still needs the body to exist, so it shouldn't be dropped,
      // but the strong count should be 0 so that the weak references can't upgrade (because that Src would be an alias of the UniqueSrc, which violates UniqueSrc's invariant)
      header.dec_strong_count();
      let this2 = UniqueSrc {
        // SAFETY: this.header has the same safety invariant as this2.header, in addition to the requirement that no other strong Src has access to this allocation, which is checked by header.strong_count() == 1
        header: this.header,
        // SAFETY: this.start has the same safety invariant as this2.start
        start: this.start,
        // SAFETY: this.len has the same safety invariant as this2.len
        len: this.len,
        _phantom: PhantomData,
      };
      forget(this); // as stated above, don't drop; additionally, now that the strong count has already been set to 0, dropping this would actually cause a panic on debug and probably big problems on release because it would cause integer overflow
      Ok(this2)
    } else {
      Err(this)
    }
  }
  
  /// If this is the only strong reference to this allocation, then it is turned into a [`UniqueSrc`].
  /// Otherwise, the contents are cloned and return in a new [`UniqueSrc`].
  /// 
  /// This is somewhat like [`Rc::make_mut`](std::rc::Rc::make_mut), but with some subtle differences.
  /// 
  /// ```rust
  /// use slice_rc::{Src, UniqueSrc};
  /// 
  /// let data = Src::single(5);
  /// let mut data = Src::make_unique(data);             // Won't clone anything
  /// *data += 1;
  /// let data = UniqueSrc::into_shared(data);
  /// let other_data = Src::clone(&data);                // Won't clone inner data
  /// let mut data = Src::make_unique(data);             // Clones inner data
  /// *data += 1;
  /// let data = UniqueSrc::into_shared(data);
  /// let mut data = Src::make_unique(data);             // Won't clone anything
  /// *data += 1;
  /// let data = UniqueSrc::into_shared(data);
  /// let mut other_data = Src::make_unique(other_data); // Won't clone anything
  /// *other_data *= 2;
  /// let other_data = UniqueSrc::into_shared(other_data);
  /// 
  /// // Now `data` and `other_data` point to different allocations.
  /// assert_eq!(*data, 8);
  /// assert_eq!(*other_data, 12);
  /// ```
  /// 
  /// If this is the only `Src` pointer to this allocation,
  /// but there are some [`WeakSrc`] pointers, then the [`WeakSrc`] pointers will be carried over to the [`UniqueSrc`].
  /// ```rust
  /// # use slice_rc::{Src, UniqueSrc};
  /// let data = Src::single(75);
  /// let weak = Src::downgrade(&data);
  /// 
  /// assert_eq!(75, *data);
  /// assert_eq!(75, *weak.upgrade().unwrap());
  /// 
  /// let mut data = Src::make_unique(data);
  /// *data += 1;
  /// 
  /// assert_eq!(76, *data);
  /// assert!(weak.upgrade().is_none());
  /// 
  /// let data = UniqueSrc::into_shared(data);
  /// 
  /// assert_eq!(76, *data);
  /// assert_eq!(76, *weak.upgrade().unwrap());
  /// ```
  /// However, if there are other `Src` pointers to this allocation, any [`WeakSrc`] pointers will remain with the old allocation.
  /// ```rust
  /// # use slice_rc::{Src, UniqueSrc};
  /// let data = Src::single(75);
  /// let other_data = Src::clone(&data);
  /// let weak = Src::downgrade(&data);
  /// 
  /// assert_eq!(75, *data);
  /// assert_eq!(75, *other_data);
  /// assert_eq!(75, *weak.upgrade().unwrap());
  /// 
  /// let mut data = Src::make_unique(data);
  /// *data += 1;
  /// 
  /// assert_eq!(76, *data);
  /// assert_eq!(75, *other_data);
  /// assert_eq!(75, *weak.upgrade().unwrap());
  /// 
  /// let data = UniqueSrc::into_shared(data);
  /// 
  /// assert_eq!(76, *data);
  /// assert_eq!(75, *other_data);
  /// assert_eq!(75, *weak.upgrade().unwrap());
  /// ```
  /// 
  /// See also [`Src::into_unique`].
  /// 
  /// Note that this method (and [`Src::into_unique`]) can currently be used to construct non-[root](crate#root) [`UniqueSrc`]s;
  /// this behavior has not been thouroghly considered and may be changed or removed in the future.
  /// As it is, the [`UniqueSrc`] will retain unique ownership of the whole allocation, even the parts it doesn't contain.
  /// This means that a [`WeakSrc`] to any part of the allocation will not be able to [`upgrade`](WeakSrc::upgrade),
  /// even if that [`WeakSrc`] does not overlap with the [`UniqueSrc`].
  pub fn make_unique(this: Src<T>) -> UniqueSrc<T> where T::Item: Clone {
    Src::into_unique(this).unwrap_or_else(|this| T::new_unique_from_clone(&*this))
  }
  
  /// Returns an `Src` pointer that refers to this `Src`'s [root](crate#root) (i.e., the entire allocation).
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let root = Src::from_array([1, 2, 3]);
  /// let slice = root.slice(1..);
  /// drop(root);
  /// 
  /// assert_eq!(*slice, [2, 3]);
  /// 
  /// let new_root = Src::root(&slice);
  /// 
  /// assert_eq!(*new_root, [1, 2, 3]);
  /// ```
  /// 
  /// This method returns an <code>[Src]\<\[T::[Item](crate::SrcTarget::Item)]></code> rather than an <code>[Src]\<T></code> for two reasons:
  /// * If <code>T: [Sized]</code>, then the root can only be a <code>[Src]\<T></code> if its total length is is `1`, which would prevent situations like this:
  /// ```rust
  /// # use slice_rc::Src;
  /// let root: Src<[i32]> = Src::from_array([1, 2, 3]);
  /// let slice: Src<i32> = root.slice(1);
  /// let new_root: Src<[i32]> = Src::root(&slice);
  /// 
  /// assert_eq!(*new_root, [1, 2, 3]);
  /// ```
  /// * If <code>T = [str]</code>, it could be a UTF-8 slice of a larger allocation that is not entirely UTF-8, which would violate the safety invariant of [`str`]:
  /// ```rust
  /// # use slice_rc::Src;
  /// let root: Src<[u8]> = Src::copied(b"\xFFhello");
  /// let s: Src<str> = Src::from_utf8(root.slice(1..)).unwrap();
  /// let new_root: Src<[u8]> = Src::root(&s);
  /// 
  /// assert_eq!(&*s, "hello");
  /// assert!(Src::from_utf8(new_root).is_err());
  /// ```
  pub fn root(this: &Src<T>) -> Src<[T::Item]> {
    let header = this.header();
    // SAFETY:
    // * the invariant for self.header guarantees that it is from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    let start = unsafe { InnerHeader::get_body_ptr::<T::Item>(this.header) };
    header.inc_strong_count();
    Src {
      // SAFETY: self.header has the same safety invariant as this.header
      header: this.header,
      // SAFETY: start was just aquired from InnerHeader::get_body_ptr::<T::Item>(self.header), which, with the assertions, meets the safety requirement
      start,
      // SAFETY: header.len() meets the safety requirements by definition
      len: header.len(),
      _phantom: PhantomData,
    }
  }
  
}

impl<T: SrcSlice + ?Sized> Src<T> {
  
  /// Constructs a new [root](crate#root) `Src` of length `0`.
  /// Note that, because `Src`s are not growable like [`Vec`]s are, this allocation will never become larger.
  /// Every reference to this allocation is a [root](crate#root).
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let s = Src::<[i32]>::empty();
  /// 
  /// assert_eq!(s.len(), 0);
  /// ```
  #[inline]
  pub fn empty() -> Src<T> {
    UniqueSrc::into_shared(UniqueSrc::empty())
  }
  
  /// Returns the number of elements in this `Src`.
  /// This method deliberately shadows [`<[T]>::len`](slice::len) and [`str::len`] because this method provides a (slightly) simpler and more efficient implementation.
  /// 
  /// This method only returns the length of the whole allocation if `self` is a [root](crate#root) `Src`.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let s = Src::from_array([1, 2, 3]);
  /// assert_eq!(s.len(), 3);
  /// ```
  #[inline]
  pub fn len(&self) -> usize {
    self.len
  }
  
  /// Returns `true` if this `Src` has a length of `0`.
  /// This method deliberately shadows [`<[T]>::is_empty`](slice::is_empty) and [`str::is_empty`] because this method provides a (slightly) simpler and more efficient implementation.
  /// 
  /// Note that this method does not imply that this `Src` was constructed via [`Src::empty`].
  /// Similarly, it does not imply that the entire allocation is empty, unless `self` is a [root](crate#root) `Src`.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let a = Src::from_array([1, 2, 3]);
  /// assert!(!a.is_empty());
  /// 
  /// let b = Src::<[i32]>::from_array([]);
  /// assert!(b.is_empty());
  /// ```
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }
  
  /// Returns an `Src` pointer to an element or subslice depending on the type of index.
  /// * If given a position (only applicable where `Self = Src<[U]>`), returns an `Src<U>` to the element at that position.
  /// * If given a range, returns the subslice corresponding to that range.
  /// 
  /// # Panics
  /// If the index is in some way out of bounds, or if <code>Self = [Src]\<[str]></code> and the indices are not at [char boundaries](str::is_char_boundary).
  /// 
  /// # Examples
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let v = Src::from_array([10, 40, 30]);
  /// assert_eq!(Src::single(40), v.slice(1));
  /// assert_eq!(Src::from_array([10, 40]), v.slice(0..2));
  /// ```
  /// Panics:
  /// ```should_panic
  /// # use slice_rc::Src;
  /// let v = Src::from_array([10, 40, 30]);
  /// let _ = v.slice(3);
  /// let _ = v.slice(0..4);
  /// ```
  #[inline]
  pub fn slice<I: SrcIndex<T>>(&self, index: I) -> Src<I::Output> {
    index.get(self.clone())
  }
  
  pub(crate) fn into_item(self, index: usize) -> Src<T::Item> {
    let header = self.header();
    assert!(index < header.len(), "index {index} out of range for slice of length {}", header.len());
    // SAFETY: the safety invariant of self.start implies this safety requirement, given the assertion that index <= header.len()
    let start_ptr = unsafe { self.start.add(index) };
    let this = Src {
      // SAFETY: self.header has the same safety invariant as this.header
      header: self.header,
      // SAFETY: start_ptr was just aquired from InnerHeader::get_elem_ptr::<T::Item>(self.header, start_inc), which, with the assertions, meets the safety requirement
      start: start_ptr,
      // SAFETY: the assertions guarantee the safety requirements
      len: (),
      _phantom: PhantomData,
    };
    forget(self); // don't modify the strong count because this is logically the same Src
    this
  }
  
  pub(crate) fn into_slice_from_bounds(self, start: Bound<usize>, end: Bound<usize>) -> Src<T> {
    let header = self.header();
    let start_inc = match start {
      Bound::Excluded(val) => val + 1,
      Bound::Included(val) => val,
      Bound::Unbounded => 0,
    };
    let end_exc = match end {
      Bound::Excluded(val) => val,
      Bound::Included(val) => val + 1,
      Bound::Unbounded => header.len(),
    };
    assert!(start_inc <= end_exc, "slice index starts at {start_inc} but ends at {end_exc}");
    assert!(end_exc <= header.len(), "range end index {end_exc} out of range for slice of length {}", header.len());
    T::validate_range(&self, start_inc..end_exc);
    let len = end_exc - start_inc;
    // SAFETY: the safety invariant of self.start implies this safety requirement, given the assertion that start_inc <= header.len()
    let start_ptr = unsafe { self.start.add(start_inc) };
    let this = Src {
      // SAFETY: self.header has the same safety invariant as this.header
      header: self.header,
      // SAFETY: start_ptr was just aquired from InnerHeader::get_elem_ptr::<T::Item>(self.header, start_inc), which, with the assertions, meets the safety requirement
      start: start_ptr,
      // SAFETY: the assertions guarantee the safety requirements
      len,
      _phantom: PhantomData,
    };
    forget(self); // don't modify the strong count because this is logically the same Src
    this
  }
  
}

impl<T: Sized> Src<T> {
  
  /// Constructs a new [root](crate#root) `Src` that contains only the given value.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let s = Src::single(42);
  /// assert_eq!(*s, 42);
  /// assert_eq!(Src::root(&s).len(), 1);
  /// ```
  #[inline]
  pub fn single(value: T) -> Src<T> {
    UninitSrc::single().init(value)
  }
  
  /// Constructs a new [root](crate#root) `Src` that contains only the value returned from the given function `f`.
  /// The [`WeakSrc`] that `f` is given will be a weak reference to this allocation, which allows constructing a self-referential value;
  /// it will return [`None`] from [`WeakSrc::upgrade`] until after `single_cyclic` has returned.
  /// 
  /// This is a convienience method for a specific subset of behavior that can be obtained via [`UninitSrc`].
  /// 
  /// ```rust
  /// use slice_rc::{Src, WeakSrc};
  /// 
  /// struct S {
  ///   me: WeakSrc<S>,
  /// }
  /// 
  /// let s = Src::single_cyclic(|me| S { me: me.clone() });
  /// 
  /// assert!(Src::ptr_eq(&s, &s.me.upgrade().unwrap()));
  /// ```
  #[inline]
  pub fn single_cyclic<F: FnOnce(&WeakSrc<T>) -> T>(f: F) -> Src<T> {
    UniqueSrc::into_shared(UniqueSrc::single_cyclic(f))
  }
  
  /// Constructs a new [root](crate#root) `Src` of length `1` with uninitialized contents.
  /// 
  /// ```rust
  /// use slice_rc::{Src, UniqueSrc};
  /// 
  /// let five = Src::<i32>::single_uninit();
  /// 
  /// let mut five = Src::into_unique(five).unwrap();
  /// five.write(5);
  /// let five = UniqueSrc::into_shared(five);
  /// 
  /// let five = unsafe { five.assume_init() };
  /// 
  /// assert_eq!(*five, 5);
  /// ```
  #[inline]
  pub fn single_uninit() -> Src<MaybeUninit<T>> {
    UniqueSrc::into_shared(UniqueSrc::single_uninit())
  }
  
  /// Constructs a new [root](crate#root) `Src` of length `1` with uninitialized contents, with the memory being filled with `0` bytes.
  /// 
  /// See [`MaybeUninit::zeroed`] for examples of correct and incorrect usage of this method.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let zero = Src::<i32>::single_zeroed();
  /// let zero = unsafe { zero.assume_init() };
  /// 
  /// assert_eq!(*zero, 0);
  /// ```
  #[inline]
  pub fn single_zeroed() -> Src<MaybeUninit<T>> {
    UniqueSrc::into_shared(UniqueSrc::single_zeroed())
  }
  
  /// Returns an `Src` equivalent to this one, but typed as a slice rather than a single element.
  /// The returned slice will have a length of `1`, and its element `0` will be at the same location in memory as `self`'s value.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// use std::ptr;
  /// 
  /// let single = Src::single(42);
  /// let slice = Src::as_slice(&single);
  /// 
  /// assert!(Src::ptr_eq(&single, &slice));
  /// assert!(ptr::eq(&*single, &slice[0]));
  /// ```
  #[inline]
  pub fn as_slice(this: &Src<T>) -> Src<[T]> {
    this.header().inc_strong_count();
    Src {
      // SAFETY: this.header has the same invariant as this2
      header: this.header,
      // SAFETY: this.start has the same invariant as this2
      start: this.start,
      // SAFETY: this.len's invariant implies this2.len's invariant
      len: 1,
      _phantom: PhantomData,
    }
  }
  
}

impl<T> Src<[T]> {
  
  /// Constructs a new [root](crate#root) `Src` of the given length with uninitialized contents.
  /// 
  /// ```rust
  /// use slice_rc::{Src, UniqueSrc};
  /// 
  /// let fives = Src::<[i32]>::new_uninit(3);
  /// 
  /// let mut fives = Src::into_unique(fives).unwrap();
  /// fives[0].write(5);
  /// fives[1].write(5);
  /// fives[2].write(5);
  /// let fives = UniqueSrc::into_shared(fives);
  /// 
  /// let fives = unsafe { fives.assume_init() };
  /// 
  /// assert_eq!(*fives, [5, 5, 5]);
  /// ```
  #[inline]
  pub fn new_uninit(len: usize) -> Src<[MaybeUninit<T>]> {
    UniqueSrc::into_shared(UniqueSrc::new_uninit(len))
  }
  
  /// Constructs a new [root](crate#root) `Src` of the given length with uninitialized contents, with the memory being filled with `0` bytes.
  /// 
  /// See [`MaybeUninit::zeroed`] for examples of correct and incorrect usage of this method.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let zeroes = Src::<[i32]>::new_zeroed(3);
  /// let zeroes = unsafe { zeroes.assume_init() };
  /// 
  /// assert_eq!(*zeroes, [0, 0, 0]);
  /// ```
  #[inline]
  pub fn new_zeroed(len: usize) -> Src<[MaybeUninit<T>]> {
    UniqueSrc::into_shared(UniqueSrc::new_zeroed(len))
  }
  
  /// Constructs a new [root](crate#root) `Src` of the given length where each element is produced by calling `f` with that element's index while walking forward through the slice.
  /// 
  /// This essentially the same as writing
  /// ```text
  /// Src::from_array([f(0), f(1), f(2), ..., f(len - 2), f(len - 1)])
  /// ```
  /// and is similar to `(0..len).map(f)`, just for `Src`s rather than iterators.
  /// 
  /// If `len == 0`, this produces an empty `Src` without ever calling `f`.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let slice = Src::from_fn(5, |i| i);
  /// assert_eq!(*slice, [0, 1, 2, 3, 4]);
  /// 
  /// let slice2 = Src::from_fn(8, |i| i * 2);
  /// assert_eq!(*slice2, [0, 2, 4, 6, 8, 10, 12, 14]);
  /// 
  /// let bool_slice = Src::from_fn(5, |i| i % 2 == 0);
  /// assert_eq!(*bool_slice, [true, false, true, false, true]);
  /// ```
  /// 
  /// You can also capture things, so you can use closures with mutable state.
  /// The slice is generated in ascending index order, starting from the front and going towards the back.
  /// ```rust
  /// # use slice_rc::Src;
  /// let mut state = 1;
  /// let s = Src::from_fn(6, |_| { let x = state; state *= 2; x });
  /// assert_eq!(*s, [1, 2, 4, 8, 16, 32]);
  /// ```
  /// 
  /// # Panics
  /// 
  /// Panics if `f` panics; in this event, any elements that have been initialized will be properly dropped.
  /// ```rust
  /// # use slice_rc::Src;
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
  /// let _ = std::panic::catch_unwind(|| {
  ///   Src::from_fn(10, |i| {
  ///     if i >= 5 { panic!() }
  ///     Droppable
  ///   })
  /// });
  /// 
  /// assert_eq!(DROPPED.get(), 5);
  /// ```
  #[inline]
  pub fn from_fn<F: FnMut(usize) -> T>(len: usize, f: F) -> Src<[T]> {
    UninitSrc::new(len).init_from_fn(f)
  }
  
  /// Constructs a new [root](crate#root) `Src` of the given length where each element is produced by calling `f` with a root [`WeakSrc`] pointer to the new allocation and that element's index while walking forward through the slice.
  /// 
  /// This method is like [`Src::from_fn`], but in this the function `f` is passed a root [`WeakSrc`] pointer to the allocation to allow constructing self-referential elements.
  /// 
  /// This is a convienience method for a specific subset of behavior that can be obtained via [`UninitSrc`].
  /// 
  /// ```rust
  /// use slice_rc::{Src, WeakSrc};
  /// 
  /// struct S {
  ///   val: usize,
  ///   root: WeakSrc<[S]>,
  /// }
  /// 
  /// let root = Src::cyclic_from_fn(5, |root, i| S {
  ///   val: i * 2,
  ///   root: root.clone(),
  /// });
  /// 
  /// assert_eq!(root.iter().map(|s| s.val).collect::<Vec<_>>(), vec![0, 2, 4, 6, 8]);
  /// assert!(root.iter().all(|s| Src::ptr_eq(&root, &s.root.upgrade().unwrap())));
  /// ```
  /// 
  /// It is possible to obtain a `WeakSrc` to the individual element that is being initialized via [`WeakSrc::slice`]:
  /// 
  /// ```rust
  /// # use slice_rc::{Src, WeakSrc};
  /// struct S {
  ///   val: usize,
  ///   me: WeakSrc<S>,
  /// }
  /// 
  /// let root = Src::cyclic_from_fn(5, |root, i| S {
  ///   val: i * 2,
  ///   me: root.slice(i),
  /// });
  /// 
  /// assert!(root.iter().enumerate().all(|(i, s)| Src::ptr_eq(&root.slice(i), &s.me.upgrade().unwrap())));
  /// ```
  pub fn cyclic_from_fn<F: FnMut(&WeakSrc<[T]>, usize) -> T>(len: usize, mut f: F) -> Src<[T]> {
    let this = UninitSrc::new(len);
    let weak = this.downgrade();
    this.init_from_fn(|i| f(&weak, i))
  }
  
  /// Constructs a new [root](crate#root) `Src` from the given iterator.
  /// 
  /// This method is essentially shorthand for
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// # fn f<T>(iter: impl IntoIterator<Item = T, IntoIter: std::iter::ExactSizeIterator>) -> Src<[T]> {
  /// let mut iter = iter.into_iter();
  /// Src::from_fn(iter.len(), |_| iter.next().unwrap())
  /// # }
  /// ```
  /// 
  /// The iterator must be [`ExactSizeIterator`] because `Src`s cannot be resized,
  /// so the number of elements must be known at allocation-time, i.e., before any of the elements are initialized.
  /// If you want to use a non-[`ExactSizeIterator`], use <code>iter.[collect](Iterator::collect)::\<[Vec]\<_>>()</code>.
  pub fn from_iter<I: IntoIterator<Item = T, IntoIter: ExactSizeIterator>>(iter: I) -> Src<[T]> {
    let mut iter = iter.into_iter();
    Self::from_fn(iter.len(), |_| iter.next().unwrap())
  }
  
  /// Constructs a new [root](crate#root) `Src` from the given array.
  /// 
  /// This method is effectively equivalent to passing an array to [`Src::from_iter`], but it is more efficient.
  /// As such, it is effectively shorthand for <code>Src::[from_fn](N, |i| values\[i])</code>, but again, more efficient
  /// (though not by enough to make <code>Src::from_array([array::from_fn]::<_, N, _>(f))</code> any better than <code>Src::[from_fn](N, f)</code>).
  /// 
  /// Note that the my assertions about efficiency are not based any kind of benchmarking,
  /// just the fact that this method uses a single [`ptr::write`] where [`Src::from_fn`] and [`Src::from_iter`] use `N` arbitrary function calls and `N` [`ptr::write`]s.
  /// As <code>[array::from_fn]</code> re-introduces at least the `N` arbitrary function calls, its difference (again, without benchmarking) is negligible.
  /// 
  /// [from_fn]: Src::from_fn
  /// [`ptr::write`]: std::ptr::write
  /// [array::from_fn]: std::array::from_fn
  #[inline]
  pub fn from_array<const N: usize>(values: [T; N]) -> Src<[T]> {
    UniqueSrc::into_shared(UniqueSrc::from_array(values))
  }
  
  /// Constructs a new [root](crate#root) `Src` of the given length where each element is the type's [default](Default::default).
  /// 
  /// This method is essentially equivalent to <code>Src::[from_fn](Src::from_fn)(len, |_| [Default::default]\())</code>.
  #[inline]
  pub fn from_default(len: usize) -> Src<[T]> where T: Default {
    Self::from_fn(len, |_| Default::default())
  }
  
  /// Constructs a new [root](crate#root) `Src` of the given length where each element is a clone of `value`.
  /// 
  /// This method is essentially equivalent to <code>Src::[from_fn](Src::from_fn)(len, |_| value.[clone](Clone::clone)())</code>.
  #[inline]
  pub fn filled(len: usize, value: &T) -> Src<[T]> where T: Clone {
    Self::from_fn(len, |_| value.clone())
  }
  
  /// Constructs a new [root](crate#root) `Src` of the given length where each element is a clone of the value returned from `f`.
  /// `f` is passed a root [`WeakSrc`] pointer to the allocation; this can be used to make self-referential structures.
  /// 
  /// ```rust
  /// use slice_rc::{Src, WeakSrc};
  /// 
  /// #[derive(Clone)]
  /// struct S {
  ///   val: i32,
  ///   root: WeakSrc<[S]>,
  /// }
  /// 
  /// let root = Src::filled_cyclic(5, |root| S { val: 42, root: root.clone() });
  /// assert!(root.iter().all(|s| s.val == 42));
  /// assert!(root.iter().all(|s| Src::ptr_eq(&root, &s.root.upgrade().unwrap())));
  /// ```
  #[inline]
  pub fn filled_cyclic<F: FnOnce(&WeakSrc<[T]>) -> T>(len: usize, f: F) -> Src<[T]> where T: Clone {
    UniqueSrc::into_shared(UniqueSrc::filled_cyclic(len, f))
  }
  
  /// Constructs a new [root](crate#root) `Src` as a clone of the given slice.
  /// 
  /// This method is essentially shorthand for <code>Src::[from_fn](Src::from_fn)(values.[len](slice::len)(), |i| values\[i].clone())</code>,
  /// but without the implicit bounds checking for slice indexing.
  #[inline]
  pub fn cloned(values: &[T]) -> Src<[T]> where T: Clone {
    UniqueSrc::into_shared(UniqueSrc::cloned(values))
  }
  
  /// Constructs a new [root](crate#root) `Src` as a copy of the given slice.
  /// 
  /// This method is functionally shorthand for <code>Src::[from_fn](Src::from_fn)(values.[len](slice::len)(), |i| values\[i])</code>,
  /// but without the implicit bounds checking for slice indexing.
  /// 
  /// This method is fairly efficient, as it is basically just an allocation (requisite for any `Src` constructor) and a [`memcpy`](std::ptr::copy_nonoverlapping).
  #[inline]
  pub fn copied(values: &[T]) -> Src<[T]> where T: Copy {
    UniqueSrc::into_shared(UniqueSrc::copied(values))
  }
  
}

impl<T> Src<MaybeUninit<T>> {
  
  /// Converts to `Src<T>`.
  /// 
  /// # Safety
  /// 
  /// As with [`MaybeUninit::assume_init`], it is up to the caller to guarantee that the inner value really is in an initialized state.
  /// Calling this when the content is not yet fully initialized causes immediate undefined behavior.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let zero = Src::<i32>::single_zeroed();
  /// let zero = unsafe { zero.assume_init() };
  /// 
  /// assert_eq!(*zero, 0);
  /// ```
  pub unsafe fn assume_init(self) -> Src<T> {
    // TODO: rephrase the safety requirements for InnerHeader to explicitly allow punning between T and type with T-like layout
    let this = Src {
      // SAFETY: self.header has *almost* the same safety invariant as this.header: the only difference is that self uses MaybeUninit<T> where this expects T
      header: self.header,
      // SAFETY: self.start has *almost* the same safety invariant as this.start: the only difference is that self uses MaybeUninit<T> where this expects T
      start: self.start.cast(),
      // SAFETY: self.len has *almost* the same safety invariant as this.len: the only difference is that self uses MaybeUninit<T> where this expects T
      len: self.len,
      _phantom: PhantomData,
    };
    forget(self); // don't decrease the strong counter because this is logically the same Src
    this
  }
  
}

impl<T> Src<[MaybeUninit<T>]> {
  
  /// Converts to `Src<[T]>`.
  /// 
  /// # Safety
  /// 
  /// As with [`MaybeUninit::assume_init`], it is up to the caller to guarantee that the inner value really is in an initialized state.
  /// Calling this when the content is not yet fully initialized causes immediate undefined behavior.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let zeroes = Src::<[i32]>::new_zeroed(3);
  /// let zeroes = unsafe { zeroes.assume_init() };
  /// 
  /// assert_eq!(*zeroes, [0, 0, 0]);
  /// ```
  pub unsafe fn assume_init(self) -> Src<[T]> {
    // TODO: rephrase the safety requirements for InnerHeader to explicitly allow punning between T and type with T-like layout
    let this = Src {
      // SAFETY: self.header has *almost* the same safety invariant as this.header: the only difference is that self uses MaybeUninit<T> where this expects T
      header: self.header,
      // SAFETY: self.start has *almost* the same safety invariant as this.start: the only difference is that self uses MaybeUninit<T> where this expects T
      start: self.start.cast(),
      // SAFETY: self.len has *almost* the same safety invariant as this.len: the only difference is that self uses MaybeUninit<T> where this expects T
      len: self.len,
      _phantom: PhantomData,
    };
    forget(self); // don't decrease the strong counter because this is logically the same Src
    this
  }
  
}

impl Src<str> {
  
  /// Constructs a new [`root`](crate#root) `Src` as a copy of the given string.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let hello = Src::new("Hello World!");
  /// 
  /// assert_eq!(&*hello, "Hello World!");
  /// ```
  #[inline]
  pub fn new(s: impl AsRef<str>) -> Src<str> {
    UniqueSrc::into_shared(UniqueSrc::new(s))
  }
  
  /// Converts an `Src` of bytes to a string `Src`.
  /// 
  /// [`str`] and [`[u8]`](slice) are both slices of bytes, so this function converts between the two.
  /// Not all byte slices are valid string slices, however: [`str`] must be valid UTF-8.
  /// This method checks to ensure that the bytes are valid UTF-8, and then does the conversion.
  /// 
  /// If you are sure that the byte slice is valid UTF-8, and you don't want to incur the overhead of the validity check,
  /// there is an unsafe version of this method, [`from_utf8_unchecked`](Src::from_utf8_unchecked),
  /// which has the same behavior but skips the check.
  /// 
  /// # Errors
  /// 
  /// Returns `Err` if the slice is not UTF-8 with a description as to why the provided slice is not UTF-8.
  /// 
  /// # Examples
  /// 
  /// Basic usage:
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let sparkle_heart = Src::from_array([240, 159, 146, 150]);
  /// 
  /// let sparkle_heart = Src::from_utf8(sparkle_heart)?;
  /// 
  /// assert_eq!("💖", &*sparkle_heart);
  /// # Ok::<_, std::str::Utf8Error>(())
  /// ```
  /// 
  /// Incorrect bytes:
  /// 
  /// ```rust
  /// # use slice_rc::Src;
  /// let sparkle_heart = Src::from_array([0, 159, 146, 150]);
  /// 
  /// assert!(Src::from_utf8(sparkle_heart).is_err());
  /// ```
  #[inline]
  pub fn from_utf8(v: Src<[u8]>) -> Result<Src<str>, Utf8Error> {
    let _: &str = str::from_utf8(&*v)?;
    // SAFETY: <str>::from_utf8() guarantees that the contents are UTF-8
    Ok(unsafe { Src::from_utf8_unchecked(v) })
  }
  
  /// Converts an `Src` of bytes to a string `Src` without checking that the string contains valid UTF-8.
  /// 
  /// See the safe version, [`from_utf8`](Src::from_utf8), for more information.
  /// 
  /// # Safety
  /// 
  /// The bytes passed in must be valid UTF-8.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let sparkle_heart = Src::from_array([240, 159, 146, 150]);
  /// 
  /// let sparkle_heart = unsafe { Src::from_utf8_unchecked(sparkle_heart) };
  /// 
  /// assert_eq!("💖", &*sparkle_heart);
  /// ```
  #[inline]
  pub unsafe fn from_utf8_unchecked(v: Src<[u8]>) -> Src<str> {
    // TODO: rephrase the safety requirements for InnerHeader to explicitly allow punning between T and type with T-like layout
    let this = Src {
      // SAFETY: v.header has *almost* the same safety invariant as this.header: the only difference is that v uses [u8] where this expects str;
      //         the pun from [u8] to str adds the safety requirement that v's content is valid UTF-8, but this requirement is passed on to the caller
      header: v.header,
      // SAFETY: v.start has *almost* the same safety invariant as this.start: the only difference is that v uses [u8] where this expects str;
      //         the pun from [u8] to str adds the safety requirement that v's content is valid UTF-8, but this requirement is passed on to the caller
      start: v.start,
      // SAFETY: v.len has *almost* the same safety invariant as this.len: the only difference is that v uses [u8] where this expects str;
      //         the pun from [u8] to str adds the safety requirement that v's content is valid UTF-8, but this requirement is passed on to the caller
      len: v.len,
      _phantom: PhantomData,
    };
    forget(v);
    this
  }
  
  /// Converts a string `Src` to a `Src` of bytes.
  /// To convert the the bytes back to a string, use the [`from_utf8`](Src::from_utf8) method.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let bytes = Src::as_bytes(&Src::new("bors"));
  /// assert_eq!(b"bors", &*bytes);
  /// ```
  #[inline]
  pub fn as_bytes(this: &Src<str>) -> Src<[u8]> {
    this.header().inc_strong_count();
    // TODO: rephrase the safety requirements for InnerHeader to explicitly allow punning between T and type with T-like layout
    Src {
      // SAFETY: this.header has *almost* the same safety invariant as this2.header: the only difference is that this uses str where this2 expects [u8];
      //         the pun from str to [u8] relaxes the safety requirement that this's content is valid UTF-8
      header: this.header,
      // SAFETY: this.start has *almost* the same safety invariant as this2.start: the only difference is that this uses str where this2 expects [u8];
      //         the pun from str to [u8] relaxes the safety requirement that this's content is valid UTF-8
      start: this.start,
      // SAFETY: this.len has *almost* the same safety invariant as this2.len: the only difference is that this uses str where this2 expects [u8];
      //         the pun from str to [u8] relaxes the safety requirement that this's content is valid UTF-8
      len: this.len,
      _phantom: PhantomData,
    }
  }
  
}

impl<T: SrcTarget + ?Sized> Clone for Src<T> {
  
  #[inline]
  fn clone(&self) -> Self {
    self.header().inc_strong_count();
    Self {
      // SAFETY: this.header has the same safety invariant as _.header
      header: self.header,
      // SAFETY: this.start has the same safety invariant as _.start
      start: self.start,
      // SAFETY: this.len has the same safety invariant as _.len
      len: self.len,
      _phantom: PhantomData,
    }
  }
  
}

impl<T: Default> Default for Src<T> {
  
  #[inline]
  fn default() -> Self {
    Self::single(T::default())
  }
  
}

impl<T: SrcTarget + ?Sized> Deref for Src<T> {
  
  type Target = T;
  
  #[inline]
  fn deref(&self) -> &Self::Target {
    T::get(self)
  }
  
}

impl<T: SrcTarget + ?Sized> Borrow<T> for Src<T> {
  
  #[inline]
  fn borrow(&self) -> &T {
    &**self
  }
  
}

impl<T: SrcTarget + ?Sized> AsRef<T> for Src<T> {
  
  #[inline]
  fn as_ref(&self) -> &T {
    &**self
  }
  
}

impl<T: SrcTarget + Index<I> + ?Sized, I> Index<I> for Src<T> {
  
  type Output = T::Output;
  
  #[inline]
  fn index(&self, index: I) -> &Self::Output {
    &self.deref()[index]
  }
  
}

impl<T: Hash + SrcTarget + ?Sized> Hash for Src<T> {
  
  #[inline]
  fn hash<H: Hasher>(&self, state: &mut H) {
    T::hash(&**self, state);
  }
  
}

impl<T: PartialEq<U> + SrcTarget + ?Sized, U: SrcTarget + ?Sized> PartialEq<Src<U>> for Src<T> {
  
  #[inline]
  fn eq(&self, other: &Src<U>) -> bool {
    T::eq(&**self, &**other)
  }
  
  #[inline]
  fn ne(&self, other: &Src<U>) -> bool {
    T::ne(&**self, &**other)
  }
  
}

impl<T: Eq + SrcTarget + ?Sized> Eq for Src<T> {}

impl<T: PartialOrd<U> + SrcTarget + ?Sized, U: SrcTarget + ?Sized> PartialOrd<Src<U>> for Src<T> {
  
  #[inline]
  fn ge(&self, other: &Src<U>) -> bool {
    T::ge(&**self, &**other)
  }
  
  #[inline]
  fn gt(&self, other: &Src<U>) -> bool {
    T::gt(&**self, &**other)
  }
  
  #[inline]
  fn le(&self, other: &Src<U>) -> bool {
    T::le(&**self, &**other)
  }
  
  #[inline]
  fn lt(&self, other: &Src<U>) -> bool {
    T::lt(&**self, &**other)
  }
  
  #[inline]
  fn partial_cmp(&self, other: &Src<U>) -> Option<Ordering> {
    T::partial_cmp(&**self, &**other)
  }
  
}

impl<T: Ord + SrcTarget + ?Sized> Ord for Src<T> {
  
  #[inline]
  fn cmp(&self, other: &Self) -> Ordering {
    T::cmp(&**self, &**other)
  }
  
}

impl<T: Debug + SrcTarget + ?Sized> Debug for Src<T> {
  
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    T::fmt(self, f)
  }
  
}

impl<T: SrcTarget + ?Sized> Pointer for Src<T> {
  
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    Pointer::fmt(&self.start, f)
  }
  
}

impl<T: SrcTarget + ?Sized> Drop for Src<T> {
  
  fn drop(&mut self) {
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * all constructor fns for Src initialize the elements
    // * the header is only accessed from InnerHeader::get_header
    // * this is one of two callsites for InnerHeader::drop_strong::<T::Item>, the other being UniqueSrc::drop;
    //   as a UniqueSrc cannot co-exist (for the same allocation) with an Src, this will be the last strong reference iff this is the last Src with access to this allocation's body
    unsafe { InnerHeader::drop_strong::<T::Item>(self.header); }
  }
  
}

#[cfg(test)]
mod tests {
  
  use std::{cell::Cell, mem::MaybeUninit, ops::Deref, panic::{catch_unwind, AssertUnwindSafe}, str::Utf8Error};
  
  use crate::*;
  
  #[test]
  fn ptr_eq() {
    let s1: Src<[u8]> = Src::from_default(0);
    let s2: Src<[u8]> = Src::clone(&s1);
    assert_eq!(s1, s2);
    assert!(Src::ptr_eq(&s1, &s2));
    let s3: Src<[u8]> = Src::from_default(0);
    assert_eq!(s1, s3);
    assert_eq!(s2, s3);
    assert!(!Src::ptr_eq(&s1, &s3));
    assert!(!Src::ptr_eq(&s2, &s3));
  }
  
  #[test]
  fn same_root() {
    let s1: Src<[u8]> = Src::from_default(1);
    let s2: Src<[u8]> = s1.slice(1..);
    assert_ne!(s1, s2);
    assert!(!Src::ptr_eq(&s1, &s2));
    assert!(Src::same_root(&s1, &s2));
    let s3: Src<[u8]> = Src::from_default(1);
    let s4: Src<[u8]> = s3.slice(1..);
    assert_eq!(s1, s3);
    assert_ne!(s3, s4);
    assert_eq!(s2, s4);
    assert!(!Src::ptr_eq(&s1, &s3));
    assert!(!Src::ptr_eq(&s2, &s4));
    assert!(!Src::ptr_eq(&s2, &s4));
    assert!(!Src::same_root(&s1, &s3));
    assert!(!Src::same_root(&s2, &s4));
    assert!(Src::same_root(&s3, &s4));
  }
  
  #[test]
  fn is_root() {
    let s1: Src<[u8]> = Src::from_default(1);
    let s2: Src<[u8]> = s1.slice(..);
    let s3: Src<[u8]> = s1.slice(1..);
    assert!(Src::is_root(&s1));
    assert!(Src::is_root(&s2));
    assert!(!Src::is_root(&s3));
  }
  
  #[test]
  fn downgrade() {
    let s1: Src<[u8]> = Src::from_default(0);
    let w: WeakSrc<[u8]> = Src::downgrade(&s1);
    let s2: Src<[u8]> = w.upgrade().unwrap();
    assert_eq!(s1, s2);
  }
  
  #[test]
  fn strong_count() {
    let s1: Src<[u8]> = Src::from_default(0);
    assert_eq!(Src::strong_count(&s1), 1);
    let s2: Src<[u8]> = Src::clone(&s1);
    assert_eq!(Src::strong_count(&s1), 2);
    assert_eq!(Src::strong_count(&s2), 2);
    let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
    assert_eq!(Src::strong_count(&s1), 2);
    assert_eq!(Src::strong_count(&s2), 2);
    assert_eq!(w1.strong_count(), 2);
    let w2: WeakSrc<[u8]> = Src::downgrade(&s1);
    assert_eq!(Src::strong_count(&s1), 2);
    assert_eq!(Src::strong_count(&s2), 2);
    assert_eq!(w1.strong_count(), 2);
    assert_eq!(w2.strong_count(), 2);
    std::mem::drop(s1);
    assert_eq!(Src::strong_count(&s2), 1);
    assert_eq!(w1.strong_count(), 1);
    assert_eq!(w2.strong_count(), 1);
    std::mem::drop(s2);
    assert_eq!(w1.strong_count(), 0);
    assert_eq!(w2.strong_count(), 0);
  }
  
  #[test]
  fn weak_count() {
    let s1: Src<[u8]> = Src::from_default(0);
    assert_eq!(Src::weak_count(&s1), 0);
    let s2: Src<[u8]> = Src::clone(&s1);
    assert_eq!(Src::weak_count(&s1), 0);
    assert_eq!(Src::weak_count(&s2), 0);
    let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
    assert_eq!(Src::weak_count(&s1), 1);
    assert_eq!(Src::weak_count(&s2), 1);
    assert_eq!(w1.weak_count(), 1);
    let w2: WeakSrc<[u8]> = w1.clone();
    assert_eq!(Src::weak_count(&s1), 2);
    assert_eq!(Src::weak_count(&s2), 2);
    assert_eq!(w1.weak_count(), 2);
    assert_eq!(w2.weak_count(), 2);
    std::mem::drop(s1);
    assert_eq!(Src::weak_count(&s2), 2);
    assert_eq!(w1.weak_count(), 2);
    assert_eq!(w2.weak_count(), 2);
    std::mem::drop(w1);
    assert_eq!(Src::weak_count(&s2), 1);
    assert_eq!(w2.weak_count(), 1);
    std::mem::drop(s2);
    assert_eq!(w2.weak_count(), 0);
  }
  
  #[test]
  fn into_unique() {
    let s1: Src<[u8]> = Src::from_default(0);
    let s2: Src<[u8]> = Src::clone(&s1);
    let s1: Src<[u8]> = Src::into_unique(s1).unwrap_err();
    std::mem::drop(s2);
    let w: WeakSrc<[u8]> = Src::downgrade(&s1);
    assert!(w.upgrade().is_some());
    let u: UniqueSrc<[u8]> = Src::into_unique(s1).unwrap();
    assert!(w.upgrade().is_none());
    let s1: Src<[u8]> = UniqueSrc::into_shared(u);
    assert!(w.upgrade().is_some());
    _ = s1;
  }
  
  #[test]
  fn make_unique() {
    { // non-unique
      let s1: Src<[u8]> = Src::from_default(0);
      let s2: Src<[u8]> = Src::clone(&s1);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let u: UniqueSrc<[u8]> = Src::make_unique(s1);
      let w2: WeakSrc<[u8]> = UniqueSrc::downgrade(&u);
      assert!(!w1.same_root(&w2));
      _ = s2;
    }
    { // unique
      let s: Src<[u8]> = Src::from_default(0);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s);
      let u: UniqueSrc<[u8]> = Src::make_unique(s);
      let w2: WeakSrc<[u8]> = UniqueSrc::downgrade(&u);
      assert!(w1.same_root(&w2));
    }
  }
  
  #[test]
  fn empty() {
    let s: Src<[u8]> = Src::empty();
    assert!(s.is_empty());
    assert_eq!(s.len(), 0);
    let s: Src<str> = Src::empty();
    assert!(s.is_empty());
    assert_eq!(s.len(), 0);
  }
  
  #[test]
  fn len() {
    let s: Src<[u8]> = Src::from_default(0);
    assert_eq!(s.len(), 0);
    let s: Src<[u8]> = Src::from_default(1);
    assert_eq!(s.len(), 1);
    let s: Src<[u8]> = Src::from_default(17);
    assert_eq!(s.len(), 17);
    let s: Src<[u8]> = s.slice(3..14);
    assert_eq!(s.len(), 11);
    let s: Src<[u8]> = s.slice(3..3);
    assert_eq!(s.len(), 0);
  }
  
  #[test]
  fn is_empty() {
    let s: Src<[u8]> = Src::from_default(0);
    assert!(s.is_empty());
    let s: Src<[u8]> = Src::from_default(1);
    assert!(!s.is_empty());
    let s: Src<[u8]> = Src::from_default(17);
    assert!(!s.is_empty());
    let s: Src<[u8]> = s.slice(3..14);
    assert!(!s.is_empty());
    let s: Src<[u8]> = s.slice(3..3);
    assert!(s.is_empty());
  }
  
  #[test]
  fn root() {
    let s1: Src<[u8]> = Src::from_default(1);
    assert!(Src::is_root(&s1));
    let s1: Src<[u8]> = s1.slice(1..);
    assert!(!Src::is_root(&s1));
    let s2: Src<[u8]> = Src::root(&s1);
    assert!(Src::is_root(&s2));
    assert!(Src::same_root(&s1, &s2));
  }
  
  #[test]
  fn slice() {
    { // slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s1, &[1, 2, 3]);
      let s1: Src<[u8]> = s1.slice(1..);
      assert_eq!(&*s1, &[2, 3]);
      let s2: Src<[u8]> = s1.slice(..1);
      assert_eq!(&*s2, &[2]);
      assert!(Src::same_root(&s1, &s2));
    }
    { // item 1
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s1, &[1, 2, 3]);
      let s2: Src<u8> = s1.slice(2);
      assert_eq!(&*s2, &3);
      let s2: Src<[u8]> = Src::as_slice(&s2);
      assert_eq!(&*s2, &[3]);
      assert!(Src::same_root(&s1, &s2));
    }
    { // item 2
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s1, &[1, 2, 3]);
      let s1: Src<[u8]> = s1.slice(1..);
      assert_eq!(&*s1, &[2, 3]);
      let s2: Src<u8> = s1.slice(0);
      assert_eq!(&*s2, &2);
      let s2: Src<[u8]> = Src::as_slice(&s2);
      assert_eq!(&*s2, &[2]);
      assert!(Src::same_root(&s1, &s2));
    }
  }
  
  #[test]
  fn single() {
    let s: Src<u8> = Src::single(42);
    assert_eq!(*s, 42);
  }
  
  #[test]
  fn single_cyclic() {
    { // non-cyclic
      let s: Src<u8> = Src::single_cyclic(|_| 42);
      assert_eq!(*s, 42);
    }
    { // cyclic
      struct S {
        
        this: WeakSrc<S>,
        i: usize,
        
      }
      let s: Src<S> = Src::single_cyclic(|weak| S { this: weak.clone(), i: 42 });
      assert_eq!(s.i, 42);
      let w: WeakSrc<S> = Src::downgrade(&s);
      assert!(WeakSrc::ptr_eq(&s.this, &w));
    }
  }
  
  #[test]
  fn single_uninit() {
    let s: Src<MaybeUninit<u8>> = Src::single_uninit();
    let mut u: UniqueSrc<MaybeUninit<u8>> = Src::make_unique(s);
    u.write(42);
    let s: Src<MaybeUninit<u8>> = UniqueSrc::into_shared(u);
    // SAFETY: just initialized it with u.write()
    let s: Src<u8> = unsafe { s.assume_init() };
    assert_eq!(*s, 42);
  }
  
  #[test]
  fn single_zeroed() {
    let s: Src<MaybeUninit<u8>> = Src::single_zeroed();
    // SAFETY: u8 is a zeroable type
    let s: Src<u8> = unsafe { s.assume_init() };
    assert_eq!(*s, 0);
  }
  
  #[test]
  fn as_slice() {
    { // single root
      let s1: Src<u8> = Src::single(42);
      let s2: Src<[u8]> = Src::as_slice(&s1);
      assert_eq!([*s1], *s2);
    }
    { // from slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let s2: Src<u8> = s1.slice(1);
      let s3: Src<[u8]> = Src::as_slice(&s2);
      assert_eq!(s1[1], *s2);
      assert_eq!([*s2], *s3);
    }
  }
  
  #[test]
  fn new_uninit() {
    let s: Src<[MaybeUninit<u8>]> = Src::new_uninit(3);
    assert_eq!(s.len(), 3);
    let mut u: UniqueSrc<[MaybeUninit<u8>]> = Src::make_unique(s);
    for (i, elem) in u.iter_mut().enumerate() {
      elem.write(i as _);
    }
    let s: Src<[MaybeUninit<u8>]> = UniqueSrc::into_shared(u);
    // SAFETY: just initialized it with all the elem.write()s
    let s: Src<[u8]> = unsafe { s.assume_init() };
    assert_eq!(*s, [0, 1, 2]);
  }
  
  #[test]
  fn new_zeroed() {
    let s: Src<[MaybeUninit<u8>]> = Src::new_zeroed(3);
    assert_eq!(s.len(), 3);
    // SAFETY: u8 is a zeroable type
    let s: Src<[u8]> = unsafe { s.assume_init() };
    assert_eq!(*s, [0, 0, 0]);
  }
  
  #[test]
  fn from_fn() {
    { // normal
      let s: Src<[usize]> = Src::from_fn(3, |i| i * 2);
      assert_eq!(*s, [0, 2, 4]);
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
        let _: Src<[DropFlagger<'_>]> = Src::from_fn(drop_flags.len(), |i| {
          if i >= 3 { panic!() }
          DropFlagger(&drop_flags[i])
        });
      });
      assert!(drop_flags[..3].iter().map(Deref::deref).all(Cell::get));
      assert!(!drop_flags[3..].iter().map(Deref::deref).any(Cell::get));
    }
  }
  
  #[test]
  fn cyclic_from_fn() {
    { // normal, not cyclic
      let s: Src<[usize]> = Src::cyclic_from_fn(3, |_, i| i * 2);
      assert_eq!(*s, [0, 2, 4]);
    }
    { // normal, cyclic
      struct S {
        
        all: WeakSrc<[S]>,
        i: usize,
        
      }
      let s1: Src<[S]> = Src::cyclic_from_fn(3, |w, i| S { all: w.clone(), i: i * 2 });
      assert_eq!(s1[0].i, 0);
      assert_eq!(s1[1].i, 2);
      assert_eq!(s1[2].i, 4);
      let s2: Src<[S]> = s1[0].all.upgrade().unwrap();
      assert!(Src::ptr_eq(&s1, &s2));
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
        let _: Src<[DropFlagger<'_>]> = Src::cyclic_from_fn(drop_flags.len(), |_, i| {
          if i >= 3 { panic!() }
          DropFlagger(&drop_flags[i])
        });
      });
      assert!(drop_flags[..3].iter().map(Deref::deref).all(Cell::get));
      assert!(!drop_flags[3..].iter().map(Deref::deref).any(Cell::get));
    }
  }
  
  #[test]
  fn from_iter() {
    let s: Src<[u8]> = Src::from_iter(vec![1, 2, 3].into_iter().map(|i| i * 2));
    assert_eq!(*s, [2, 4, 6]);
  }
  
  #[test]
  fn from_array() {
    let s: Src<[u8]> = Src::from_array([1, 2, 3]);
    assert_eq!(*s, [1, 2, 3]);
  }
  
  #[test]
  fn from_default() {
    #[derive(Copy, Clone, Eq, PartialEq, Debug)]
    struct D42(u8);
    impl Default for D42 {
      
      fn default() -> Self {
        Self(42)
      }
      
    }
    let s: Src<[u8]> = Src::from_default(3);
    assert_eq!(*s, [0, 0, 0]);
    let s: Src<[D42]> = Src::from_default(3);
    assert_eq!(*s, [D42(42), D42(42), D42(42)]);
  }
  
  #[test]
  fn filled() {
    let s: Src<[u8]> = Src::filled(3, &42);
    assert_eq!(*s, [42, 42, 42]);
  }
  
  #[test]
  fn filled_cyclic() {
    { // non-cyclic
      let s: Src<[u8]> = Src::filled_cyclic(3, |_| 42);
      assert_eq!(*s, [42, 42, 42]);
    }
    { // cyclic
      #[derive(Clone)]
      struct S {
        
        all: WeakSrc<[S]>,
        i: usize,
        
      }
      let s: Src<[S]> = Src::filled_cyclic(3, |weak| S { all: weak.clone(), i: 42 });
      assert_eq!(s[0].i, 42);
      assert_eq!(s[1].i, 42);
      assert_eq!(s[2].i, 42);
      let w: WeakSrc<[S]> = Src::downgrade(&s);
      assert!(WeakSrc::ptr_eq(&s[0].all, &w));
    }
  }
  
  #[test]
  fn cloned() {
    #[derive(Clone, Eq, PartialEq, Debug)]
    struct NonCopy(u8);
    let s: Src<[NonCopy]> = Src::cloned(&[NonCopy(1), NonCopy(2), NonCopy(3)]);
    assert_eq!(*s, [NonCopy(1), NonCopy(2), NonCopy(3)]);
  }
  
  #[test]
  fn copied() {
    let s: Src<[u8]> = Src::copied(&[1, 2, 3]);
    assert_eq!(*s, [1, 2, 3]);
  }
  
  #[test]
  fn assume_init_single() {
    let s: Src<MaybeUninit<u8>> = Src::single_zeroed();
    // SAFETY: u8 is a zeroable type
    let s: Src<u8> = unsafe { s.assume_init() };
    assert_eq!(*s, 0);
  }
  
  #[test]
  fn assume_init_slice() {
    let s: Src<[MaybeUninit<u8>]> = Src::new_zeroed(3);
    // SAFETY: u8 is a zeroable type
    let s: Src<[u8]> = unsafe { s.assume_init() };
    assert_eq!(*s, [0, 0, 0]);
  }
  
  #[test]
  fn new() {
    let s: Src<str> = Src::new("Hello World!");
    assert_eq!(&*s, "Hello World!");
  }
  
  #[test]
  fn from_utf8() {
    { // UTF-8
      let s: Src<[u8]> = Src::copied(b"Hello World!");
      let s: Src<str> = Src::from_utf8(s).unwrap();
      assert_eq!(&*s, "Hello World!");
    }
    { // not UTF-8
      let s: Src<[u8]> = Src::copied(&[0xFF]);
      let _: Utf8Error = Src::from_utf8(s).unwrap_err();
    }
  }
  
  #[test]
  fn from_utf8_unchecked() {
    let s: Src<[u8]> = Src::copied(b"Hello World!");
    // SAFETY: just got the bytes from a str
    let s: Src<str> = unsafe { Src::from_utf8_unchecked(s) };
    assert_eq!(&*s, "Hello World!");
  }
  
  #[test]
  fn as_bytes() {
    let s: Src<str> = Src::new("Hello World!");
    let s: Src<[u8]> = Src::as_bytes(&s);
    assert_eq!(&*s, b"Hello World!");
  }
  
  #[test]
  fn clone() {
    let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
    assert_eq!(Src::strong_count(&s1), 1);
    let s2: Src<[u8]> = s1.clone();
    assert_eq!(Src::strong_count(&s1), 2);
    assert_eq!(*s1, *s2);
    assert!(Src::ptr_eq(&s1, &s2));
  }
  
  #[test]
  fn deref() {
    let s: Src<[u8]> = Src::from_array([1, 2, 3]);
    assert_eq!(Deref::deref(&s), &[1, 2, 3]);
  }
  
  #[test]
  fn drop() {
    let drop_flags: [_; 3] = std::array::from_fn(|_| Cell::new(false));
    struct DropFlagger<'a>(&'a Cell<bool>);
    impl Drop for DropFlagger<'_> {
      
      fn drop(&mut self) {
        self.0.update(|v| !v)
      }
      
    }
    assert!(!drop_flags.iter().any(Cell::get));
    let s1: Src<[DropFlagger<'_>]> = Src::from_iter(drop_flags.iter().map(DropFlagger));
    assert!(!drop_flags.iter().any(Cell::get));
    assert_eq!(Src::strong_count(&s1), 1);
    let s2: Src<[DropFlagger<'_>]> = s1.clone();
    assert!(!drop_flags.iter().any(Cell::get));
    assert_eq!(Src::strong_count(&s1), 2);
    assert_eq!(Src::strong_count(&s2), 2);
    std::mem::drop(s1);
    assert!(!drop_flags.iter().any(Cell::get));
    assert_eq!(Src::strong_count(&s2), 1);
    std::mem::drop(s2);
    assert!(drop_flags.iter().all(Cell::get));
  }
  
}
