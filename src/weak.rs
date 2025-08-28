use std::{fmt::{self, Debug, Formatter, Pointer}, marker::PhantomData, mem::forget, num::NonZero, ops::Bound, ptr::NonNull};

use crate::{inner::InnerHeader, Src, SrcIndex, SrcSlice, SrcTarget};

const fn non_null_max<T>() -> NonNull<T> {
  NonNull::without_provenance(NonZero::<usize>::MAX)
}

/// `WeakSrc` is a version of [`Src`] that holds a non-owning reference to the managed allocation.
/// 
/// This is this crate's analog to [`std::rc::Weak`]; see the [crate-level documentation] for a description of how this crate's types differ from those of [`std::rc`].
/// 
/// The allocation is accessed by calling [`upgrade`](WeakSrc::upgrade) on the `WeakSrc` pointer, which returns an <code>[Option]<[Src]\<T>></code>.
/// 
/// Since a `WeakSrc` pointer does not count toward ownership, it will not prevent the value stored in the allocation from being dropped,
/// and `WeakSrc` itself makes no guarantees about the value still being present. Thus it may return `None` when `upgrade`d.
/// Note however that a `WeakSrc` *does* prevent the allocation itself (the backing store) from being deallocated.
/// 
/// A `WeakSrc` pointer is useful for keeping a temporary reference to the allocation managed by `Src` without preventing its inner value from being dropped.
/// It is also used to prevent circular references between `Src` pointers, since mutual owning references would never allow either `Src` to be dropped.
/// For example, a tree could have strong `Src` pointers from parent nodes to children, and `WeakSrc` pointers from children back to their parents.
/// 
/// The typical way to obtain a `WeakSrc` pointer is to call [`Src::downgrade`].
/// 
/// # Dangling
/// 
/// [`WeakSrc::dangling`] allows constructing a "dangling" `WeakSrc` pointer;
/// dangling `WeakSrc` pointers don't have a backing allocation, and as such, are guaranteed to return [`None`] from [`WeakSrc::upgrade`].
/// Dangling `WeakSrc`s are considered [root](crate#root) and [empty](WeakSrc::is_empty).
/// 
/// `WeakSrc` pointers which are attached to an allocation are not considered dangling,
/// even if that allocation has been dropped or the `WeakSrc` is otherwise un-[upgrade](WeakSrc::upgrade)able.
/// 
/// [crate-level documentation]: crate#how-do-this-crates-types-differ-from-the-stdrc-ones
pub struct WeakSrc<T: SrcTarget + ?Sized> {
  
  // SAFETY:
  // requires:
  // * initialized from InnerHeader::new_inner::<T::Item>(_) or non_null_max::<ItemHeader>()
  pub(crate) header: NonNull<InnerHeader>,
  // SAFETY:
  // requires:
  // * either:
  //   * initialized from either InnerHeader::get_body_ptr::<T::Item>(self.header) or InnerHeader::get_elem_ptr::<T::Item>(self.header, i) where 0 <= i <= InnerHeader::get_header(self.header).len()
  //   * all body elements have been properly initialized (e.g., self.start.as_ref() will not cause UB), or strong_count == 0
  // * or, iff self.header is non_null_max::<ItemHeader>(), then self.start is non_null_max::<T::Item>()
  pub(crate) start: NonNull<T::Item>,
  // SAFETY:
  // only applies if self.header != non_null_max::<ItemHeader>():
  // requires when T: SrcSlice:
  // * self.start.add(self.len) <= InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  // requires when T: Sized:
  // * self.start < InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  pub(crate) len: T::Len,
  pub(crate) _phantom: PhantomData<*const T>,
  
}

impl<T: SrcTarget + ?Sized> WeakSrc<T> {
  
  // SAFETY:
  // requires:
  // * this weak is not dangling
  unsafe fn header(&self) -> &InnerHeader {
    // SAFETY:
    // * all constructor fns for Src and UniinitSrc initialize header from InnerHeader::new_inner::<T::Item>; a WeakSrc must be constructed either from a Src, an UninitSrc, or must be dangling; the safety requirement that this is not the lattermost is passed on to the caller
    // * the header is only accessed from InnerHeader::get_header
    unsafe { InnerHeader::get_header(self.header) }
  }
  
  /// Constructs a new [dangling](WeakSrc#dangling) `WeakSrc`.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use slice_rc::WeakSrc;
  /// 
  /// let dangling = WeakSrc::<i32>::dangling();
  /// 
  /// assert!(dangling.is_dangling());
  /// ```
  #[inline]
  pub fn dangling() -> WeakSrc<T> {
    WeakSrc {
      header: non_null_max(),
      start: non_null_max(),
      len: T::Len::default(),
      _phantom: PhantomData,
    }
  }
  
  /// Returns `true` if this `WeakSrc` is [dangling](WeakSrc#dangling).
  /// This only returns `true` for `WeakSrc`s that were constructed from [`WeakSrc::dangling`];
  /// `WeakSrc`s that are un-[upgrade](WeakSrc::upgrade)able for other reasons are not considered dangling,
  /// and therefore this method returns `false` for those cases.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use slice_rc::WeakSrc;
  /// 
  /// let dangling = WeakSrc::<i32>::dangling();
  /// 
  /// assert!(dangling.is_dangling());
  /// ```
  /// 
  /// Not dangling:
  /// 
  /// ```rust
  /// # use slice_rc::Src;
  /// let s = Src::single(42);
  /// let w = Src::downgrade(&s);
  /// drop(s);
  /// 
  /// assert!(!w.is_dangling());
  /// assert!(w.upgrade().is_none());
  /// ```
  #[inline]
  pub fn is_dangling(&self) -> bool {
    self.header == non_null_max()
  }
  
  /// Attempts to upgrade the `WeakSrc` pointer to an [`Src`], delaying dropping the inner value if successful.
  /// 
  /// Returns [`None`] if the inner value has since been dropped,
  /// if the inner value is uniquely owned by a [`UniqueSrc`](crate::UniqueSrc),
  /// or if the inner value is uninitialized via [`UninitSrc`](crate::UninitSrc) or one of the cyclic helper methods, e.g. [`Src::cyclic_from_fn`].
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let five = Src::single(5);
  /// 
  /// let weak_five = Src::downgrade(&five);
  /// 
  /// let strong_five = weak_five.upgrade();
  /// assert!(strong_five.is_some());
  /// 
  /// drop(strong_five);
  /// drop(five);
  /// 
  /// assert!(weak_five.upgrade().is_none());
  /// ```
  pub fn upgrade(&self) -> Option<Src<T>> {
    if self.is_dangling() {
      return None
    }
    // SAFETY: we just checked that this weak is not dangling
    let header = unsafe { self.header() };
    if header.strong_count() == 0 {
      return None
    }
    header.inc_strong_count();
    Some(Src {
      // SAFETY: if this weak is not dangling (which we checked earlier), then this self.header has the same safety invariant as _.header
      header: self.header,
      // SAFETY: if this weak is not dangling (which we checked earlier), then this self.start has the same safety invariant as _.start
      start: self.start,
      // SAFETY: if this weak is not dangling (which we checked earlier), then this self.len has the same safety invariant as _.len
      len: self.len,
      _phantom: PhantomData,
    })
  }
  
  /// Returns `true` if the two `WeakSrc`s point to slices starting at the same location in memory or are both [dangling](WeakSrc#dangling), akin to [`ptr::eq`](std::ptr::eq).
  /// 
  /// ```rust
  /// use slice_rc::{Src, WeakSrc};
  /// 
  /// let slice = Src::from_array([1, 2, 3]);
  /// let weak_slice = Src::downgrade(&slice);
  /// let same_weak_slice = weak_slice.clone();
  /// let weak_sub_slice = weak_slice.slice(1..);
  /// let other_slice = Src::from_array([1, 2, 3]);
  /// let other_weak_slice = Src::downgrade(&other_slice);
  /// 
  /// assert!(WeakSrc::ptr_eq(&weak_slice, &same_weak_slice));
  /// assert!(!WeakSrc::ptr_eq(&weak_slice, &weak_sub_slice));
  /// assert!(!WeakSrc::ptr_eq(&weak_slice, &other_weak_slice));
  /// ```
  /// 
  /// If `WeakSrc::ptr_eq(&a, &b)` returns true, then <code>WeakSrc::[same_root](WeakSrc::same_root)(&a, &b)</code> will also be true.
  /// 
  /// The type parameter, `U`, is to allow `WeakSrc`s of different types that _could_ be of the same allocation, and therefore, _could_ be equal by pointer, to be compared, e.g.:
  /// ```rust
  /// # use slice_rc::{Src, WeakSrc};
  /// let strong: Src<i32> = Src::single(4);
  /// let single: WeakSrc<i32> = Src::downgrade(&strong);
  /// let slice: WeakSrc<[i32]> = single.as_slice();
  /// 
  /// assert!(WeakSrc::ptr_eq(&single, &slice));
  /// ```
  /// 
  /// Note that this method currently ignores the length of the slice:
  /// ```rust
  /// # use slice_rc::{Src, WeakSrc};
  /// let root_strong = Src::from_array([1, 2, 3]);
  /// let root = Src::downgrade(&root_strong);
  /// let first = root.slice(0);
  /// 
  /// assert!(WeakSrc::ptr_eq(&root, &first));
  /// 
  /// let mid_to_end_slice = root.slice(1..);
  /// let mid_slice = root.slice(1..=1);
  /// 
  /// assert!(WeakSrc::ptr_eq(&mid_to_end_slice, &mid_slice));
  /// ```
  /// It is undecided whether this behavior is desireable, and as such, it may change;
  /// notably, [`Weak::ptr_eq`](std::rc::Weak::ptr_eq) does ignore metadata for `?Sized` types
  /// (though that's irrelevant for slices because [`Weak`]s can only point to the whole slice, and therefore the length will always be the same for [`Weak`]s that point to the same allocation),
  /// while [`ptr::eq`](std::ptr::eq) does consider the metadata (which causes inconsistent results for trait objects, but that is irrelevant here because `WeakSrc`s don't support trait objects).
  /// 
  /// See also [`WeakSrc::same_root`].
  /// 
  /// [`Weak`]: std::rc::Weak
  #[inline]
  pub fn ptr_eq<U: SrcTarget<Item = T::Item> + ?Sized>(&self, other: &WeakSrc<U>) -> bool {
    self.start == other.start
  }
  
  /// Returns `true` if the two `WeakSrc`s share the same [root](crate#root) (i.e., they point to parts of the same allocation) or are both [dangling](WeakSrc#dangling).
  /// 
  /// ```rust
  /// use slice_rc::{Src, WeakSrc};
  /// 
  /// let slice = Src::from_array([1, 2, 3]);
  /// let weak_slice = Src::downgrade(&slice);
  /// let same_weak_slice = weak_slice.clone();
  /// let other_slice = Src::from_array([1, 2, 3]);
  /// let other_weak_slice = Src::downgrade(&other_slice);
  /// 
  /// assert!(WeakSrc::same_root(&weak_slice, &same_weak_slice));
  /// assert!(!WeakSrc::same_root(&weak_slice, &other_weak_slice));
  /// ```
  /// 
  /// Notably, neither slice has to be the root, nor do they need to overlap at all:
  /// ```rust
  /// # use slice_rc::{Src, WeakSrc};
  /// let strong = Src::from_array([1, 2, 3]);
  /// let root = Src::downgrade(&strong);
  /// let a = root.slice(..1);
  /// let b = root.slice(2..);
  /// 
  /// assert!(WeakSrc::same_root(&a, &b));
  /// ```
  /// 
  /// The type parameter, `U`, is to allow `WeakSrc`s of different types that _could_ share the same root, to be compared, e.g.:
  /// ```rust
  /// # use slice_rc::{Src, WeakSrc};
  /// let strong: Src<i32> = Src::single(4);
  /// let single: WeakSrc<i32> = Src::downgrade(&strong);
  /// let slice: WeakSrc<[i32]> = single.as_slice();
  /// 
  /// assert!(WeakSrc::same_root(&single, &slice));
  /// ```
  /// 
  /// This method ignores the length of the slices in question, but unlike [`WeakSrc::ptr_eq`], this will not change,
  /// as the roots remains the same regardless of which parts of it are included in these slices.
  /// 
  /// See also [`WeakSrc::ptr_eq`], [`WeakSrc::is_root`], and [`WeakSrc::root`].
  #[inline]
  pub fn same_root<U: SrcTarget<Item = T::Item> + ?Sized>(&self, other: &WeakSrc<U>) -> bool {
    self.header == other.header
  }
  
  /// Returns `true` if this `WeakSrc` contains its [root](crate#root) (i.e., it references its entire allocation), or is [dangling](WeakSrc#dangling).
  /// Notably, this `WeakSrc` does not have to be the first one that was initialized, it just has to cover the entire allocation.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let strong = Src::from_array([1, 2, 3]);
  /// let root = Src::downgrade(&strong);
  /// let also_root = root.slice(..);
  /// let slice = root.slice(1..);
  /// 
  /// assert!(root.is_root());
  /// assert!(also_root.is_root());
  /// assert!(!slice.is_root());
  /// ```
  /// 
  /// See also [`WeakSrc::same_root`] and [`WeakSrc::root`].
  #[inline]
  pub fn is_root(&self) -> bool {
    if self.is_dangling() {
      return true
    }
    // SAFETY: we just checked that this weak is not dangling
    let header = unsafe { self.header() };
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    let root_start = unsafe { InnerHeader::get_body_ptr(self.header) };
    self.start == root_start && T::len_as_usize(self.len) == header.len()
  }
  
  /// Gets the number of strong ([`Src`]) pointers pointing to this allocation.
  /// 
  /// If `self` is [dangling](WeakSrc#dangling), this will return `0`.
  pub fn strong_count(&self) -> usize {
    if !self.is_dangling() {
      // SAFETY: we just checked that this weak is not dangling
      unsafe { self.header() }.strong_count()
    } else {
      0
    }
  }
  
  /// Gets the number of `WeakSrc` pointers pointing to this allocation.
  /// 
  /// If no strong pointers remain (or this `WeakSrc` is otherwise un-[upgrade](WeakSrc::upgrade)able), this will return `0`.
  pub fn weak_count(&self) -> usize {
    if !self.is_dangling() {
      // SAFETY: we just checked that this weak is not dangling
      let header = unsafe { self.header() };
      if header.strong_count() > 0 {
        header.weak_count() - 1 // subtract implicit weak held by strongs
      } else {
        0
      }
    } else {
      0
    }
  }
  
  /// Returns a `WeakSrc` pointer that refers to this `WeakSrc`'s [root](crate#root) (i.e., the entire allocation).
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let strong = Src::from_array([1, 2, 3]);
  /// let root = Src::downgrade(&strong);
  /// let slice = root.slice(1..);
  /// drop(root);
  /// 
  /// assert_eq!(*slice.upgrade().unwrap(), [2, 3]);
  /// 
  /// let new_root = slice.root();
  /// 
  /// assert_eq!(*new_root.upgrade().unwrap(), [1, 2, 3]);
  /// ```
  /// 
  /// This method returns a <code>[WeakSrc]\<\[T::[Item](crate::SrcTarget::Item)]></code> rather than a <code>[WeakSrc]\<T></code> for two reasons:
  /// * If <code>T: [Sized]</code>, then the root can only be a <code>[WeakSrc]\<T></code> if its total length is is `1`, which would prevent situations like this:
  /// ```rust
  /// # use slice_rc::{Src, WeakSrc};
  /// let strong = Src::from_array([1, 2, 3]);
  /// let root: WeakSrc<[i32]> = Src::downgrade(&strong);
  /// let slice: WeakSrc<i32> = root.slice(1);
  /// let new_root: WeakSrc<[i32]> = slice.root();
  /// 
  /// assert_eq!(*new_root.upgrade().unwrap(), [1, 2, 3]);
  /// ```
  /// * If <code>T = [str]</code>, it could be a UTF-8 slice of a larger allocation that is not entirely UTF-8, which would violate the safety invariant of [`str`]:
  /// ```rust
  /// # use slice_rc::{Src, WeakSrc};
  /// let root: Src<[u8]> = Src::copied(b"\xFFhello");
  /// let weak_root: WeakSrc<[u8]> = Src::downgrade(&root);
  /// let s: Src<str> = Src::from_utf8(root.slice(1..)).unwrap();
  /// let weak_s: WeakSrc<str> = Src::downgrade(&s);
  /// let new_weak_root: WeakSrc<[u8]> = weak_s.root();
  /// 
  /// assert_eq!(&*weak_s.upgrade().unwrap(), "hello");
  /// assert!(Src::from_utf8(new_weak_root.upgrade().unwrap()).is_err());
  /// ```
  pub fn root(&self) -> WeakSrc<[T::Item]> {
    if self.is_dangling() {
      return WeakSrc::dangling()
    }
    // SAFETY: we just checked that this weak is not dangling
    let header = unsafe { self.header() };
    // SAFETY:
    // * all constructor fns for Src and UninitSrc initialize header from InnerHeader::new_inner::<T::Item>; a WeakSrc must be constructed either from a Src, an UninitSrc, or must be dangling; we just checked that this weak is not dangling
    // * the header is only accessed from InnerHeader::get_header
    let start = unsafe { InnerHeader::get_body_ptr(self.header) };
    header.inc_weak_count();
    WeakSrc {
      // SAFETY: this self.header has the same safety invariant as this.header
      header: self.header,
      // SAFETY: if this weak is not dangling (which we checked earlier), the start that we just calculated earlier meets the safety invariant by definition
      start,
      // SAFETY: if this weak is not dangling (which we checked earlier), header.len() meets the safety invariant by definition
      len: header.len(),
      _phantom: PhantomData,
    }
  }
  
}

impl<T: SrcSlice + ?Sized> WeakSrc<T> {
  
  /// Returns the numeber of elements in this `WeakSrc`. If `self` is [dangling](WeakSrc#dangling), returns `0`.
  /// 
  /// This method only returns the length of the whole allocation if `self` is a [root](crate#root) `WeakSrc`.
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let s = Src::from_array([1, 2, 3]);
  /// let w = Src::downgrade(&s);
  /// assert_eq!(w.len(), 3);
  /// ```
  #[inline]
  pub fn len(&self) -> usize {
    self.len
  }
  
  /// Returns `true` if this `WeakSrc` has a length of `0` or is [dangling](WeakSrc#dangling).
  /// 
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let a_strong = Src::from_array([1, 2, 3]);
  /// let a = Src::downgrade(&a_strong);
  /// assert!(!a.is_empty());
  /// 
  /// let b_strong = Src::<[i32]>::from_array([]);
  /// let b = Src::downgrade(&b_strong);
  /// assert!(b.is_empty());
  /// ```
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }
  
  /// Returns a `WeakSrc` pointer to an element or subslice depending on the type of index.
  /// * If given a position (only applicable where `Self = WeakSrc<[U]>`), returns an `WeakSrc<U>` to the element at that position.
  /// * If given a range, returns the subslice corresponding to that range.
  /// 
  /// # Panics
  /// If the index is in some way out of bounds, or if <code>Self = WeakSrc\<[str]></code> and the indices are not at [char boundaries](str::is_char_boundary).
  /// 
  /// Also panics if `self` is un-[upgrade](WeakSrc::upgrade)able;
  /// this is problematic for [`UniqueSrc`](crate::UniqueSrc) and [`UninitSrc`](crate::UninitSrc), and is intended to be relaxed in the future.
  /// 
  /// # Examples
  /// ```rust
  /// use slice_rc::Src;
  /// 
  /// let v = Src::from_array([10, 40, 30]);
  /// let weak = Src::downgrade(&v);
  /// assert_eq!(Src::single(40), weak.slice(1).upgrade().unwrap());
  /// assert_eq!(Src::from_array([10, 40]), weak.slice(0..2).upgrade().unwrap());
  /// ```
  /// Panics:
  /// ```should_panic
  /// # use slice_rc::Src;
  /// let v = Src::from_array([10, 40, 30]);
  /// let weak = Src::downgrade(&v);
  /// let _ = weak.slice(3);
  /// let _ = weak.slice(0..4);
  /// ```
  #[inline]
  pub fn slice<I: SrcIndex<T>>(&self, index: I) -> WeakSrc<I::Output> {
    index.get_weak(self.clone())
  }
  
  pub(crate) fn into_item(self, index: usize) -> WeakSrc<T::Item> {
    assert!(!self.is_dangling(), "cannot slice a dangling WeakSrc");
    // SAFETY: we just checked that this weak is not dangling
    let header = unsafe { self.header() };
    assert!(index < header.len(), "index {index} out of range for slice of length {}", header.len());
    // SAFETY: the safety invariant of self.start implies this safety requirement, given the assertion that index <= header.len() and that this weak is not dangling
    let start_ptr = unsafe { self.start.add(index) };
    let this = WeakSrc {
      // SAFETY: the safety invariant of self.header is the same as this.header
      header: self.header,
      // SAFETY: if this weak is not dangling (which we checked earlier), the start_ptr that we just calculated earlier meets the safety invariant by definition
      start: start_ptr,
      // SAFETY: if this weak is not dangling (which we checked earlier), the safety invariant is checked by the assertion above
      len: (),
      _phantom: PhantomData,
    };
    forget(self); // don't modify the weak count because this is logically the same WeakSrc
    this
  }
  
  pub(crate) fn into_slice_from_bounds(self, start: Bound<usize>, end: Bound<usize>) -> WeakSrc<T> {
    assert!(!self.is_dangling(), "cannot slice a dangling WeakSrc");
    // SAFETY: we just checked that this weak is not dangling
    let header = unsafe { self.header() };
    assert!(header.strong_count() > 0, "cannot slice a WeakSrc whose strong references have been dropped");
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
    // SAFETY: we just checked that this weak is not dangling and not dropped
    unsafe { T::validate_range_weak(&self, start_inc..end_exc) };
    let len = end_exc - start_inc;
    // SAFETY: the safety invariant of self.start implies this safety requirement, given the assertion that start_inc <= header.len() and that this weak is not dangling
    let start_ptr = unsafe { self.start.add(start_inc) };
    let this = WeakSrc {
      // SAFETY: the safety invariant of self.header is the same as this.header
      header: self.header,
      // SAFETY: if this weak is not dangling (which we checked earlier), the start_ptr that we just calculated earlier meets the safety invariant by definition
      start: start_ptr,
      // SAFETY: if this weak is not dangling (which we checked earlier), the safety invariant is checked by the assertions above
      len,
      _phantom: PhantomData,
    };
    forget(self); // don't modify the weak count because this is logically the same WeakSrc
    this
  }
  
  // SAFETY:
  // requires:
  // * self is not dangling nor dropped
  pub(crate) unsafe fn get_slice(&self) -> &[T::Item] {
    let s = NonNull::slice_from_raw_parts(self.start, self.len);
    // SAFETY: the safety requirements of this fn combined with the invariants of WeakSrc guarantee that this refers to a properly initialized slice
    unsafe { s.as_ref() }
  }
  
}

impl<T: Sized> WeakSrc<T> {
  
  /// Returns a `WeakSrc` equivalent to this one, but typed as a slice rather than a single element.
  /// The returned slice will have a length of `1`, and its element `0` will be at the same location in memory as `self`'s value.
  /// 
  /// ```rust
  /// use slice_rc::{Src, WeakSrc};
  /// use std::ptr;
  /// 
  /// let strong = Src::single(42);
  /// let single = Src::downgrade(&strong);
  /// let slice = single.as_slice();
  /// 
  /// assert!(WeakSrc::ptr_eq(&single, &slice));
  /// assert!(ptr::eq(&*single.upgrade().unwrap(), &slice.upgrade().unwrap()[0]));
  /// ```
  #[inline]
  pub fn as_slice(&self) -> WeakSrc<[T]> {
    if !self.is_dangling() {
      // SAFETY: we just checked that this weak is not dangling
      unsafe { self.header() }.inc_weak_count();
    }
    WeakSrc {
      // SAFETY: the safety invariant of self.header is the same as this.header
      header: self.header,
      // SAFETY: the safety invariant of self.start is the same as this.start
      start: self.start,
      // SAFETY: if this weak is dangling, then self.len has no safety invariant; if it is weak, then the safety invariant of self.len is logically identical to that of this.len
      len: 1,
      _phantom: PhantomData,
    }
  }
  
}

impl<T: SrcTarget + ?Sized> Clone for WeakSrc<T> {
  
  fn clone(&self) -> Self {
    if !self.is_dangling() {
      // SAFETY: we just checked that this weak is not dangling
      unsafe { self.header() }.inc_weak_count();
    }
    Self {
      // SAFETY: the safety invariant of self.header is the same as _.header
      header: self.header,
      // SAFETY: the safety invariant of self.start is the same as _.start
      start: self.start,
      // SAFETY: the safety invariant of self.len is the same as _.len
      len: self.len,
      _phantom: PhantomData,
    }
  }
  
}

impl<T: SrcTarget + ?Sized> Debug for WeakSrc<T> {
  
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "(WeakSrc)")
  }
  
}

impl<T: SrcTarget + ?Sized> Pointer for WeakSrc<T> {
  
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    Pointer::fmt(&self.start, f)
  }
  
}

impl<T: SrcTarget + ?Sized> Default for WeakSrc<T> {
  
  #[inline]
  fn default() -> Self {
    Self::dangling()
  }
  
}

impl<T: SrcTarget + ?Sized> Drop for WeakSrc<T> {
  
  fn drop(&mut self) {
    if !self.is_dangling() {
      // SAFETY:
      // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>; WeakSrcs are either constructed from WeakSrc::dangling (which is covered by self.is_dangling()), or from a Src
      // * the header is only accessed from InnerHeader::get_header
      unsafe { InnerHeader::drop_weak::<T::Item>(self.header); }
    }
  }
  
}

#[cfg(test)]
mod tests {
  
  use std::cell::Cell;
  use crate::*;
  
  #[test]
  fn dangling() {
    let w: WeakSrc<[u8]> = WeakSrc::dangling();
    assert!(w.is_dangling());
    assert!(w.upgrade().is_none());
  }
  
  #[test]
  fn is_dangling() {
    { // dangling
      let w: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(w.is_dangling());
    }
    { // not dangling
      let s: Src<[u8]> = Src::from_default(0);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert!(!w.is_dangling());
      std::mem::drop(s);
      assert!(!w.is_dangling());
    }
  }
  
  #[test]
  fn upgrade() {
    { // dangling
      let w: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(w.upgrade().is_none());
    }
    { // not dangling
      let s1: Src<[u8]> = Src::from_default(0);
      let w: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s2: Src<[u8]> = w.upgrade().unwrap();
      assert!(Src::ptr_eq(&s1, &s2));
    }
  }
  
  #[test]
  fn ptr_eq() {
    { // dangling
      let w1: WeakSrc<[u8]> = WeakSrc::dangling();
      let w2: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(w1.ptr_eq(&w2));
    }
    { // not dangling, same root
      let s: Src<[u8]> = Src::from_default(1);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s);
      let w2: WeakSrc<[u8]> = w1.clone();
      assert!(w1.ptr_eq(&w2));
      let w3: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(!w1.ptr_eq(&w3));
      assert!(!w2.ptr_eq(&w3));
      let w4: WeakSrc<[u8]> = Src::downgrade(&s).slice(1..);
      let w5: WeakSrc<[u8]> = Src::downgrade(&s).slice(1..);
      assert!(w4.ptr_eq(&w5));
      assert!(!w4.ptr_eq(&w1));
      assert!(!w4.ptr_eq(&w3));
    }
    { // not dangling, different roots
      let s1: Src<[u8]> = Src::from_default(0);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s2: Src<[u8]> = Src::from_default(0);
      let w2: WeakSrc<[u8]> = Src::downgrade(&s2);
      assert!(!w1.ptr_eq(&w2));
      let w3: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(!w1.ptr_eq(&w3));
      assert!(!w2.ptr_eq(&w3));
      std::mem::drop((s1, s2));
      assert!(!w1.ptr_eq(&w3));
      assert!(!w2.ptr_eq(&w3));
    }
  }
  
  #[test]
  fn same_root() {
    { // dangling
      let w1: WeakSrc<[u8]> = WeakSrc::dangling();
      let w2: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(w1.same_root(&w2));
    }
    { // not dangling, same root
      let s: Src<[u8]> = Src::from_default(1);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s);
      let w2: WeakSrc<[u8]> = w1.clone();
      assert!(w1.same_root(&w2));
      let w3: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(!w1.same_root(&w3));
      assert!(!w2.same_root(&w3));
      let w4: WeakSrc<[u8]> = Src::downgrade(&s).slice(1..);
      assert!(w4.same_root(&w1));
      assert!(!w4.same_root(&w3));
    }
    { // not dangling, different roots
      let s1: Src<[u8]> = Src::from_default(0);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s2: Src<[u8]> = Src::from_default(0);
      let w2: WeakSrc<[u8]> = Src::downgrade(&s2);
      assert!(!w1.same_root(&w2));
      let w3: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(!w1.same_root(&w3));
      assert!(!w2.same_root(&w3));
      std::mem::drop((s1, s2));
      assert!(!w1.same_root(&w3));
      assert!(!w2.same_root(&w3));
    }
  }
  
  #[test]
  fn is_root() {
    { // dangling
      let w: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(w.is_root());
    }
    {
      let s: Src<[u8]> = Src::from_default(1);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s);
      assert!(w1.is_root());
      let w2: WeakSrc<[u8]> = Src::downgrade(&s).slice(1..);
      assert!(!w2.is_root());
      std::mem::drop(s);
      assert!(w1.is_root());
      assert!(!w2.is_root());
    }
  }
  
  #[test]
  fn strong_count() {
    { // dangling
      let w: WeakSrc<[u8]> = WeakSrc::dangling();
      assert_eq!(w.strong_count(), 0);
    }
    { // not dangling
      let s1: Src<[u8]> = Src::from_default(0);
      let w: WeakSrc<[u8]> = Src::downgrade(&s1);
      assert_eq!(w.strong_count(), 1);
      let s2: Src<[u8]> = s1.clone();
      assert_eq!(w.strong_count(), 2);
      std::mem::drop(s1);
      assert_eq!(w.strong_count(), 1);
      std::mem::drop(s2);
      assert_eq!(w.strong_count(), 0);
    }
  }
  
  #[test]
  fn weak_count() {
    { // dangling
      let w: WeakSrc<[u8]> = WeakSrc::dangling();
      assert_eq!(w.weak_count(), 0);
    }
    { // not dangling
      let s: Src<[u8]> = Src::from_default(0);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s);
      assert_eq!(w1.weak_count(), 1);
      let w2: WeakSrc<[u8]> = w1.clone();
      assert_eq!(w1.weak_count(), 2);
      assert_eq!(w2.weak_count(), 2);
      let w3: WeakSrc<[u8]> = Src::downgrade(&s);
      assert_eq!(w1.weak_count(), 3);
      assert_eq!(w2.weak_count(), 3);
      assert_eq!(w3.weak_count(), 3);
      std::mem::drop(w1);
      assert_eq!(w2.weak_count(), 2);
      assert_eq!(w3.weak_count(), 2);
      std::mem::drop(s);
      assert_eq!(w2.weak_count(), 0);
      assert_eq!(w3.weak_count(), 0);
    }
  }
  
  #[test]
  fn len() {
    { // dangling
      let w: WeakSrc<[u8]> = WeakSrc::dangling();
      assert_eq!(w.len(), 0);
    }
    { // not dangling
      let s: Src<[u8]> = Src::from_default(0);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert_eq!(w.len(), 0);
      let s: Src<[u8]> = Src::from_default(1);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert_eq!(w.len(), 1);
      let s: Src<[u8]> = Src::from_default(17);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert_eq!(w.len(), 17);
      let w: WeakSrc<[u8]> = w.slice(3..14);
      assert_eq!(w.len(), 11);
      let w: WeakSrc<[u8]> = w.slice(3..3);
      assert_eq!(w.len(), 0);
    }
  }
  
  #[test]
  fn is_empty() {
    { // dangling
      let w: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(w.is_empty());
    }
    { // not dangling
      let s: Src<[u8]> = Src::from_default(0);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert!(w.is_empty());
      let s: Src<[u8]> = Src::from_default(1);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert!(!w.is_empty());
      let s: Src<[u8]> = Src::from_default(17);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert!(!w.is_empty());
      let w: WeakSrc<[u8]> = w.slice(3..14);
      assert!(!w.is_empty());
      let w: WeakSrc<[u8]> = w.slice(3..3);
      assert!(w.is_empty());
    }
  }
  
  #[test]
  fn root() {
    { // dangling
      let w1: WeakSrc<[u8]> = WeakSrc::dangling();
      let w2: WeakSrc<[u8]> = w1.root();
      assert!(w2.is_root());
      assert!(w1.ptr_eq(&w2));
    }
    { // not dangling
      let s: Src<[u8]> = Src::from_default(1);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert!(w.is_root());
      let w: WeakSrc<[u8]> = w.slice(1..);
      assert!(!w.is_root());
      let w: WeakSrc<[u8]> = w.root();
      assert!(w.is_root());
    }
  }
  
  #[test]
  #[should_panic]
  fn slice_dangling() {
    let w: WeakSrc<[u8]> = WeakSrc::dangling();
    let _: WeakSrc<[u8]> = w.slice(..);
  }
  
  #[test]
  fn slice() {
    { // slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[1, 2, 3]);
      let w1: WeakSrc<[u8]> = w1.slice(1..);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[2, 3]);
      let w2: WeakSrc<[u8]> = w1.slice(..1);
      let s2: Src<[u8]> = w2.upgrade().unwrap();
      assert_eq!(&*s2, &[2]);
      assert!(w1.same_root(&w2));
    }
    { // item 1
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[1, 2, 3]);
      let w2: WeakSrc<u8> = w1.slice(2);
      let s2: Src<u8> = w2.upgrade().unwrap();
      assert_eq!(&*s2, &3);
      let w2: WeakSrc<[u8]> = w2.as_slice();
      let s2: Src<[u8]> = w2.upgrade().unwrap();
      assert_eq!(&*s2, &[3]);
      assert!(w1.same_root(&w2));
    }
    { // item 2
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[1, 2, 3]);
      let w1: WeakSrc<[u8]> = w1.slice(1..);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[2, 3]);
      let w2: WeakSrc<u8> = w1.slice(0);
      let s2: Src<u8> = w2.upgrade().unwrap();
      assert_eq!(&*s2, &2);
      let w2: WeakSrc<[u8]> = w2.as_slice();
      let s2: Src<[u8]> = w2.upgrade().unwrap();
      assert_eq!(&*s2, &[2]);
      assert!(w1.same_root(&w2));
    }
  }
  
  #[test]
  fn as_slice() {
    { // dangling
      let w: WeakSrc<u8> = WeakSrc::dangling();
      let w: WeakSrc<[u8]> = w.as_slice();
      assert!(w.is_dangling());
    }
    { // single root
      let s1: Src<u8> = Src::single(42);
      let w1: WeakSrc<u8> = Src::downgrade(&s1);
      let w2: WeakSrc<[u8]> = w1.as_slice();
      let s2: Src<[u8]> = w2.upgrade().unwrap();
      assert_eq!([*s1], *s2);
    }
    { // from slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let w2: WeakSrc<u8> = w1.slice(1);
      let s2: Src<u8> = w2.upgrade().unwrap();
      let w3: WeakSrc<[u8]> = w2.as_slice();
      let s3: Src<[u8]> = w3.upgrade().unwrap();
      assert_eq!(s1[1], *s2);
      assert_eq!([*s2], *s3);
    }
  }
  
  #[test]
  fn clone() {
    { // dangling
      let w1: WeakSrc<[u8]> = WeakSrc::dangling();
      assert_eq!(w1.weak_count(), 0);
      let w2: WeakSrc<[u8]> = w1.clone();
      assert_eq!(w1.weak_count(), 0);
      assert_eq!(w2.weak_count(), 0);
    }
    { // not dangling
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      assert_eq!(w1.weak_count(), 1);
      let w2: WeakSrc<[u8]> = w1.clone();
      assert_eq!(w1.weak_count(), 2);
      let s2: Src<[u8]> = w2.upgrade().unwrap();
      assert_eq!(*s1, *s2);
      assert!(w1.ptr_eq(&w2));
      std::mem::drop((s1, s2));
      assert_eq!(w1.weak_count(), 0);
    }
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
    let s: Src<[DropFlagger<'_>]> = Src::from_iter(drop_flags.iter().map(DropFlagger));
    assert!(!drop_flags.iter().any(Cell::get));
    let w1: WeakSrc<[DropFlagger<'_>]> = Src::downgrade(&s);
    assert!(!drop_flags.iter().any(Cell::get));
    assert_eq!(w1.weak_count(), 1);
    let w2: WeakSrc<[DropFlagger<'_>]> = w1.clone();
    assert!(!drop_flags.iter().any(Cell::get));
    assert_eq!(w1.weak_count(), 2);
    assert_eq!(w2.weak_count(), 2);
    std::mem::drop(w1);
    assert!(!drop_flags.iter().any(Cell::get));
    assert_eq!(w2.weak_count(), 1);
    std::mem::drop(s);
    assert!(drop_flags.iter().all(Cell::get));
    assert_eq!(w2.weak_count(), 0);
    std::mem::drop(w2);
    assert!(drop_flags.iter().all(Cell::get));
  }
  
}
