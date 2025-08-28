use std::{borrow::{Borrow, BorrowMut}, cmp::Ordering, fmt::{self, Debug, Formatter, Pointer}, hash::{Hash, Hasher}, marker::PhantomData, mem::{forget, MaybeUninit}, ops::{Deref, DerefMut, Index, IndexMut}, ptr::NonNull, str::Utf8Error};

use crate::{inner::{AllocUninit, AllocZeroed}, InnerHeader, Src, SrcSlice, SrcTarget, UninitSrc, WeakSrc};

/// A uniquely owned [`Src`].
/// 
/// This represents an [`Src`] that is known to be uniquely owned - that is, have exactly one strong reference.
/// Multiple [weak pointers](WeakSrc) can be created, but attempts to upgrade those to strong references will fail unless the `UniqueSrc` has been converted to a regular shared [`Src`].
/// 
/// Because they are uniquely owned, the contents of a `UniqueSrc` can be freely mutated.
/// This could be used as an initialization step (that is the suggested usage of [`UniqueRc`](std::rc::UniqueRc)),
/// but I find [`UninitSrc`] to be better for initialization, as there is no intermediate step with [dangling](WeakSrc#dangling) weak pointers.
/// 
/// Still, the ability to mutably access the contents of an [`Src`] can be useful, hence this type's inclusion in the crate.
/// (Also, [`Src::into_unique`] and [`Src::make_unique`] are currently this crate's substitutes for [`Rc::get_mut`](std::rc::Rc::get_mut) and [`Rc::make_mut`](std::rc::Rc::make_mut) respectively;
/// since I made that decision, I have since realized that they are not equivalent, and will therefore probably add `get_mut` and `make_mut` methods to [`Src`] at some point.
/// In the mean time, this is the next best thing.)
/// 
/// Note that, while this struct currently has no methods to explicitly support non-[root](crate#root) `UniqueSrc`s,
/// it is technically possible to construct them by making a non-[root](crate#root) [`Src`] and turning into a `UniqueSrc` via [`Src::into_unique`] or [`Src::make_unique`];
/// The behavior of these non-[root](crate#root) `UniqueSrc`s has not been thoroughly considered and may be changed or removed.
/// 
/// Many of the inherent methods of `UniqueSrc` are associated functions, which means that you have to call them as e.g.,
/// [`UniqueSrc::downgrade(&value)`](UniqueSrc::downgrade) instead of `value.downgrade()`;
/// this avoids conflicts with methods of the inner type `T`.
/// However, some methods, e.g. [`Src::len`], intentionally shadow a known method of the inner type because they use a more efficient computation for the same result,
/// and there may be some in the future (e.g. the hypothetical `UniqueSrc::slice`), which will be permitted to remain as methods because their inner type will be known not to have a conflicting method.
pub struct UniqueSrc<T: SrcTarget + ?Sized> {
  
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

impl<T: SrcTarget + ?Sized> UniqueSrc<T> {
  
  fn header(&self) -> &InnerHeader {
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    unsafe { InnerHeader::get_header(self.header) }
  }
  
  /// Creates a [`WeakSrc`] pointer to this slice.
  /// The [`WeakSrc`] refers to the same slice as this `UniqueSrc`, and therefore, refers to the [root](crate#root) if and only if this `UniqueSrc` does.
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let root = UniqueSrc::from_array([1, 2, 3]);
  /// 
  /// let weak_root = UniqueSrc::downgrade(&root);
  /// ```
  pub fn downgrade(this: &UniqueSrc<T>) -> WeakSrc<T> {
    // safety note: the strong count is 0 until this UniqueSrc is turned into a Src, so the WeakSrc will never read or write from the body during the lifetime of the UniqueSrc
    this.header().inc_weak_count();
    WeakSrc {
      // SAFETY: the safety invariant of this.header implies that of _.header
      header: this.header,
      // SAFETY: the safety invariant of this.start implies that of _.start
      start: this.start,
      // SAFETY: the safety invariant of this.len implies that of _.len
      len: this.len,
      _phantom: PhantomData,
    }
  }
  
  /// Turns this `UniqueSrc` into an [`Src`].
  /// Because `UniqueSrc` has strictly stronger guarantees, this conversion is not fallible.
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let x = UniqueSrc::single(3);
  /// assert_eq!(*UniqueSrc::into_shared(x), 3);
  /// ```
  /// 
  /// See also [`Src::into_unique`] and [`Src::make_unique`].
  pub fn into_shared(this: UniqueSrc<T>) -> Src<T> {
    this.header().inc_strong_count();
    let this2 = Src {
      // SAFETY: the safety invariant of this.header is the same as this2.header
      header: this.header,
      // SAFETY: the safety invariant of this.start is the same as this2.start
      start: this.start,
      // SAFETY: the safety invariant of this.len is the same as this2.len
      len: this.len,
      _phantom: PhantomData,
    };
    forget(this);
    this2
  }
  
}

impl<T: SrcSlice + ?Sized> UniqueSrc<T> {
  
  /// Constructs a new [root](crate#root) `UniqueSrc` of length `0`.
  /// Note that, because `UniqueSrc`s are not growable like [`Vec`]s are, this allocation will never become larger.
  /// Every reference to this allocation is a [root](crate#root).
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let s = UniqueSrc::<[i32]>::empty();
  /// 
  /// assert_eq!(s.len(), 0);
  /// ```
  #[inline]
  pub fn empty() -> UniqueSrc<T> {
    let this = UniqueSrc::<[T::Item]>::from_array([]);
    debug_assert_eq!(this.len, 0);
    let this2 = UniqueSrc {
      // SAFETY: the safety invariant of this.header is the same as this2.header
      header: this.header,
      // SAFETY: the safety invariant of this.start is the same as this2.start
      start: this.start,
      // SAFETY: the safety invariant of this.len implies that of this.len
      len: this.len,
      _phantom: PhantomData,
    };
    forget(this);
    this2
  }
  
  /// Returns the number of elements in this `UniqueSrc`.
  /// This method deliberately shadows [`<[T]>::len`](slice::len) and [`str::len`] because this method provides a (slightly) simpler and more efficient implementation.
  /// 
  /// This method only returns the length of the whole allocation if `self` is a [root](crate#root) `UniqueSrc`.
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let s = UniqueSrc::from_array([1, 2, 3]);
  /// assert_eq!(s.len(), 3);
  /// ```
  #[inline]
  pub fn len(&self) -> usize {
    self.len
  }
  
  /// Returns `true` if this `UniqueSrc` has a length of `0`.
  /// This method deliberately shadows [`<[T]>::is_empty`](slice::is_empty) and [`str::is_empty`] because this method provides a (slightly) simpler and more efficient implementation.
  /// 
  /// Note that this method does not imply that this `UniqueSrc` was constructed via [`UniqueSrc::empty`].
  /// Similarly, it does not imply that the entire allocation is empty, unless `self` is a [root](crate#root) `UniqueSrc`.
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let a = UniqueSrc::from_array([1, 2, 3]);
  /// assert!(!a.is_empty());
  /// 
  /// let b = UniqueSrc::<[i32]>::from_array([]);
  /// assert!(b.is_empty());
  /// ```
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }
  
}

impl<T: Sized> UniqueSrc<T> {
  
  /// Constructs a new [root](crate#root) `UniqueSrc` that contains only the given value.
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let s = UniqueSrc::single(42);
  /// assert_eq!(*s, 42);
  /// ```
  #[inline]
  pub fn single(value: T) -> UniqueSrc<T> {
    UninitSrc::single().init_unique(value)
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` that contains only the value returned from the given function `f`.
  /// The [`WeakSrc`] that `f` is given will be a weak reference to this allocation, which allows constructing a self-referential value;
  /// it will return [`None`] from [`WeakSrc::upgrade`] until after `single_cyclic` has returned.
  /// 
  /// This is a convienience method for a specific subset of behavior that can be obtained via [`UninitSrc`].
  /// 
  /// ```rust
  /// use slice_rc::{Src, UniqueSrc, WeakSrc};
  /// 
  /// struct S {
  ///   me: WeakSrc<S>,
  /// }
  /// 
  /// let s = UniqueSrc::single_cyclic(|me| S { me: me.clone() });
  /// 
  /// assert!(s.me.upgrade().is_none());
  /// 
  /// let s = UniqueSrc::into_shared(s);
  /// 
  /// assert!(Src::ptr_eq(&s, &s.me.upgrade().unwrap()));
  /// ```
  pub fn single_cyclic<F: FnOnce(&WeakSrc<T>) -> T>(f: F) -> UniqueSrc<T> {
    let this = UninitSrc::single();
    let weak = this.downgrade();
    this.init_unique(f(&weak))
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` of length `1` with uninitialized contents.
  /// 
  /// ```rust
  /// use slice_rc::{UniqueSrc};
  /// 
  /// let mut five = UniqueSrc::<i32>::single_uninit();
  /// 
  /// five.write(5);
  /// 
  /// let five = unsafe { five.assume_init() };
  /// 
  /// assert_eq!(*five, 5);
  /// ```
  #[inline]
  pub fn single_uninit() -> UniqueSrc<MaybeUninit<T>> {
    let this = UniqueSrc::<[T]>::new_uninit(1);
    debug_assert_eq!(this.len, 1);
    let this2 = UniqueSrc {
      // SAFETY: the safety invariant of this.header is the same as this2.header
      header: this.header,
      // SAFETY: the safety invariant of this.start is the same as this2.start
      start: this.start,
      // SAFETY: the safety invariant of this.len implies that of this.len
      len: (),
      _phantom: PhantomData,
    };
    forget(this);
    this2
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` of length `1` with uninitialized contents, with the memory being filled with `0` bytes.
  /// 
  /// See [`MaybeUninit::zeroed`] for examples of correct and incorrect usage of this method.
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let zero = UniqueSrc::<i32>::single_zeroed();
  /// let zero = unsafe { zero.assume_init() };
  /// 
  /// assert_eq!(*zero, 0);
  /// ```
  #[inline]
  pub fn single_zeroed() -> UniqueSrc<MaybeUninit<T>> {
    let this = UniqueSrc::<[T]>::new_zeroed(1);
    debug_assert_eq!(this.len, 1);
    let this2 = UniqueSrc {
      // SAFETY: the safety invariant of this.header is the same as this2.header
      header: this.header,
      // SAFETY: the safety invariant of this.start is the same as this2.start
      start: this.start,
      // SAFETY: the safety invariant of this.len implies that of this2.len
      len: (),
      _phantom: PhantomData,
    };
    forget(this);
    this2
  }
  
  /// Returns a `UniqueSrc` equivalent to this one, but typed as a slice rather than a single element.
  /// The returned slice will have a length of `1`, and its element `0` will be at the same location in memory as `self`'s value.
  /// 
  /// ```rust
  /// use slice_rc::{Src, UniqueSrc};
  /// use std::ptr;
  /// 
  /// let single = UniqueSrc::single(42);
  /// let single_weak = UniqueSrc::downgrade(&single);
  /// let slice = UniqueSrc::as_slice(single);
  /// let slice = UniqueSrc::into_shared(slice);
  /// let single = single_weak.upgrade().unwrap();
  /// 
  /// assert!(Src::ptr_eq(&single, &slice));
  /// assert!(ptr::eq(&*single, &slice[0]));
  /// ```
  #[inline]
  pub fn as_slice(this: UniqueSrc<T>) -> UniqueSrc<[T]> {
    let this2 = UniqueSrc {
      // SAFETY: the safety invariant of this.header is the same as this2.header
      header: this.header,
      // SAFETY: the safety invariant of this.start is the same as this2.start
      start: this.start,
      // SAFETY: the safety invariant of this.len implies this2.len
      len: 1,
      _phantom: PhantomData,
    };
    forget(this);
    this2
  }
  
}

impl<T> UniqueSrc<[T]> {
  
  /// Constructs a new [root](crate#root) `UniqueSrc` of the given length with uninitialized contents.
  /// 
  /// ```rust
  /// use slice_rc::{Src, UniqueSrc};
  /// 
  /// let mut fives = UniqueSrc::<[i32]>::new_uninit(3);
  /// 
  /// fives[0].write(5);
  /// fives[1].write(5);
  /// fives[2].write(5);
  /// 
  /// let fives = unsafe { fives.assume_init() };
  /// 
  /// assert_eq!(*fives, [5, 5, 5]);
  /// ```
  pub fn new_uninit(len: usize) -> UniqueSrc<[MaybeUninit<T>]> {
    let header = InnerHeader::new_inner::<T, AllocUninit>(len);
    // SAFETY:
    // * we just got this from InnerHeader::new_inner::<T>
    // * no one else has seen the ptr yet, so the read/write requirements are fine
    let start = unsafe { InnerHeader::get_body_ptr::<T>(header) }.cast();
    UniqueSrc {
      // the safety invariant of _.header is fulfilled by definition
      header,
      // the safety invariant of _.start is fulfilled by definition
      start,
      // the safety invariant of _.len is fulfilled by definition
      len,
      _phantom: PhantomData,
    }
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` of the given length with uninitialized contents, with the memory being filled with `0` bytes.
  /// 
  /// See [`MaybeUninit::zeroed`] for examples of correct and incorrect usage of this method.
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let zeroes = UniqueSrc::<[i32]>::new_zeroed(3);
  /// let zeroes = unsafe { zeroes.assume_init() };
  /// 
  /// assert_eq!(*zeroes, [0, 0, 0]);
  /// ```
  pub fn new_zeroed(len: usize) -> UniqueSrc<[MaybeUninit<T>]> {
    let header = InnerHeader::new_inner::<T, AllocZeroed>(len);
    // SAFETY:
    // * we just got this from InnerHeader::new_inner::<T>
    // * no one else has seen the ptr yet, so the read/write requirements are fine
    let start = unsafe { InnerHeader::get_body_ptr::<T>(header) }.cast();
    UniqueSrc {
      // the safety invariant of _.header is fulfilled by definition
      header,
      // the safety invariant of _.start is fulfilled by definition
      start,
      // the safety invariant of _.len is fulfilled by definition
      len,
      _phantom: PhantomData,
    }
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` of the given length where each element is produced by calling `f` with that element's index while walking forward through the slice.
  /// 
  /// This essentially the same as writing
  /// ```text
  /// UniqueSrc::from_array([f(0), f(1), f(2), ..., f(len - 2), f(len - 1)])
  /// ```
  /// and is similar to `(0..len).map(f)`, just for `UniqueSrc`s rather than iterators.
  /// 
  /// If `len == 0`, this produces an empty `UniqueSrc` without ever calling `f`.
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let slice = UniqueSrc::from_fn(5, |i| i);
  /// assert_eq!(*slice, [0, 1, 2, 3, 4]);
  /// 
  /// let slice2 = UniqueSrc::from_fn(8, |i| i * 2);
  /// assert_eq!(*slice2, [0, 2, 4, 6, 8, 10, 12, 14]);
  /// 
  /// let bool_slice = UniqueSrc::from_fn(5, |i| i % 2 == 0);
  /// assert_eq!(*bool_slice, [true, false, true, false, true]);
  /// ```
  /// 
  /// You can also capture things, so you can use closures with mutable state.
  /// The slice is generated in ascending index order, starting from the front and going towards the back.
  /// ```rust
  /// # use slice_rc::UniqueSrc;
  /// let mut state = 1;
  /// let s = UniqueSrc::from_fn(6, |_| { let x = state; state *= 2; x });
  /// assert_eq!(*s, [1, 2, 4, 8, 16, 32]);
  /// ```
  /// 
  /// # Panics
  /// 
  /// Panics if `f` panics; in this event, any elements that have been initialized will be properly dropped.
  /// ```rust
  /// # use slice_rc::UniqueSrc;
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
  ///   UniqueSrc::from_fn(10, |i| {
  ///     if i >= 5 { panic!() }
  ///     Droppable
  ///   })
  /// });
  /// 
  /// assert_eq!(DROPPED.get(), 5);
  /// ```
  #[inline]
  pub fn from_fn<F: FnMut(usize) -> T>(len: usize, f: F) -> UniqueSrc<[T]> {
    UninitSrc::new(len).init_unique_from_fn(f)
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` of the given length where each element is produced by calling `f` with a root [`WeakSrc`] pointer to the new allocation and that element's index while walking forward through the slice.
  /// 
  /// This method is like [`UniqueSrc::from_fn`], but in this the function `f` is passed a root [`WeakSrc`] pointer to the allocation to allow constructing self-referential elements.
  /// 
  /// This is a convienience method for a specific subset of behavior that can be obtained via [`UninitSrc`].
  /// 
  /// ```rust
  /// use slice_rc::{Src, UniqueSrc, WeakSrc};
  /// 
  /// struct S {
  ///   val: usize,
  ///   root: WeakSrc<[S]>,
  /// }
  /// 
  /// let root = UniqueSrc::cyclic_from_fn(5, |root, i| S {
  ///   val: i * 2,
  ///   root: root.clone(),
  /// });
  /// 
  /// assert_eq!(root.iter().map(|s| s.val).collect::<Vec<_>>(), vec![0, 2, 4, 6, 8]);
  /// 
  /// let root = UniqueSrc::into_shared(root);
  /// 
  /// assert!(root.iter().all(|s| Src::ptr_eq(&root, &s.root.upgrade().unwrap())));
  /// ```
  /// 
  /// Note: it should be possible to obtain a weak to just the current element that is being constructed via `weak.slice(i)`,
  /// but currently a [`WeakSrc`] cannot be sliced while it is non-upgradeable (as it is in this case).
  /// This is a known issue that will be fixed in the future.
  pub fn cyclic_from_fn<F: FnMut(&WeakSrc<[T]>, usize) -> T>(len: usize, mut f: F) -> UniqueSrc<[T]> {
    let this = UninitSrc::new(len);
    let weak = this.downgrade();
    this.init_unique_from_fn(|i| f(&weak, i))
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` from the given iterator.
  /// 
  /// This method is essentially shorthand for
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// # fn f<T>(iter: impl IntoIterator<Item = T, IntoIter: std::iter::ExactSizeIterator>) -> UniqueSrc<[T]> {
  /// let mut iter = iter.into_iter();
  /// UniqueSrc::from_fn(iter.len(), |_| iter.next().unwrap())
  /// # }
  /// ```
  /// 
  /// The iterator must be [`ExactSizeIterator`] because `UniqueSrc`s cannot be resized,
  /// so the number of elements must be known at allocation-time, i.e., before any of the elements are initialized.
  /// If you want to use a non-[`ExactSizeIterator`], use <code>iter.[collect](Iterator::collect)::\<[Vec]\<_>>()</code>.
  #[inline]
  pub fn from_iter<I: IntoIterator<Item = T, IntoIter: ExactSizeIterator>>(iter: I) -> UniqueSrc<[T]> {
    let mut iter = iter.into_iter();
    UniqueSrc::from_fn(iter.len(), |_| iter.next().unwrap())
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` from the given array.
  /// 
  /// This method is effectively equivalent to passing an array to [`UniqueSrc::from_iter`], but it is more efficient.
  /// As such, it is effectively shorthand for <code>UniqueSrc::[from_fn](N, |i| values\[i])</code>, but again, more efficient
  /// (though not by enough to make <code>UniqueSrc::from_array([array::from_fn]::<_, N, _>(f))</code> any better than <code>UniqueSrc::[from_fn](N, f)</code>).
  /// 
  /// Note that the my assertions about efficiency are not based any kind of benchmarking,
  /// just the fact that this method uses a single [`ptr::write`] where [`UniqueSrc::from_fn`] and [`UniqueSrc::from_iter`] use `N` arbitrary function calls and `N` [`ptr::write`]s.
  /// As <code>[array::from_fn]</code> re-introduces at least the `N` arbitrary function calls, its difference (again, without benchmarking) is negligible.
  /// 
  /// [from_fn]: UniqueSrc::from_fn
  /// [`ptr::write`]: std::ptr::write
  /// [array::from_fn]: std::array::from_fn
  pub fn from_array<const N: usize>(values: [T; N]) -> UniqueSrc<[T]> {
    let header = InnerHeader::new_inner::<T, AllocUninit>(N);
    // SAFETY:
    // * we just got this from InnerHeader::new_inner::<T>
    // * no one else has seen the ptr yet, so the read/write requirements are fine
    let start = unsafe { InnerHeader::get_body_ptr::<T>(header) };
    // SAFETY: no one else has seen the body, so write is fine; InnerHeader::new_inner::<T>(N) guarantees N elements, so we definitely have room for [T; N]
    unsafe { start.cast().write(values) };
    UniqueSrc {
      // the safety invariant of _.header is fulfilled by definition
      header,
      // with start.write(_), the safety invariant of _.start is fulfilled by definition
      start,
      // the safety invariant of _.len is fulfilled by definition
      len: N,
      _phantom: PhantomData,
    }
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` of the given length where each element is the type's [default](Default::default).
  /// 
  /// This method is essentially equivalent to <code>UniqueSrc::[from_fn](UniqueSrc::from_fn)(len, |_| [Default::default]\())</code>.
  #[inline]
  pub fn from_default(len: usize) -> UniqueSrc<[T]> where T: Default {
    UniqueSrc::from_fn(len, |_| Default::default())
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` of the given length where each element is a clone of `value`.
  /// 
  /// This method is essentially equivalent to <code>UniqueSrc::[from_fn](UniqueSrc::from_fn)(len, |_| value.[clone](Clone::clone)())</code>.
  #[inline]
  pub fn filled(len: usize, value: &T) -> UniqueSrc<[T]> where T: Clone {
    UniqueSrc::from_fn(len, |_| value.clone())
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` of the given length where each element is a clone of the value returned from `f`.
  /// `f` is passed a root [`WeakSrc`] pointer to the allocation; this can be used to make self-referential structures.
  /// 
  /// ```rust
  /// use slice_rc::{Src, UniqueSrc, WeakSrc};
  /// 
  /// #[derive(Clone)]
  /// struct S {
  ///   val: i32,
  ///   root: WeakSrc<[S]>,
  /// }
  /// 
  /// let root = UniqueSrc::filled_cyclic(5, |root| S { val: 42, root: root.clone() });
  /// 
  /// assert!(root.iter().all(|s| s.val == 42));
  /// 
  /// let root = UniqueSrc::into_shared(root);
  /// 
  /// assert!(root.iter().all(|s| Src::ptr_eq(&root, &s.root.upgrade().unwrap())));
  /// ```
  pub fn filled_cyclic<F: FnOnce(&WeakSrc<[T]>) -> T>(len: usize, f: F) -> UniqueSrc<[T]> where T: Clone {
    let this = UninitSrc::new(len);
    let weak = this.downgrade();
    this.init_unique_filled(&f(&weak))
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` as a clone of the given slice.
  /// 
  /// This method is essentially shorthand for <code>UniqueSrc::[from_fn](UniqueSrc::from_fn)(values.[len](slice::len)(), |i| values\[i].clone())</code>,
  /// but without the implicit bounds checking for slice indexing.
  #[inline]
  pub fn cloned(values: &[T]) -> UniqueSrc<[T]> where T: Clone {
    UniqueSrc::from_fn(values.len(), |i| {
      // SAFETY: i ranges from 0..len==src.len()
      unsafe { values.get_unchecked(i) }.clone()
    })
  }
  
  /// Constructs a new [root](crate#root) `UniqueSrc` as a copy of the given slice.
  /// 
  /// This method is functionally shorthand for <code>UniqueSrc::[from_fn](UniqueSrc::from_fn)(values.[len](slice::len)(), |i| values\[i])</code>,
  /// but without the implicit bounds checking for slice indexing.
  /// 
  /// This method is fairly efficient, as it is basically just an allocation (requisite for any `UniqueSrc` constructor) and a [`memcpy`](std::ptr::copy_nonoverlapping).
  #[inline]
  pub fn copied(values: &[T]) -> UniqueSrc<[T]> where T: Copy {
    let len = values.len();
    let header = InnerHeader::new_inner::<T, AllocUninit>(len);
    // SAFETY:
    // * we just got this from InnerHeader::new_inner::<T>
    // * no one else has seen the ptr yet, so the read/write requirements are fine
    let start = unsafe { InnerHeader::get_body_ptr::<T>(header) };
    let values = NonNull::from_ref(values).cast();
    // SAFETY:
    // * values is from a reference, and is therefore valid
    // * InnerHeader::new_inner::<T>(len) guarantees that start is valid for len * size_of::<T>() bytes and aligned for T
    // * start just came from a new allocation, and therefore doesn't overlap with a slice that was passed into this function
    unsafe { values.copy_to_nonoverlapping(start, len); }
    UniqueSrc {
      // the safety invariant of _.header is fulfilled by definition
      header,
      // with values.copy_to_nonoverlapping(_, _), the safety invariant of _.start is fulfilled by definition
      start,
      // the safety invariant of _.len is fulfilled by definition
      len,
      _phantom: PhantomData,
    }
  }
  
}

impl<T> UniqueSrc<MaybeUninit<T>> {
  
  /// Converts to `UniqueSrc<T>`.
  /// 
  /// # Safety
  /// 
  /// As with [`MaybeUninit::assume_init`], it is up to the caller to guarantee that the inner value really is in an initialized state.
  /// Calling this when the content is not yet fully initialized causes immediate undefined behavior.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let zero = UniqueSrc::<i32>::single_zeroed();
  /// let zero = unsafe { zero.assume_init() };
  /// 
  /// assert_eq!(*zero, 0);
  /// ```
  pub unsafe fn assume_init(self) -> UniqueSrc<T> {
    // TODO: rephrase the safety requirements for InnerHeader to explicitly allow punning between T and type with T-like layout
    let this = UniqueSrc {
      // SAFETY: self.header has *almost* the same safety invariant as this.header: the only difference is that self uses MaybeUninit<T> where this expects T
      header: self.header,
      // SAFETY: self.start has *almost* the same safety invariant as this.start: the only difference is that self uses MaybeUninit<T> where this expects T
      start: self.start.cast(),
      // SAFETY: self.len has *almost* the same safety invariant as this.len: the only difference is that self uses MaybeUninit<T> where this expects T
      len: self.len,
      _phantom: PhantomData,
    };
    forget(self);
    this
  }
  
}

impl<T> UniqueSrc<[MaybeUninit<T>]> {
  
  /// Converts to `UniqueSrc<[T]>`.
  /// 
  /// # Safety
  /// 
  /// As with [`MaybeUninit::assume_init`], it is up to the caller to guarantee that the inner value really is in an initialized state.
  /// Calling this when the content is not yet fully initialized causes immediate undefined behavior.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let zeroes = UniqueSrc::<[i32]>::new_zeroed(3);
  /// let zeroes = unsafe { zeroes.assume_init() };
  /// 
  /// assert_eq!(*zeroes, [0, 0, 0]);
  /// ```
  pub unsafe fn assume_init(self) -> UniqueSrc<[T]> {
    // TODO: rephrase the safety requirements for InnerHeader to explicitly allow punning between T and type with T-like layout
    let this = UniqueSrc {
      // SAFETY: self.header has *almost* the same safety invariant as this.header: the only difference is that self uses MaybeUninit<T> where this expects T
      header: self.header,
      // SAFETY: self.start has *almost* the same safety invariant as this.start: the only difference is that self uses MaybeUninit<T> where this expects T
      start: self.start.cast(),
      // SAFETY: self.len has *almost* the same safety invariant as this.len: the only difference is that self uses MaybeUninit<T> where this expects T
      len: self.len,
      _phantom: PhantomData,
    };
    forget(self);
    this
  }
  
}

impl UniqueSrc<str> {
  
  /// Constructs a new [`root`](crate#root) `UniqueSrc` as a copy of the given string.
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let hello = UniqueSrc::new("Hello World!");
  /// 
  /// assert_eq!(&*hello, "Hello World!");
  /// ```
  #[inline]
  pub fn new(s: impl AsRef<str>) -> UniqueSrc<str> {
    let s = s.as_ref();
    let this = UniqueSrc::copied(s.as_bytes());
    // SAFETY: the bytes here came from a str, which already upholds the UTF-8 safety invariant
    unsafe { UniqueSrc::from_utf8_unchecked(this) }
  }
  
  /// Converts an `UniqueSrc` of bytes to a string `UniqueSrc`.
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
  /// use slice_rc::UniqueSrc;
  /// 
  /// let sparkle_heart = UniqueSrc::from_array([240, 159, 146, 150]);
  /// 
  /// let sparkle_heart = UniqueSrc::from_utf8(sparkle_heart)?;
  /// 
  /// assert_eq!("💖", &*sparkle_heart);
  /// # Ok::<_, std::str::Utf8Error>(())
  /// ```
  /// 
  /// Incorrect bytes:
  /// 
  /// ```rust
  /// # use slice_rc::UniqueSrc;
  /// let sparkle_heart = UniqueSrc::from_array([0, 159, 146, 150]);
  /// 
  /// assert!(UniqueSrc::from_utf8(sparkle_heart).is_err());
  /// ```
  #[inline]
  pub fn from_utf8(v: UniqueSrc<[u8]>) -> Result<UniqueSrc<str>, Utf8Error> {
    let _: &str = <str>::from_utf8(&*v)?;
    // SAFETY: <str>::from_utf8() guarantees that the contents are UTF-8
    Ok(unsafe { UniqueSrc::from_utf8_unchecked(v) })
  }
  
  /// Converts an `UniqueSrc` of bytes to a string `UniqueSrc` without checking that the string contains valid UTF-8.
  /// 
  /// See the safe version, [`from_utf8`](UniqueSrc::from_utf8), for more information.
  /// 
  /// # Safety
  /// 
  /// The bytes passed in must be valid UTF-8.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let sparkle_heart = UniqueSrc::from_array([240, 159, 146, 150]);
  /// 
  /// let sparkle_heart = unsafe { UniqueSrc::from_utf8_unchecked(sparkle_heart) };
  /// 
  /// assert_eq!("💖", &*sparkle_heart);
  /// ```
  #[inline]
  pub unsafe fn from_utf8_unchecked(v: UniqueSrc<[u8]>) -> UniqueSrc<str> {
    // TODO: rephrase the safety requirements for InnerHeader to explicitly allow punning between T and type with T-like layout
    let this = UniqueSrc {
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
  
  /// Converts a string `UniqueSrc` to a `UniqueSrc` of bytes.
  /// To convert the the bytes back to a string, use the [`from_utf8`](UniqueSrc::from_utf8) method.
  /// 
  /// # Examples
  /// 
  /// ```rust
  /// use slice_rc::UniqueSrc;
  /// 
  /// let bytes = UniqueSrc::as_bytes(UniqueSrc::new("bors"));
  /// assert_eq!(b"bors", &*bytes);
  /// ```
  #[inline]
  pub fn as_bytes(this: UniqueSrc<str>) -> UniqueSrc<[u8]> {
    // TODO: rephrase the safety requirements for InnerHeader to explicitly allow punning between T and type with T-like layout
    let this2 = UniqueSrc {
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
    };
    forget(this);
    this2
  }
  
}

impl<T: Default> Default for UniqueSrc<T> {
  
  #[inline]
  fn default() -> Self {
    Self::single(T::default())
  }
  
}

impl<T: SrcTarget + ?Sized> Deref for UniqueSrc<T> {
  
  type Target = T;
  
  #[inline]
  fn deref(&self) -> &Self::Target {
    T::get_unique(self)
  }
  
}

impl<T: SrcTarget + ?Sized> DerefMut for UniqueSrc<T> {
  
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    T::get_unique_mut(self)
  }
  
}

impl<T: SrcTarget + ?Sized> Borrow<T> for UniqueSrc<T> {
  
  #[inline]
  fn borrow(&self) -> &T {
    &**self
  }
  
}

impl<T: SrcTarget + ?Sized> BorrowMut<T> for UniqueSrc<T> {
  
  #[inline]
  fn borrow_mut(&mut self) -> &mut T {
    &mut **self
  }
  
}

impl<T: SrcTarget + ?Sized> AsRef<T> for UniqueSrc<T> {
  
  #[inline]
  fn as_ref(&self) -> &T {
    &**self
  }
  
}

impl<T: SrcTarget + ?Sized> AsMut<T> for UniqueSrc<T> {
  
  #[inline]
  fn as_mut(&mut self) -> &mut T {
    &mut **self
  }
  
}

impl<T: SrcTarget + Index<I> + ?Sized, I> Index<I> for UniqueSrc<T> {
  
  type Output = T::Output;
  
  #[inline]
  fn index(&self, index: I) -> &Self::Output {
    &self.deref()[index]
  }
  
}

impl<T: SrcTarget + IndexMut<I> + ?Sized, I> IndexMut<I> for UniqueSrc<T> {
  
  #[inline]
  fn index_mut(&mut self, index: I) -> &mut Self::Output {
    &mut self.deref_mut()[index]
  }
  
}

impl<T: Hash + SrcTarget + ?Sized> Hash for UniqueSrc<T> {
  
  #[inline]
  fn hash<H: Hasher>(&self, state: &mut H) {
    T::hash(&**self, state);
  }
  
}

impl<T: PartialEq<U> + SrcTarget + ?Sized, U: SrcTarget + ?Sized> PartialEq<UniqueSrc<U>> for UniqueSrc<T> {
  
  #[inline]
  fn eq(&self, other: &UniqueSrc<U>) -> bool {
    T::eq(&**self, &**other)
  }
  
  #[inline]
  fn ne(&self, other: &UniqueSrc<U>) -> bool {
    T::ne(&**self, &**other)
  }
  
}

impl<T: Eq + SrcTarget + ?Sized> Eq for UniqueSrc<T> {}

impl<T: PartialOrd<U> + SrcTarget + ?Sized, U: SrcTarget + ?Sized> PartialOrd<UniqueSrc<U>> for UniqueSrc<T> {
  
  #[inline]
  fn ge(&self, other: &UniqueSrc<U>) -> bool {
    T::ge(&**self, &**other)
  }
  
  #[inline]
  fn gt(&self, other: &UniqueSrc<U>) -> bool {
    T::gt(&**self, &**other)
  }
  
  #[inline]
  fn le(&self, other: &UniqueSrc<U>) -> bool {
    T::le(&**self, &**other)
  }
  
  #[inline]
  fn lt(&self, other: &UniqueSrc<U>) -> bool {
    T::lt(&**self, &**other)
  }
  
  #[inline]
  fn partial_cmp(&self, other: &UniqueSrc<U>) -> Option<Ordering> {
    T::partial_cmp(&**self, &**other)
  }
  
}

impl<T: Ord + SrcTarget + ?Sized> Ord for UniqueSrc<T> {
  
  #[inline]
  fn cmp(&self, other: &Self) -> Ordering {
    T::cmp(&**self, &**other)
  }
  
}

impl<T: Debug + SrcTarget + ?Sized> Debug for UniqueSrc<T> {
  
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    T::fmt(self, f)
  }
  
}

impl<T: SrcTarget + ?Sized> Pointer for UniqueSrc<T> {
  
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    Pointer::fmt(&self.start, f)
  }
  
}

impl<T: SrcTarget + ?Sized> Drop for UniqueSrc<T> {
  
  fn drop(&mut self) {
    // the UninqueSrc doesn't hold a strong ref so that the weaks can't be upgraded, but for most purposes it is just a Src that is known to be the only one; so drop it as if it were one
    self.header().inc_strong_count();
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * all constructor fns for Src initialize the elements
    // * the header is only accessed from InnerHeader::get_header
    // * this is guaranteed to be the last strong reference, because UniqueSrc's invariant prevents any other strong references from existing
    unsafe { InnerHeader::drop_strong::<T::Item>(self.header); }
  }
  
}

#[cfg(test)]
mod tests {
  
  use std::{cell::Cell, mem::MaybeUninit, ops::{Deref, DerefMut}, panic::{catch_unwind, AssertUnwindSafe}, str::Utf8Error};
  use crate::*;
  
  #[test]
  fn downgrade() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(3);
    let w: WeakSrc<[u8]> = UniqueSrc::downgrade(&u);
    assert!(w.upgrade().is_none());
    let s1: Src<[u8]> = UniqueSrc::into_shared(u);
    let s2: Src<[u8]> = w.upgrade().unwrap();
    assert_eq!(s1, s2);
    assert!(Src::ptr_eq(&s1, &s2));
  }
  
  #[test]
  fn into_shared() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_array([1, 2, 3]);
    let s1: Src<[u8]> = UniqueSrc::into_shared(u);
    let s2: Src<[u8]> = s1.clone();
    assert_eq!(*s1, [1, 2, 3]);
    assert!(Src::ptr_eq(&s1, &s2));
  }
  
  #[test]
  fn empty() {
    let u: UniqueSrc<[u8]> = UniqueSrc::empty();
    assert!(u.is_empty());
    assert_eq!(u.len(), 0);
    let u: UniqueSrc<str> = UniqueSrc::empty();
    assert!(u.is_empty());
    assert_eq!(u.len(), 0);
  }
  
  #[test]
  fn len() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(0);
    assert_eq!(u.len(), 0);
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(1);
    assert_eq!(u.len(), 1);
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(17);
    assert_eq!(u.len(), 17);
  }
  
  #[test]
  fn is_empty() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(0);
    assert!(u.is_empty());
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(1);
    assert!(!u.is_empty());
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(17);
    assert!(!u.is_empty());
  }
  
  #[test]
  fn single() {
    let u: UniqueSrc<u8> = UniqueSrc::single(42);
    let s: Src<u8> = UniqueSrc::into_shared(u);
    assert!(Src::is_root(&s));
    let s: Src<[u8]> = Src::as_slice(&s);
    assert_eq!(s.len(), 1);
  }
  
  #[test]
  fn single_cyclic() {
    { // non-cyclic
      let u: UniqueSrc<u8> = UniqueSrc::single_cyclic(|_| 42);
      assert_eq!(*u, 42);
    }
    { // cyclic
      struct S {
        
        this: WeakSrc<S>,
        i: usize,
        
      }
      let u: UniqueSrc<S> = UniqueSrc::single_cyclic(|weak| S { this: weak.clone(), i: 42 });
      assert_eq!(u.i, 42);
      let w: WeakSrc<S> = UniqueSrc::downgrade(&u);
      assert!(WeakSrc::ptr_eq(&u.this, &w));
    }
  }
  
  #[test]
  fn single_uninit() {
    let mut u: UniqueSrc<MaybeUninit<u8>> = UniqueSrc::single_uninit();
    u.write(42);
    // SAFETY: just initialized this with u.write()
    let u: UniqueSrc<u8> = unsafe { u.assume_init() };
    assert_eq!(*u, 42);
  }
  
  #[test]
  fn single_zeroed() {
    let u: UniqueSrc<MaybeUninit<u8>> = UniqueSrc::single_zeroed();
    // SAFETY: u8 is a zeroable type
    let u: UniqueSrc<u8> = unsafe { u.assume_init() };
    assert_eq!(*u, 0);
  }
  
  #[test]
  fn as_slice() {
    let u: UniqueSrc<u8> = UniqueSrc::single(42);
    let u: UniqueSrc<[u8]> = UniqueSrc::as_slice(u);
    assert_eq!([42], *u);
  }
  
  #[test]
  fn new_uninit() {
    let mut u: UniqueSrc<[MaybeUninit<u8>]> = UniqueSrc::new_uninit(3);
    assert_eq!(u.len(), 3);
    for (i, elem) in u.iter_mut().enumerate() {
      elem.write(i as _);
    }
    // SAFETY: just initialized it with all the elem.write()s
    let u: UniqueSrc<[u8]> = unsafe { u.assume_init() };
    assert_eq!(*u, [0, 1, 2]);
  }
  
  #[test]
  fn new_zeroed() {
    let u: UniqueSrc<[MaybeUninit<u8>]> = UniqueSrc::new_zeroed(3);
    assert_eq!(u.len(), 3);
    // SAFETY: u8 is a zeroable type
    let u: UniqueSrc<[u8]> = unsafe { u.assume_init() };
    assert_eq!(*u, [0, 0, 0]);
  }
  
  #[test]
  fn from_fn() {
    { // normal
      let u: UniqueSrc<[usize]> = UniqueSrc::from_fn(3, |i| i * 2);
      assert_eq!(*u, [0, 2, 4]);
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
        let _: UniqueSrc<[DropFlagger<'_>]> = UniqueSrc::from_fn(drop_flags.len(), |i| {
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
      let u: UniqueSrc<[usize]> = UniqueSrc::cyclic_from_fn(3, |_, i| i * 2);
      assert_eq!(*u, [0, 2, 4]);
    }
    { // normal, cyclic
      struct S {
        
        all: WeakSrc<[S]>,
        i: usize,
        
      }
      let u: UniqueSrc<[S]> = UniqueSrc::cyclic_from_fn(3, |w, i| S { all: w.clone(), i: i * 2 });
      assert_eq!(u[0].i, 0);
      assert_eq!(u[1].i, 2);
      assert_eq!(u[2].i, 4);
      assert!(u[0].all.upgrade().is_none());
      let s1: Src<[S]> = UniqueSrc::into_shared(u);
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
        let _: UniqueSrc<[DropFlagger<'_>]> = UniqueSrc::cyclic_from_fn(drop_flags.len(), |_, i| {
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
    let u: UniqueSrc<[u8]> = UniqueSrc::from_iter(vec![1, 2, 3].into_iter().map(|i| i * 2));
    assert_eq!(*u, [2, 4, 6]);
  }
  
  #[test]
  fn from_array() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_array([1, 2, 3]);
    assert_eq!(*u, [1, 2, 3]);
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
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(3);
    assert_eq!(*u, [0, 0, 0]);
    let u: UniqueSrc<[D42]> = UniqueSrc::from_default(3);
    assert_eq!(*u, [D42(42), D42(42), D42(42)]);
  }
  
  #[test]
  fn filled() {
    let u: UniqueSrc<[u8]> = UniqueSrc::filled(3, &42);
    assert_eq!(*u, [42, 42, 42]);
  }
  
  #[test]
  fn filled_cyclic() {
    { // non-cyclic
      let u: UniqueSrc<[u8]> = UniqueSrc::filled_cyclic(3, |_| 42);
      assert_eq!(*u, [42, 42, 42]);
    }
    { // cyclic
      #[derive(Clone)]
      struct S {
        
        all: WeakSrc<[S]>,
        i: usize,
        
      }
      let u: UniqueSrc<[S]> = UniqueSrc::filled_cyclic(3, |weak| S { all: weak.clone(), i: 42 });
      assert_eq!(u[0].i, 42);
      assert_eq!(u[1].i, 42);
      assert_eq!(u[2].i, 42);
      let w: WeakSrc<[S]> = UniqueSrc::downgrade(&u);
      assert!(WeakSrc::ptr_eq(&u[0].all, &w));
    }
  }
  
  #[test]
  fn cloned() {
    #[derive(Clone, Eq, PartialEq, Debug)]
    struct NonCopy(u8);
    let u: UniqueSrc<[NonCopy]> = UniqueSrc::cloned(&[NonCopy(1), NonCopy(2), NonCopy(3)]);
    assert_eq!(*u, [NonCopy(1), NonCopy(2), NonCopy(3)]);
  }
  
  #[test]
  fn copied() {
    let u: UniqueSrc<[u8]> = UniqueSrc::copied(&[1, 2, 3]);
    assert_eq!(*u, [1, 2, 3]);
  }
  
  #[test]
  fn assume_init_single() {
    let u: UniqueSrc<MaybeUninit<u8>> = UniqueSrc::single_zeroed();
    // SAFETY: u8 is a zeroable type
    let u: UniqueSrc<u8> = unsafe { u.assume_init() };
    assert_eq!(*u, 0);
  }
  
  #[test]
  fn assume_init_slice() {
    let u: UniqueSrc<[MaybeUninit<u8>]> = UniqueSrc::new_zeroed(3);
    // SAFETY: u8 is a zeroable type
    let u: UniqueSrc<[u8]> = unsafe { u.assume_init() };
    assert_eq!(*u, [0, 0, 0]);
  }
  
  #[test]
  fn new() {
    let u: UniqueSrc<str> = UniqueSrc::new("Hello World!");
    assert_eq!(&*u, "Hello World!");
  }
  
  #[test]
  fn from_utf8() {
    { // UTF-8
      let u: UniqueSrc<[u8]> = UniqueSrc::copied(b"Hello World!");
      let u: UniqueSrc<str> = UniqueSrc::from_utf8(u).unwrap();
      assert_eq!(&*u, "Hello World!");
    }
    { // not UTF-8
      let u: UniqueSrc<[u8]> = UniqueSrc::copied(&[0xFF]);
      let _: Utf8Error = UniqueSrc::from_utf8(u).unwrap_err();
    }
  }
  
  #[test]
  fn from_utf8_unchecked() {
    let u: UniqueSrc<[u8]> = UniqueSrc::copied(b"Hello World!");
    // SAFETY: just got the bytes from a str
    let u: UniqueSrc<str> = unsafe { UniqueSrc::from_utf8_unchecked(u) };
    assert_eq!(&*u, "Hello World!");
  }
  
  #[test]
  fn as_bytes() {
    let u: UniqueSrc<str> = UniqueSrc::new("Hello World!");
    let u: UniqueSrc<[u8]> = UniqueSrc::as_bytes(u);
    assert_eq!(&*u, b"Hello World!");
  }
  
  #[test]
  fn deref() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_array([1, 2, 3]);
    assert_eq!(Deref::deref(&u), &[1, 2, 3]);
  }
  
  #[test]
  fn deref_mut() {
    let mut u: UniqueSrc<[i8]> = UniqueSrc::from_array([1, 2, 3]);
    assert_eq!(DerefMut::deref_mut(&mut u), &mut [1, 2, 3]);
    u[0] -= 4;
    u[1] = 42;
    u[2] *= 2;
    assert_eq!(DerefMut::deref_mut(&mut u), &mut [-3, 42, 6]);
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
    let u: UniqueSrc<[DropFlagger<'_>]> = UniqueSrc::from_iter(drop_flags.iter().map(DropFlagger));
    assert!(!drop_flags.iter().any(Cell::get));
    std::mem::drop(u);
    assert!(drop_flags.iter().all(Cell::get));
  }
  
}
