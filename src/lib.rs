mod inner;

use std::{borrow::{Borrow, BorrowMut}, cmp::Ordering, fmt::{self, Debug, Formatter, Pointer}, hash::{Hash, Hasher}, marker::PhantomData, mem::{forget, MaybeUninit}, ops::{Bound, Deref, DerefMut, Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive}, ptr::{without_provenance_mut, NonNull}, slice, str::Utf8Error, usize};

use inner::*;

pub struct Src<T: SrcTarget + ?Sized> {
  
  // SAFETY:
  // requires:
  // * initialized from InnerHeader::new_inner::<T::Item>(_)
  header: NonNull<InnerHeader>,
  // SAFETY:
  // requires:
  // * initialized from either InnerHeader::get_body_ptr::<T::Item>(self.header) or InnerHeader::get_elem_ptr::<T::Item>(self.header, i) where 0 <= i <= InnerHeader::get_header(self.header).len()
  // * all body elements have been properly initialized (e.g., self.start.as_ref() will not cause UB)
  start: NonNull<T::Item>,
  // SAFETY:
  // requires when T: SrcSlice:
  // * self.start.add(self.len) <= InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  // requires when T: Sized:
  // * self.start < InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  len: T::Len,
  _phantom: PhantomData<*const T>,
  
}

impl<T: SrcTarget + ?Sized> Src<T> {
  
  fn header(&self) -> &InnerHeader {
    // SAFETY:
    // * the invariant for self.header guarantees that it is from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    unsafe { InnerHeader::get_header(self.header) }
  }
  
  #[inline]
  pub fn ptr_eq(this: &Src<T>, other: &Src<T>) -> bool {
    this.start == other.start
  }
  
  #[inline]
  pub fn same_root(this: &Src<T>, other: &Src<T>) -> bool {
    this.header == other.header
  }
  
  #[inline]
  pub fn is_root(this: &Src<T>) -> bool {
    // SAFETY:
    // * the invariant for this.header guarantees that it is from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    let root_start = unsafe { InnerHeader::get_body_ptr(this.header) };
    this.start == root_start && T::len_as_usize(this.len) == this.header().len()
  }
  
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
  
  pub fn strong_count(this: &Src<T>) -> usize {
    this.header().strong_count()
  }
  
  pub fn weak_count(this: &Src<T>) -> usize {
    this.header().weak_count()
  }
  
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
  
  pub fn make_unique(this: Src<T>) -> UniqueSrc<T> where T::Item: Clone {
    Src::into_unique(this).unwrap_or_else(|this| T::new_unique_from_clone(&*this))
  }
  
}

impl<T: SrcSlice + ?Sized> Src<T> {
  
  // technically unnecessary (because a self.deref().len() will get the same number), but potentially more efficient because there is no need to construct the whole slice
  #[inline]
  pub fn len(&self) -> usize {
    self.len
  }
  
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }
  
  pub fn into_root(self) -> Src<T> {
    let header = self.header();
    // SAFETY:
    // * the invariant for self.header guarantees that it is from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    let start = unsafe { InnerHeader::get_body_ptr::<T::Item>(self.header) };
    let this = Src {
      // SAFETY: self.header has the same safety invariant as this.header
      header: self.header,
      // SAFETY: start was just aquired from InnerHeader::get_body_ptr::<T::Item>(self.header), which, with the assertions, meets the safety requirement
      start,
      // SAFETY: header.len() meets the safety requirements by definition
      len: header.len(),
      _phantom: PhantomData,
    };
    forget(self); // don't modify the strong count because this is logically the same Src
    this
  }
  
  #[inline]
  pub fn clone_root(&self) -> Src<T> {
    self.clone().into_root()
  }
  
  #[inline]
  pub fn downgrade_root(&self) -> WeakSrc<T> {
    Self::downgrade(self).into_root()
  }
  
  #[inline]
  pub fn into_slice<I: SrcIndex<T>>(self, index: I) -> Src<I::Output> {
    index.get(self)
  }
  
  #[inline]
  pub fn clone_slice<I: SrcIndex<T>>(&self, index: I) -> Src<I::Output> {
    self.clone().into_slice(index)
  }
  
  #[inline]
  pub fn downgrade_slice<I: SrcIndex<T>>(&self, index: I) -> WeakSrc<I::Output> {
    Src::downgrade(self).into_slice(index)
  }
  
  fn into_item(self, index: usize) -> Src<T::Item> {
    let header = self.header();
    assert!(index < header.len(), "index {index} out of range for slice of length {}", header.len());
    let start_ptr = unsafe { InnerHeader::get_elem_ptr::<T::Item>(self.header, index) };
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
  
  fn into_slice_from_bounds(self, start: Bound<usize>, end: Bound<usize>) -> Src<T> {
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
    // SAFETY:
    // * the invariant for self.header guarantees that it is from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    // * the assertions verify that start_exc <= end_exc <= header.len()
    let start_ptr = unsafe { InnerHeader::get_elem_ptr::<T::Item>(self.header, start_inc) };
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

impl<T> Src<T> {
  
  #[inline]
  pub fn single(value: T) -> Src<T> {
    UninitSrc::single().init(value)
  }
  
  #[inline]
  pub fn single_uninit() -> Src<MaybeUninit<T>> {
    UniqueSrc::into_shared(UniqueSrc::single_uninit())
  }
  
  #[inline]
  pub fn single_zeroed() -> Src<MaybeUninit<T>> {
    UniqueSrc::into_shared(UniqueSrc::single_zeroed())
  }
  
  #[inline]
  pub fn as_slice(this: Src<T>) -> Src<[T]> {
    let this2 = Src {
      // SAFETY: this.header has the same invariant as this2
      header: this.header,
      // SAFETY: this.start has the same invariant as this2
      start: this.start,
      // SAFETY: this.len's invariant implies this2.len's invariant
      len: 1,
      _phantom: PhantomData,
    };
    forget(this); // don't modify the strong count because this is logically the same Src
    this2
  }
  
  #[inline]
  pub fn clone_as_slice(this: &Src<T>) -> Src<[T]> {
    Src::as_slice(Src::clone(this))
  }
  
  #[inline]
  pub fn downgrade_as_slice(this: &Src<T>) -> WeakSrc<[T]> {
    Self::downgrade(this).as_slice()
  }
  
}

impl<T> Src<[T]> {
  
  #[inline]
  pub fn new_uninit(len: usize) -> Src<[MaybeUninit<T>]> {
    UniqueSrc::into_shared(UniqueSrc::new_uninit(len))
  }
  
  #[inline]
  pub fn new_zeroed(len: usize) -> Src<[MaybeUninit<T>]> {
    UniqueSrc::into_shared(UniqueSrc::new_zeroed(len))
  }
  
  #[inline]
  pub fn from_fn<F: FnMut(usize) -> T>(len: usize, f: F) -> Src<[T]> {
    UninitSrc::new(len).init_from_fn(f)
  }
  
  pub fn cyclic_from_fn<F: FnMut(&WeakSrc<[T]>, usize) -> T>(len: usize, mut f: F) -> Src<[T]> {
    let this = UninitSrc::new(len);
    let weak = this.downgrade();
    this.init_from_fn(|i| f(&weak, i))
  }
  
  pub fn from_iter<I: IntoIterator<Item = T, IntoIter: ExactSizeIterator>>(iter: I) -> Src<[T]> {
    let mut iter = iter.into_iter();
    Self::from_fn(iter.len(), |_| iter.next().unwrap())
  }
  
  #[inline]
  pub fn from_array<const N: usize>(values: [T; N]) -> Src<[T]> {
    UniqueSrc::into_shared(UniqueSrc::from_array(values))
  }
  
  #[inline]
  pub fn from_default(len: usize) -> Src<[T]> where T: Default {
    Self::from_fn(len, |_| Default::default())
  }
  
  #[inline]
  pub fn filled(len: usize, value: &T) -> Src<[T]> where T: Clone {
    Self::from_fn(len, |_| value.clone())
  }
  
  #[inline]
  pub fn clone_from_slice(values: &[T]) -> Src<[T]> where T: Clone {
    UniqueSrc::into_shared(UniqueSrc::clone_from_slice(values))
  }
  
  #[inline]
  pub fn copy_from_slice(values: &[T]) -> Src<[T]> where T: Copy {
    UniqueSrc::into_shared(UniqueSrc::copy_from_slice(values))
  }
  
}

impl<T> Src<MaybeUninit<T>> {
  
  // SAFETY: As with MaybeUninit::assume_init, it is up to the caller to guarantee that the inner value really is in an initialized state. Calling this when the content is not yet fully initialized causes immediate undefined behavior.
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
  
  // SAFETY: As with MaybeUninit::assume_init, it is up to the caller to guarantee that the inner value really is in an initialized state. Calling this when the content is not yet fully initialized causes immediate undefined behavior.
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
  
  #[inline]
  pub fn new(s: impl AsRef<str>) -> Src<str> {
    UniqueSrc::into_shared(UniqueSrc::new(s))
  }
  
  #[inline]
  pub fn from_utf8(v: Src<[u8]>) -> Result<Src<str>, Utf8Error> {
    let _: &str = str::from_utf8(&*v)?;
    // SAFETY: <str>::from_utf8() guarantees that the contents are UTF-8
    Ok(unsafe { Src::from_utf8_unchecked(v) })
  }
  
  // SAFETY:
  // The bytes passed in must be valid UTF-8
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
  
  #[inline]
  pub fn as_bytes(this: Src<str>) -> Src<[u8]> {
    // TODO: rephrase the safety requirements for InnerHeader to explicitly allow punning between T and type with T-like layout
    let this2 = Src {
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

const fn non_null_max<T>() -> NonNull<T> {
  let max_ptr = without_provenance_mut(usize::MAX);
  // SAFETY: usize::MAX != 0usize
  unsafe { NonNull::new_unchecked(max_ptr) }
}

pub struct WeakSrc<T: SrcTarget + ?Sized> {
  
  // SAFETY:
  // requires:
  // * initialized from InnerHeader::new_inner::<T::Item>(_) or non_null_max::<ItemHeader>()
  header: NonNull<InnerHeader>,
  // SAFETY:
  // requires:
  // * either:
  //   * initialized from either InnerHeader::get_body_ptr::<T::Item>(self.header) or InnerHeader::get_elem_ptr::<T::Item>(self.header, i) where 0 <= i <= InnerHeader::get_header(self.header).len()
  //   * all body elements have been properly initialized (e.g., self.start.as_ref() will not cause UB), or strong_count == 0
  // * or, iff self.header is non_null_max::<ItemHeader>(), then self.start is non_null_max::<T::Item>()
  start: NonNull<T::Item>,
  // SAFETY:
  // only applies if self.header != non_null_max::<ItemHeader>():
  // requires when T: SrcSlice:
  // * self.start.add(self.len) <= InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  // requires when T: Sized:
  // * self.start < InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  len: T::Len,
  _phantom: PhantomData<*const T>,
  
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
  
  #[inline]
  pub fn dangling() -> WeakSrc<T> {
    WeakSrc {
      header: non_null_max(),
      start: non_null_max(),
      len: T::Len::default(),
      _phantom: PhantomData,
    }
  }
  
  #[inline]
  pub fn is_dangling(&self) -> bool {
    self.header == non_null_max()
  }
  
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
  
  #[inline]
  pub fn ptr_eq(&self, other: &Src<T>) -> bool {
    self.start == other.start
  }
  
  #[inline]
  pub fn same_root(&self, other: &Src<T>) -> bool {
    self.header == other.header
  }
  
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
  
  pub fn strong_count(&self) -> usize {
    if !self.is_dangling() {
      // SAFETY: we just checked that this weak is not dangling
      unsafe { self.header() }.strong_count()
    } else {
      0
    }
  }
  
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
  
}

impl<T: SrcSlice + ?Sized> WeakSrc<T> {
  
  #[inline]
  pub fn len(&self) -> usize {
    self.len
  }
  
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }
  
  pub fn into_root(self) -> WeakSrc<T> {
    if self.is_dangling() {
      return WeakSrc::dangling()
    }
    // SAFETY: we just checked that this weak is not dangling
    let header = unsafe { self.header() };
    // SAFETY:
    // * all constructor fns for Src and UninitSrc initialize header from InnerHeader::new_inner::<T::Item>; a WeakSrc must be constructed either from a Src, an UninitSrc, or must be dangling; we just checked that this weak is not dangling
    // * the header is only accessed from InnerHeader::get_header
    let start = unsafe { InnerHeader::get_body_ptr(self.header) };
    let this = WeakSrc {
      // SAFETY: this self.header has the same safety invariant as this.header
      header: self.header,
      // SAFETY: if this weak is not dangling (which we checked earlier), the start that we just calculated earlier meets the safety invariant by definition
      start,
      // SAFETY: if this weak is not dangling (which we checked earlier), header.len() meets the safety invariant by definition
      len: header.len(),
      _phantom: PhantomData,
    };
    forget(self); // don't decrease the weak counter because this is logically the same WeakSrc
    this
  }
  
  #[inline]
  pub fn clone_root(&self) -> WeakSrc<T> {
    self.clone().into_root()
  }
  
  #[inline]
  pub fn upgrade_root(&self) -> Option<Src<T>> {
    self.upgrade().map(Src::into_root)
  }
  
  #[inline]
  pub fn into_slice<I: SrcIndex<T>>(self, index: I) -> WeakSrc<I::Output> {
    index.get_weak(self)
  }
  
  #[inline]
  pub fn clone_slice<I: SrcIndex<T>>(&self, index: I) -> WeakSrc<I::Output> {
    self.clone().into_slice(index)
  }
  
  #[inline]
  pub fn upgrade_slice<I: SrcIndex<T>>(&self, index: I) -> Option<Src<I::Output>> {
    self.upgrade().map(move |s| Src::into_slice(s, index))
  }
  
  fn into_item(self, index: usize) -> WeakSrc<T::Item> {
    assert!(!self.is_dangling(), "cannot slice a dangling WeakSrc");
    // SAFETY: we just checked that this weak is not dangling
    let header = unsafe { self.header() };
    assert!(index < header.len(), "index {index} out of range for slice of length {}", header.len());
    let start_ptr = unsafe { InnerHeader::get_elem_ptr::<T::Item>(self.header, index) };
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
  
  fn into_slice_from_bounds(self, start: Bound<usize>, end: Bound<usize>) -> WeakSrc<T> {
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
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    // * the assertions verify that start_exc <= end_exc <= header.len
    let start_ptr = unsafe { InnerHeader::get_elem_ptr::<T::Item>(self.header, start_inc) };
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
  unsafe fn get_slice(&self) -> &[T::Item] {
    let s = NonNull::slice_from_raw_parts(self.start, self.len);
    // SAFETY: the safety requirements of this fn combined with the invariants of WeakSrc guarantee that this refers to a properly initialized slice
    unsafe { s.as_ref() }
  }
  
}

impl<T> WeakSrc<T> {
  
  #[inline]
  pub fn as_slice(self) -> WeakSrc<[T]> {
    let this = WeakSrc {
      // SAFETY: the safety invariant of self.header is the same as this.header
      header: self.header,
      // SAFETY: the safety invariant of self.start is the same as this.start
      start: self.start,
      // SAFETY: if this weak is dangling, then self.len has no safety invariant; if it is weak, then the safety invariant of self.len is logically identical to that of this.len
      len: 1,
      _phantom: PhantomData,
    };
    forget(self); // don't modify the weak count because this is logically the same WeakSrc
    this
  }
  
  #[inline]
  pub fn clone_as_slice(&self) -> WeakSrc<[T]> {
    self.clone().as_slice()
  }
  
  #[inline]
  pub fn upgrade_as_slice(&self) -> Option<Src<[T]>> {
    self.upgrade().map(Src::as_slice)
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

pub struct UninitSrc<T: SrcTarget + ?Sized> {
  
  // SAFETY:
  // requires:
  // * initialized from InnerHeader::new_inner::<T::Item>(_)
  header: NonNull<InnerHeader>,
  // SAFETY:
  // requires when T: SrcSlice:
  // * self.start.add(self.len) <= InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  // requires when T: Sized:
  // * self.start < InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  len: T::Len,
  _phantom: PhantomData<*const T>,
  
}

impl<T: SrcTarget + ?Sized> UninitSrc<T> {
  
  fn header(&self) -> &InnerHeader {
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    unsafe { InnerHeader::get_header(self.header) }
  }
  
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
  
  #[inline]
  pub fn len(&self) -> usize {
    self.len
  }
  
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }
  
  #[inline]
  pub fn downgrade_slice<I: SrcIndex<T>>(&self, index: I) -> WeakSrc<I::Output> {
    self.downgrade().into_slice(index)
  }
  
}

impl<T> UninitSrc<T> {
  
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
  
  #[inline]
  pub fn init(self, value: T) -> Src<T> {
    UniqueSrc::into_shared(self.init_unique(value))
  }
  
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
  
  #[inline]
  pub fn downgrade_as_slice(&self) -> WeakSrc<[T]> {
    self.downgrade().as_slice()
  }
  
}

impl<T> UninitSrc<[T]> {
  
  // NOTE: this could be generalized to UninitSrc<T> for T: SrcSlice, but given
  //   a) that there's no way to initialize any T: SrcSlice other than [T], and
  //   b) that UninitSrc is really only useful for self-reference, which is not relevant for str,
  // this is placed here for simplicity
  #[inline]
  pub fn new(len: usize) -> UninitSrc<[T]> {
    let header = InnerHeader::new_inner::<T, Alloc>(len);
    Self {
      // SAFETY: the safety invariant of _.header is fulfilled by definition
      header,
      // SAFETY: the safety invariant of _.len is fulfilled by definition
      len,
      _phantom: PhantomData,
    }
  }
  
  #[inline]
  pub fn init_from_fn<F: FnMut(usize) -> T>(self, f: F) -> Src<[T]> {
    UniqueSrc::into_shared(self.init_unique_from_fn(f))
  }
  
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
  
  #[inline]
  pub fn init_from_default(self) -> Src<[T]> where T: Default {
    self.init_from_fn(|_| T::default())
  }
  
  #[inline]
  pub fn init_unique_from_default(self) -> UniqueSrc<[T]> where T: Default {
    self.init_unique_from_fn(|_| T::default())
  }
  
  #[inline]
  pub fn init_filled(self, value: &T) -> Src<[T]> where T: Clone {
    self.init_from_fn(|_| value.clone())
  }
  
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

pub struct UniqueSrc<T: SrcTarget + ?Sized> {
  
  // SAFETY:
  // requires:
  // * initialized from InnerHeader::new_inner::<T::Item>(_)
  header: NonNull<InnerHeader>,
  // SAFETY:
  // requires:
  // * initialized from either InnerHeader::get_body_ptr::<T::Item>(self.header) or InnerHeader::get_elem_ptr::<T::Item>(self.header, i) where 0 <= i <= InnerHeader::get_header(self.header).len()
  // * all body elements have been properly initialized (e.g., self.start.as_ref() will not cause UB)
  start: NonNull<T::Item>,
  // SAFETY:
  // requires when T: SrcSlice:
  // * self.start.add(self.len) <= InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  // requires when T: Sized:
  // * self.start < InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  len: T::Len,
  _phantom: PhantomData<*const T>,
  
}

impl<T: SrcTarget + ?Sized> UniqueSrc<T> {
  
  fn header(&self) -> &InnerHeader {
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    unsafe { InnerHeader::get_header(self.header) }
  }
  
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
  
  #[inline]
  pub fn len(&self) -> usize {
    self.len
  }
  
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }
  
  #[inline]
  pub fn downgrade_slice<I: SrcIndex<T>>(&self, index: I) -> WeakSrc<I::Output> {
    UniqueSrc::downgrade(&self).into_slice(index)
  }
  
}

impl<T> UniqueSrc<T> {
  
  #[inline]
  pub fn single(value: T) -> UniqueSrc<T> {
    UninitSrc::single().init_unique(value)
  }
  
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
  
  #[inline]
  pub fn downgrade_as_slice(this: &UniqueSrc<T>) -> WeakSrc<[T]> {
    UniqueSrc::downgrade(this).as_slice()
  }
  
}

impl<T> UniqueSrc<[T]> {
  
  pub fn new_uninit(len: usize) -> UniqueSrc<[MaybeUninit<T>]> {
    let header = InnerHeader::new_inner::<T, Alloc>(len);
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
  
  #[inline]
  pub fn from_fn<F: FnMut(usize) -> T>(len: usize, f: F) -> UniqueSrc<[T]> {
    UninitSrc::new(len).init_unique_from_fn(f)
  }
  
  pub fn cyclic_from_fn<F: FnMut(&WeakSrc<[T]>, usize) -> T>(len: usize, mut f: F) -> UniqueSrc<[T]> {
    let this = UninitSrc::new(len);
    let weak = this.downgrade();
    this.init_unique_from_fn(|i| f(&weak, i))
  }
  
  #[inline]
  pub fn from_iter<I: IntoIterator<Item = T, IntoIter: ExactSizeIterator>>(iter: I) -> UniqueSrc<[T]> {
    let mut iter = iter.into_iter();
    UniqueSrc::from_fn(iter.len(), |_| iter.next().unwrap())
  }
  
  pub fn from_array<const N: usize>(values: [T; N]) -> UniqueSrc<[T]> {
    let header = InnerHeader::new_inner::<T, Alloc>(N);
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
  
  #[inline]
  pub fn from_default(len: usize) -> UniqueSrc<[T]> where T: Default {
    UniqueSrc::from_fn(len, |_| Default::default())
  }
  
  #[inline]
  pub fn filled(len: usize, value: &T) -> UniqueSrc<[T]> where T: Clone {
    UniqueSrc::from_fn(len, |_| value.clone())
  }
  
  #[inline]
  pub fn clone_from_slice(values: &[T]) -> UniqueSrc<[T]> where T: Clone {
    UniqueSrc::from_fn(values.len(), |i| {
      // SAFETY: i ranges from 0..len==src.len()
      unsafe { values.get_unchecked(i) }.clone()
    })
  }
  
  #[inline]
  pub fn copy_from_slice(values: &[T]) -> UniqueSrc<[T]> where T: Copy {
    let len = values.len();
    let header = InnerHeader::new_inner::<T, Alloc>(len);
    // SAFETY:
    // * we just got this from InnerHeader::new_inner::<T>
    // * no one else has seen the ptr yet, so the read/write requirements are fine
    let start = unsafe { InnerHeader::get_body_ptr::<T>(header) };
    // SAFETY: references can't be null
    let values = unsafe { NonNull::new_unchecked(values.as_ptr().cast_mut()) };
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
  
  // SAFETY: As with MaybeUninit::assume_init, it is up to the caller to guarantee that the inner value really is in an initialized state. Calling this when the content is not yet fully initialized causes immediate undefined behavior.
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
  
  // SAFETY: As with MaybeUninit::assume_init, it is up to the caller to guarantee that the inner value really is in an initialized state. Calling this when the content is not yet fully initialized causes immediate undefined behavior.
  pub unsafe fn assume_init(self) -> UniqueSrc<[T]> {
    // TODO: rephrase the safety requirements for InnerHeader to explicitly allow punning between T and type with T-like layout
    UniqueSrc {
      // SAFETY: self.header has *almost* the same safety invariant as this.header: the only difference is that self uses MaybeUninit<T> where this expects T
      header: self.header,
      // SAFETY: self.start has *almost* the same safety invariant as this.start: the only difference is that self uses MaybeUninit<T> where this expects T
      start: self.start.cast(),
      // SAFETY: self.len has *almost* the same safety invariant as this.len: the only difference is that self uses MaybeUninit<T> where this expects T
      len: self.len,
      _phantom: PhantomData,
    }
  }
  
}

impl UniqueSrc<str> {
  
  #[inline]
  pub fn new(s: impl AsRef<str>) -> UniqueSrc<str> {
    let s = s.as_ref();
    let this = UniqueSrc::copy_from_slice(s.as_bytes());
    // SAFETY: the bytes here came from a str, which already upholds the UTF-8 safety invariant
    unsafe { UniqueSrc::from_utf8_unchecked(this) }
  }
  
  #[inline]
  pub fn from_utf8(v: UniqueSrc<[u8]>) -> Result<UniqueSrc<str>, Utf8Error> {
    let _: &str = <str>::from_utf8(&*v)?;
    // SAFETY: <str>::from_utf8() guarantees that the contents are UTF-8
    Ok(unsafe { UniqueSrc::from_utf8_unchecked(v) })
  }
  
  // SAFETY:
  // The bytes passed in must be valid UTF-8
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

pub trait SrcIndex<T: SrcSlice + ?Sized> {
  
  type Output: SrcTarget + ?Sized;
  
  fn get(self, slice: Src<T>) -> Src<Self::Output>;
  
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

pub trait SrcTarget: private::SealedSrcTarget {
  
  type Item;
  
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
    UniqueSrc::clone_from_slice(self)
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
