use std::{borrow::Borrow, cmp::Ordering, fmt::{self, Debug, Formatter, Pointer}, hash::{Hash, Hasher}, marker::PhantomData, mem::{forget, MaybeUninit}, ops::{Bound, Deref, Index}, ptr::NonNull, str::Utf8Error};

use crate::{InnerHeader, SrcIndex, SrcSlice, SrcTarget, UninitSrc, UniqueSrc, WeakSrc};

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
  
  pub(crate) fn into_item(self, index: usize) -> Src<T::Item> {
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
  pub fn cloned(values: &[T]) -> Src<[T]> where T: Clone {
    UniqueSrc::into_shared(UniqueSrc::cloned(values))
  }
  
  #[inline]
  pub fn copied(values: &[T]) -> Src<[T]> where T: Copy {
    UniqueSrc::into_shared(UniqueSrc::copied(values))
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
