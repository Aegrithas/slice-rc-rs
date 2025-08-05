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
    let s2: Src<[u8]> = s1.clone_slice(1..);
    assert_ne!(s1, s2);
    assert!(!Src::ptr_eq(&s1, &s2));
    assert!(Src::same_root(&s1, &s2));
    let s3: Src<[u8]> = Src::from_default(1);
    let s4: Src<[u8]> = s3.clone_slice(1..);
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
    let s2: Src<[u8]> = s1.clone_slice(..);
    let s3: Src<[u8]> = s1.clone_slice(1..);
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
  fn len() {
    let s: Src<[u8]> = Src::from_default(0);
    assert_eq!(s.len(), 0);
    let s: Src<[u8]> = Src::from_default(1);
    assert_eq!(s.len(), 1);
    let s: Src<[u8]> = Src::from_default(17);
    assert_eq!(s.len(), 17);
  }
  
  #[test]
  fn is_empty() {
    let s: Src<[u8]> = Src::from_default(0);
    assert!(s.is_empty());
    let s: Src<[u8]> = Src::from_default(1);
    assert!(!s.is_empty());
    let s: Src<[u8]> = Src::from_default(17);
    assert!(!s.is_empty());
  }
  
  #[test]
  fn into_root() {
    let s: Src<[u8]> = Src::from_default(1);
    assert!(Src::is_root(&s));
    let s: Src<[u8]> = s.into_slice(1..);
    assert!(!Src::is_root(&s));
    let s: Src<[u8]> = s.into_root();
    assert!(Src::is_root(&s));
  }
  
  #[test]
  fn clone_root() {
    let s1: Src<[u8]> = Src::from_default(1);
    assert!(Src::is_root(&s1));
    let s1: Src<[u8]> = s1.into_slice(1..);
    assert!(!Src::is_root(&s1));
    let s2: Src<[u8]> = s1.clone_root();
    assert!(Src::is_root(&s2));
    assert!(Src::same_root(&s1, &s2));
  }
  
  #[test]
  fn downgrade_root() {
    let s1: Src<[u8]> = Src::from_default(1);
    assert!(Src::is_root(&s1));
    let s1: Src<[u8]> = s1.into_slice(1..);
    assert!(!Src::is_root(&s1));
    let w: WeakSrc<[u8]> = s1.downgrade_root();
    assert!(w.is_root());
    let s2: Src<[u8]> = w.upgrade().unwrap();
    assert!(Src::is_root(&s2));
    assert!(Src::same_root(&s1, &s2));
  }
  
  #[test]
  fn into_slice() {
    { // slice
      let s: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s, &[1, 2, 3]);
      let s: Src<[u8]> = s.into_slice(1..);
      assert_eq!(&*s, &[2, 3]);
      let s: Src<[u8]> = s.into_slice(..1);
      assert_eq!(&*s, &[2]);
    }
    { // item 1
      let s: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s, &[1, 2, 3]);
      let s: Src<u8> = s.into_slice(2);
      assert_eq!(&*s, &3);
    }
    { // item 2
      let s: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s, &[1, 2, 3]);
      let s: Src<[u8]> = s.into_slice(1..);
      assert_eq!(&*s, &[2, 3]);
      let s: Src<u8> = s.into_slice(0);
      assert_eq!(&*s, &2);
    }
  }
  
  #[test]
  fn clone_slice() {
    { // slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s1, &[1, 2, 3]);
      let s1: Src<[u8]> = s1.into_slice(1..);
      assert_eq!(&*s1, &[2, 3]);
      let s2: Src<[u8]> = s1.clone_slice(..1);
      assert_eq!(&*s2, &[2]);
      assert!(Src::same_root(&s1, &s2));
    }
    { // item 1
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s1, &[1, 2, 3]);
      let s2: Src<u8> = s1.clone_slice(2);
      assert_eq!(&*s2, &3);
      let s2: Src<[u8]> = Src::as_slice(s2);
      assert_eq!(&*s2, &[3]);
      assert!(Src::same_root(&s1, &s2));
    }
    { // item 2
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s1, &[1, 2, 3]);
      let s1: Src<[u8]> = s1.into_slice(1..);
      assert_eq!(&*s1, &[2, 3]);
      let s2: Src<u8> = s1.clone_slice(0);
      assert_eq!(&*s2, &2);
      let s2: Src<[u8]> = Src::as_slice(s2);
      assert_eq!(&*s2, &[2]);
      assert!(Src::same_root(&s1, &s2));
    }
  }
  
  #[test]
  fn downgrade_slice() {
    { // slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s1, &[1, 2, 3]);
      let s1: Src<[u8]> = s1.into_slice(1..);
      assert_eq!(&*s1, &[2, 3]);
      let w: WeakSrc<[u8]> = s1.downgrade_slice(..1);
      let s2: Src<[u8]> = w.upgrade().unwrap();
      assert_eq!(&*s2, &[2]);
      assert!(Src::same_root(&s1, &s2));
    }
    { // item 1
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s1, &[1, 2, 3]);
      let w: WeakSrc<u8> = s1.downgrade_slice(2);
      let s2: Src<u8> = w.upgrade().unwrap();
      assert_eq!(&*s2, &3);
      let s2: Src<[u8]> = Src::as_slice(s2);
      assert_eq!(&*s2, &[3]);
      assert!(Src::same_root(&s1, &s2));
    }
    { // item 2
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      assert_eq!(&*s1, &[1, 2, 3]);
      let s1: Src<[u8]> = s1.into_slice(1..);
      assert_eq!(&*s1, &[2, 3]);
      let w: WeakSrc<u8> = s1.downgrade_slice(0);
      let s2: Src<u8> = w.upgrade().unwrap();
      assert_eq!(&*s2, &2);
      let s2: Src<[u8]> = Src::as_slice(s2);
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
      let s2: Src<[u8]> = Src::as_slice(Src::clone(&s1));
      assert_eq!([*s1], *s2);
    }
    { // from slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let s2: Src<u8> = s1.clone_slice(1);
      let s3: Src<[u8]> = Src::as_slice(Src::clone(&s2));
      assert_eq!(s1[1], *s2);
      assert_eq!([*s2], *s3);
    }
  }
  
  #[test]
  fn clone_as_slice() {
    { // single root
      let s1: Src<u8> = Src::single(42);
      let s2: Src<[u8]> = Src::clone_as_slice(&s1);
      assert_eq!([*s1], *s2);
    }
    { // from slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let s2: Src<u8> = s1.clone_slice(1);
      let s3: Src<[u8]> = Src::clone_as_slice(&s2);
      assert_eq!(s1[1], *s2);
      assert_eq!([*s2], *s3);
    }
  }
  
  #[test]
  fn downgrade_as_slice() {
    { // single root
      let s1: Src<u8> = Src::single(42);
      let w: WeakSrc<[u8]> = Src::downgrade_as_slice(&s1);
      let s2: Src<[u8]> = w.upgrade().unwrap();
      assert_eq!([*s1], *s2);
    }
    { // from slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let s2: Src<u8> = s1.clone_slice(1);
      let w: WeakSrc<[u8]> = Src::downgrade_as_slice(&s2);
      let s3: Src<[u8]> = w.upgrade().unwrap();
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
    let s: Src<[u8]> = Src::as_bytes(s);
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
