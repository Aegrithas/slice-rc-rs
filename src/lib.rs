mod inner;

use std::{borrow::Borrow, cmp::Ordering, fmt::{self, Debug, Formatter, Pointer}, hash::{Hash, Hasher}, marker::PhantomData, mem::forget, ops::{Bound, Deref, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive}, ptr::{without_provenance_mut, NonNull}, slice, str::Utf8Error, usize};

use inner::*;

pub struct Src<T: SrcTarget + ?Sized> {
  
  header: NonNull<InnerHeader>,
  start: NonNull<T::Item>,
  len: T::Len,
  _phantom: PhantomData<*const T>,
  
}

impl<T: SrcTarget + ?Sized> Src<T> {
  
  fn header(&self) -> &InnerHeader {
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    unsafe { InnerHeader::get_header(self.header) }
  }
  
  #[inline]
  pub fn ptr_eq(this: &Src<T>, other: &Src<T>) -> bool {
    this.start == other.start
  }
  
  #[inline]
  pub fn root_ptr_eq(this: &Src<T>, other: &Src<T>) -> bool {
    this.header == other.header
  }
  
  #[inline]
  pub fn is_root(this: &Src<T>) -> bool {
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    let root_start = unsafe { InnerHeader::get_body_ptr(this.header) };
    this.start == root_start
  }
  
  pub fn downgrade(this: &Src<T>) -> WeakSrc<T> {
    this.header().inc_weak_count();
    WeakSrc {
      header: this.header,
      start: this.start,
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
  
  pub fn clone_root(&self) -> Src<T> {
    let header = self.header();
    header.inc_strong_count();
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    let start = unsafe { InnerHeader::get_body_ptr(self.header) };
    Src {
      header: self.header,
      start,
      len: header.len(),
      _phantom: PhantomData,
    }
  }
  
  #[inline]
  pub fn clone_slice<I: CloneSliceIndex<T>>(&self, index: I) -> Src<I::Output> {
    index.clone_get(self)
  }
  
  fn clone_item(this: &Src<T>, index: usize) -> Src<T::Item> {
    let header = this.header();
    assert!(index < header.len(), "index {index} out of range for slice of length {}", header.len());
    let start_ptr = unsafe { InnerHeader::get_elem_ptr::<T::Item>(this.header, index) };
    header.inc_strong_count();
    Src {
      header: this.header,
      start: start_ptr,
      len: (),
      _phantom: PhantomData,
    }
  }
  
  fn clone_from_bounds(this: &Src<T>, start: Bound<usize>, end: Bound<usize>) -> Src<T> {
    let header = this.header();
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
    T::validate_indices(this, start_inc, end_exc);
    let len = end_exc - start_inc;
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    // * the assertions verify that start_exc <= end_exc <= header.len
    let start_ptr = unsafe { InnerHeader::get_elem_ptr::<T::Item>(this.header, start_inc) };
    header.inc_strong_count();
    Self {
      header: this.header,
      start: start_ptr,
      len,
      _phantom: PhantomData,
    }
  }
  
}

impl<T> Src<T> {
  
  #[inline]
  pub fn single(value: T) -> Src<T> {
    UninitSrc::single().init(value)
  }
  
  #[inline]
  pub fn clone_as_slice(&self) -> Src<[T]> {
    self.header().inc_strong_count();
    Src {
      header: self.header,
      start: self.start,
      len: 1,
      _phantom: PhantomData,
    }
  }
  
}

impl<T> Src<[T]> {
  
  #[inline]
  pub fn from_fn<F: FnMut(usize) -> T>(len: usize, f: F) -> Src<[T]> {
    UninitSrc::new(len).init_from_fn(f)
  }
  
  pub fn cyclic_from_fn<F: FnMut(&WeakSrc<[T]>, usize) -> T>(len: usize, mut f: F) -> Src<[T]> {
    let this = UninitSrc::new(len);
    let weak = this.weak();
    this.init_from_fn(|i| f(&weak, i))
  }
  
  pub fn from_iter<I: IntoIterator<Item = T, IntoIter: ExactSizeIterator>>(iter: I) -> Src<[T]> {
    let mut iter = iter.into_iter();
    Self::from_fn(iter.len(), |_| iter.next().unwrap())
  }
  
  #[inline]
  pub fn from_array<const N: usize>(values: [T; N]) -> Src<[T]> {
    let header = InnerHeader::new_inner::<T>(N, 1);
    // SAFETY:
    // * we just got this from InnerHeader::new_inner::<T>
    // * no one else has seen the ptr yet, so the read/write requirements are fine
    let start = unsafe { InnerHeader::get_body_ptr::<T>(header) };
    // SAFETY: no one else has seen the body, so write is fine; InnerHeader::new_inner::<T>(N) guarantees N elements, so we definitely have room for [T; N]
    unsafe { start.cast().write(values) };
    Self {
      header,
      start,
      len: N,
      _phantom: PhantomData,
    }
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
    Self::from_fn(values.len(), |i| {
      // SAFETY: i ranges from 0..len==src.len()
      unsafe { values.get_unchecked(i) }.clone()
    })
  }
  
  #[inline]
  pub fn copy_from_slice(values: &[T]) -> Src<[T]> where T: Copy {
    Self::from_fn(values.len(), |i| {
      // SAFETY: i ranges from 0..len==src.len()
      *unsafe { values.get_unchecked(i) }
    })
  }
  
}

impl Src<str> {
  
  #[inline]
  pub fn new(s: impl AsRef<str>) -> Src<str> {
    let s = s.as_ref();
    let Src { header, start, len, _phantom } = Src::copy_from_slice(s.as_bytes());
    Src { header, start, len, _phantom: PhantomData }
  }
  
  #[inline]
  pub fn from_utf8(v: Src<[u8]>) -> Result<Src<str>, Utf8Error> {
    let _: &str = <str>::from_utf8(&*v)?;
    // SAFETY: <str>::from_utf8() guarantees that the contents are UTF-8
    Ok(unsafe { Src::from_utf8_unchecked(v) })
  }
  
  // SAFETY:
  // The bytes passed in must be valid UTF-8
  #[inline]
  pub unsafe fn from_utf8_unchecked(v: Src<[u8]>) -> Src<str> {
    let Src { header, start, len, _phantom } = v;
    Src { header, start, len, _phantom: PhantomData }
  }
  
  #[inline]
  pub fn as_bytes(self: Src<str>) -> Src<[u8]> {
    let Src { header, start, len, _phantom } = self;
    Src { header, start, len, _phantom: PhantomData }
  }
  
}

impl<T: SrcTarget + ?Sized> Clone for Src<T> {
  
  #[inline]
  fn clone(&self) -> Self {
    self.header().inc_strong_count();
    Self {
      header: self.header,
      start: self.start,
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
    // * this is the only callsite for InnerHeader::drop_strong::<T::Item>; therefore, this will be the last strong reference iff this is the last Src with access to this allocation's body
    unsafe { InnerHeader::drop_strong::<T::Item>(self.header); }
  }
  
}

const fn non_null_max<T>() -> NonNull<T> {
  let max_ptr = without_provenance_mut(usize::MAX);
  // SAFETY: usize::MAX != 0usize
  unsafe { NonNull::new_unchecked(max_ptr) }
}

pub struct WeakSrc<T: SrcTarget + ?Sized> {
  
  header: NonNull<InnerHeader>,
  start: NonNull<T::Item>,
  len: T::Len,
  _phantom: PhantomData<*const T>,
  
}

impl<T: SrcTarget + ?Sized> WeakSrc<T> {
  
  fn header(&self) -> &InnerHeader {
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
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
    let header = self.header();
    if header.strong_count() == 0 {
      return None
    }
    header.inc_strong_count();
    Some(Src {
      header: self.header,
      start: self.start,
      len: self.len,
      _phantom: PhantomData,
    })
  }
  
  #[inline]
  pub fn ptr_eq(&self, other: &Src<T>) -> bool {
    self.start == other.start
  }
  
  #[inline]
  pub fn root_ptr_eq(&self, other: &Src<T>) -> bool {
    self.header == other.header
  }
  
  #[inline]
  pub fn is_root(&self) -> bool {
    // SAFETY:
    // * all constructor fns for Src initialize header from InnerHeader::new_inner::<T::Item>
    // * the header is only accessed from InnerHeader::get_header
    let root_start = unsafe { InnerHeader::get_body_ptr(self.header) };
    self.start == root_start
  }
  
  pub fn strong_count(&self) -> usize {
    self.header().strong_count()
  }
  
  pub fn weak_count(&self) -> usize {
    self.header().weak_count()
  }
  
  // NOTE: WeakSrc could technically support len(), is_empty(), clone_slice(), and clone_root() but I'm not sure it makes sense to; for now, I'm skipping it, but if it becomes important later I may recant
  
}

impl<T> WeakSrc<T> {
  
  #[inline]
  pub fn clone_as_slice(&self) -> WeakSrc<[T]> {
    self.header().inc_weak_count();
    WeakSrc {
      header: self.header,
      start: self.start,
      len: 1,
      _phantom: PhantomData,
    }
  }
  
}

impl<T: SrcTarget + ?Sized> Clone for WeakSrc<T> {
  
  fn clone(&self) -> Self {
    if !self.is_dangling() {
      self.header().inc_weak_count();
    }
    Self {
      header: self.header,
      start: self.start,
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
  
  header: NonNull<InnerHeader>,
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
  
  pub fn weak(&self) -> WeakSrc<T> {
    // safety note: the strong count is 0 until this UninitSrc is initialized into a Src, so the WeakSrc will never read or write from the body during the lifetime of the UninitSrc
    self.header().inc_weak_count();
    // SAFETY:
    // * all constructor fns for UninitSrc<T> initialize self.header from InnerHeader::new_inner::<T>
    // * the header is only accessed from InnerHeader::get_header
    let start = unsafe { InnerHeader::get_body_ptr::<T::Item>(self.header) };
    WeakSrc {
      header: self.header,
      start,
      len: self.len,
      _phantom: PhantomData,
    }
  }
  
  #[inline]
  pub fn weak_count(&self) -> usize {
    self.header().weak_count()
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
  
}

impl<T> UninitSrc<T> {
  
  #[inline]
  pub fn single() -> UninitSrc<T> {
    let UninitSrc { header, len, _phantom } = UninitSrc::<[T]>::new(1);
    debug_assert_eq!(len, 1);
    UninitSrc {
      header,
      len: (),
      _phantom: PhantomData,
    }
  }
  
  pub fn init(self, value: T) -> Src<T> {
    // SAFETY:
    // * all constructor fns for UninitSrc<T> initialize self.header from InnerHeader::new_inner::<T>
    // * the header is only accessed from InnerHeader::get_header
    let start = unsafe { InnerHeader::get_body_ptr::<T>(self.header) };
    // SAFETY: no one else has seen the body of the allocation (because the weaks only look at the header after the strong count has been initialized), so this write is okay
    unsafe { start.write(value); }
    self.header().inc_strong_count();
    let this = Src {
      header: self.header,
      start,
      len: self.len,
      _phantom: PhantomData,
    };
    forget(self); // don't drop the weak held by the UninitSrc; it logically transfers to the Src
    this
  }
  
}

impl<T> UninitSrc<[T]> {
  
  // NOTE: this could be generalized to UninitSrc<T> for T: SrcSlice, but given
  //   a) that there's no way to initialize any T: SrcSlice other than [T], and
  //   b) that UninitSrc is really only useful for self-reference, which is not relevant for str,
  // this is placed here for simplicity
  #[inline]
  pub fn new(len: usize) -> UninitSrc<[T]> {
    let header = InnerHeader::new_inner::<T>(len, 0);
    Self {
      header,
      len,
      _phantom: PhantomData,
    }
  }
  
  pub fn init_from_fn<F: FnMut(usize) -> T>(self, mut f: F) -> Src<[T]> {
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
    forget(guard);
    header.inc_strong_count();
    let this = Src {
      header: self.header,
      start,
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
  pub fn init_filled(self, value: &T) -> Src<[T]> where T: Clone {
    self.init_from_fn(|_| value.clone())
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

pub trait CloneSliceIndex<T: SrcSlice + ?Sized> {
  
  type Output: SrcTarget + ?Sized;
  
  fn clone_get(self, slice: &Src<T>) -> Src<Self::Output>;
  
}

impl<T> CloneSliceIndex<[T]> for usize {
  
  type Output = T;
  
  #[inline]
  fn clone_get(self, slice: &Src<[T]>) -> Src<Self::Output> {
    Src::clone_item(slice, self)
  }
  
}

impl<T> CloneSliceIndex<[T]> for (Bound<usize>, Bound<usize>) {
  
  type Output = [T];
  
  #[inline]
  fn clone_get(self, slice: &Src<[T]>) -> Src<Self::Output> {
    let (start, end) = self;
    Src::clone_from_bounds(slice, start, end)
  }
  
}

impl<T> CloneSliceIndex<[T]> for Range<usize> {
  
  type Output = [T];
  
  #[inline]
  fn clone_get(self, slice: &Src<[T]>) -> Src<Self::Output> {
    let Range { start, end } = self;
    Src::clone_from_bounds(slice, Bound::Included(start), Bound::Excluded(end))
  }
  
}

impl<T> CloneSliceIndex<[T]> for RangeFrom<usize> {
  
  type Output = [T];
  
  #[inline]
  fn clone_get(self, slice: &Src<[T]>) -> Src<Self::Output> {
    let RangeFrom { start } = self;
    Src::clone_from_bounds(slice, Bound::Included(start), Bound::Unbounded)
  }
  
}

impl<T> CloneSliceIndex<[T]> for RangeFull {
  
  type Output = [T];
  
  #[inline]
  fn clone_get(self, slice: &Src<[T]>) -> Src<Self::Output> {
    let RangeFull = self;
    Src::clone_from_bounds(slice, Bound::Unbounded, Bound::Unbounded)
  }
  
}

impl<T> CloneSliceIndex<[T]> for RangeInclusive<usize> {
  
  type Output = [T];
  
  #[inline]
  fn clone_get(self, slice: &Src<[T]>) -> Src<Self::Output> {
    let (start, end) = self.into_inner();
    Src::clone_from_bounds(slice, Bound::Included(start), Bound::Included(end))
  }
  
}

impl<T> CloneSliceIndex<[T]> for RangeTo<usize> {
  
  type Output = [T];
  
  #[inline]
  fn clone_get(self, slice: &Src<[T]>) -> Src<Self::Output> {
    let RangeTo { end } = self;
    Src::clone_from_bounds(slice, Bound::Unbounded, Bound::Excluded(end))
  }
  
}

impl<T> CloneSliceIndex<[T]> for RangeToInclusive<usize> {
  
  type Output = [T];
  
  #[inline]
  fn clone_get(self, slice: &Src<[T]>) -> Src<Self::Output> {
    let RangeToInclusive { end } = self;
    Src::clone_from_bounds(slice, Bound::Unbounded, Bound::Included(end))
  }
  
}

impl CloneSliceIndex<str> for (Bound<usize>, Bound<usize>) {
  
  type Output = str;
  
  #[inline]
  fn clone_get(self, slice: &Src<str>) -> Src<Self::Output> {
    let (start, end) = self;
    Src::clone_from_bounds(slice, start, end)
  }
  
}

impl CloneSliceIndex<str> for Range<usize> {
  
  type Output = str;
  
  #[inline]
  fn clone_get(self, slice: &Src<str>) -> Src<Self::Output> {
    let Range { start, end } = self;
    Src::clone_from_bounds(slice, Bound::Included(start), Bound::Excluded(end))
  }
  
}

impl CloneSliceIndex<str> for RangeFrom<usize> {
  
  type Output = str;
  
  #[inline]
  fn clone_get(self, slice: &Src<str>) -> Src<Self::Output> {
    let RangeFrom { start } = self;
    Src::clone_from_bounds(slice, Bound::Included(start), Bound::Unbounded)
  }
  
}

impl CloneSliceIndex<str> for RangeFull {
  
  type Output = str;
  
  #[inline]
  fn clone_get(self, slice: &Src<str>) -> Src<Self::Output> {
    let RangeFull = self;
    Src::clone_from_bounds(slice, Bound::Unbounded, Bound::Unbounded)
  }
  
}

impl CloneSliceIndex<str> for RangeInclusive<usize> {
  
  type Output = str;
  
  #[inline]
  fn clone_get(self, slice: &Src<str>) -> Src<Self::Output> {
    let (start, end) = self.into_inner();
    Src::clone_from_bounds(slice, Bound::Included(start), Bound::Included(end))
  }
  
}

impl CloneSliceIndex<str> for RangeTo<usize> {
  
  type Output = str;
  
  #[inline]
  fn clone_get(self, slice: &Src<str>) -> Src<Self::Output> {
    let RangeTo { end } = self;
    Src::clone_from_bounds(slice, Bound::Unbounded, Bound::Excluded(end))
  }
  
}

impl CloneSliceIndex<str> for RangeToInclusive<usize> {
  
  type Output = str;
  
  #[inline]
  fn clone_get(self, slice: &Src<str>) -> Src<Self::Output> {
    let RangeToInclusive { end } = self;
    Src::clone_from_bounds(slice, Bound::Unbounded, Bound::Included(end))
  }
  
}

pub trait SrcTarget: sealed::SrcTarget {}

#[diagnostic::do_not_recommend]
impl<T> SrcTarget for T {}

#[diagnostic::do_not_recommend]
impl<T> sealed::SrcTarget for T {
  
  type Item = T;
  
  type Len = ();
  
  fn get(rc: &Src<Self>) -> &Self {
    // SAFETY:
    // all constructor fns of Src guarantee initialization of all elements
    unsafe { rc.start.as_ref() }
  }
  
}

impl<T> SrcTarget for [T] {}

impl<T> sealed::SrcTarget for [T] {
  
  type Item = T;
  
  type Len = usize;
  
  fn get(rc: &Src<Self>) -> &Self {
    let start = rc.start.as_ptr().cast_const();
    let len = rc.len;
    // SAFETY:
    // * all constructor fns of Src guarantee initialization of all elements; if this is a sliced clone, Src::clone_from_bounds guarantees that start and len will still be valid
    unsafe { slice::from_raw_parts(start, len) }
  }
  
}

impl SrcTarget for str {}

impl sealed::SrcTarget for str {
  
  type Item = u8;
  
  type Len = usize;
  
  fn get(rc: &Src<Self>) -> &Self {
    let start = rc.start.as_ptr().cast_const();
    let len = rc.len;
    // SAFETY: all constructor fns of Src guarantee initialization of all elements (well, one of them unsafely passes that requirement on to the caller); if this is a sliced clone, Src::clone_from_bounds guarantees that start and len will still be valid
    let slice: &[u8] = unsafe { slice::from_raw_parts(start, len) };
    // SAFETY: all constructor fns of Src<str> guarantee the contents are UTF8
    unsafe { str::from_utf8_unchecked(slice) }
  }
  
}

pub trait SrcSlice: SrcTarget + sealed::SrcSlice {}

impl<T> SrcSlice for [T] {}

impl<T> sealed::SrcSlice for [T] {
  
  #[inline]
  fn validate_indices(_this: &Src<Self>, _start_inc: usize, _end_exc: usize) {}
  
}

impl SrcSlice for str {}

impl sealed::SrcSlice for str {
  
  fn validate_indices(this: &Src<Self>, start_inc: usize, end_exc: usize) {
    let s: &str = &**this;
    let _ = s[start_inc..end_exc]; // construct the slice just to trigger the appropriate errors if these indices are not at char boundaries
  }
  
}

mod sealed {
  
  pub trait SrcTarget {
    
    type Item;
    
    type Len: Copy + Default;
    
    fn get(rc: &super::Src<Self>) -> &Self where Self: super::SrcTarget;
    
  }
  
  pub trait SrcSlice: SrcTarget<Len = usize> {
    
    fn validate_indices(this: &super::Src<Self>, start_inc: usize, end_exc: usize) where Self: super::SrcSlice;
    
  }
  
}
