mod inner;

use std::{error::Error, fmt::{self, Debug, Display, Formatter}, marker::PhantomData, ops::{Bound, Deref, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive}, ptr::{without_provenance_mut, NonNull}, slice, usize};

use inner::*;

pub struct SliceRc<T> {
  
  header: NonNull<InnerHeader>,
  start: NonNull<T>,
  len: usize,
  _phantom: PhantomData<*const [T]>,
  
}

impl<T> SliceRc<T> {
  
  #[inline]
  pub fn from_fn<F: FnMut(usize) -> T>(len: usize, f: F) -> SliceRc<T> {
    Self::try_from_fn(len, f).unwrap()
  }
  
  pub fn try_from_fn<F: FnMut(usize) -> T>(len: usize, mut f: F) -> Result<SliceRc<T>, AllocError> {
    let header = InnerHeader::new_inner::<T>(len)?;
    // SAFETY: we just got this from InnerHeader::new_inner::<T>; no one else has seen the ptr yet, so the read/write requirements are fine
    let start = unsafe { InnerHeader::get_body_ptr::<T>(header) };
    for i in 0..len {
      // SAFETY: we just got this from InnerHeader::new_inner::<T>; no one else has seen the ptr yet except start, which is not being read or written, so the read/write requirements are fine
      let ptr = unsafe { InnerHeader::get_elem_ptr::<T>(header, i) };
      let val = f(i);
      // SAFETY: no one else has seen this element, so write is fine
      unsafe { ptr.write(val) };
    }
    Ok(Self {
      header,
      start,
      len,
      _phantom: PhantomData,
    })
  }
  
  #[inline]
  pub fn ptr_eq(this: &SliceRc<T>, other: &SliceRc<T>) -> bool {
    this.start == other.start
  }
  
  #[inline]
  pub fn root_ptr_eq(this: &SliceRc<T>, other: &SliceRc<T>) -> bool {
    this.header == other.header
  }
  
  // technically unnecessary (because a self.deref().len() will get the same number), but potentially more efficient because there is no need to construct the whole slice
  #[inline]
  pub fn len(&self) -> usize {
    self.len
  }
  
  #[inline]
  pub fn is_root(&self) -> bool {
    // SAFETY:
    // * all constructor fns for SliceRc initialize header from InnerHeader::new_inner::<T>
    // * the header is only accessed from InnerHeader::get_header
    let root_start = unsafe { InnerHeader::get_body_ptr(self.header) };
    self.start == root_start
  }
  
  pub fn clone_root(&self) -> SliceRc<T> {
    // SAFETY:
    // * all constructor fns for SliceRc initialize header from InnerHeader::new_inner::<T>
    // * the header is only accessed from InnerHeader::get_header
    let start = unsafe { InnerHeader::get_body_ptr(self.header) };
    // SAFETY:
    // * all constructor fns for SliceRc initialize header from InnerHeader::new_inner::<T>
    // * the header is only accessed from InnerHeader::get_header
    let header = unsafe { InnerHeader::get_header(self.header) };
    header.inc_strong_count();
    Self {
      header: self.header,
      start,
      len: header.len(), // header.len not self.len, because we're reconstructing the whole slice
      _phantom: PhantomData,
    }
  }
  
  #[inline]
  pub fn clone_slice<I: CloneSliceIndex<SliceRc<T>>>(&self, index: I) -> SliceRc<T> {
    index.get(self)
  }
  
  fn clone_from_bounds(this: &SliceRc<T>, bounds: (Bound<usize>, Bound<usize>)) -> SliceRc<T> {
    let (start, end) = bounds;
    // SAFETY:
    // * all constructor fns for SliceRc initialize header from InnerHeader::new_inner::<T>
    // * the header is only accessed from InnerHeader::get_header
    let header = unsafe { InnerHeader::get_header(this.header) };
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
    let len = end_exc - start_inc;
    // SAFETY:
    // * all constructor fns for SliceRc initialize header from InnerHeader::new_inner::<T>
    // * the header is only accessed from InnerHeader::get_header
    // * the assertion verifies that start_exc <= end_exc <= header.len
    let start_ptr = unsafe { InnerHeader::get_elem_ptr::<T>(this.header, start_inc) };
    header.inc_strong_count();
    Self {
      header: this.header,
      start: start_ptr,
      len,
      _phantom: PhantomData,
    }
  }
  
  pub fn downgrade(this: &SliceRc<T>) -> WeakSliceRc<T> {
    // SAFETY:
    // * all constructor fns for SliceRc initialize header from InnerHeader::new_inner::<T>
    // * the header is only accessed from InnerHeader::get_header
    let header = unsafe { InnerHeader::get_header(this.header) };
    header.inc_weak_count();
    WeakSliceRc {
      header: this.header,
      start: this.start,
      len: this.len,
      _phantom: PhantomData,
    }
  }
  
}

impl<T: Default> SliceRc<T> {
  
  #[inline]
  pub fn from_default(len: usize) -> SliceRc<T> {
    Self::from_fn(len, |_| Default::default())
  }
  
  #[inline]
  pub fn try_from_default(len: usize) -> Result<SliceRc<T>, AllocError> {
    Self::try_from_fn(len, |_| Default::default())
  }
  
}

impl<T: Clone> SliceRc<T> {
  
  #[inline]
  pub fn clone_from(src: &[T]) -> SliceRc<T> {
    Self::from_fn(src.len(), |i| {
      // SAFETY: i ranges from 0..len==src.len()
      unsafe { src.get_unchecked(i) }.clone()
    })
  }
  
  #[inline]
  pub fn try_clone_from(src: &[T]) -> Result<SliceRc<T>, AllocError> {
    Self::try_from_fn(src.len(), |i| {
      // SAFETY: i ranges from 0..len==src.len()
      unsafe { src.get_unchecked(i) }.clone()
    })
  }
  
}

impl<T: Copy> SliceRc<T> {
  
  #[inline]
  pub fn copy_from(src: &[T]) -> SliceRc<T> {
    Self::from_fn(src.len(), |i| {
      // SAFETY: i ranges from 0..len==src.len()
      *unsafe { src.get_unchecked(i) }
    })
  }
  
  #[inline]
  pub fn try_copy_from(src: &[T]) -> Result<SliceRc<T>, AllocError> {
    Self::try_from_fn(src.len(), |i| {
      // SAFETY: i ranges from 0..len==src.len()
      *unsafe { src.get_unchecked(i) }
    })
  }
  
}

impl<T> Clone for SliceRc<T> {
  
  #[inline]
  fn clone(&self) -> Self {
    self.clone_slice(..)
  }
  
}

impl<T> Deref for SliceRc<T> {
  
  type Target = [T];
  
  fn deref(&self) -> &Self::Target {
    let start = self.start.as_ptr().cast_const();
    let len = self.len;
    // SAFETY:
    // * all constructor fns of SliceRc guarantee initialization of all elements; if this is a sliced clone, SliceRc::clone_from_bounds guarantees that start and len will still be valid
    unsafe { slice::from_raw_parts(start, len) }
  }
  
}

impl<T: Debug> Debug for SliceRc<T> {
  
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    let values: &[T] = &**self;
    Debug::fmt(values, f)
  }
  
}

impl<T> Drop for SliceRc<T> {
  
  fn drop(&mut self) {
    // SAFETY:
    // * all constructor fns for SliceRc initialize header from InnerHeader::new_inner::<T>
    // * all constructor fns for SliceRc initialize the elements
    // * the header is only accessed from InnerHeader::get_header
    // * this is the only callsite for InnerHeader::drop_strong; therefore, this will be the last strong reference iff this is the last SliceRc with access to this allocation's body
    unsafe { InnerHeader::drop_strong::<T>(self.header); }
  }
  
}

const fn non_null_max<T>() -> NonNull<T> {
  let max_ptr = without_provenance_mut(usize::MAX);
  // SAFETY:
  // usize::MAX != 0usize
  unsafe { NonNull::new_unchecked(max_ptr) }
}

pub struct WeakSliceRc<T> {
  
  header: NonNull<InnerHeader>,
  start: NonNull<T>,
  len: usize,
  _phantom: PhantomData<*const [T]>,
  
}

impl<T> WeakSliceRc<T> {
  
  #[inline]
  pub fn dangling() -> WeakSliceRc<T> {
    WeakSliceRc {
      header: non_null_max(),
      start: non_null_max(),
      len: 0,
      _phantom: PhantomData,
    }
  }
  
  #[inline]
  pub fn is_dangling(&self) -> bool {
    self.header == non_null_max()
  }
  
  pub fn upgrade(&self) -> Option<SliceRc<T>> {
    if self.is_dangling() {
      return None
    }
    // SAFETY:
    // * all constructor fns for SliceRc initialize header from InnerHeader::new_inner::<T>; WeakSliceRcs are either constructed from WeakSliceRc::dangling (which is covered by self.is_dangling()), or from a SliceRc
    // * the header is only accessed from InnerHeader::get_header
    let header = unsafe { InnerHeader::get_header(self.header) };
    if header.strong_count() == 0 {
      return None
    }
    header.inc_strong_count();
    Some(SliceRc {
      header: self.header,
      start: self.start,
      len: self.len,
      _phantom: PhantomData,
    })
  }
  
  // NOTE: WeakSliceRc could technically support len() and clone_slice(), but I'm not sure it makes sense to; for now, I'm skipping it, but if it becomes important later I may recant
  
}

impl<T> Clone for WeakSliceRc<T> {
  
  fn clone(&self) -> Self {
    if !self.is_dangling() {
      // SAFETY:
      // * all constructor fns for SliceRc initialize header from InnerHeader::new_inner::<T>; WeakSliceRcs are either constructed from WeakSliceRc::dangling (which is covered by self.is_dangling()), or from a SliceRc
      // * the header is only accessed from InnerHeader::get_header
      let header = unsafe { InnerHeader::get_header(self.header) };
      header.inc_weak_count();
    }
    Self {
      header: self.header,
      start: self.start,
      len: self.len,
      _phantom: PhantomData,
    }
  }
  
}

impl<T> Debug for WeakSliceRc<T> {
  
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "(WeakSliceRc)")
  }
  
}

impl<T> Default for WeakSliceRc<T> {
  
  #[inline]
  fn default() -> Self {
    Self::dangling()
  }
  
}

impl<T> Drop for WeakSliceRc<T> {
  
  fn drop(&mut self) {
    if !self.is_dangling() {
      // SAFETY:
      // * all constructor fns for SliceRc initialize header from InnerHeader::new_inner::<T>; WeakSliceRcs are either constructed from WeakSliceRc::dangling (which is covered by self.is_dangling()), or from a SliceRc
      // * the header is only accessed from InnerHeader::get_header
      unsafe { InnerHeader::drop_weak::<T>(self.header); }
    }
  }
  
}

pub trait CloneSliceIndex<Rc> {
  
  fn get(self, slice: &Rc) -> Rc;
  
}

impl<T> CloneSliceIndex<SliceRc<T>> for (Bound<usize>, Bound<usize>) {
  
  #[inline]
  fn get(self, slice: &SliceRc<T>) -> SliceRc<T> {
    SliceRc::clone_from_bounds(slice, self)
  }
  
}

impl<T> CloneSliceIndex<SliceRc<T>> for Range<usize> {
  
  #[inline]
  fn get(self, slice: &SliceRc<T>) -> SliceRc<T> {
    let Range { start, end } = self;
    (Bound::Included(start), Bound::Excluded(end)).get(slice)
  }
  
}

impl<T> CloneSliceIndex<SliceRc<T>> for RangeFrom<usize> {
  
  #[inline]
  fn get(self, slice: &SliceRc<T>) -> SliceRc<T> {
    let RangeFrom { start } = self;
    (Bound::Included(start), Bound::Unbounded).get(slice)
  }
  
}

impl<T> CloneSliceIndex<SliceRc<T>> for RangeFull {
  
  #[inline]
  fn get(self, slice: &SliceRc<T>) -> SliceRc<T> {
    let RangeFull = self;
    (Bound::Unbounded, Bound::Unbounded).get(slice)
  }
  
}

impl<T> CloneSliceIndex<SliceRc<T>> for RangeInclusive<usize> {
  
  #[inline]
  fn get(self, slice: &SliceRc<T>) -> SliceRc<T> {
    let (start, end) = self.into_inner();
    (Bound::Included(start), Bound::Included(end)).get(slice)
  }
  
}

impl<T> CloneSliceIndex<SliceRc<T>> for RangeTo<usize> {
  
  #[inline]
  fn get(self, slice: &SliceRc<T>) -> SliceRc<T> {
    let RangeTo { end } = self;
    (Bound::Unbounded, Bound::Excluded(end)).get(slice)
  }
  
}

impl<T> CloneSliceIndex<SliceRc<T>> for RangeToInclusive<usize> {
  
  #[inline]
  fn get(self, slice: &SliceRc<T>) -> SliceRc<T> {
    let RangeToInclusive { end } = self;
    (Bound::Unbounded, Bound::Included(end)).get(slice)
  }
  
}

#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
pub enum AllocError {
  
  /// Layout overflowed valid allocation size; this will always be the result for this size allocation (for the same size of usize).
  TooLarge,
  /// Allocator failed
  OutOfMemory
  
}

impl Display for AllocError {
  
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      Self::TooLarge => write!(f, "tried to allocate a chunk of memory that is too large"),
      Self::OutOfMemory => write!(f, "ran out of memory trying to allocate"),
    }
  }
  
}

impl Error for AllocError {}
