use std::{alloc::{alloc, dealloc, Layout, LayoutError}, cell::Cell, error::Error, fmt::{self, Debug, Display, Formatter}, marker::PhantomData, ops::{Bound, Deref, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive}, ptr::{without_provenance_mut, NonNull}, slice, usize};

// NOTE: this should not need to be dropped; `Layout` and `usize` are `Copy`, so drop doesn't matter; `Cell<T>` should only need to be dropped if `T` does
struct InnerHeader {
  
  // note: layout and body_offset could potentially be elided because usages could instead read len to reconstruct them
  layout: Layout,
  body_offset: usize,
  len: usize,
  strong_count: Cell<usize>,
  weak_count: Cell<usize>,
  
}

impl InnerHeader {
  
  fn inner_layout<T>(len: usize) -> Result<(Layout, usize), LayoutError> {
    Layout::new::<InnerHeader>().extend(Layout::array::<T>(len)?)
  }
  
  // SAFETY:
  // various static methods on InnerHeader offer access to the contents; nothing else is guaranteed to be sound
  fn new_inner<T>(len: usize) -> Result<NonNull<InnerHeader>, AllocError> {
    let (layout, body_offset) = Self::inner_layout::<T>(len).map_err(|_| AllocError::TooLarge)?;
    // SAFETY: layout is guaranteed to be non-zero because it contains an `InnerHeader`
    let ptr = unsafe { alloc(layout) }.cast();
    let Some(ptr) = NonNull::new(ptr) else {
      return Err(AllocError::OutOfMemory)
    };
    let strong = Cell::new(1);
    // all strong references logically hold one collective weak reference
    let weak = Cell::new(1);
    let header = Self { layout, body_offset, len, strong_count: strong, weak_count: weak };
    // SAFETY: this ptr just came from std::alloc::alloc; therefore, it is both aligned and valid for reads and writes
    unsafe { ptr.write(header); }
    Ok(ptr)
  }
  
  // SAFETY:
  // requires:
  // * ptr must be from InnerHeader::new_inner::<T>(_)
  // * no one else may have mutable access to the header; this is true if all accesses (after construction) are through this method
  unsafe fn get_header<'a>(ptr: NonNull<InnerHeader>) -> &'a InnerHeader {
    // SAFETY: InnerHeader::new_inner initializes a header at this address
    unsafe { ptr.as_ref() }
  }
  
  // SAFETY:
  // requires:
  // * ptr must be from InnerHeader::new_inner::<T>(_)
  // * no one else may have mutable access to the header; this is true if all accesses (after construction) are through InnerHeader::get_header
  // guarantees:
  // * get_body_ptr(_).add(i) points to a valid (aligned, etc.) element in the allocated object iff i < header.len; usage of each element must guarantee the initialization and read/write requirement of NonNull
  unsafe fn get_body_ptr<T>(ptr: NonNull<InnerHeader>) -> NonNull<T> {
    let header = unsafe { InnerHeader::get_header(ptr) };
    let body_offset = header.body_offset;
    unsafe { ptr.byte_add(body_offset).cast::<T>() }
  }
  
  // SAFETY:
  // requires:
  // * ptr must be from InnerHeader::new_inner::<T>(_)
  // * every element of body must be initialized
  // * no one else may have mutable access to the header; this is true if all accesses (after construction) are through InnerHeader::get_header
  // * no one else may have any access to any element of the body
  // guarantees:
  // * body is deinitialized after this call; none of the elements are valid and should not be read
  unsafe fn drop_body<T>(ptr: NonNull<InnerHeader>) {
    // SAFETY: safety requirements are passed on to the caller
    let header = unsafe { InnerHeader::get_header(ptr) };
    let len = header.len;
    // SAFETY: safety requirements are passed on to the caller
    let ptr = unsafe { InnerHeader::get_body_ptr::<T>(ptr) };
    for i in 0..len {
      // SAFETY: InnerHeader::get_body_ptr guarantees that ptr.add(i) is valid
      let ptr = unsafe { ptr.add(i) };
      // SAFETY: safety requirements are passed on to the caller
      unsafe { ptr.drop_in_place(); }
    }
  }
  
  // SAFTEY:
  // requires:
  // * ptr must be from InnerHeader::new_inner::<T>(_)
  // * no one else may have mutable access to the header; this is true if all accesses (after construction) are through InnerHeader::get_header
  // guarantees:
  // * the body of the ptr will not be read, so it may be uninitialized; if it is initialized, it will not be dropped
  // * ptr will no longer point to a valid allocated object
  unsafe fn dealloc<T>(ptr: NonNull<InnerHeader>) {
    // SAFTEY: safety requirements are passed on to the caller
    let header = unsafe { InnerHeader::get_header(ptr) };
    let layout = header.layout;
    // SAFETY: InnerHeader::new_inner generates its pointer from this layout
    unsafe { dealloc(ptr.as_ptr().cast(), layout); }
  }
  
  // SAFETY:
  // requires:
  // * ptr must be from InnerHeader::new_inner::<T>(_)
  // * every element of body must be initialized
  // * no one else may have mutable access to the header; this is true if all accesses (after construction) are through InnerHeader::get_header
  // * if this is the last strong reference, no one else may have any access to any element of the body
  // guarantees:
  // * if this was the last strong reference, the body will be dropped and a weak will be dropped
  unsafe fn drop_strong<T>(ptr: NonNull<InnerHeader>) {
    // SAFETY: safety requirements are passed on to the caller
    let header = unsafe { InnerHeader::get_header(ptr) };
    header.dec_strong_count();
    if header.strong_count() == 0 {
      // SAFETY: safety requirements are passed on to the caller
      unsafe { InnerHeader::drop_body::<T>(ptr); }
      // all strong references logically hold one collective weak reference, so drop a weak when the last strong is dropped
      // SAFETY: safety requirements are passed on to the caller
      // importantly, this happens after InnerHeader::drop_body, so that if the memory gets dealloc'd, it won't try to drop_in_place on the freed memory
      unsafe { InnerHeader::drop_weak::<T>(ptr); }
    }
  }
  
  // SAFETY:
  // requires:
  // * ptr must be from InnerHeader::new_inner::<T>(_)
  // * no one else may have mutable access to the header; this is true if all accesses (after construction) are through InnerHeader::get_header
  // guarantees:
  // * the body of the ptr will not be read, so it may be uninitialized; if it is initialized, it will not be dropped
  // * if this was the last weak reference, ptr will no longer point to a valid allocated object
  unsafe fn drop_weak<T>(ptr: NonNull<InnerHeader>) {
    // SAFETY: safety requirements are passed on to the caller
    let header = unsafe { InnerHeader::get_header(ptr) };
    header.dec_weak_count();
    if header.weak_count() == 0 {
      // all strong references logically hold one collective weak reference, so if weak_count.get() == 0, the strongs must have already released their weak
      debug_assert_eq!(header.strong_count(), 0, "dropped last weak reference, but there are still strong references");
      // SAFETY: safety requirements are passed on to the caller
      unsafe { InnerHeader::dealloc::<T>(ptr); }
      // note that the InnerHeader has effectively been std::mem::forgot()ten, but that's okay because it should have no meaningful destructor
    }
  }
  
  // Shorthand for InnerHeader::get_body_ptr(ptr).add(i)
  //
  // SAFETY:
  // requires:
  // * ptr must be from InnerHeader::new_inner::<T>(len)
  // * no one else may have mutable access to the header; this is true if all accesses (after construction) are through InnerHeader::get_header
  // * i must be less than len (assuming the pointer is before InnerHeader::drop_body)
  // guarantees:
  // * get_elem_ptr(_, i) points to a valid (aligned, etc.) element in the allocated object iff i < header.len; usage of each element must guarantee the initialization and read/write requirement of NonNull
  unsafe fn get_elem_ptr<T>(ptr: NonNull<InnerHeader>, i: usize) -> NonNull<T> {
    // SAFETY: safety requirements are passed on to the caller
    unsafe { InnerHeader::get_body_ptr(ptr).add(i) }
  }
  
  fn strong_count(&self) -> usize {
    let strong_count = &self.strong_count;
    debug_assert!(strong_count.get() < usize::MAX, "tried to make too many (2^{}) strong references", usize::BITS);
    strong_count.get()
  }
  
  fn weak_count(&self) -> usize {
    let weak_count = &self.weak_count;
    debug_assert!(weak_count.get() < usize::MAX, "tried to make too many (2^{}) weak references", usize::BITS);
    weak_count.get()
  }
  
  fn inc_strong_count(&self) {
    let strong_count = &self.strong_count;
    debug_assert!(strong_count.get() < usize::MAX, "tried to make too many (2^{}) strong references", usize::BITS);
    strong_count.set(strong_count.get().wrapping_add(1));
  }
  
  fn inc_weak_count(&self) {
    let weak_count = &self.weak_count;
    debug_assert!(weak_count.get() < usize::MAX, "tried to make too many (2^{}) weak references", usize::BITS);
    weak_count.set(weak_count.get().wrapping_add(1));
  }
  
  fn dec_strong_count(&self) {
    let strong_count = &self.strong_count;
    debug_assert!(strong_count.get() > 0, "tried remove a non-existant strong_count");
    strong_count.set(strong_count.get().wrapping_add(1));
  }
  
  fn dec_weak_count(&self) {
    let weak_count = &self.weak_count;
    debug_assert!(weak_count.get() > 0, "tried remove a non-existant strong_count");
    weak_count.set(weak_count.get().wrapping_add(1));
  }
  
}

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
      len: header.len, // header.len not self.len, because we're reconstructing the whole slice
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
      Bound::Unbounded => header.len,
    };
    assert!(start_inc <= end_exc, "slice index starts at {start_inc} but ends at {end_exc}");
    assert!(end_exc <= header.len, "range end index {end_exc} out of range for slice of length {}", header.len);
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
