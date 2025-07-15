use std::{alloc::{alloc, dealloc, handle_alloc_error, Layout, LayoutError}, cell::Cell, ptr::NonNull};

// NOTE: this should not need to be dropped; `Layout` and `usize` are `Copy`, so drop doesn't matter; `Cell<T>` should only need to be dropped if `T` does
pub struct InnerHeader {
  
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
  pub fn new_inner<T>(len: usize, init_strong_count: usize) -> NonNull<InnerHeader> {
    let Ok((layout, body_offset)) = Self::inner_layout::<T>(len) else {
      panic!("length overflow")
    };
    // SAFETY: layout is guaranteed to be non-zero because it contains an `InnerHeader`
    let ptr = unsafe { alloc(layout) }.cast();
    let Some(ptr) = NonNull::new(ptr) else {
      handle_alloc_error(layout)
    };
    let strong_count = Cell::new(init_strong_count);
    // all strong references logically hold one collective weak reference
    let weak_count = Cell::new(1);
    let header = Self { layout, body_offset, len, strong_count, weak_count };
    // SAFETY: this ptr just came from std::alloc::alloc; therefore, it is both aligned and valid for reads and writes
    unsafe { ptr.write(header); }
    ptr
  }
  
  // SAFETY:
  // requires:
  // * ptr must be from InnerHeader::new_inner::<T>(_)
  // * no one else may have mutable access to the header; this is true if all accesses (after construction) are through this method
  pub unsafe fn get_header<'a>(ptr: NonNull<InnerHeader>) -> &'a InnerHeader {
    // SAFETY: InnerHeader::new_inner initializes a header at this address
    unsafe { ptr.as_ref() }
  }
  
  // SAFETY:
  // requires:
  // * ptr must be from InnerHeader::new_inner::<T>(_)
  // * no one else may have mutable access to the header; this is true if all accesses (after construction) are through InnerHeader::get_header
  // guarantees:
  // * get_body_ptr(_).add(i) points to a valid (aligned, etc.) element in the allocated object iff i < header.len; usage of each element must guarantee the initialization and read/write requirement of NonNull
  pub unsafe fn get_body_ptr<T>(ptr: NonNull<InnerHeader>) -> NonNull<T> {
    // SAFETY: safety requirements are passed on to the caller
    let header = unsafe { InnerHeader::get_header(ptr) };
    let body_offset = header.body_offset;
    // SAFETY: safety requirements are passed on to the caller
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
  pub unsafe fn drop_body<T>(ptr: NonNull<InnerHeader>) {
    // SAFETY: safety requirements are passed on to the caller
    let header = unsafe { InnerHeader::get_header(ptr) };
    // SAFETY: safety requirements are passed on to the caller
    unsafe { InnerHeader::drop_body_up_to::<T>(ptr, header.len); }
  }
  
  // SAFETY:
  // requires:
  // * ptr must be from InnerHeader::new_inner::<T>(_)
  // * the first len elements must be initialized
  // * no one else may have mutable access to the header; this is true if all accesses (after construction) are through InnerHeader::get_header
  // * no one else may have any access to any of the first len elements of the body
  // guarantees
  // * first len elements are deinitialized after this call; those elements are not valid and should not be read
  pub unsafe fn drop_body_up_to<T>(ptr: NonNull<InnerHeader>, len: usize) {
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
  pub unsafe fn dealloc<T>(ptr: NonNull<InnerHeader>) {
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
  pub unsafe fn drop_strong<T>(ptr: NonNull<InnerHeader>) {
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
  pub unsafe fn drop_weak<T>(ptr: NonNull<InnerHeader>) {
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
  pub unsafe fn get_elem_ptr<T>(ptr: NonNull<InnerHeader>, i: usize) -> NonNull<T> {
    // SAFETY: safety requirements are passed on to the caller
    unsafe { InnerHeader::get_body_ptr(ptr).add(i) }
  }
  
  pub fn len(&self) -> usize {
    self.len
  }
  
  pub fn strong_count(&self) -> usize {
    let strong_count = &self.strong_count;
    debug_assert!(strong_count.get() < usize::MAX, "tried to make too many (2^{}) strong references", usize::BITS);
    strong_count.get()
  }
  
  pub fn weak_count(&self) -> usize {
    let weak_count = &self.weak_count;
    debug_assert!(weak_count.get() < usize::MAX, "tried to make too many (2^{}) weak references", usize::BITS);
    weak_count.get()
  }
  
  pub fn inc_strong_count(&self) {
    let strong_count = &self.strong_count;
    debug_assert!(strong_count.get() < usize::MAX, "tried to make too many (2^{}) strong references", usize::BITS);
    strong_count.set(strong_count.get().wrapping_add(1));
  }
  
  pub fn inc_weak_count(&self) {
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
