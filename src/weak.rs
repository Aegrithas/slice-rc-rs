use std::{fmt::{self, Debug, Formatter, Pointer}, marker::PhantomData, mem::forget, ops::Bound, ptr::{without_provenance_mut, NonNull}};

use crate::{inner::InnerHeader, Src, SrcIndex, SrcSlice, SrcTarget};

const fn non_null_max<T>() -> NonNull<T> {
  let max_ptr = without_provenance_mut(usize::MAX);
  // SAFETY: usize::MAX != 0usize
  unsafe { NonNull::new_unchecked(max_ptr) }
}

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
  pub fn ptr_eq(&self, other: &WeakSrc<T>) -> bool {
    self.start == other.start
  }
  
  #[inline]
  pub fn same_root(&self, other: &WeakSrc<T>) -> bool {
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
  
  pub(crate) fn into_item(self, index: usize) -> WeakSrc<T::Item> {
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
  pub(crate) unsafe fn get_slice(&self) -> &[T::Item] {
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
