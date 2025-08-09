use std::{fmt::{self, Debug, Formatter, Pointer}, marker::PhantomData, mem::forget, num::NonZero, ops::Bound, ptr::NonNull};

use crate::{inner::InnerHeader, Src, SrcIndex, SrcSlice, SrcTarget};

const fn non_null_max<T>() -> NonNull<T> {
  NonNull::without_provenance(NonZero::<usize>::MAX)
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
  pub fn ptr_eq<U: SrcTarget<Item = T::Item> + ?Sized>(&self, other: &WeakSrc<U>) -> bool {
    self.start == other.start
  }
  
  #[inline]
  pub fn same_root<U: SrcTarget<Item = T::Item> + ?Sized>(&self, other: &WeakSrc<U>) -> bool {
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
  
  pub fn into_root(self) -> WeakSrc<[T::Item]> {
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
  pub fn clone_root(&self) -> WeakSrc<[T::Item]> {
    self.clone().into_root()
  }
  
  #[inline]
  pub fn upgrade_root(&self) -> Option<Src<[T::Item]>> {
    self.upgrade().map(Src::into_root)
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
      let w4: WeakSrc<[u8]> = s.downgrade_slice(1..);
      let w5: WeakSrc<[u8]> = s.downgrade_slice(1..);
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
      let w4: WeakSrc<[u8]> = s.downgrade_slice(1..);
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
      let w2: WeakSrc<[u8]> = s.downgrade_slice(1..);
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
      let w: WeakSrc<[u8]> = w.into_slice(3..14);
      assert_eq!(w.len(), 11);
      let w: WeakSrc<[u8]> = w.into_slice(3..3);
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
      let w: WeakSrc<[u8]> = w.into_slice(3..14);
      assert!(!w.is_empty());
      let w: WeakSrc<[u8]> = w.into_slice(3..3);
      assert!(w.is_empty());
    }
  }
  
  #[test]
  fn into_root() {
    { // dangling
      let w1: WeakSrc<[u8]> = WeakSrc::dangling();
      let w2: WeakSrc<[u8]> = w1.clone().into_root();
      assert!(w2.is_root());
      assert!(w1.ptr_eq(&w2));
    }
    { // not dangling
      let s: Src<[u8]> = Src::from_default(1);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert!(w.is_root());
      let w: WeakSrc<[u8]> = w.into_slice(1..);
      assert!(!w.is_root());
      let w: WeakSrc<[u8]> = w.into_root();
      assert!(w.is_root());
    }
  }
  
  #[test]
  fn clone_root() {
    { // dangling
      let w1: WeakSrc<[u8]> = WeakSrc::dangling();
      let w2: WeakSrc<[u8]> = w1.clone_root();
      assert!(w2.is_root());
      assert!(w1.ptr_eq(&w2));
    }
    { // not dangling
      let s: Src<[u8]> = Src::from_default(1);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert!(w.is_root());
      let w: WeakSrc<[u8]> = w.into_slice(1..);
      assert!(!w.is_root());
      let w: WeakSrc<[u8]> = w.clone_root();
      assert!(w.is_root());
    }
  }
  
  #[test]
  fn upgrade_root() {
    { // dangling
      let w1: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(w1.clone().upgrade_root().is_none());
    }
    { // not dangling
      let s: Src<[u8]> = Src::from_default(1);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert!(w.is_root());
      let w: WeakSrc<[u8]> = w.into_slice(1..);
      assert!(!w.is_root());
      let s: Src<[u8]> = w.upgrade_root().unwrap();
      assert!(Src::is_root(&s));
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      assert!(w.is_root());
    }
  }
  
  #[test]
  #[should_panic]
  fn into_slice_dangling() {
    let w: WeakSrc<[u8]> = WeakSrc::dangling();
    let _: WeakSrc<[u8]> = w.into_slice(..);
  }
  
  #[test]
  fn into_slice() {
    { // slice
      let s: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      let s: Src<[u8]> = w.upgrade().unwrap();
      assert_eq!(&*s, &[1, 2, 3]);
      let w: WeakSrc<[u8]> = w.into_slice(1..);
      let s: Src<[u8]> = w.upgrade().unwrap();
      assert_eq!(&*s, &[2, 3]);
      let w: WeakSrc<[u8]> = w.into_slice(..1);
      let s: Src<[u8]> = w.upgrade().unwrap();
      assert_eq!(&*s, &[2]);
    }
    { // item 1
      let s: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      let s: Src<[u8]> = w.upgrade().unwrap();
      assert_eq!(&*s, &[1, 2, 3]);
      let w: WeakSrc<u8> = w.into_slice(2);
      let s: Src<u8> = w.upgrade().unwrap();
      assert_eq!(&*s, &3);
    }
    { // item 2
      let s: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w: WeakSrc<[u8]> = Src::downgrade(&s);
      let s: Src<[u8]> = w.upgrade().unwrap();
      assert_eq!(&*s, &[1, 2, 3]);
      let w: WeakSrc<[u8]> = w.into_slice(1..);
      let s: Src<[u8]> = w.upgrade().unwrap();
      assert_eq!(&*s, &[2, 3]);
      let w: WeakSrc<u8> = w.into_slice(0);
      let s: Src<u8> = w.upgrade().unwrap();
      assert_eq!(&*s, &2);
    }
  }
  
  #[test]
  #[should_panic]
  fn clone_slice_dangling() {
    let w: WeakSrc<[u8]> = WeakSrc::dangling();
    let _: WeakSrc<[u8]> = w.clone_slice(..);
  }
  
  #[test]
  fn clone_slice() {
    { // slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[1, 2, 3]);
      let w1: WeakSrc<[u8]> = w1.into_slice(1..);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[2, 3]);
      let w2: WeakSrc<[u8]> = w1.clone_slice(..1);
      let s2: Src<[u8]> = w2.upgrade().unwrap();
      assert_eq!(&*s2, &[2]);
      assert!(w1.same_root(&w2));
    }
    { // item 1
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[1, 2, 3]);
      let w2: WeakSrc<u8> = w1.clone_slice(2);
      let s2: Src<u8> = w2.upgrade().unwrap();
      assert_eq!(&*s2, &3);
      let w2: WeakSrc<[u8]> = WeakSrc::as_slice(w2);
      let s2: Src<[u8]> = w2.upgrade().unwrap();
      assert_eq!(&*s2, &[3]);
      assert!(w1.same_root(&w2));
    }
    { // item 2
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[1, 2, 3]);
      let w1: WeakSrc<[u8]> = w1.into_slice(1..);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[2, 3]);
      let w2: WeakSrc<u8> = w1.clone_slice(0);
      let s2: Src<u8> = w2.upgrade().unwrap();
      assert_eq!(&*s2, &2);
      let w2: WeakSrc<[u8]> = WeakSrc::as_slice(w2);
      let s2: Src<[u8]> = w2.upgrade().unwrap();
      assert_eq!(&*s2, &[2]);
      assert!(w1.same_root(&w2));
    }
  }
  
  #[test]
  fn upgrade_slice() {
    { // dangling
      let w: WeakSrc<[u8]> = WeakSrc::dangling();
      assert!(w.upgrade_slice(..).is_none());
    }
    { // slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[1, 2, 3]);
      let w1: WeakSrc<[u8]> = w1.into_slice(1..);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[2, 3]);
      let s2: Src<[u8]> = w1.upgrade_slice(..1).unwrap();
      let w2: WeakSrc<[u8]> = Src::downgrade(&s2);
      assert_eq!(&*s2, &[2]);
      assert!(w1.same_root(&w2));
    }
    { // item 1
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[1, 2, 3]);
      let s2: Src<u8> = w1.upgrade_slice(2).unwrap();
      let w2: WeakSrc<u8> = Src::downgrade(&s2);
      assert_eq!(&*s2, &3);
      let w2: WeakSrc<[u8]> = WeakSrc::as_slice(w2);
      let s2: Src<[u8]> = w2.upgrade().unwrap();
      assert_eq!(&*s2, &[3]);
      assert!(w1.same_root(&w2));
    }
    { // item 2
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[1, 2, 3]);
      let w1: WeakSrc<[u8]> = w1.into_slice(1..);
      let s1: Src<[u8]> = w1.upgrade().unwrap();
      assert_eq!(&*s1, &[2, 3]);
      let s2: Src<u8> = w1.upgrade_slice(0).unwrap();
      let w2: WeakSrc<u8> = Src::downgrade(&s2);
      assert_eq!(&*s2, &2);
      let w2: WeakSrc<[u8]> = WeakSrc::as_slice(w2);
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
      let w2: WeakSrc<[u8]> = w1.clone().as_slice();
      let s2: Src<[u8]> = w2.upgrade().unwrap();
      assert_eq!([*s1], *s2);
    }
    { // from slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let w2: WeakSrc<u8> = w1.clone_slice(1);
      let s2: Src<u8> = w2.upgrade().unwrap();
      let w3: WeakSrc<[u8]> = w2.clone().as_slice();
      let s3: Src<[u8]> = w3.upgrade().unwrap();
      assert_eq!(s1[1], *s2);
      assert_eq!([*s2], *s3);
    }
  }
  
  #[test]
  fn clone_as_slice() {
    { // dangling
      let w: WeakSrc<u8> = WeakSrc::dangling();
      let w: WeakSrc<[u8]> = w.clone_as_slice();
      assert!(w.is_dangling());
    }
    { // single root
      let s1: Src<u8> = Src::single(42);
      let w1: WeakSrc<u8> = Src::downgrade(&s1);
      let w2: WeakSrc<[u8]> = w1.clone_as_slice();
      let s2: Src<[u8]> = w2.upgrade().unwrap();
      assert_eq!([*s1], *s2);
    }
    { // from slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let w2: WeakSrc<u8> = w1.clone_slice(1);
      let s2: Src<u8> = w2.upgrade().unwrap();
      let w3: WeakSrc<[u8]> = w2.clone_as_slice();
      let s3: Src<[u8]> = w3.upgrade().unwrap();
      assert_eq!(s1[1], *s2);
      assert_eq!([*s2], *s3);
    }
  }
  
  #[test]
  fn upgrade_as_slice() {
    { // dangling
      let w: WeakSrc<u8> = WeakSrc::dangling();
      assert!(w.upgrade_as_slice().is_none());
    }
    { // single root
      let s1: Src<u8> = Src::single(42);
      let w1: WeakSrc<u8> = Src::downgrade(&s1);
      let s2: Src<[u8]> = w1.upgrade_as_slice().unwrap();
      assert_eq!([*s1], *s2);
    }
    { // from slice
      let s1: Src<[u8]> = Src::from_array([1, 2, 3]);
      let w1: WeakSrc<[u8]> = Src::downgrade(&s1);
      let w2: WeakSrc<u8> = w1.clone_slice(1);
      let s2: Src<u8> = w2.upgrade().unwrap();
      let s3: Src<[u8]> = w2.upgrade_as_slice().unwrap();
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
