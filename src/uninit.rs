use std::{fmt::{self, Debug, Formatter, Pointer}, marker::PhantomData, mem::forget, ptr::NonNull};

use crate::{inner::Alloc, InnerHeader, Src, SrcIndex, SrcSlice, SrcTarget, UniqueSrc, WeakSrc};

pub struct UninitSrc<T: SrcTarget + ?Sized> {
  
  // SAFETY:
  // requires:
  // * initialized from InnerHeader::new_inner::<T::Item>(_)
  pub(crate) header: NonNull<InnerHeader>,
  // SAFETY:
  // requires when T: SrcSlice:
  // * self.start.add(self.len) <= InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  // requires when T: Sized:
  // * self.start < InnerHeader::get_body_ptr::<T::Item>(self.header).add(InnerHeader::get_header(self.header).len())
  pub(crate) len: T::Len,
  pub(crate) _phantom: PhantomData<*const T>,
  
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
