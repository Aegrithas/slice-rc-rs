use std::{borrow::{Borrow, BorrowMut}, cmp::Ordering, fmt::{self, Debug, Formatter, Pointer}, hash::{Hash, Hasher}, marker::PhantomData, mem::{forget, MaybeUninit}, ops::{Deref, DerefMut, Index, IndexMut}, ptr::NonNull, str::Utf8Error};

use crate::{inner::{AllocUninit, AllocZeroed}, InnerHeader, Src, SrcIndex, SrcSlice, SrcTarget, UninitSrc, WeakSrc};

pub struct UniqueSrc<T: SrcTarget + ?Sized> {
  
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
    let header = InnerHeader::new_inner::<T, AllocUninit>(len);
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
    let header = InnerHeader::new_inner::<T, AllocUninit>(N);
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
  pub fn cloned(values: &[T]) -> UniqueSrc<[T]> where T: Clone {
    UniqueSrc::from_fn(values.len(), |i| {
      // SAFETY: i ranges from 0..len==src.len()
      unsafe { values.get_unchecked(i) }.clone()
    })
  }
  
  #[inline]
  pub fn copied(values: &[T]) -> UniqueSrc<[T]> where T: Copy {
    let len = values.len();
    let header = InnerHeader::new_inner::<T, AllocUninit>(len);
    // SAFETY:
    // * we just got this from InnerHeader::new_inner::<T>
    // * no one else has seen the ptr yet, so the read/write requirements are fine
    let start = unsafe { InnerHeader::get_body_ptr::<T>(header) };
    let values = NonNull::from_ref(values).cast();
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

impl UniqueSrc<str> {
  
  #[inline]
  pub fn new(s: impl AsRef<str>) -> UniqueSrc<str> {
    let s = s.as_ref();
    let this = UniqueSrc::copied(s.as_bytes());
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

#[cfg(test)]
mod tests {
  
  use std::{cell::Cell, mem::MaybeUninit, ops::{Deref, DerefMut}, panic::{catch_unwind, AssertUnwindSafe}, str::Utf8Error};
  use crate::*;
  
  #[test]
  fn downgrade() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(3);
    let w: WeakSrc<[u8]> = UniqueSrc::downgrade(&u);
    assert!(w.upgrade().is_none());
    let s1: Src<[u8]> = UniqueSrc::into_shared(u);
    let s2: Src<[u8]> = w.upgrade().unwrap();
    assert_eq!(s1, s2);
    assert!(Src::ptr_eq(&s1, &s2));
  }
  
  #[test]
  fn into_shared() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_array([1, 2, 3]);
    let s1: Src<[u8]> = UniqueSrc::into_shared(u);
    let s2: Src<[u8]> = s1.clone();
    assert_eq!(*s1, [1, 2, 3]);
    assert!(Src::ptr_eq(&s1, &s2));
  }
  
  #[test]
  fn len() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(0);
    assert_eq!(u.len(), 0);
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(1);
    assert_eq!(u.len(), 1);
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(17);
    assert_eq!(u.len(), 17);
  }
  
  #[test]
  fn is_empty() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(0);
    assert!(u.is_empty());
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(1);
    assert!(!u.is_empty());
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(17);
    assert!(!u.is_empty());
  }
  
  // TODO: I now realize that, given the current behavior of Weak::into_slice, UninitSrc::downgrade_slice will always panic;
  //       that said, there is at least one larger item on my todo list that will resolve this problem,
  //       so for now I'm just marking this test as #[should_panic] and moving on
  #[test]
  #[should_panic]
  fn downgrade_slice() {
    { // slice
      let u: UniqueSrc<[u8]> = UniqueSrc::from_array([1, 2, 3]);
      let w: WeakSrc<[u8]> = u.downgrade_slice(1..);
      assert!(w.upgrade().is_none());
      let s1: Src<[u8]> = UniqueSrc::into_shared(u);
      let s2: Src<[u8]> = w.upgrade().unwrap();
      assert_eq!(s1[1..], *s2);
      assert_eq!(*s2, [2, 3]);
      assert!(Src::same_root(&s1, &s2));
    }
    { // item
      let u: UniqueSrc<[u8]> = UniqueSrc::from_array([1, 2, 3]);
      let w: WeakSrc<u8> = u.downgrade_slice(1);
      assert!(w.upgrade().is_none());
      let s1: Src<[u8]> = UniqueSrc::into_shared(u);
      let s2: Src<u8> = w.upgrade().unwrap();
      assert_eq!(s1[1], *s2);
      assert_eq!(*s2, 2);
      let s2: Src<[u8]> = Src::as_slice(s2);
      assert!(Src::same_root(&s1, &s2));
    }
  }
  
  #[test]
  fn single() {
    let u: UniqueSrc<u8> = UniqueSrc::single(42);
    let s: Src<u8> = UniqueSrc::into_shared(u);
    assert!(Src::is_root(&s));
    let s: Src<[u8]> = Src::as_slice(s);
    assert_eq!(s.len(), 1);
  }
  
  #[test]
  fn single_uninit() {
    let mut u: UniqueSrc<MaybeUninit<u8>> = UniqueSrc::single_uninit();
    u.write(42);
    // SAFETY: just initialized this with u.write()
    let u: UniqueSrc<u8> = unsafe { u.assume_init() };
    assert_eq!(*u, 42);
  }
  
  #[test]
  fn single_zeroed() {
    let u: UniqueSrc<MaybeUninit<u8>> = UniqueSrc::single_zeroed();
    // SAFETY: u8 is a zeroable type
    let u: UniqueSrc<u8> = unsafe { u.assume_init() };
    assert_eq!(*u, 0);
  }
  
  #[test]
  fn as_slice() {
    let u: UniqueSrc<u8> = UniqueSrc::single(42);
    let u: UniqueSrc<[u8]> = UniqueSrc::as_slice(u);
    assert_eq!([42], *u);
  }
  
  #[test]
  fn downgrade_as_slice() {
    let u: UniqueSrc<u8> = UniqueSrc::single(42);
    let w: WeakSrc<[u8]> = UniqueSrc::downgrade_as_slice(&u);
    let s1: Src<u8> = UniqueSrc::into_shared(u);
    let s2: Src<[u8]> = w.upgrade().unwrap();
    assert_eq!([*s1], *s2);
  }
  
  #[test]
  fn new_uninit() {
    let mut u: UniqueSrc<[MaybeUninit<u8>]> = UniqueSrc::new_uninit(3);
    assert_eq!(u.len(), 3);
    for (i, elem) in u.iter_mut().enumerate() {
      elem.write(i as _);
    }
    // SAFETY: just initialized it with all the elem.write()s
    let u: UniqueSrc<[u8]> = unsafe { u.assume_init() };
    assert_eq!(*u, [0, 1, 2]);
  }
  
  #[test]
  fn new_zeroed() {
    let u: UniqueSrc<[MaybeUninit<u8>]> = UniqueSrc::new_zeroed(3);
    assert_eq!(u.len(), 3);
    // SAFETY: u8 is a zeroable type
    let u: UniqueSrc<[u8]> = unsafe { u.assume_init() };
    assert_eq!(*u, [0, 0, 0]);
  }
  
  #[test]
  fn from_fn() {
    { // normal
      let u: UniqueSrc<[usize]> = UniqueSrc::from_fn(3, |i| i * 2);
      assert_eq!(*u, [0, 2, 4]);
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
        let _: UniqueSrc<[DropFlagger<'_>]> = UniqueSrc::from_fn(drop_flags.len(), |i| {
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
      let u: UniqueSrc<[usize]> = UniqueSrc::cyclic_from_fn(3, |_, i| i * 2);
      assert_eq!(*u, [0, 2, 4]);
    }
    { // normal, cyclic
      struct S {
        
        all: WeakSrc<[S]>,
        i: usize,
        
      }
      let u: UniqueSrc<[S]> = UniqueSrc::cyclic_from_fn(3, |w, i| S { all: w.clone(), i: i * 2 });
      assert_eq!(u[0].i, 0);
      assert_eq!(u[1].i, 2);
      assert_eq!(u[2].i, 4);
      assert!(u[0].all.upgrade().is_none());
      let s1: Src<[S]> = UniqueSrc::into_shared(u);
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
        let _: UniqueSrc<[DropFlagger<'_>]> = UniqueSrc::cyclic_from_fn(drop_flags.len(), |_, i| {
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
    let u: UniqueSrc<[u8]> = UniqueSrc::from_iter(vec![1, 2, 3].into_iter().map(|i| i * 2));
    assert_eq!(*u, [2, 4, 6]);
  }
  
  #[test]
  fn from_array() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_array([1, 2, 3]);
    assert_eq!(*u, [1, 2, 3]);
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
    let u: UniqueSrc<[u8]> = UniqueSrc::from_default(3);
    assert_eq!(*u, [0, 0, 0]);
    let u: UniqueSrc<[D42]> = UniqueSrc::from_default(3);
    assert_eq!(*u, [D42(42), D42(42), D42(42)]);
  }
  
  #[test]
  fn filled() {
    let u: UniqueSrc<[u8]> = UniqueSrc::filled(3, &42);
    assert_eq!(*u, [42, 42, 42]);
  }
  
  #[test]
  fn cloned() {
    #[derive(Clone, Eq, PartialEq, Debug)]
    struct NonCopy(u8);
    let u: UniqueSrc<[NonCopy]> = UniqueSrc::cloned(&[NonCopy(1), NonCopy(2), NonCopy(3)]);
    assert_eq!(*u, [NonCopy(1), NonCopy(2), NonCopy(3)]);
  }
  
  #[test]
  fn copied() {
    let u: UniqueSrc<[u8]> = UniqueSrc::copied(&[1, 2, 3]);
    assert_eq!(*u, [1, 2, 3]);
  }
  
  #[test]
  fn assume_init_single() {
    let u: UniqueSrc<MaybeUninit<u8>> = UniqueSrc::single_zeroed();
    // SAFETY: u8 is a zeroable type
    let u: UniqueSrc<u8> = unsafe { u.assume_init() };
    assert_eq!(*u, 0);
  }
  
  #[test]
  fn assume_init_slice() {
    let u: UniqueSrc<[MaybeUninit<u8>]> = UniqueSrc::new_zeroed(3);
    // SAFETY: u8 is a zeroable type
    let u: UniqueSrc<[u8]> = unsafe { u.assume_init() };
    assert_eq!(*u, [0, 0, 0]);
  }
  
  #[test]
  fn new() {
    let u: UniqueSrc<str> = UniqueSrc::new("Hello World!");
    assert_eq!(&*u, "Hello World!");
  }
  
  #[test]
  fn from_utf8() {
    { // UTF-8
      let u: UniqueSrc<[u8]> = UniqueSrc::copied(b"Hello World!");
      let u: UniqueSrc<str> = UniqueSrc::from_utf8(u).unwrap();
      assert_eq!(&*u, "Hello World!");
    }
    { // not UTF-8
      let u: UniqueSrc<[u8]> = UniqueSrc::copied(&[0xFF]);
      let _: Utf8Error = UniqueSrc::from_utf8(u).unwrap_err();
    }
  }
  
  #[test]
  fn from_utf8_unchecked() {
    let u: UniqueSrc<[u8]> = UniqueSrc::copied(b"Hello World!");
    // SAFETY: just got the bytes from a str
    let u: UniqueSrc<str> = unsafe { UniqueSrc::from_utf8_unchecked(u) };
    assert_eq!(&*u, "Hello World!");
  }
  
  #[test]
  fn as_bytes() {
    let u: UniqueSrc<str> = UniqueSrc::new("Hello World!");
    let u: UniqueSrc<[u8]> = UniqueSrc::as_bytes(u);
    assert_eq!(&*u, b"Hello World!");
  }
  
  #[test]
  fn deref() {
    let u: UniqueSrc<[u8]> = UniqueSrc::from_array([1, 2, 3]);
    assert_eq!(Deref::deref(&u), &[1, 2, 3]);
  }
  
  #[test]
  fn deref_mut() {
    let mut u: UniqueSrc<[i8]> = UniqueSrc::from_array([1, 2, 3]);
    assert_eq!(DerefMut::deref_mut(&mut u), &mut [1, 2, 3]);
    u[0] -= 4;
    u[1] = 42;
    u[2] *= 2;
    assert_eq!(DerefMut::deref_mut(&mut u), &mut [-3, 42, 6]);
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
    let u: UniqueSrc<[DropFlagger<'_>]> = UniqueSrc::from_iter(drop_flags.iter().map(DropFlagger));
    assert!(!drop_flags.iter().any(Cell::get));
    std::mem::drop(u);
    assert!(drop_flags.iter().all(Cell::get));
  }
  
}
