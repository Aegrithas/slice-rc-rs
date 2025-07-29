use std::{borrow::{Borrow, BorrowMut}, cmp::Ordering, fmt::{self, Debug, Formatter, Pointer}, hash::{Hash, Hasher}, marker::PhantomData, mem::{forget, MaybeUninit}, ops::{Deref, DerefMut, Index, IndexMut}, ptr::NonNull, str::Utf8Error};

use crate::{inner::{Alloc, AllocZeroed}, InnerHeader, Src, SrcIndex, SrcSlice, SrcTarget, UninitSrc, WeakSrc};

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
    let header = InnerHeader::new_inner::<T, Alloc>(len);
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
    let header = InnerHeader::new_inner::<T, Alloc>(N);
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
    let header = InnerHeader::new_inner::<T, Alloc>(len);
    // SAFETY:
    // * we just got this from InnerHeader::new_inner::<T>
    // * no one else has seen the ptr yet, so the read/write requirements are fine
    let start = unsafe { InnerHeader::get_body_ptr::<T>(header) };
    // SAFETY: references can't be null
    let values = unsafe { NonNull::new_unchecked(values.as_ptr().cast_mut()) };
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
    UniqueSrc {
      // SAFETY: self.header has *almost* the same safety invariant as this.header: the only difference is that self uses MaybeUninit<T> where this expects T
      header: self.header,
      // SAFETY: self.start has *almost* the same safety invariant as this.start: the only difference is that self uses MaybeUninit<T> where this expects T
      start: self.start.cast(),
      // SAFETY: self.len has *almost* the same safety invariant as this.len: the only difference is that self uses MaybeUninit<T> where this expects T
      len: self.len,
      _phantom: PhantomData,
    }
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
