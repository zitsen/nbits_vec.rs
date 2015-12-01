use alloc::raw_vec::RawVec;
use std::any::Any;
use std::ops::*;
use std::num::{One, Zero};
use std::mem;
use std::cmp;
use std::ptr;
use std::slice;
use std::marker::PhantomData;
use std::sync::Arc;

macro_rules! _apply_bit_opts {
    ($t: ident, $(($tr: ident, $func: ident)),*) => (
        $(
            impl $tr for $t {
                fn $func(&mut self, rhs: $t) {
                    self.buf.$func(rhs.storage)
                }
            }
        )*
    );
    ($t: ident, $(($tr: ident, $func: ident, $out: ident)),*) => (
        $(
            impl $tr for $t {
                type Output = $t;
                fn $func(self, rhs: $t) -> $t {
                    $t::new(self.buf.$func(rhs.storage))
                }
            }
         )*
    )
}
macro_rules! nbits_set {
    ($(($t: ident, $size: expr, $mask: expr)),*) => (
        $(
            /// Struct for each NBits
            #[derive(Copy, Clone, Eq, Debug, PartialEq, Hash, Deref)]
            pub struct $t<'a>(&'a usize);
            impl<'a> $t<'a> {
                pub fn new(value: &'a usize) -> Self {
                    $t(value)
                }
            }
            impl<'a> Nbits for $t<'a> {
                #[inline]
                fn bits() -> usize {
                    $size
                }
                #[inline]
                fn mask() -> Self {
                    $t::new($mask)
                }
                #[inline]
                fn zero() -> Self {
                    $t::new(&ZERO_BIT)
                }
                #[inline]
                fn val(&self) -> usize {
                    self.0 & $mask
                }
            }

            impl<'a> Deref for $t<'a> {
                type Target = usize;
                fn deref(&self) -> &usize {
                    self.0
                }
            }

            impl<'a> From<$t<'a>> for usize {
                fn from(v: $t<'a>) -> usize {
                    v.val()
                }
            }

            impl<'a> From<&'a usize> for $t<'a> {
                fn from(v: &'a usize) -> $t<'a> {
                    $t::new(v)
                }
            }
            /*
            impl Into<$t> for usize {
                fn into(self) -> $t {
                    $t(self)
                }
            }
            */
            /*
            _apply_bit_opts! {
                $t,
                (BitAnd, bitand, $t),
                (BitXor, bitxor, $t),
                (BitOr, bitor, $t)
            }
            _apply_bit_opts! {
                $t,
                (BitAndAssign, bitand_assign),
                (BitOrAssign, bitor_assign),
                (BitXorAssign, bitxor_assign)
            }
            */
        )*
        #[test]
        fn test_struct_as_nbits() {
            $(
                assert_eq!(mem::size_of::<$t>(), mem::size_of::<usize>());
                assert_eq!($t::bits(), $size);
                assert_eq!($t::zero().val(), 0);
                assert_eq!($t::mask().val().count_ones(), $size);
                assert_eq!($t::mask().val().trailing_zeros(), 0);
                assert_eq!($t::mask().val().leading_zeros() as usize, mem::size_of::<usize>() * 8 - $size);
             )*
        }
        //#[derive(Copy, Clone, Eq, Debug, PartialEq, Hash)]
        //pub enum AsNbits {
        //    $($t($t),)*
        //}

        //pub use AsNbits::*;
        /*
        impl AsNbits {
            pub fn new(value: usize, width: usize) -> Self {
                match width {
                    $($size => $t::new(value),)*
                    _ => unreachable!(),
                }
            }
            pub fn ones(width: usize) -> Self {
                match width {
                    $($size => AsNbits::$t($t::ones()), )*
                    _ => unreachable!(),
                }
            }
            pub fn bits(self) -> usize {
                match self {
                    $(AsNbits::$t(..) => $t::bits(),)*
                }
            }

            pub fn zero(width: usize) -> Self {
                match self {
                    $(AsNbits::$t(..) => AsNbits::$t($t::zero()),)*
                }
            }

            pub fn val(self) -> usize {
                match self {
                    $(AsNbits::$t(v) => v.val(),)*
                }
            }
        }
        impl Deref for AsNbits {
            type Target = usize;
            fn deref(&self) -> &usize {
                match self {
                    $(&AsNbits::$t(ref v) => &v.storage,)*
                }
            }
        }*/
     )
}

static ZERO_BIT: usize = 0;
static ONE_BIT_MASK: usize = 0b1;
static TWO_BIT_MASK: usize = 0b11;
nbits_set! {
    (As1bits, 1, &ONE_BIT_MASK),
    (As2bits, 2, &TWO_BIT_MASK)
}
pub trait Nbits:
    // Default +
    // BitAnd<Output=usize> +
{
    fn bits() -> usize;
    fn mask() -> Self;
    fn zero() -> Self;
    fn val(&self) -> usize;
}

pub struct NbitsVec<T: Nbits, B = usize> {
    buf: RawVec<B>,
    len: usize,
    _marker: PhantomData<T>,
}

impl<
T:  Nbits,
B:  Default +
    Shl<usize, Output=B> +
    Shr<usize, Output=B> +
    Eq + PartialEq + Copy +
    One +
    Zero +
    Not<Output=B> +
    BitOr<Output=B> +
    BitAnd<Output=B>
> Default for NbitsVec<T, B> {
    fn default() -> Self {
        NbitsVec {
            buf: RawVec::new(),
            len: 0,
            _marker: PhantomData,
        }
    }
}

impl<
T:  Nbits,
B:  Shl<usize, Output=B> +
    Shr<usize, Output=B> +
    BitOr<Output=B> +
    BitAnd<Output=B> +
    Eq + PartialEq + Copy +
    One +
    Zero +
    Not<Output=B> +
> NbitsVec<T, B> {
    /// Constructs a new, empty NbitsVec<T>
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<As2bits> = NbitsVec::new();
    /// # }
    /// ```
    #[inline]
    pub fn new() -> Self {
        NbitsVec {
            buf: RawVec::new(),
            len: 0,
            _marker: PhantomData,
        }
    }
    /// Constructs a new, empty Vec<T> with the specified capacity.
    ///
    /// The vector will be able to hold exactly capacity elements without reallocating. If capacity
    /// is 0, the vector will not allocate.
    ///
    /// It is important to note that this function does not specify the length of the returned
    /// vector, but only the capacity.
    ///
    /// # Examples
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<As2bits> = NbitsVec::with_capacity(10);
    /// assert!(vec.capacity() >= 10);
    /// # }
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        NbitsVec {
            buf: RawVec::with_capacity(Self::capacity_to_storage(capacity)),
            len: 0,
            _marker: PhantomData,
        }
    }

    pub unsafe fn from_raw_parts(ptr: *mut B, length: usize, capacity: usize) -> Self {
        NbitsVec {
            buf: RawVec::from_raw_parts(ptr, Self::capacity_to_storage(capacity)),
            len: length,
            _marker: PhantomData,
        }
    }

    /// Returns the number of elements the vector can hold without reallocating.
    ///
    /// # Examples
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::{NbitsVec, As1bits};
    /// # fn main() {
    /// let v: NbitsVec<As1bits> = NbitsVec::with_capacity(10);
    /// assert!(v.capacity() >= 10);
    /// assert_eq!(v.capacity(), std::mem::size_of::<usize>() * 8);
    /// # }
    /// ```
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        Self::storage_to_capacity(self.buf.cap())
    }

    /// Reserves capacity for at least additional more elements to be inserted in the given NbitsVec<T>.
    /// The collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows usize.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let mut v: NbitsVec<As2bits> = NbitsVec::new();
    /// assert!(v.capacity() == 0);
    /// v.reserve(100);
    /// assert!(v.capacity() >= 100);
    /// # }
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        let required_cap = self.len().checked_add(additional).expect("capacity overflow");
        let used_cap = Self::capacity_to_storage(self.len());
        let need_extra_cap = Self::capacity_to_storage(required_cap);
        self.buf.reserve(used_cap, need_extra_cap);
    }

    /// Reserves the minimum capacity for exactly additional more elements to be inserted in the
    /// given `NbitsVec<T>`. Does nothing if the capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows usize.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate bits_vec;
    /// use bits_vec::raw::*;
    /// # fn main() {
    /// let mut v: NbitsVec<As2bits> = NbitsVec::new();
    /// assert!(v.capacity() == 0);
    /// v.reserve_exact(64);
    /// assert_eq!(v.capacity(), 64);
    /// v.reserve_exact(127);
    /// assert!(v.capacity() >= 127);
    /// v.reserve_exact(128);
    /// assert_eq!(v.capacity(), 128);
    /// # }
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        let required_cap = self.len().checked_add(additional).expect("capacity overflow");
        let used_cap = Self::capacity_to_storage(self.len());
        let need_extra_cap = Self::capacity_to_storage(required_cap);
        self.buf.reserve_exact(used_cap, need_extra_cap);
    }
    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator may still inform the
    /// vector that there is space for a few more elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<As2bits> = NbitsVec::with_capacity(10);
    /// vec.shrink_to_fit();
    /// assert_eq!(vec.capacity(), 0);
    /// # }
    /// ```
    ///
    /// # Unimplemented
    pub fn shrink_to_fit(&mut self) {
        let fit_len = Self::capacity_to_storage(self.len());
        self.buf.shrink_to_fit(fit_len);
    }

    pub fn into_boxed_slice(self) -> Box<[T]> {
        unimplemented!();
    }

    /// Shorten a vector to be `len` elements long, dropping excess elements.
    ///
    /// If `len` is greater than the vector's current length, this has no effect.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<As2bits> = NbitsVec::with_capacity(2);
    /// unsafe { vec.set_len(2) }
    /// vec.truncate(3);
    /// assert_eq!(vec.len(), 2);
    /// vec.truncate(1);
    /// assert_eq!(vec.len(), 1);
    /// # }
    /// ```
    pub fn truncate(&mut self, len: usize) {
        if self.len() > len {
            self.len = len;
            self.shrink_to_fit();
        }
    }
    pub fn as_slice(&self) -> &[T] {
        unimplemented!();
    }
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unimplemented!();
    }
    /// Sets the length of a vector.
    ///
    /// This will explicitly set the size of the vector, without actually modifying its buffers or
    /// reserving additional capacity as needed, so it is up to the caller to ensure that the vector
    /// is actually the specified size.
    ///
    /// Recommend to use [resize()](#method.resize) when you actually want to `resize` the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let mut v: NbitsVec<As2bits> = NbitsVec::new();
    /// unsafe {
    ///     v.set_len(3);
    /// }
    /// assert_eq!(v.len(), 3);
    /// assert_eq!(v.capacity(), 0); // as documented, the capacity will not change
    /// unsafe {
    ///     v.set_len(1)
    /// }
    /// assert_eq!(v.len(), 1);
    /// # }
    /// ```
    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }
    pub fn swap_remove(&mut self, index: usize) -> T {
        unimplemented!();
    }
    pub fn insert(&mut self, index: usize, element: T) {
        unimplemented!();
    }
    pub fn remove(&mut self, index: usize) {
        unimplemented!();
    }
    pub fn retain<F>(&mut self, f: F)
        where F: FnMut(&T) -> bool
    {
        unimplemented!();
    }
    pub fn push(&mut self, value: T) {
        unimplemented!();
    }
    pub fn pop(&mut self) -> Option<T> {
        unimplemented!();
    }
    pub fn append(&mut self, other: &mut NbitsVec<T>) {
        unimplemented!();
    }

    // pub fn drain<R>(&mut self, range: R) -> Drain<T>
    // where R: RangeArgument<usize> {
    // unimplemented!();
    // }
    //
    pub fn clear(&mut self) {
        unsafe { self.set_len(0) }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns the number of bits in current length.
    ///
    /// It is related to the element numbers - not the capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let vec: NbitsVec<As2bits> = NbitsVec::with_capacity(10);
    /// assert_eq!(vec.bits(), 0);
    /// # }
    /// ```
    #[inline]
    pub fn bits(&self) -> usize {
        self.len() * T::bits()
    }

    /// Returns whether or not the vector is empty.
    ///
    /// Alias to `len() == 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let vec: NbitsVec<As2bits> = NbitsVec::with_capacity(10);
    /// assert!(vec.is_empty());
    /// # }
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn split_off(&mut self, at: usize) -> Self {
        unimplemented!();
    }
    /// Resizes the Vec in-place so that len() is equal to new_len.
    ///
    /// If new_len is greater than len(), the Vec is extended by the difference, with each
    /// additional slot filled with value. If new_len is less than len(), the Vec is simply
    /// truncated.
    ///
    pub fn resize<V: AsRef<T>>(&mut self, new_len: usize, value: V) {
        if self.len() > new_len {
            self.extend_with_element(new_len, value);
        } else {
            self.truncate(new_len);
        }
    }

    /// Extend the vector by `n` additional clones of `value`.
    fn extend_with_element<V: AsRef<T>>(&mut self, n: usize, value: V) {
        self.reserve_exact(n);
    }

    /// Set `bit` at some bit index.
    ///
    /// # Unsafety
    ///
    /// Be aware of the function will not check the index. Users should ensure to do this manually.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<As2bits> = NbitsVec::with_capacity(10);
    /// vec.reserve(10);
    /// unsafe { vec.set_len(7) };
    /// vec.set_bit(0, true);
    /// # }
    /// ```
    ///
    pub fn set_bit(&mut self, at: usize, bit: bool) {
        let bits = self.bits();
        if at >= bits {
            panic!("attempt to set bit out of bounds");
        }
        let element_bits = mem::size_of::<B>() * 8;
        let storage_index = at / element_bits;
        // assert!(storage_index < self.buf.len());
        let storage_offset = at % element_bits;
        let mask: B = B::one() << storage_offset;
        unsafe {
            let ptr = self.buf.ptr().offset(storage_index as isize);
            if bit {
                ptr::write(ptr, ptr::read(ptr) | mask);
            } else {
                ptr::write(ptr, ptr::read(ptr) & !mask);
            }
        }
    }

    /// Get `bit` at some bit index.
    ///
    /// Returns `None` if required index is out of bounds, else return `bool` for bit value.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<As2bits> = NbitsVec::with_capacity(10);
    /// vec.reserve(10);
    /// assert!(vec.get_bit(0).is_none());
    /// unsafe { vec.set_len(8) };
    /// for i in 0..8 {
    ///     vec.set_bit(i, true);
    ///     assert_eq!(vec.get_bit(i), Some(true));
    /// }
    /// for i in 0..8 {
    ///     vec.set_bit(i, false);
    ///     assert_eq!(vec.get_bit(i), Some(false));
    /// }
    /// # }
    /// ```
    ///
    pub fn get_bit(&self, at: usize) -> Option<bool> {
        let bits = self.bits();
        if at >= bits {
            return None;
        }
        let element_bits = mem::size_of::<B>() * 8;
        let storage_index = at / element_bits;
        let storage_offset = at % element_bits;
        let ptr = unsafe { self.buf.ptr().offset(storage_index as isize) };
        let bit = unsafe { ptr::read(ptr) } >> storage_offset & B::one();
        Some(bit != B::zero())
    }


    pub fn set_bits(&mut self, at: usize, n: usize, bits: usize) {
        let max_n = mem::size_of::<usize>();
        if n > max_n {
            panic!("required setting {} bits but max is {}", n, max_n);
        }
        let mut value = bits;
        for idx in (at..).take(n) {
            self.set_bit(idx, value & 1 == 1);
            value.shr_assign(1);
        }
    }
    pub fn get_bits(&self, at: usize, n: usize) -> usize {
        let max_n = mem::size_of::<usize>();
        if n > max_n {
            panic!("required setting {} bits but max is {}", n, max_n);
        }
        (at..).take(n).fold(0, |v, x| {
            if self.get_bit(x).unwrap() {
                (v << 1) | 1
            } else {
                v << 1
            }
        })
    }

    fn set_two_bits(&mut self, at: usize, bit: usize) {
        let bits = self.bits() / 2;
        if at >= bits {
            panic!("attempt to set two bits at {}, but only have {}", at, bits);
        }
        let element_bits = mem::size_of::<usize>() * 8 / 2;
        let storage_index = at / element_bits;
    }

    pub fn push_all(&mut self, other: &[T]) {
        unimplemented!();
    }
    // And any lost functions from `dedup` to the end.

    pub fn get_mut(&self, index: usize) {
        unimplemented!();
    }

    /// Examples
    ///
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<As2bits> = NbitsVec::with_capacity(10);
    /// unsafe { vec.set_len(2) }
    /// vec.set(0, 0b11usize);
    /// assert!(vec.get_bit(0).unwrap());
    /// assert!(vec.get_bit(1).unwrap());
    /// let a = 0;
    /// let v = As2bits::new(&a);
    /// vec.set(0, v.val());
    /// assert_eq!(vec.get_bit(0), Some(false));
    /// assert_eq!(vec.get_bit(1), Some(false));
    /// # }
    /// ```
    pub fn set(&mut self, index: usize, value: usize) {
        if index >= self.len {
            panic!("attempt to set at {} but only {}", index, self.len);
        }
        self.set_bits(index * T::bits(), T::bits(), value.into());
    }
    /// Examples
    ///
    /// ```
    /// # extern crate bits_vec;
    /// # use bits_vec::raw::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<As2bits> = NbitsVec::with_capacity(10);
    /// unsafe { vec.set_len(2) }
    /// vec.set(0, 0b11usize);
    /// assert_eq!(vec.get(0), 0b11);
    /// # }
    /// ```
    pub fn get(&self, index: usize) -> usize {
        if index >= self.len {
            panic!("attempt to get at {} but only {}", index, self.len);
        }
        self.get_bits(index * T::bits(), T::bits())
    }

    /// Converts capacity to storage size
    fn capacity_to_storage(capacity: usize) -> usize {
        if capacity == 0 {
            0
        } else {
            (capacity * T::bits() - 1) / (mem::size_of::<B>() * 8) + 1
        }
    }

    /// Converts the storage size to capacity.
    fn storage_to_capacity(storage: usize) -> usize {
        storage * mem::size_of::<B>() * 8 / T::bits()
    }
}

#[cfg(test)]
mod tests {
}
//
// pub struct Value<T: Nbits, S: BitOr<Output=usize> = usize> {
// refer: Arc<NbitsVec<T, S>>,
// index: usize,
// }
//
// impl<T: Nbits> Value<T> {
// fn to_nbits(&self) -> T {
// unimplemented!();
// }
// fn val(&self) -> usize {
// self.to_nbits().val()
// }
// fn set<V: AsRef<T>>(&mut self, val: V) {
// unimplemented!();
// }
// }
//
// pub struct Iter<T: Nbits, S = usize> {
// parent: Arc<NbitsVec<T, S>>,
// index: usize,
// }
//
// impl<T: Nbits> Iter<T> {
// fn finished(&self) -> bool {
// unsafe { (*self.parent).len() >= self.index }
// }
// }
//
// impl<T: Nbits> Iterator for Iter<T> {
// type Item = T;
// #[inline]
// fn next(&mut self) -> Option<T> {
// self.index += 1;
// if self.finished() {
// None
// } else {
// Some(unsafe { (*self.parent).get(self.index) })
// }
// }
// }
//
// pub struct IterMut<T: Nbits, S = usize> {
// parent: *mut NbitsVec<T, S>,
// index: usize,
// }
//
