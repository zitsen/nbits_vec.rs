//! [![travis-badge][]][travis] [![release-badge][]][cargo] [![downloads]][cargo]
//! [![docs-badge][]][docs] [![license-badge][]][license]
//!
//! A crate aims to resolve small bits values storage and operations problem.
//!
//! Small bits values will be stored in a vector of `T::Block` - which is a `PrimInt` in
//! memory. Here, we only consider the case that one `T::Block` will store some of the
//! small bits values, such as 1, 2, 3, 4, 5 bits stored in `u8`, `u16`, `u32`, `u64`.
//!
//! **WARN**: In this crate, I([@zitsen](http://github.com/zitsen)) decided to use
//! `RawVec` from unstable `alloc` crate as vector background,
//! which means the API would only be avaliable in `nightly` version of Rust and that
//! the API might be changed in some time the `alloc` API changed.
//! So a `stable` version may never give out.
//!
//! See usage in [struct documentation](struct.NbitsVec.html).
//!
//! [travis-badge]: https://img.shields.io/travis/zitsen/nbits_vec.rs.svg?style=flat-square
//! [travis]: https://travis-ci.org/zitsen/nbits_vec.rs
//! [release-badge]: https://img.shields.io/crates/v/nbits_vec.svg?style=flat-square
//! [downloads]: https://img.shields.io/crates/d/nbits_vec.svg?style=flat-square
//! [cargo]: https://crates.io/crates/nbits_vec
//! [docs-badge]: https://img.shields.io/badge/API-docs-blue.svg?style=flat-square
//! [docs]: https://zitsen.github.io/nbits_vec.rs
//! [license-badge]: https://img.shields.io/crates/l/nbits_vec.svg?style=flat-square
//! [license]: https://github.com/zitsen/nbits_vec.rs/blob/master/LICENSE

#![feature(raw_vec_internals)]


extern crate num_traits;
extern crate alloc;

use alloc::raw_vec::RawVec;

use std::cmp;
use std::fmt::{self, Debug};
use std::hash::{self, Hash};
use std::mem;
use std::ptr;
use std::slice;
use std::ops::{BitAnd, BitOr, Not, Shl, Shr};
use std::marker::{PhantomData, Send, Sync};

use num_traits::{Zero, One};

use self::value::*;

pub mod value;
pub mod consts;
// pub mod traits;
/// Implement vector contains small `N`-bits values using `T::Block` as unit
/// buffer.
///
/// The `N` is an [typenum] which is nonzero and smaller than the size of `T::Block`.
/// The `T::Block` is a `PrimInt` - primitive iterger type, we expect as `Unsigned`,
/// suck as `u8`, `u32`, `u64`, but it's ok to use `i32`,`i64`,etc.
///
/// According to the benchmarks, we sugguest that:
///
/// * Use exact size `T::Block`, means to use `u8`, `u64`, not `usize`.
/// * Prefer `u64` in an long vector.
/// * Prefer `u8` in an short vector.
/// * Prefer `u64`/`u32` than `u8` if cares `insert`/`remove`.
/// * Anytime ignore the `u16` from your choise unless you really want it.
///
/// Note that the result only based on my machine.
/// Anyone is welcome for sugguestions to use.
///
/// [typenum]: https://crates.io/crates/typenum
///
/// # Examples
///
/// ```rust
/// extern crate nbits_vec as nbits_vec;
/// use nbits_vec::NbitsVec;
/// use nbits_vec::consts::N2B64 as N2;
/// type NVec = NbitsVec<N2>;
/// fn main() {
///     // News.
///     let _ = NVec::with_capacity(5);
///     let mut vec = NVec::new();
///     // Pushes and pops.
///     vec.push(0b11);
///     vec.push(0b10);
///     let val = vec.pop();
///     # assert_eq!(val, Some(0b10));
///     # let val = vec.pop();
///     # assert_eq!(val, Some(0b11));
///     // Resizes and reserves.
///     vec.resize(10, 0b01);
///     vec.reserve(12);
///     assert!(vec.capacity() >= 10 + 12);
///     # assert_eq!(vec.len(), 10);
///     # assert_eq!(vec.get(3), 0b01);
///     // Gets and sets.
///     vec.set(7, 0b10);
///     # assert_eq!(vec.get(7), 0b10);
///     let _ = vec.get(7);
///     // Inserts and removes.
///     vec.insert(4, 0b01);
///     # assert_eq!(vec.len(), 11);
///     let _ = vec.remove(4);
///     # assert_eq!(vec.len(), 10);
///     // Fills `8` values from `2` as `0b11`.
///     vec.fill(2, 8, 0b11);
/// }
/// ```
pub struct NbitsVec<T: Value> {
    buf: RawVec<T::Block>,
    len: usize,
    _marker: PhantomData<T>,
}

impl<T: ValueExt> NbitsVec<T> {
    /// Constructs a new, empty NbitsVec<N>
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::new();
    /// # }
    /// ```
    ///
    /// # Panics
    ///
    /// Constructor will panic if the `T::Block` unit bits is smaller than `N`bits.
    /// This should panic in `new`, `with_capacity`, `from_raw_parts` methods.
    #[inline]
    pub fn new() -> Self {
        NbitsVec {
            buf: RawVec::new(),
            len: 0,
            _marker: PhantomData,
        }
    }
    /// Constructs a new, empty Vec<N> with the specified capacity.
    ///
    /// The vector will be able to hold exactly capacity elements without reallocating. If capacity
    /// is 0, the vector will not allocate.
    ///
    /// It is important to note that this function does not specify the length of the returned
    /// vector, but only the capacity.
    ///
    /// # Examples
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// assert!(vec.capacity() >= 10);
    /// # }
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        NbitsVec {
            buf: RawVec::with_capacity(T::raw_cap_from(capacity)),
            len: 0,
            _marker: PhantomData,
        }
    }

    /// Constructs a `NbitsVec<T>` directly from the raw components of another vector,
    /// like [standard Vec][std::vec::Vec] does.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't checked:
    ///
    /// * `ptr` needs to have been previously allocated via `Vec<T>/NbitsVec<T>`.
    /// * `length` needs to be the length that less than or equal to `capacity`.
    /// * `capacity` needs to be the `capacity` as a `NbitsVec<T>`, not the size that
    /// the pointer was allocated with.
    ///
    /// # Examples
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// use std::mem;
    /// fn main() {
    ///     let mut v: NbitsVec<N2> = NbitsVec::with_capacity(10);
    ///     v.push(1); v.push(2); v.push(3);
    ///     let p = v.raw_mut_ptr();
    ///     let len = v.len();
    ///     let cap = v.capacity();
    ///     unsafe {
    ///         mem::forget(v);
    ///         let rebuilt: NbitsVec<N2> = NbitsVec::from_raw_parts(p, len, cap);
    ///         assert!(cap == rebuilt.capacity());
    ///     }
    /// }
    /// ```
    ///
    /// [std::vec::Vec]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.from_raw_parts
    #[inline]
    pub unsafe fn from_raw_parts(ptr: *mut T::Block, length: usize, capacity: usize) -> Self {
        NbitsVec {
            buf: RawVec::from_raw_parts(ptr, T::raw_cap_from(capacity)),
            len: length,
            _marker: PhantomData,
        }
    }

    /// Returns the number of elements the vector can hold without reallocating.
    ///
    /// # Examples
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::{NbitsVec};
    /// # use nbits_vec::consts::N1B64 as N1;
    /// # fn main() {
    /// let v: NbitsVec<N1> = NbitsVec::with_capacity(10);
    /// println!("{:?}", v);
    /// assert!(v.capacity() >= 10);
    /// assert_eq!(v.capacity(), 64);
    /// # }
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        T::cap_from(self.buf.cap())
    }

    /// Reserves capacity for at least additional more elements to be inserted in the given
    /// NbitsVec<N>.
    /// The collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows usize.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut v: NbitsVec<N2> = NbitsVec::new();
    /// assert!(v.capacity() == 0);
    /// v.reserve(100);
    /// assert!(v.capacity() >= 100);
    /// # }
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        let required_cap = self.len().checked_add(additional).expect("capacity overflow");
        let used_cap = T::raw_cap_from(self.len());
        let need_extra_cap = T::raw_cap_from(required_cap);
        self.buf.reserve(used_cap, need_extra_cap);
    }

    /// Reserves the minimum capacity for exactly additional more elements to be inserted in the
    /// given `NbitsVec<N>`. Does nothing if the capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows usize.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// use nbits_vec::*;
    /// # fn main() {
    /// let mut v: NbitsVec<N2> = NbitsVec::new();
    /// assert!(v.capacity() == 0);
    /// v.reserve_exact(64);
    /// assert_eq!(v.capacity(), 64);
    /// v.reserve_exact(127);
    /// assert!(v.capacity() >= 127);
    /// v.reserve_exact(128);
    /// assert_eq!(v.capacity(), 128);
    /// # }
    /// ```
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        let required_cap = self.len().checked_add(additional).expect("capacity overflow");
        let used_cap = T::raw_cap_from(self.len());
        let need_extra_cap = T::raw_cap_from(required_cap);
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
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// vec.shrink_to_fit();
    /// assert_eq!(vec.capacity(), 0);
    /// # }
    /// ```
    ///
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        let fit_len = T::raw_cap_from(self.len());
        self.buf.shrink_to_fit(fit_len);
    }

    /// Shorten a vector to be `len` elements long, dropping excess elements.
    ///
    /// If `len` is greater than the vector's current length, this has no effect.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::with_capacity(2);
    /// unsafe { vec.set_len(2) }
    /// vec.truncate(3);
    /// assert_eq!(vec.len(), 2);
    /// vec.truncate(1);
    /// assert_eq!(vec.len(), 1);
    /// # }
    /// ```
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if self.len() > len {
            self.len = len;
            self.shrink_to_fit();
        }
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
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut v: NbitsVec<N2> = NbitsVec::new();
    /// unsafe {
    ///     v.set_len(3);
    /// }
    /// # assert_eq!(v.len(), 3);
    /// # assert_eq!(v.capacity(), 0); // as documented, the capacity will not change
    /// # unsafe {
    /// #    v.set_len(1)
    /// # }
    /// # assert_eq!(v.len(), 1);
    /// # }
    /// ```
    #[inline]
    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut v: NbitsVec<N2> = NbitsVec::new();
    /// v.push(0b01);
    /// v.push(0b10);
    /// assert_eq!(v.len(), 2);
    /// v.insert(1, 0b11);
    /// assert_eq!(v.get(1), 0b11);
    /// assert_eq!(v.get(2), 0b10);
    /// # }
    #[inline]
    pub fn insert(&mut self, index: usize, element: T::Block) {
        self.align(index, index + 1);
        self.set(index, element);
    }

    /// Removes and returns the element at position `index` within the vector, shifting all elements
    /// after position `index` one position to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut v: NbitsVec<N2> = NbitsVec::new();
    /// v.push(0b01);
    /// v.push(0b10);
    /// assert_eq!(v.remove(0), 0b01);
    /// # }
    /// ```
    #[inline]
    pub fn remove(&mut self, index: usize) -> T::Block {
        if index >= self.len {
            panic!("index is out of bounds");
        }
        if self.is_empty() {
            panic!("vector is empty");
        }
        if self.len() == 1 {
            return self.pop().expect("swap removed with one element");
        }
        let removed = self.get(index);
        self.align(index + 1, index);
        removed
    }

    /// Removes an element from anywhere in the vector and return it, replacing it with the last
    /// element.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    /// Panics if vector is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut v: NbitsVec<N2> = NbitsVec::new();
    /// v.push(0b01);
    /// v.push(0b10);
    /// v.push(0b11);
    /// assert_eq!(v.len(), 3);
    /// println!("{:?}", v);
    /// assert_eq!(v.swap_remove(0), 0b01);
    /// println!("{:?}", v);
    /// assert_eq!(v.len(), 2);
    /// assert_eq!(v.get(0), 0b11);
    /// assert_eq!(v.get(1), 0b10);
    /// println!("{:?}", v);
    /// assert_eq!(v.swap_remove(0), 0b11);
    /// # }
    /// ```
    #[inline]
    pub fn swap_remove(&mut self, index: usize) -> T::Block {
        if index >= self.len {
            panic!("index is out of bounds");
        }
        if self.is_empty() {
            panic!("vector is empty");
        }
        if self.len() == 1 {
            return self.pop().expect("swap removed with one element");
        }
        let value = self.get(index);
        let last = self.pop().expect("swap removed with last element");
        self.set(index, last);
        value
    }

    /// Moves all the elements of `other` into `Self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the vector overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::new();
    /// let mut other: NbitsVec<N2> = NbitsVec::new();
    /// other.resize(2, 0b10);
    /// vec.append(&mut other);
    /// assert_eq!(vec.len(), 2);
    /// assert_eq!(other.len(), 0);
    /// # assert_eq!(vec.get(0), 0b10);
    /// # assert_eq!(vec.get(1), 0b10);
    /// # }
    /// ```
    #[inline]
    pub fn append(&mut self, other: &mut Self) {
        let other_len = other.len();
        self.reserve_exact(other_len);
        for i in 0..other_len {
            let v = other.get(i);
            self.push(v);
        }
        unsafe { other.set_len(0) }
    }

    /// Simplely sets the `len` as 0.
    #[inline]
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Returns the number of values.
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
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// assert_eq!(vec.bits(), 0);
    /// # }
    /// ```
    #[inline]
    pub fn bits(&self) -> usize {
        self.len() * T::nbits()
    }

    /// Total bits in buf.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::NbitsVec;
    /// # use nbits_vec::consts::N2B64 as N2;
    /// # fn main() {
    /// let vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// assert_eq!(vec.cap_bits(), std::mem::size_of::<usize>() * 8);
    /// # }
    /// ```
    #[inline]
    pub fn cap_bits(&self) -> usize {
        self.raw_cap() * T::block_bits()
    }

    /// Returns whether or not the vector is empty.
    ///
    /// Alias to `len() == 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// assert!(vec.is_empty());
    /// # }
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::new();
    /// vec.push(0b10);
    /// vec.push(0b01);
    /// assert_eq!(vec.len(), 2);
    /// # }
    /// ```
    #[inline]
    pub fn push(&mut self, value: T::Block) {
        let len = self.len();
        if self.capacity() == len {
            self.reserve(1);
        }
        self.len += 1;
        self.set(len, value);
    }

    /// Removes the last element from a vector and returns it, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::new();
    /// vec.push(0b10);
    /// vec.push(0b11);
    /// assert_eq!(vec.pop(), Some(0b11));
    /// assert_eq!(vec.pop(), Some(0b10));
    /// assert_eq!(vec.len(), 0);
    /// # }
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T::Block> {
        if self.len == 0 {
            None
        } else {
            let ret = Some(self.get(self.len() - 1));
            self.len -= 1;
            ret
        }
    }

    /// Resizes the Vec in-place so that len() is equal to new_len.
    ///
    /// If new_len is greater than len(), the Vec is extended by the difference, with each
    /// additional slot filled with value. If new_len is less than len(), the Vec is simply
    /// truncated. Note that `resize` expand memeory will use `reserve_exact` method to
    /// fit size.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::new();
    /// vec.resize(10, 0);
    /// # assert_eq!(vec.capacity(), 12);
    /// # }
    /// ```
    #[inline]
    pub fn resize(&mut self, new_len: usize, value: T::Block) {
        let len = self.len();
        if len < new_len {
            let n = new_len - len;
            self.reserve_exact(n);
            self.len = new_len;
            self.fill(len, n, value);
        } else {
            self.truncate(new_len);
        }
    }

    /// Move a value flag from `from` to `to`, mask or zero the interval bits.
    ///
    /// Indeed, it means to insert or remove `to - from` count of values.
    ///
    /// Show what it does:
    ///
    /// * from < to:
    ///
    /// ```text
    ///   - Before-align: -----1-------------0--------
    ///                        |from         |to
    ///   - After-align:  -----000000000000001--------------0------
    ///                                      |`from`        |`to`
    /// ```
    ///
    /// * from > to:
    ///
    /// ```text
    ///   - Before-align: -----1-------------0--------
    ///                        |to           |from
    ///   - After-align:  -----0--------
    ///                        |from, to
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::new();
    /// // Prepare data.
    /// vec.resize(24, 0);
    /// vec.fill(0, 12, 1);
    /// vec.fill(12, 12, 2);
    /// # println!("{:?}", vec);
    /// // Left align will reduce the length.
    /// vec.align(1, 0);
    /// # assert_eq!(vec.len(), 23);
    /// # assert!((0..).take(11).all(|x| vec.get(x) == 1));
    /// # assert!((11..).take(12).all(|x| vec.get(x) == 2));
    /// vec.align(11, 3);
    /// # assert_eq!(vec.len(), 23 - 8);
    /// # assert!((0..).take(3).all(|x| vec.get(x) == 1));
    /// # assert!((3..vec.len()).all(|x| vec.get(x) == 2));
    /// // Right align will expand the length.
    /// vec.align(6, 7);
    /// # assert_eq!(vec.len(), 23 - 8 + 1);
    /// # assert!((6..7).all(|x| vec.get(x) == 0));
    /// # assert!((7..vec.len()).all(|x| vec.get(x) == 2));
    /// vec.align(13, 33);
    /// # assert_eq!(vec.len(), 23 - 8 + 1 + 33 - 13);
    /// # assert!((13..33).all(|x| vec.get(x) == 0));
    /// # assert!((33..vec.len()).all(|x| vec.get(x) == 2));
    /// println!("{:?}", vec);
    /// # }
    /// ```
    #[inline]
    pub fn align(&mut self, from: usize, to: usize) {
        if from > to {
            // Reduce `interval` length.
            let interval = from - to;
            for from in from..self.len() {
                let value = self.get(from);
                self.set(from - interval, value);
            }
            self.len = self.len - interval;
        } else {
            // Expand with `interval` length values.
            let interval = to - from;
            let len = self.len();
            self.reserve_exact(interval);
            self.len = len + interval;
            for from in (from..len).rev() {
                let value = self.get(from);
                self.set(from + interval, value);
            }
            // Set interval values as 0.
            self.fill(from, interval, T::Block::zero());
        }
    }

    /// Fill vector buf as `value` from `index` with size `length`.
    ///
    /// ## Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::new();
    /// vec.resize(24, 0);
    /// # println!("{:?}", vec);
    /// vec.fill(1, 2, 2); // length < buf_unit
    /// # assert!((1..).take(2).all(|x| vec.get(x) == 2));
    /// vec.fill(0, 8, 1); // offset: 0, 0
    /// # assert!((0..).take(8).all(|x| vec.get(x) == 1));
    /// vec.fill(7, 10, 2); // offset: n, n
    /// # assert!((7..).take(10).all(|x| vec.get(x) == 2));
    /// vec.fill(8, 11, 1); // offset: 0, n
    /// # assert!((8..).take(11).all(|x| vec.get(x) == 1));
    /// # }
    /// ```
    #[inline]
    pub fn fill(&mut self, index: usize, length: usize, value: T::Block) {
        for i in index..cmp::min(index + length, self.len) {
            unsafe { self.unchecked_set(i, value) }
        }
    }

    /// ## Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// unsafe { vec.set_len(2) }
    /// vec.set(0, 0b11);
    /// assert_eq!(vec.get(0), 0b11);
    /// # }
    /// ```
    #[inline]
    pub fn set(&mut self, index: usize, value: T::Block) {
        if index >= self.len {
            panic!("attempt to set at {} but only {}", index, self.len);
        }
        unsafe { self.unchecked_set(index, value) }
    }

    // `set` the `index`th value as `value` without length checked.
    #[inline]
    unsafe fn unchecked_set(&mut self, index: usize, value: T::Block) {
        let nbits = T::nbits();
        let offset = index * nbits;
        if nbits == 1 {
            self.set_raw_bit(offset, value & T::Block::one() == T::Block::one());
            return;
        }
        let bi = T::bit_index(offset);
        if T::is_packed() {
            let ptr = self.buf.ptr().offset(bi as isize);
            ptr::write(ptr, value);
            return;
        }
        let bo = T::bit_offset(offset);
        let bo2 = T::bit_offset(offset + nbits);
        let block_bits = T::block_bits();
        if T::is_aligned() || bo < bo2 || bo2 == 0 {
            let mask = T::mask();
            let ptr = self.buf.ptr().offset(bi as isize);
            let ori = ptr::read(ptr);
            let new = ori & !(mask << bo) | ((value & mask) << bo);
            if ori != new {
                ptr::write(ptr, new);
            }
        } else {
            let mask = T::mask();
            let ptr = self.buf.ptr().offset(bi as isize);
            let ori = ptr::read(ptr);
            let new = T::Block::zero()
                          .not()
                          .shr(block_bits - bo)
                          .bitand(ori)
                          .bitor(value.bitand(mask).shl(bo));
            if ori != new {
                ptr::write(ptr, new);
            }
            let ptr = ptr.offset(1);
            let ori = ptr::read(ptr);
            let new = value.shr(nbits - bo2).bitand(mask).bitor(mask.not().bitand(ori));
            if ori != new {
                ptr::write(ptr, new);
            }
        }
    }

    /// Set `length` bits of buf at `offset`th bit as `value`.
    ///
    /// ## Unsafety
    ///
    /// `set_raw_bits` will not check the `offset`. Users should ensure to do this manually.
    ///
    /// ## Panics
    ///
    /// This method should panic while required `length` is longer than the buf unit bits size.
    ///
    /// ## Examples
    ///
    /// ```no_run
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    ///
    /// unsafe {
    ///     println!("Set buf 0 as 1");
    ///     vec.set_raw_bits(0, 1, 1);
    ///     println!("Set buf bits [1, 2] as `10`");
    ///     vec.set_raw_bits(1, 2, 2);
    ///     println!("Set buf bits [3, 6] as `1010`");
    ///     vec.set_raw_bits(3, 4, 0b1010);
    /// }
    /// println!("{:?}", vec);
    /// unsafe {
    ///     assert_eq!(vec.get_raw_bits(0, 1), 1);
    ///     assert_eq!(vec.get_raw_bits(1, 2), 2);
    ///     assert_eq!(vec.get_raw_bits(3, 4), 0b1010);
    /// }
    /// # }
    /// ```
    #[inline]
    pub unsafe fn set_raw_bits(&mut self, pos: usize, length: usize, value: T::Block) {
        let block_bits = T::block_bits();
        let loc = T::bit_loc(pos);
        debug_assert!(length > 0 && length <= block_bits);
        // 1. Index out of bounds, but without panics or warnigns.
        if loc.0 >= self.raw_cap() {
            println!("index out of bounds");
            return;
        }

        let ptr = self.raw_mut_ptr().offset(loc.0 as isize);
        let ori = ptr::read(ptr);

        // 2. One bit only.
        if length == 1 {
            let mask = T::Block::one() << loc.1;
            let old = (ori >> loc.1) & T::Block::one();
            let new = value & T::Block::one();
            if old != new {
                if new == T::Block::one() {
                    ptr::write(ptr, ori | mask)
                } else {
                    ptr::write(ptr, !mask & ori)
                }
            }
            return;
        }

        // 3. If request pos and length is packed.
        if length == block_bits && loc.1 == 0 {
            ptr::write(ptr, value);
            return;
        }

        let remain = block_bits - length;
        // Value mask
        let mask = !T::Block::zero() >> remain;
        // 4.0. At the begining of the block
        if loc.1 == 0 {
            let new = value & mask | (ori & !mask);
            if ori != new {
                ptr::write(ptr, new);
            }
            return;
        }
        // 4.1 In current index which request to the raw value bits end.
        let end_off = (loc.1 + length) % block_bits;
        if end_off == 0 {
            let new = ((value & mask) << loc.1) | (ori & (!mask >> length));
            if ori != new {
                ptr::write(ptr, new);
            }
            return;
        }
        // 4.2 In current index but only selected bits.
        if end_off > loc.1 {
            let new = ori & !(mask << loc.1) | ((value & mask) << loc.1);
            if ori != new {
                ptr::write(ptr, new);
            }
            return;
        }
        // 5.1 Request for next block but out of bounds.
        if self.raw_cap() == loc.0 + 1 {
            let new = ((value & mask) << loc.1) | (ori & (!mask >> (block_bits - loc.1)));
            if ori != new {
                ptr::write(ptr, new);
            }
            return;
        }

        // 5.3 No other condition should care.
        let new = T::Block::zero()
                      .not()
                      .shr(block_bits - loc.1)
                      .bitand(ori)
                      .bitor(value.shl(loc.1));
        if ori != new {
            ptr::write(ptr, new);
        }
        let ptr = ptr.offset(1);
        let ori = ptr::read(ptr);
        let remain = block_bits - end_off;
        let mask = T::Block::zero().not().shr(remain);
        let new = value.shr(length - end_off).bitand(mask).bitor(mask.not().bitand(ori));
        if ori != new {
            ptr::write(ptr, new);
        }
    }

    /// Set buf unit bit at `index`th unit of `offset`bit.
    #[inline]
    pub unsafe fn set_raw_bit(&mut self, offset: usize, bit: bool) {
        let loc = T::bit_loc(offset);
        let mask = T::Block::one() << loc.1;
        let ptr = self.buf.ptr().offset(loc.0 as isize);
        let cur = ptr::read(ptr);
        let old = cur >> loc.1 & T::Block::one();
        match (old == T::Block::one(), bit) {
            (lhs, rhs) if lhs == rhs => (),
            (_, true) => ptr::write(ptr, cur | mask),
            (_, false) => ptr::write(ptr, cur & !mask),
        }
    }

    /// Get `N` bits value as `B`.
    ///
    /// ## Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// unsafe { vec.set_len(2) }
    /// vec.set(0, 0b11);
    /// assert_eq!(vec.get(0), 0b11);
    /// # }
    /// ```
    #[inline]
    pub fn get(&self, index: usize) -> T::Block {
        if index >= self.len {
            panic!("index out of bounds: attempt to get at {} but only {}",
                   index,
                   self.len);
        }
        let nbits = T::nbits();
        let bit_pos = index * nbits;
        let bi = T::bit_index(bit_pos);
        let bo = T::bit_offset(bit_pos);
        unsafe {
            let ptr = self.raw_ptr().offset(bi as isize);
            if nbits == 1 {
                return ptr::read(ptr) >> bo & T::Block::one();
            }
            let bo2 = T::bit_offset(bit_pos + nbits);
            let block_bits = T::block_bits();
            if bo2 == 0 {
                ptr::read(ptr) >> (block_bits - nbits)
            } else if bo < bo2 {
                ptr::read(ptr) << (block_bits - bo2) >> (block_bits - nbits)
            } else {
                (ptr::read(ptr) >> bo) |
                (ptr::read(ptr.offset(1)) << (block_bits - bo2) >> (block_bits - nbits))
            }
        }
    }

    /// Get `length` bits of buf at `offset`th bit.
    ///
    /// # Unsafety
    ///
    /// `get_raw_bits` will not check the `offset`. Users should ensure to do this manually.
    ///
    /// # Panics
    ///
    /// This method should panic while required `length` is longer than the buf unit bits size.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate nbits_vec;
    /// # use nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::new();
    /// vec.resize(10, 0);
    /// println!("{:?}", vec);
    /// for i in 0..8 {
    ///     unsafe { vec.set_raw_bit(i, if i % 2 == 0 { true } else { false }); }
    /// }
    /// println!("{:?}", vec);
    /// unsafe {
    ///     println!("Get buf bits at 0 with length 1");
    ///     assert_eq!(vec.get_raw_bits(0, 1), 1);
    ///     println!("Get buf bits at 1 with length 2");
    ///     assert_eq!(vec.get_raw_bits(1, 2), 2);
    ///     println!("Get buf bits at 3 with length 4");
    ///     assert_eq!(vec.get_raw_bits(3, 4), 0b1010);
    /// }
    /// # }
    /// ```
    #[inline]
    pub unsafe fn get_raw_bits(&self, pos: usize, length: usize) -> T::Block {
        debug_assert!(length > 0 && length <= T::block_bits());
        let loc = T::bit_loc(pos);
        // 1. Index out of bounds, but without panics or warnigns.
        if loc.0 >= self.raw_cap() {
            return T::Block::zero();
        }
        let ptr = self.raw_ptr().offset(loc.0 as isize);
        // 2. One bit only.
        if length == 1 {
            return ptr::read(ptr) >> loc.1 & T::Block::one();
        }
        let block_bits = T::block_bits();
        // 3. If request pos and length is packed.
        if length == block_bits && loc.1 == 0 {
            return ptr::read(ptr);
        }
        let end_off = (loc.1 + length) % block_bits;
        // 4.1 In current index which request to the raw value bits end.
        if end_off == 0 {
            return ptr::read(ptr) >> (block_bits - length);
        }
        // 4.2 In current index but only selected bits.
        if end_off > loc.1 {
            return ptr::read(ptr) << (block_bits - end_off) >> (block_bits - length);
        }
        // 5. Request for next block.
        //
        // 5.1 Next block out of bounds.
        if self.raw_cap() == loc.0 + 1 {
            return ptr::read(ptr) >> loc.1;
        }
        // 5.2 Request length is fullfill the block, so we cut current left and next right
        //     for the new value.
        if length == block_bits {
            return ptr::read(ptr) >> loc.1 | (ptr::read(ptr.offset(1)) << (block_bits - loc.1));
        }
        // 5.3. No other condition should care.
        let e = block_bits - end_off;
        (ptr::read(ptr) >> loc.1) | (ptr::read(ptr.offset(1)) << e >> (block_bits - length))
    }

    /// Get raw bit at `pos`.
    #[inline]
    pub unsafe fn get_raw_bit(&self, pos: usize) -> bool {
        self.get_raw_bits(pos, 1) == T::Block::one()
    }

    /// Returns mutable ptr of `T::Block`.
    #[inline]
    pub fn raw_mut_ptr(&mut self) -> *mut T::Block {
        self.buf.ptr()
    }

    /// Returns ptr of `T::Block`.
    #[inline]
    pub fn raw_ptr(&self) -> *const T::Block {
        self.buf.ptr()
    }

    /// Return raw slice of `T::Block`.
    #[inline]
    pub fn as_raw_slice(&self) -> &[T::Block] {
        unsafe {
            let p = self.buf.ptr();
            debug_assert!(!p.is_null());
            slice::from_raw_parts(p, self.used_raw_cap())
        }
    }

    /// Returns mutable raw slice of `T::Block`.
    #[inline]
    pub fn as_mut_raw_slice(&mut self) -> &mut [T::Block] {
        unsafe {
            let p = self.buf.ptr();
            debug_assert!(!p.is_null());
            slice::from_raw_parts_mut(p, self.used_raw_cap())
        }
    }

    /// Returns raw boxed slice of `T::Block`.
    #[inline]
    pub fn into_raw_boxed_slice(mut self) -> Box<[T::Block]> {
        unsafe {
            self.shrink_to_fit();
            let buf = ptr::read(&self.buf);
            mem::forget(self);
            buf.into_box()
        }
    }

    /// Used capacity in `RawVec`.
    #[inline]
    fn used_raw_cap(&self) -> usize {
        let loc = T::bit_loc(self.bits());
        if loc.1 == 0 {
            loc.0
        } else {
            loc.0 + 1
        }
    }

    /// The `RawVec` buffer capacity(T::Block).
    #[inline]
    fn raw_cap(&self) -> usize {
        self.buf.cap()
    }
}

impl<T: OneBit> NbitsVec<T> {}
impl<T: Aligned> NbitsVec<T> {}

impl<T: ValueExt> Default for NbitsVec<T> {
    #[inline]
    fn default() -> Self {
        NbitsVec {
            buf: RawVec::new(),
            len: 0,
            _marker: PhantomData,
        }
    }
}

impl<T: Value> Debug for NbitsVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f,
                    "NbitsVec<{}> {{ len: {}, buf: RawVec {{ cap: {}, [",
                    T::nbits(),
                    self.len,
                    self.buf.cap()));
        let ptr = self.buf.ptr();
        for i in 0..self.buf.cap() {
            unsafe {
                try!(write!(f, "{:#x}, ", ptr::read(ptr.offset(i as isize))));
            }
        }
        write!(f, "] }}")
    }
}

impl<T: ValueExt> Hash for NbitsVec<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        Hash::hash(self.as_raw_slice(), state);
    }
}

impl<T: ValueExt> PartialEq for NbitsVec<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.as_raw_slice() == other.as_raw_slice()
    }
    #[inline]
    fn ne(&self, other: &Self) -> bool {
        self.len() != other.len() || self.as_raw_slice() == other.as_raw_slice()
    }
}

impl<T: ValueExt> Eq for NbitsVec<T> {}

impl<T: ValueExt> Clone for NbitsVec<T> {
    fn clone(&self) -> Self {
        let mut new = Self::with_capacity(self.len());
        unsafe {
            ptr::copy_nonoverlapping(self.buf.ptr(), new.buf.ptr(), self.used_raw_cap());
            new.set_len(self.len());
        }
        new
    }
}

impl<T: ValueExt> PartialOrd for NbitsVec<T> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_raw_slice(), other.as_raw_slice())
    }
}

impl<T: ValueExt> Ord for NbitsVec<T> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Ord::cmp(self.as_raw_slice(), other.as_raw_slice())
    }
}

unsafe impl<T: ValueExt> Send for NbitsVec<T> {}

unsafe impl<T: ValueExt> Sync for NbitsVec<T> {}

pub type N1 = consts::N1B8;
pub type N2 = consts::N2B8;
pub type N3 = consts::N3B8;
pub type N4 = consts::N4B8;

#[cfg(test)]
mod tests;
