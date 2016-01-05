//! A crate aims to resolve small bits values storage and operations problem.
//!
//! [![Build Status](https://travis-ci.org/zitsen/raw_nbits_vec.rs.svg?branch=master)]
//! (https://travis-ci.org/zitsen/raw_nbits_vec.rs)
//!
//! [Documentation](http://zitsen.github.io/raw_nbits_vec.rs)
//!
//! Small bits values will be stored in a vector of `Block` - which is a `PrimInt` in
//! memory. Here, we only consider the case that one `Block` will store some of the
//! small bits values, such as 1, 2, 3, 4, 5 bits stored in `u8`, `u16`, `u32`, `u64`.
//!
//! **WARN**: In this crate, I([@zitsen](http://github.com/zitsen)) decided to use
//! `RawVec` from unstable `alloc` crate as vector background,
//! which means the API would only be avaliable in `nightly` version of Rust and that
//! the API might be changed in some time the `alloc` API changed.
//! So a `stable` version may never give out.
//!

#![feature(alloc)]
#![feature(plugin)]
#![plugin(clippy)]

extern crate alloc;
extern crate num;
extern crate typenum;

use alloc::raw_vec::RawVec;
use num::PrimInt;
use std::cmp;
use std::fmt::{self, Debug};
use std::hash::{self, Hash};
use std::mem;
use std::ptr;
use std::slice;
use std::ops::{BitAnd, BitOr, Shl, Shr};
use std::marker::{PhantomData, Send, Sync};
use typenum::NonZero;
use typenum::uint::Unsigned;

/// Implement vector contains small `N`-bits values using `Block` as unit
/// buffer.
///
/// The `N` is an [typenum] which is nonzero and smaller than the size of `Block`.
/// The `Block` is a `PrimInt` - primitive iterger type, we expect as `Unsigned`,
/// suck as `u8`, `u32`, `u64`, but it's ok to use `i32`,`i64`,etc.
///
/// According to the benchmarks, we sugguest that:
///
/// * Use exact size `Block`, means to use `u8`, `u64`, not `usize`.
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
/// extern crate raw_nbits_vec as nbits_vec;
/// use nbits_vec::{NbitsVec, N2};
/// type NVec = NbitsVec<N2, u8>;
/// fn main() {
///     // News.
///     let _: NbitsVec<N2, usize> = NbitsVec::with_capacity(5);
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
pub struct NbitsVec<N: Unsigned + NonZero, Block: PrimInt = usize> {
    buf: RawVec<Block>,
    len: usize,
    _marker: PhantomData<N>,
}

impl<N: Unsigned + NonZero, Block: PrimInt> NbitsVec<N, Block> {
    /// Constructs a new, empty NbitsVec<N>
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    /// ```
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::new();
    /// # }
    /// ```
    ///
    /// # Panics
    ///
    /// Constructor will panic if the `Block` unit bits is smaller than `N`bits.
    /// This should panic in `new`, `with_capacity`, `from_raw_parts` methods.
    #[inline]
    pub fn new() -> Self {
        Self::check_if_n_valid();
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// assert!(vec.capacity() >= 10);
    /// # }
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::check_if_n_valid();
        NbitsVec {
            buf: RawVec::with_capacity(Self::raw_cap_from(capacity)),
            len: 0,
            _marker: PhantomData,
        }
    }

    /// Constructs a `NbitsVec<N, Block>` directly from the raw components of another vector,
    /// like [standard Vec][std::vec::Vec] does.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't checked:
    ///
    /// * `ptr` needs to have been previously allocated via `Vec<T>/NbitsVec<N, Block>`.
    /// * `length` needs to be the length that less than or equal to `capacity`.
    /// * `capacity` needs to be the `capacity` as a `NbitsVec<N, Block>`, not the size that
    /// the pointer was allocated with.
    ///
    /// # Examples
    /// ```
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
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
    pub unsafe fn from_raw_parts(ptr: *mut Block, length: usize, capacity: usize) -> Self {
        Self::check_if_n_valid();
        NbitsVec {
            buf: RawVec::from_raw_parts(ptr, Self::raw_cap_from(capacity)),
            len: length,
            _marker: PhantomData,
        }
    }

    /// Returns the number of elements the vector can hold without reallocating.
    ///
    /// # Examples
    /// ```
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::{NbitsVec, N1};
    /// # fn main() {
    /// let v: NbitsVec<N1> = NbitsVec::with_capacity(10);
    /// assert!(v.capacity() >= 10);
    /// assert_eq!(v.capacity(), std::mem::size_of::<usize>() * 8);
    /// # }
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        Self::cap_from(self.buf.cap())
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
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
        let used_cap = Self::raw_cap_from(self.len());
        let need_extra_cap = Self::raw_cap_from(required_cap);
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
    /// # extern crate raw_nbits_vec;
    /// use raw_nbits_vec::*;
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
        let used_cap = Self::raw_cap_from(self.len());
        let need_extra_cap = Self::raw_cap_from(required_cap);
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// vec.shrink_to_fit();
    /// assert_eq!(vec.capacity(), 0);
    /// # }
    /// ```
    ///
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        let fit_len = Self::raw_cap_from(self.len());
        self.buf.shrink_to_fit(fit_len);
    }

    /// Shorten a vector to be `len` elements long, dropping excess elements.
    ///
    /// If `len` is greater than the vector's current length, this has no effect.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
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
    pub fn insert(&mut self, index: usize, element: Block) {
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let mut v: NbitsVec<N2> = NbitsVec::new();
    /// v.push(0b01);
    /// v.push(0b10);
    /// assert_eq!(v.remove(0), 0b01);
    /// # }
    /// ```
    #[inline]
    pub fn remove(&mut self, index: usize) -> Block {
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
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
    pub fn swap_remove(&mut self, index: usize) -> Block {
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// assert_eq!(vec.bits(), 0);
    /// # }
    /// ```
    #[inline]
    pub fn bits(&self) -> usize {
        self.len() * Self::nbits()
    }

    /// Total bits in buf.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// assert_eq!(vec.cap_bits(), std::mem::size_of::<usize>() * 8);
    /// # }
    /// ```
    #[inline]
    pub fn cap_bits(&self) -> usize {
        self.raw_cap() * Self::block_bits()
    }

    /// Returns whether or not the vector is empty.
    ///
    /// Alias to `len() == 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::new();
    /// vec.push(0b10);
    /// vec.push(0b01);
    /// assert_eq!(vec.len(), 2);
    /// # }
    /// ```
    #[inline]
    pub fn push(&mut self, value: Block) {
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
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
    pub fn pop(&mut self) -> Option<Block> {
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::new();
    /// vec.resize(10, 0);
    /// # assert_eq!(vec.capacity(), std::mem::size_of::<usize>() * 8 / 2);
    /// # }
    /// ```
    #[inline]
    pub fn resize(&mut self, new_len: usize, value: Block) {
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2, u8> = NbitsVec::new();
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
            self.fill(from, interval, Block::zero());
        }
    }

    /// Fill vector buf as `value` from `index` with size `length`.
    ///
    /// ## Examples
    ///
    /// ```
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2, u8> = NbitsVec::new();
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
    pub fn fill(&mut self, index: usize, length: usize, value: Block) {
        for i in index..cmp::min(index + length, self.len) {
            unsafe { self.unchecked_set(i, value) }
        }
    }

    /// ## Examples
    ///
    /// ```
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// unsafe { vec.set_len(2) }
    /// vec.set(0, 0b11);
    /// assert_eq!(vec.get(0), 0b11);
    /// # }
    /// ```
    #[inline]
    pub fn set(&mut self, index: usize, value: Block) {
        if index >= self.len {
            panic!("attempt to set at {} but only {}", index, self.len);
        }
        unsafe { self.unchecked_set(index, value) }
    }

    // `set` the `index`th value as `value` without length checked.
    #[inline]
    unsafe fn unchecked_set(&mut self, index: usize, value: Block) {
        let nbits = Self::nbits();
        let offset = index * nbits;
        if nbits == 1 {
            self.set_raw_bit(offset, value & Block::one() == Block::one());
            return;
        }
        let bi = Self::bit_index(offset);
        if Self::is_packed() {
            let ptr = self.buf.ptr().offset(bi as isize);
            ptr::write(ptr, value);
            return;
        }
        let bo = Self::bit_offset(offset);
        let bo2 = Self::bit_offset(offset + nbits);
        let block_bits = Self::block_bits();
        if Self::is_aligned() || bo < bo2 || bo2 == 0 {
            let mask = Self::mask();
            let ptr = self.buf.ptr().offset(bi as isize);
            let ori = ptr::read(ptr);
            let new = ori & !(mask << bo) | ((value & mask) << bo);
            if ori != new {
                ptr::write(ptr, new);
            }
        } else {
            let mask = Self::mask();
            let ptr = self.buf.ptr().offset(bi as isize);
            let ori = ptr::read(ptr);
            let new = Block::zero()
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
    /// ```
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
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
    pub unsafe fn set_raw_bits(&mut self, pos: usize, length: usize, value: Block) {
        let block_bits = Self::block_bits();
        let loc = Self::bit_loc(pos);
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
            let mask = Block::one() << loc.1;
            let old = (ori >> loc.1) & Block::one();
            let new = value & Block::one();
            if old != new {
                if new == Block::one() {
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
        let mask = !Block::zero() >> remain;
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
        let new = Block::zero().not().shr(block_bits - loc.1).bitand(ori).bitor(value.shl(loc.1));
        if ori != new {
            ptr::write(ptr, new);
        }
        let ptr = ptr.offset(1);
        let ori = ptr::read(ptr);
        let remain = block_bits - end_off;
        let mask = Block::zero().not().shr(remain);
        let new = value.shr(length - end_off).bitand(mask).bitor(mask.not().bitand(ori));
        if ori != new {
            ptr::write(ptr, new);
        }
    }

    /// Set buf unit bit at `index`th unit of `offset`bit.
    #[inline]
    pub unsafe fn set_raw_bit(&mut self, offset: usize, bit: bool) {
        let loc = Self::bit_loc(offset);
        let mask = Block::one() << loc.1;
        let ptr = self.buf.ptr().offset(loc.0 as isize);
        let cur = ptr::read(ptr);
        let old = cur >> loc.1 & Block::one();
        match (old == Block::one(), bit) {
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
    /// # fn main() {
    /// let mut vec: NbitsVec<N2> = NbitsVec::with_capacity(10);
    /// unsafe { vec.set_len(2) }
    /// vec.set(0, 0b11);
    /// assert_eq!(vec.get(0), 0b11);
    /// # }
    /// ```
    #[inline]
    pub fn get(&self, index: usize) -> Block {
        if index >= self.len {
            panic!("index out of bounds: attempt to get at {} but only {}",
                   index,
                   self.len);
        }
        let nbits = Self::nbits();
        let bit_pos = index * nbits;
        let bi = Self::bit_index(bit_pos);
        let bo = Self::bit_offset(bit_pos);
        unsafe {
            let ptr = self.raw_ptr().offset(bi as isize);
            if nbits == 1 {
                return ptr::read(ptr) >> bo & Block::one();
            }
            let bo2 = Self::bit_offset(bit_pos + nbits);
            let block_bits = Self::block_bits();
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
    /// # extern crate raw_nbits_vec;
    /// # use raw_nbits_vec::*;
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
    pub unsafe fn get_raw_bits(&self, pos: usize, length: usize) -> Block {
        debug_assert!(length > 0 && length <= Self::block_bits());
        let loc = Self::bit_loc(pos);
        // 1. Index out of bounds, but without panics or warnigns.
        if loc.0 >= self.raw_cap() {
            return Block::zero();
        }
        let ptr = self.raw_ptr().offset(loc.0 as isize);
        // 2. One bit only.
        if length == 1 {
            return ptr::read(ptr) >> loc.1 & Block::one();
        }
        let block_bits = Self::block_bits();
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
        self.get_raw_bits(pos, 1) == Block::one()
    }

    /// Returns mutable ptr of `Block`.
    #[inline]
    pub fn raw_mut_ptr(&mut self) -> *mut Block {
        self.buf.ptr()
    }

    /// Returns ptr of `Block`.
    #[inline]
    pub fn raw_ptr(&self) -> *const Block {
        self.buf.ptr()
    }

    /// Return raw slice of `Block`.
    #[inline]
    pub fn as_raw_slice(&self) -> &[Block] {
        unsafe {
            let p = self.buf.ptr();
            debug_assert!(!p.is_null());
            slice::from_raw_parts(p, self.used_raw_cap())
        }
    }

    /// Returns mutable raw slice of `Block`.
    #[inline]
    pub fn as_mut_raw_slice(&mut self) -> &mut [Block] {
        unsafe {
            let p = self.buf.ptr();
            debug_assert!(!p.is_null());
            slice::from_raw_parts_mut(p, self.used_raw_cap())
        }
    }

    /// Returns raw boxed slice of `Block`.
    #[inline]
    pub fn into_raw_boxed_slice(mut self) -> Box<[Block]> {
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
        let loc = Self::bit_loc(self.bits());
        if loc.1 == 0 {
            loc.0
        } else {
            loc.0 + 1
        }
    }

    /// The `RawVec` buffer capacity(Block).
    #[inline]
    fn raw_cap(&self) -> usize {
        self.buf.cap()
    }

    /// A `NbitsVec` is `aligned` when `block_bits` is divisible by `nbits`.
    #[inline]
    fn is_aligned() -> bool {
        Self::block_bits() % Self::nbits() == 0
    }

    /// A `NbitsVec` is `packed` when `block_bits` is equal to `nbits`.
    #[inline]
    fn is_packed() -> bool {
        Self::block_bits() == Self::nbits()
    }

    /// Converts capacity to storage size
    #[inline]
    fn raw_cap_from(cap: usize) -> usize {
        let loc = Self::loc(cap);
        if loc.1 == 0 {
            loc.0
        } else {
            loc.0 + 1
        }
    }

    /// Converts the storage size to capacity.
    #[inline]
    fn cap_from(raw_cap: usize) -> usize {
        raw_cap * Self::block_bits() / Self::nbits()
    }

    /// Converts the vector index to buf `(index, offset)` tuple.
    #[inline]
    fn loc(index: usize) -> Loc {
        let bits = index * Self::nbits();
        let rbits = Self::block_bits();
        (bits / rbits, bits % rbits)
    }

    /// Converts bit index to buf `BitLoc`.
    #[inline]
    fn bit_loc(bit: usize) -> BitLoc {
        let rbits = Self::block_bits();
        (bit / rbits, bit % rbits)
    }

    /// Returns block offset of bit position `bit`.
    #[inline]
    fn bit_offset(bit: usize) -> usize {
        bit % Self::block_bits()
    }

    /// Returns block index of bit position `bit`.
    #[inline]
    fn bit_index(bit: usize) -> usize {
        bit / Self::block_bits()
    }

    /// Returns size of `Block`.
    #[inline]
    fn block_bits() -> usize {
        mem::size_of::<Block>() * 8
    }

    /// Returns `N` in usize.
    #[inline]
    pub fn nbits() -> usize {
        N::to_usize()
    }

    /// Bit mask.
    #[inline]
    pub fn mask() -> Block {
        Block::zero().not().shr(Self::block_bits() - Self::nbits())
    }

    #[inline]
    fn check_if_n_valid() {
        if Self::nbits() > Self::block_bits() {
            panic!("`N` should be less than block's bits count, while your expect storing \
                    `{}`bits in a `{}`bits block vector",
                   Self::nbits(),
                   Self::block_bits());
        }
    }
}

type Loc = (usize, usize);
type BitLoc = Loc;

impl<N: Unsigned + NonZero, Block: PrimInt> Default for NbitsVec<N, Block> {
    fn default() -> Self {
        NbitsVec {
            buf: RawVec::new(),
            len: 0,
            _marker: PhantomData,
        }
    }
}

impl<N: Unsigned + NonZero, Block: PrimInt + fmt::LowerHex> Debug for NbitsVec<N, Block> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f,
                    "NbitsVec<{}> {{ len: {}, buf: RawVec {{ cap: {}, [",
                    N::to_usize(),
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

impl<N: Unsigned + NonZero, Block: PrimInt + Hash> Hash for NbitsVec<N, Block> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        Hash::hash(self.as_raw_slice(), state);
    }
}

impl<N: Unsigned + NonZero, Block: PrimInt> PartialEq for NbitsVec<N, Block> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.as_raw_slice() == other.as_raw_slice()
    }
    #[inline]
    fn ne(&self, other: &Self) -> bool {
        self.len() != other.len() || self.as_raw_slice() == other.as_raw_slice()
    }
}

impl<N: Unsigned + NonZero, Block: PrimInt> Eq for NbitsVec<N, Block> {}

impl<N: Unsigned + NonZero, Block: PrimInt> Clone for NbitsVec<N, Block> {
    fn clone(&self) -> Self {
        let mut new = Self::with_capacity(self.len());
        unsafe {
            ptr::copy_nonoverlapping(self.buf.ptr(), new.buf.ptr(), self.used_raw_cap());
            new.set_len(self.len());
        }
        new
    }
}

impl<N: Unsigned + NonZero, Block: PrimInt> PartialOrd for NbitsVec<N, Block> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_raw_slice(), other.as_raw_slice())
    }
}

impl<N: Unsigned + NonZero, Block: PrimInt> Ord for NbitsVec<N, Block> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Ord::cmp(self.as_raw_slice(), other.as_raw_slice())
    }
}

unsafe impl<N: Unsigned + NonZero, Block: PrimInt> Send for NbitsVec<N, Block> {}

unsafe impl<N: Unsigned + NonZero, Block: PrimInt> Sync for NbitsVec<N, Block> {}

#[cfg_attr(rustfmt, rustfmt_skip)]
pub use typenum::consts::{
    U1 as N1,
    U2 as N2,
    U3 as N3,
    U4 as N4,
    U5 as N5,
    U6 as N6,
    U7 as N7,
    U8 as N8,
    U9 as N9,
    U10 as N10,
    U11 as N11,
    U12 as N12,
    U13 as N13,
    U14 as N14,
    U15 as N15,
    U16 as N16,
    U17 as N17,
    U18 as N18,
    U19 as N19,
    U20 as N20,
    U21 as N21,
    U22 as N22,
    U23 as N23,
    U24 as N24,
    U25 as N25,
    U26 as N26,
    U27 as N27,
    U28 as N28,
    U29 as N29,
    U30 as N30,
    U31 as N31,
    U32 as N32,
    U33 as N33,
    U34 as N34,
    U35 as N35,
    U36 as N36,
    U37 as N37,
    U38 as N38,
    U39 as N39,
    U40 as N40,
    U41 as N41,
    U42 as N42,
    U43 as N43,
    U44 as N44,
    U45 as N45,
    U46 as N46,
    U47 as N47,
    U48 as N48,
    U49 as N49,
    U50 as N50,
    U51 as N51,
    U52 as N52,
    U53 as N53,
    U54 as N54,
    U55 as N55,
    U56 as N56,
    U57 as N57,
    U58 as N58,
    U59 as N59,
    U60 as N60,
    U61 as N61,
    U62 as N62,
    U63 as N63,
};

#[cfg(test)]
mod tests;
