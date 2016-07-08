use std::mem;
use std::hash::Hash;
use std::fmt::LowerHex;

use num_traits::{PrimInt, One, Zero};

pub trait Value {
    /// The storage type of `Value`s.
    ///
    /// The `Block` should be one of the primitive integer ie. `u8`, `u16`  `u32`, `u64`.
    /// Recommend that not to use `usize` because it is platform dependent.
    type Block: PrimInt + One + Zero + LowerHex + Hash;

    /// The value bit width.
    #[inline(always)]
    fn nbits() -> usize;

    /// Return 1
    #[inline(always)]
    fn one() -> Self::Block {
        Self::Block::one()
    }

    /// Return 0
    #[inline(always)]
    fn zero() -> Self::Block {
        Self::Block::zero()
    }

    /// The value's bit mask in the `Block`.
    ///
    /// For example, 2-bit value mask is 0b11, 3-bit mask is 0b111.
    #[inline(always)]
    fn mask() -> Self::Block {
        (!Self::zero()) >>
        ((Self::block_bits() - Self::nbits() % Self::block_bits()) % Self::block_bits())
    }

    /// Bit-size of `Block`.
    #[inline]
    fn block_bits() -> usize {
        mem::size_of::<Self::Block>() * 8
    }

    /// Value is `aligned` when `block_bits` is divisible by `nbits`.
    #[inline]
    fn is_aligned() -> bool {
        Self::block_bits() % Self::nbits() == 0
    }

    /// Value is `packed` when `block_bits` is equal to `nbits`.
    #[inline]
    fn is_packed() -> bool {
        Self::block_bits() == Self::nbits()
    }
}

pub trait ValueExt : Value {
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
    fn loc(index: usize) -> (usize, usize) {
        let bits = index * Self::nbits();
        let rbits = Self::block_bits();
        (bits / rbits, bits % rbits)
    }

    /// Converts bit index to buf `BitLoc`.
    #[inline]
    fn bit_loc(bit: usize) -> (usize, usize) {
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
}

pub trait OneBit: ValueExt {
}

pub trait Packed: ValueExt {
}

pub trait Aligned : ValueExt {
}
