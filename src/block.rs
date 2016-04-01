use std::ops::{BitAnd, BitOr, Shl, Shr};
use std::num::{One, Zero};
pub trait Block: BitAnd + BitOr + One + Zero {
    type Nbits: BitAnd;
}
pub enum N1 {}
impl Block for u8 {
    type Nbits = N1;
}

fn main() {}
