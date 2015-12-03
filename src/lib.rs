#![feature(custom_derive)]
#![feature(concat_idents)]
#![feature(alloc)]
#![feature(step_by)]
#![feature(test)]

extern crate alloc;
extern crate num;

#[cfg(test)]
extern crate test;
mod raw;
mod types;
pub use raw::*;
pub use types::*;

#[cfg(test)]
mod tests {
    macro_rules! bench_test {
        ($(($m: ident, $nbits: ident, $storage: ident)),*) => {
            mod get {
                $(
                    mod $m {
                        use super::super::super::*;
                        use test::{self, Bencher};
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            let n = test::black_box(1000);
                            let mut vec: NbitsVec<$nbits, $storage> = NbitsVec::with_capacity(n);
                            unsafe { vec.set_len(n) }
                            b.iter(|| {
                                (0..n).fold(0, |_a, i| vec.get(i));
                            })
                        }
                    }
                )*
            }
            mod resize {
                $(
                    mod $m {
                        use super::super::super::*;
                        use test::{self, Bencher};
                        use num::Zero;
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            b.iter(|| {
                                let n = test::black_box(1000);
                                let mut vec: NbitsVec<$nbits, $storage> = NbitsVec::new();
                                for i in (0..n).step_by(10) {
                                    vec.resize(i, $storage::zero());
                                }
                            })
                        }
                    }
                )*
            }
            /*
            mod set {
                $(
                    mod $m {
                        use super::super::super::*;
                        use test::{self, Bencher};
                        #[bench]
                        fn set(b: &mut Bencher) {
                            b.iter(|| {
                                let n = test::black_box(100);
                                let mut vec: NbitsVec<As1bits> = NbitsVec::with_capacity(n);
                                unsafe { vec.set_len(n) };
                                for i in 0..n {
                                    vec.set(i, i as u64);
                                }
                            });
                        }
                    }
                )*
            }
            */
            /*
            mod fill {
                $(
                    mod $m {
                        use super::super::super::*;
                        use test::{self, Bencher};
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            b.iter(|| {
                                let n = test::black_box(100);
                                let mut vec: NbitsVec<As1bits> = NbitsVec::with_capacity(n);
                                unsafe { vec.set_len(n) };
                                vec.fill_bits(0, n, false);
                            });
                        }
                    }
                )*
            }
            mod set_bit_by_bit {
                $(
                    mod $m {
                        use super::super::super::*;
                        use test::{self, Bencher};
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            b.iter(|| {
                                let n = test::black_box(100);
                                let mut vec: NbitsVec<As1bits> = NbitsVec::with_capacity(n);
                                unsafe { vec.set_len(n) };
                                for i in 0..n {
                                    vec.set_bit_by_bit(i, i as u64);
                                }
                            });
                        }
                    }
                )*
            }
            */
        }
    }
    bench_test! {
        (test_4bits_usize, As4bits, usize),
        (test_4bits_u64, As4bits, u64),
        (test_4bits_u32, As4bits, u32),
        (test_4bits_u16, As4bits, u16),
        (test_4bits_u8, As4bits, u8),
        (test_3bits_usize, As3bits, usize),
        (test_3bits_u64, As3bits, u64),
        (test_3bits_u32, As3bits, u32),
        (test_3bits_u16, As3bits, u16),
        (test_3bits_u8, As3bits, u8),
        (test_2bits_usize, As2bits, usize),
        (test_2bits_u64, As2bits, u64),
        (test_2bits_u32, As2bits, u32),
        (test_2bits_u16, As2bits, u16),
        (test_2bits_u8, As2bits, u8),
        (test_1bits_usize, As1bits, usize),
        (test_1bits_u64, As1bits, u64),
        (test_1bits_u32, As1bits, u32),
        (test_1bits_u16, As1bits, u16),
        (test_1bits_u8, As1bits, u8)
    }
}
