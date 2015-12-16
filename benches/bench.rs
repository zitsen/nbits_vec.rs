#![feature(test)]
#![feature(step_by)]
extern crate raw_nbits_vec;
extern crate test;
extern crate num;

mod tests {
    macro_rules! bench_test {
        ($(($m: ident, $nbits: ident, $storage: ident)),*) => {
            mod get {
                $(
                    mod $m {
                        use raw_nbits_vec::*;
                        use test::{self, Bencher};
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            let n = test::black_box(100);
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
                        use raw_nbits_vec::*;
                        use test::{self, Bencher};
                        use num::Zero;
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            let n = test::black_box(100);
                            let mut vec: NbitsVec<$nbits, $storage> = NbitsVec::new();
                            b.iter(|| {
                                for i in (0..n).step_by(10) {
                                    vec.resize(i, $storage::zero());
                                }
                            })
                        }
                    }
                )*
            }
            mod set {
                $(
                    mod $m {
                        use raw_nbits_vec::*;
                        use test::{self, Bencher};
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            b.iter(|| {
                                let n = test::black_box(100);
                                let mut vec: NbitsVec<$nbits, $storage> = NbitsVec::with_capacity(n);
                                unsafe { vec.set_len(n) };
                                for i in 0..n {
                                    vec.set(i, ::num::cast(i).unwrap());
                                }
                            });
                        }
                    }
                )*
            }
            mod new {
                $(
                    mod $m {
                        use raw_nbits_vec::*;
                        use test::{self, Bencher};
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            b.iter(|| {
                                let n = test::black_box(100);
                                let vec: NbitsVec<$nbits, $storage> = NbitsVec::with_capacity(n);
                                vec
                            });
                        }
                    }
                 )*
            }
            mod push {
                $(
                    mod $m {
                        use raw_nbits_vec::*;
                        use test::{self, Bencher};
                        #[bench]
                        fn push(b: &mut Bencher) {
                            let n = test::black_box(100);
                            let mut vec: NbitsVec<$nbits, $storage> = NbitsVec::with_capacity(n);
                            b.iter(|| {
                                for i in 0..n {
                                    vec.push(::num::cast(i).unwrap())
                                }
                            });
                        }
                    }
                 )*
            }
        }
    }
    bench_test! {
        (test_4bits_usize, N4, usize),
        (test_4bits_u64, N4, u64),
        (test_4bits_u32, N4, u32),
        (test_4bits_u16, N4, u16),
        (test_4bits_u8, N4, u8),
        (test_3bits_usize, N3, usize),
        (test_3bits_u64, N3, u64),
        (test_3bits_u32, N3, u32),
        (test_3bits_u16, N3, u16),
        (test_3bits_u8, N3, u8),
        (test_2bits_usize, N2, usize),
        (test_2bits_u64, N2, u64),
        (test_2bits_u32, N2, u32),
        (test_2bits_u16, N2, u16),
        (test_2bits_u8, N2, u8),
        (test_1bits_usize, N1, usize),
        (test_1bits_u64, N1, u64),
        (test_1bits_u32, N1, u32),
        (test_1bits_u16, N1, u16),
        (test_1bits_u8, N1, u8)
    }
}
