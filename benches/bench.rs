#![feature(test)]
//#![feature(step_by)]
extern crate nbits_vec;
extern crate test;

mod tests {
    macro_rules! bench_test {
        ($(($m: ident, $nbits: ident)),*) => {
            mod get {
                $(
                    mod $m {
                        use nbits_vec::*;
                        use nbits_vec::consts::$nbits;
                        use test::{self, Bencher};
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            let n = test::black_box(1000);
                            let mut vec: NbitsVec<$nbits> = NbitsVec::with_capacity(n);
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
                        use nbits_vec::*;
                        use nbits_vec::consts::$nbits;
                        use test::{self, Bencher};
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            let n = test::black_box(1000);
                            let mut vec: NbitsVec<$nbits> = NbitsVec::new();
                            b.iter(|| {
                                for i in (0..n).step_by(10) {
                                    vec.resize(i, 0);
                                }
                            })
                        }
                    }
                )*
            }
            mod set {
                $(
                    mod $m {
                        use nbits_vec::*;
                        use nbits_vec::consts::$nbits;
                        use test::{self, Bencher};
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            b.iter(|| {
                                let n = test::black_box(1000);
                                let mut vec: NbitsVec<$nbits> = NbitsVec::with_capacity(n);
                                unsafe { vec.set_len(n) };
                                for i in 0..n {
                                    vec.set(i, 0b1010);
                                }
                            });
                        }
                    }
                )*
            }
            mod new {
                $(
                    mod $m {
                        use nbits_vec::*;
                        use nbits_vec::consts::$nbits;
                        use test::{self, Bencher};
                        #[bench]
                        fn bench(b: &mut Bencher) {
                            b.iter(|| {
                                let n = test::black_box(1000);
                                let vec: NbitsVec<$nbits> = NbitsVec::with_capacity(n);
                                vec
                            });
                        }
                    }
                 )*
            }
            mod push {
                $(
                    mod $m {
                        use nbits_vec::*;
                        use nbits_vec::consts::$nbits;
                        use test::{self, Bencher};
                        #[bench]
                        fn push(b: &mut Bencher) {
                            let n = test::black_box(1000);
                            let mut vec: NbitsVec<$nbits> = NbitsVec::with_capacity(n);
                            b.iter(|| {
                                for _i in 0..n {
                                    vec.push(1);
                                }
                            });
                        }
                    }
                 )*
            }
            mod align {
                $(
                    mod $m {
                        use nbits_vec::*;
                        use nbits_vec::consts::$nbits;
                        use test::{self,Bencher};

                        #[bench]
                        fn align(b: &mut Bencher) {
                            let n = test::black_box(7);
                            let mut vec: NbitsVec<$nbits> = NbitsVec::new();
                            b.iter(|| {
                                for i in (0..).map(|x| x * x).take(n) {
                                    vec.align(i, i * 2);
                                }
                                for i in (1..n).map(|x| x * x).rev() {
                                    vec.align(i * 2, i);
                                }
                            })
                        }
                    }
                 )*
            }
        }
    }
    bench_test! {
        (test_4bits_u64, N4B64),
        (test_4bits_u32, N4B32),
        (test_4bits_u16, N4B16),
        (test_4bits_u8, N4B8),
        (test_3bits_u64, N3B64),
        (test_3bits_u32, N3B32),
        (test_3bits_u16, N3B16),
        (test_3bits_u8, N3B8),
        (test_2bits_u64, N2B64),
        (test_2bits_u32, N2B32),
        (test_2bits_u16, N2B16),
        (test_2bits_u8, N2B8),
        (test_1bits_u64, N1B64),
        (test_1bits_u32, N1B32),
        (test_1bits_u16, N1B16),
        (test_1bits_u8, N1B8)
    }
}
