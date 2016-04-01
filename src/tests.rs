macro_rules! generate_test {
    ( $(($m: ident, $($nbits: ident => $block: ident),*)) * ) => {
        $(
            mod $m {
                $(
                    mod $block {
                        use ::NbitsVec;
                        pub use ::value::*;
                        pub use ::consts::$nbits;
                        pub type NV = NbitsVec<$nbits>;

                        pub fn mask(n: usize) -> $block {
                            (0..n).fold(0, |b, _x| b << 1 | 1)
                        }

                        mod struct_static {
                            use ::std::mem::size_of;
                            use super::*;

                            #[test]
                            fn nbits() {
                                assert!($nbits::nbits() > 0);
                            }

                            #[test]
                            fn block_bits() {
                                assert_eq!($nbits::block_bits(), size_of::<$block>() * 8);
                            }

                            #[test]
                            fn bit_loc() {
                                assert_eq!($nbits::bit_loc(0), (0, 0));
                                assert_eq!($nbits::bit_loc(1), (0, 1));
                                let block_bits = $nbits::block_bits();
                                for i in 3..79 {
                                    assert_eq!($nbits::bit_loc(i),
                                                (i / block_bits, i % block_bits));
                                }
                            }

                            #[test]
                            fn mask_ok() {
                                assert_eq!($nbits::mask(), mask($nbits::nbits()));
                            }

                        }
                        mod private_api {
                            use super::*;

                            #[test]
                            fn raw_bit() {
                                let mut vec = NV::with_capacity(100);
                                unsafe {
                                    for i in 0..(100 * $nbits::nbits()) {
                                        vec.set_raw_bit(i, true);
                                        assert_eq!(vec.get_raw_bit(i), true);
                                        vec.set_raw_bit(i, false);
                                        assert_eq!(vec.get_raw_bit(i), false);
                                    }
                                }
                            }

                            #[test]
                            fn raw_bits() {
                                let mut vec = NV::with_capacity(100);
                                unsafe {
                                    for n in 2..8 {
                                        for i in 0..(100 * $nbits::nbits() - n) {
                                            vec.set_raw_bits(i, n, 0b1001);
                                            println!("N = {}, i = {}", n, i);
                                            vec.get_raw_bits(i, n);
                                            assert_eq!(vec.get_raw_bits(i, n), 0b1001 & mask(n));
                                        }
                                        for i in 0..n {
                                            let j = 100 * $nbits::nbits() - i;
                                            vec.get_raw_bits(j, n);
                                        }
                                    }
                                }
                            }

                            #[test]
                            fn get_raw_bits() {
                                let vec = NV::with_capacity(100);
                                unsafe {
                                    vec.get_raw_bits(1, 1);
                                    vec.get_raw_bits(2, 2);
                                    vec.get_raw_bits(3, 3);
                                }
                            }

                            #[cfg(build = "debug")]
                            #[test]
                            #[should_panic]
                            fn failed_get_raw_bits() {
                                let vec = NV::with_capacity(100);
                                unsafe {
                                    vec.get_raw_bits(0, 100);
                                }
                            }
                        }
                        mod public_api {
                            use super::*;

                            #[test]
                            fn new() {
                                let vec = NV::new();
                                assert_eq!(vec.capacity(), 0);
                                assert_eq!(vec.len(), 0);
                                assert_eq!(vec.used_raw_cap(), 0);
                                assert_eq!(vec.raw_cap(), 0);
                            }
                            #[test]
                            fn push_pop() {
                                let mut vec = NV::new();
                                vec.push(1);
                                assert!(vec.capacity() >= 1);
                                assert_eq!(vec.len(), 1);
                                assert_eq!(vec.used_raw_cap(), 1);
                                assert_eq!(vec.raw_cap(), 1);
                                println!("{:?}", vec);
                                assert_eq!(vec.pop(), Some(1));
                                println!("Push...");
                                for _i in 0..100 {
                                    vec.push(1);
                                }
                                for _i in 0..100 {
                                    println!("{}", _i);
                                    assert_eq!(vec.pop(), Some(1));
                                }
                            }
                            #[test]
                            fn resize() {
                                let mut vec = NV::new();
                                println!("resize 100 `1`");
                                vec.resize(100, 1);
                                assert_eq!(vec.len(), 100);
                                assert!(vec.capacity() >= 100);
                                let bigger_cap = vec.capacity();
                                println!("resize to 10 `0`");
                                vec.resize(10, 0);
                                assert_eq!(vec.len(), 10);
                                assert!(vec.capacity() < bigger_cap);
                            }
                            #[test]
                            fn resize_large() {
                                let mut vec = NV::new();
                                const LEN: usize = 10000;
                                vec.resize(LEN, 1);
                                vec.resize(LEN * 2, 2);
                                vec.resize(LEN * 3, 3);
                            }
                            #[test]
                            fn get_set() {
                                let mut vec = NV::new();
                                vec.resize(100, 0b1111);
                                for i in 0..100 {
                                    vec.set(i, 0);
                                }
                                for i in 0..100 {
                                    let v = vec.get(i);
                                    assert_eq!(v, 0);
                                }
                            }
                            #[test]
                            fn fill() {
                                let mut vec = NV::new();
                                vec.resize(1000, 0b11111);
                                for i in 0..500 {
                                    vec.fill(i, i, 0b111001 >> (i / 100));
                                    for j in (i..).take(i) {
                                        assert_eq!(vec.get(j),
                                        0b111001 >> (i / 100) & $nbits::mask());
                                    }
                                }
                            }
                            #[test]
                            fn align() {
                                let mut vec = NV::new();
                                let n = 7;
                                for i in (0..).map(|x| x * x).take(n) {
                                    let l = vec.len();
                                    vec.align(i, i * 2);
                                    assert_eq!(vec.len(), l + i);
                                }
                                for i in (0..n).map(|x| x * x).rev() {
                                    let l = vec.len();
                                    vec.align(i * 2, i);
                                    assert_eq!(vec.len(), l - i);
                                }
                            }
                        }

                        mod threadsafe {
                            use super::*;

                            #[test]
                            fn new() {
                                use std::thread;
                                use std::sync::mpsc::channel;
                                let (tx, rx) = channel();
                                for _ in 0..10 {
                                    let tx = tx.clone();
                                    thread::spawn(move || {
                                        tx.send(NV::new()).unwrap();
                                    });
                                }
                                for _ in 0..10 {
                                    let _ = rx.recv().unwrap();
                                }
                            }
                            #[test]
                            fn with_capacity() {
                                use std::thread;
                                use std::sync::mpsc::channel;
                                let (tx, rx) = channel();
                                for i in 0..10 {
                                    let tx = tx.clone();
                                    thread::spawn(move || {
                                        tx.send(NV::with_capacity(i)).unwrap();
                                    });
                                }
                                for i in 0..10 {
                                    let j = rx.recv().unwrap();
                                    println!("{} capacity: {}", i, j.capacity());
                                }
                            }
                        }
                    }
                 )*
            }
         )*
    }
}

generate_test! {
    (n1, N1B8 => u8, N1B16 => u16, N1B32 => u32, N1B64 => u64)
    (n2, N2B8 => u8, N2B16 => u16, N2B32 => u32, N2B64 => u64)
    (n3, N3B8 => u8, N3B16 => u16, N3B32 => u32, N3B64 => u64)
    (n4, N4B8 => u8, N4B16 => u16, N4B32 => u32, N4B64 => u64)
    (n5, N5B8 => u8, N5B16 => u16, N5B32 => u32, N5B64 => u64)
    (n6, N6B8 => u8, N6B16 => u16, N6B32 => u32, N6B64 => u64)
    (n7, N7B8 => u8, N7B16 => u16, N7B32 => u32, N7B64 => u64)
}
