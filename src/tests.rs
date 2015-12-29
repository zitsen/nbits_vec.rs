macro_rules! generate_test {
    ( $(($m: ident $nbits: ident => $($block: ident)*)) * ) => {
        $(
            mod $m {
                $(
                    mod $block {
                        mod struct_static {
                            use ::{NbitsVec, $nbits, Loc};
                            use ::std::mem::size_of;
                            type NV = NbitsVec<$nbits, $block>;
                            #[test]
                            fn nbits() {
                                assert!(NV::nbits() > 0);
                            }
                            #[test]
                            fn block_bits() {
                                assert_eq!(NV::block_bits(), size_of::<$block>() * 8);
                            }
                            #[test]
                            fn bit_loc() {
                                assert_eq!(NV::bit_loc(0), Loc::new(0, 0));
                                assert_eq!(NV::bit_loc(1), Loc::new(0, 1));
                                let block_bits = NV::block_bits();
                                for i in 3..79 {
                                    assert_eq!(NV::bit_loc(i),
                                                Loc::new(i / block_bits, i % block_bits));
                                }
                            }
                        }
                        mod public_api {
                            use ::{NbitsVec, $nbits};
                            type NV = NbitsVec<$nbits, $block>;
                            #[test]
                            fn new() {
                                let vec = NV::new();
                                assert_eq!(vec.capacity(), 0);
                                assert_eq!(vec.len(), 0);
                                assert_eq!(vec.used_buf_cap(), 0);
                                assert_eq!(vec.buf_cap(), 0);
                            }
                            #[test]
                            fn push_pop() {
                                let mut vec = NV::new();
                                vec.push(1);
                                assert!(vec.capacity() > 1);
                                assert_eq!(vec.len(), 1);
                                assert_eq!(vec.used_buf_cap(), 1);
                                assert_eq!(vec.buf_cap(), 1);
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
                                vec.resize(100, 1);
                                assert_eq!(vec.len(), 100);
                                assert!(vec.capacity() >= 100);
                                let bigger_cap = vec.capacity();
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
                        }

                        mod threadsafe {
                            use ::{NbitsVec, $nbits};
                            type NV = NbitsVec<$nbits, $block>;

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
    (n1 N1 => u8 u16 u32 u64 usize)
    (n2 N2 => u8 u16 u32 u64 usize)
    (n3 N3 => u8 u16 u32 u64 usize)
    (n4 N4 => u8 u16 u32 u64 usize)
}

macro_rules! panic_test {
    ( $(($m: ident $nbits: ident => $($block: ident)*)) * ) => {
        $(
            mod $m {
                $(
                    mod $block {
                        use ::{NbitsVec, $nbits};
                        type NV = NbitsVec<$nbits, $block>;
                        #[test]
                        #[should_panic]
                        fn panic_new() {
                            NV::new();
                        }
                        #[test]
                        #[should_panic]
                        fn panic_with_capacity() {
                            NV::with_capacity(10);
                        }
                        #[test]
                        #[should_panic]
                        fn panic_from_raw_parts() {
                            unsafe {
                                NV::from_raw_parts(::std::ptr::null_mut(), 0, 0);
                            }
                        }
                    }
                 )*
            }
         )*
    }
}

panic_test! {
    (n9 N9 => u8)
    (n17 N17 => u8 u16)
    (n33 N33 => u8 u16 u32)
}
