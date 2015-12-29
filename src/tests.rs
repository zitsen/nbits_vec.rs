macro_rules! generate_test {
    ( $(($m: ident $nbits: ident => $($block: ident)*)) * ) => {
        $(
            mod $m {
                $(
                    mod $block {
                        mod struct_static {
                            use ::{NbitsVec, $nbits};
                            use ::std::mem::size_of;
                            type NV = NbitsVec<$nbits, $block>;
                            #[test]
                            fn unit_bits() {
                                assert!(NV::unit_bits() > 0);
                            }
                            #[test]
                            fn buf_unit_bits() {
                                assert_eq!(NV::buf_unit_bits(), size_of::<$block>() * 8);
                            }
                            #[test]
                            fn bit_index_to_buf() {
                                assert_eq!(NV::bit_index_to_buf(0), (0, 0));
                                assert_eq!(NV::bit_index_to_buf(1), (0, 1));
                                let buf_unit_bits = NV::buf_unit_bits();
                                for i in 3..79 {
                                    assert_eq!(NV::bit_index_to_buf(i),
                                                (i / buf_unit_bits, i % buf_unit_bits));
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
