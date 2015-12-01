use raw::Nbits;

#[macro_export]
macro_rules! nbits_set {
    ($(($t: ident, $size: expr)),*) => (
        $(
            /// Struct for each NBits
            pub struct $t;
            impl Nbits for $t {
                #[inline]
                fn bits() -> usize {
                    $size
                }
            }
        )*
    )
}

nbits_set! {
    (As1bits, 1),
    (As2bits, 2),
    (As3bits, 3),
    (As4bits, 4)
}
