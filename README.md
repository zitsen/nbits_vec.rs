# nbits_vec

[![travis-badge][]][travis] [![release-badge][]][cargo] [![downloads]][cargo]
[![docs-badge][]][docs] [![license-badge][]][license]

A crate aims to resolve small bits values storage and operations problem.

Small bits values will be stored in a vector of `Block` - which is a `PrimInt` in
memory. Here, we only consider the case that one `Block` will store some of the
small bits values, such as 1, 2, 3, 4, 5 bits stored in `u8`, `u16`, `u32`, `u64`.

**WARN**: In this crate, I([@zitsen](http://github.com/zitsen)) decided to use
`RawVec` from unstable `alloc` crate as vector background,
which means the API would only be avaliable in `nightly` version of Rust and that
the API might be changed in some time the `alloc` API changed.
So a `stable` version may never give out.

See usage in [struct documentation](struct.NbitsVec.html).

[travis-badge]: https://img.shields.io/travis/zitsen/nbits_vec.rs.svg?style=flat-square
[travis]: https://travis-ci.org/zitsen/nbits_vec.rs
[release-badge]: https://img.shields.io/crates/v/nbits_vec.svg?style=flat-square
[downloads]: https://img.shields.io/crates/d/nbits_vec.svg?style=flat-square
[cargo]: https://crates.io/crates/nbits_vec
[docs-badge]: https://img.shields.io/badge/API-docs-blue.svg?style=flat-square
[docs]: https://zitsen.github.io/nbits_vec.rs
[license-badge]: https://img.shields.io/crates/l/nbits_vec.svg?style=flat-square
[license]: https://github.com/zitsen/nbits_vec.rs/blob/master/LICENSE
