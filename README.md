# nbits_vec

A crate aims to resolve small bits values storage and operations problem.

[![Build Status](https://travis-ci.org/zitsen/nbits_vec.rs.svg?branch=master)]
(https://travis-ci.org/zitsen/nbits_vec.rs)

[Documentation](http://zitsen.github.io/nbits_vec.rs)

Small bits values will be stored in a vector of `Block` - which is a `PrimInt` in
memory. Here, we only consider the case that one `Block` will store some of the
small bits values, such as 1, 2, 3, 4, 5 bits stored in `u8`, `u16`, `u32`, `u64`.

**WARN**: In this crate, I([@zitsen](http://github.com/zitsen)) decided to use
`RawVec` from unstable `alloc` crate as vector background,
which means the API would only be avaliable in `nightly` version of Rust and that
the API might be changed in some time the `alloc` API changed.
So a `stable` version may never give out.

