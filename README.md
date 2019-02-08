# AtomicBox - Safe atomic boxes for Rust.

The Rust standard library provides atomic booleans, integers, and pointers.
`AtomicPtr` is safe for loading, storing, and so forth; but pointers are
unsafe to use.

It turns out that a safe atomic `Box` type is possible. Unfortunately, the
only operation it supports is `swap`. Still, this is sufficient for some
lock-free data structures, so here it is!


## License

AtomicBox is distributed under the terms of both the MIT license and the
Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT), and
[COPYRIGHT](COPYRIGHT) for details.
