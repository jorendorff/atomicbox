# AtomicBox - Safe atomic boxes for Rust.

The Rust standard library provides atomic booleans, integers, and pointers.
`AtomicPtr` is safe for loading, storing, and so forth; but pointers are
unsafe to use.

It turns out that a safe atomic `Box` type is possible. Unfortunately, the
only operation it supports is `swap`. Still, this is sufficient for some
lock-free data structures, so here it is!
