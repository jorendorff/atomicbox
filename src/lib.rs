//! **Safe atomic boxes.**
//!
//! [![Documentation](https://docs.rs/atomicbox/badge.svg)](https://docs.rs/atomicbox)
//! [![](https://img.shields.io/crates/v/atomicbox.svg)](https://crates.io/crates/atomicbox)
//! [![](https://img.shields.io/crates/d/atomicbox.svg)](https://crates.io/crates/atomicbox)
//! [![Build Status](https://github.com/jorendorff/atomicbox/actions/workflows/ci.yml/badge.svg)](https://github.com/jorendorff/atomicbox/actions?query=workflow%3Aci)
//!
//! This crate provides `AtomicBox<T>` and `AtomicOptionBox<T>` types: safe, owning
//! versions of the standard library's `AtomicPtr`.
//!
//! Unfortunately, the only operations you can perform on an atomic box are
//! swaps and stores: you can't just use the box without taking ownership of it.
//! Imagine a `Box` without `Deref` or `DerefMut` implementations, and you'll
//! get the idea. Still, this is sufficient for some lock-free data structures,
//! so here it is!
//!
//! ## Why no `Deref`?
//!
//! It wouldn't be safe. The point of an `AtomicBox` is that other threads can
//! obtain the boxed value, take ownership of it, even drop it, all without
//! taking a lock. So there is no safe way to borrow that value—except to swap
//! it out of the `AtomicBox` yourself.
//!
//! This is pretty much the same reason you can't borrow a reference to the
//! contents of any other atomic type. It would invite data races. The only
//! difference here is that those contents happen to be on the heap.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

mod atomic_box;
mod atomic_option_box;

pub use atomic_box::AtomicBox;
pub use atomic_option_box::AtomicOptionBox;
