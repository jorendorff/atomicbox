//! Safe atomic boxes.
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
//! The reason it's safe for a normal `Box` to implement `Deref` is apparent
//! from the `deref` method's signature:
//!
//! ```ignore
//! fn deref(&self) -> &Self::Target;
//! ```
//!
//! Dereferencing a box returns a reference, call it `r`, whose lifetime is
//! enclosed by the lifetime of `&self`, the borrow of the box itself. Since the
//! box is borrowed by a shared reference, nobody can change the box's value
//! while it exists. This ensures that `r` remains valid throughout its
//! lifetime.
//!
//! But the point of an atomic type is that it permits mutation even while
//! borrowed by a shared reference. So the fact that you've got a shared
//! reference to an atomic box doesn't mean nobody will store some new pointer
//! in it and free the old one you're borrowing.
//!
//! This is the same reason you can't borrow a reference to the contents of any
//! other atomic type. The only difference here is that those contents happen to
//! be on the heap.

mod atomic_box;
mod atomic_box_base;
mod atomic_option_box;

pub use atomic_box::AtomicBox;
pub use atomic_option_box::AtomicOptionBox;
