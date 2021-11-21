use atomic_box_base::{AtomicBoxBase, PointerConvertible};
use std::fmt::{self, Debug, Formatter};
use std::ptr::null_mut;
use std::sync::atomic::Ordering;

// TODO: move into impl block once https://github.com/rust-lang/rust/issues/8995
// is solved.
type OptionBox<T> = Option<Box<T>>;

impl<T> PointerConvertible for OptionBox<T> {
    type Target = T;

    fn into_raw(b: Self) -> *mut T {
        match b {
            Some(box_value) => Box::into_raw(box_value),
            None => null_mut(),
        }
    }

    unsafe fn from_raw(ptr: *mut T) -> Self {
        if ptr.is_null() {
            None
        } else {
            Some(Box::from_raw(ptr))
        }
    }
}

/// A type that holds a single `OptionBox<T>` value and can be safely shared
/// between threads.
pub struct AtomicOptionBox<T> {
    base: AtomicBoxBase<OptionBox<T>>,
}

impl<T> AtomicOptionBox<T> {
    /// Creates a new `AtomicOptionBox` with the given value.
    ///
    /// # Examples
    ///
    ///     use atomicbox::AtomicOptionBox;
    ///
    ///     let atomic_box = AtomicOptionBox::new(Some(Box::new(0)));
    ///
    pub fn new(value: OptionBox<T>) -> AtomicOptionBox<T> {
        AtomicOptionBox {
            base: AtomicBoxBase::new(value),
        }
    }

    /// Atomically set this `AtomicOptionBox` to `other` and return the
    /// previous value.
    ///
    /// This does not allocate or free memory, and it neither clones nor drops
    /// any values.  `other` is moved into `self`; the value previously in
    /// `self` is returned.
    ///
    /// `ordering` must be either `Ordering::AcqRel` or `Ordering::SeqCst`,
    /// as other values would not be safe if `T` contains any data.
    ///
    /// # Panics
    ///
    /// Panics if `ordering` is not one of the two allowed values.
    ///
    /// # Examples
    ///
    ///     use std::sync::atomic::Ordering;
    ///     use atomicbox::AtomicOptionBox;
    ///
    ///     let atom = AtomicOptionBox::new(None);
    ///     let prev_value = atom.swap(Some(Box::new("ok")), Ordering::AcqRel);
    ///     assert_eq!(prev_value, None);
    ///
    pub fn swap(&self, other: OptionBox<T>, order: Ordering) -> OptionBox<T> {
        self.base.swap(other, order)
    }

    /// Atomically set this `AtomicOptionBox` to `other` and drop the
    /// previous value.
    ///
    /// The `AtomicOptionBox` takes ownership of `other`.
    ///
    /// `ordering` must be either `Ordering::AcqRel` or `Ordering::SeqCst`,
    /// as other values would not be safe if `T` contains any data.
    ///
    /// # Panics
    ///
    /// Panics if `ordering` is not one of the two allowed values.
    ///
    /// # Examples
    ///
    ///     use std::sync::atomic::Ordering;
    ///     use atomicbox::AtomicOptionBox;
    ///
    ///     let atom = AtomicOptionBox::new(None);
    ///     atom.store(Some(Box::new("ok")), Ordering::AcqRel);
    ///     assert_eq!(atom.into_inner(), Some(Box::new("ok")));
    ///
    pub fn store(&self, other: OptionBox<T>, order: Ordering) {
        self.base.store(other, order)
    }

    /// Atomically set this `AtomicOptionBox` to `None` and return the
    /// previous value.
    ///
    /// This does not allocate or free memory, and it neither clones nor drops
    /// any values. It is equivalent to calling `self.swap(None, order)`
    ///
    /// `ordering` must be either `Ordering::AcqRel` or `Ordering::SeqCst`,
    /// as other values would not be safe if `T` contains any data.
    ///
    /// # Panics
    ///
    /// Panics if `ordering` is not one of the two allowed values.
    ///
    /// # Examples
    ///
    ///     use std::sync::atomic::Ordering;
    ///     use atomicbox::AtomicOptionBox;
    ///
    ///     let atom = AtomicOptionBox::new(Some(Box::new("ok")));
    ///     let prev_value = atom.take(Ordering::AcqRel);
    ///     assert!(prev_value.is_some());
    ///     let prev_value = atom.take(Ordering::AcqRel);
    ///     assert!(prev_value.is_none());
    ///
    pub fn take(&self, order: Ordering) -> OptionBox<T> {
        self.base.swap(None, order)
    }

    /// Atomically swaps the contents of this `AtomicOptionBox` with the contents of `other`.
    ///
    /// This does not allocate or free memory, and it neither clones nor drops
    /// any values. The pointers in `*other` and `self` are simply exchanged.
    ///
    /// `ordering` must be either `Ordering::AcqRel` or `Ordering::SeqCst`,
    /// as other values would not be safe if `T` contains any data.
    ///
    /// # Panics
    ///
    /// Panics if `ordering` is not one of the two allowed values.
    ///
    /// # Examples
    ///
    ///     use std::sync::atomic::Ordering;
    ///     use atomicbox::AtomicOptionBox;
    ///
    ///     let atom = AtomicOptionBox::new(None);
    ///     let mut boxed = Some(Box::new("ok"));
    ///     let prev_value = atom.swap_mut(&mut boxed, Ordering::AcqRel);
    ///     assert_eq!(boxed, None);
    ///
    pub fn swap_mut(&self, other: &mut OptionBox<T>, order: Ordering) {
        self.base.swap_mut(other, order)
    }

    /// Consume this `AtomicOptionBox`, returning the last option value it
    /// contained.
    ///
    /// # Examples
    ///
    ///     use atomicbox::AtomicOptionBox;
    ///
    ///     let atom = AtomicOptionBox::new(Some(Box::new("hello")));
    ///     assert_eq!(atom.into_inner(), Some(Box::new("hello")));
    ///
    pub fn into_inner(self) -> OptionBox<T> {
        self.base.into_inner()
    }

    /// Returns a mutable reference to the contained value.
    ///
    /// This is safe because it borrows the `AtomicOptionBox` mutably, which
    /// ensures that no other threads can concurrently access either the atomic
    /// pointer field or the boxed data it points to.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        // I have a convoluted theory that Relaxed is good enough here.
        // See comment in AtomicBox::get_mut().
        let ptr = self.base.ptr.load(Ordering::Relaxed);
        if ptr.is_null() {
            None
        } else {
            Some(unsafe { &mut *(ptr as *mut T) })
        }
    }
}

impl<T> Default for AtomicOptionBox<T> {
    /// The default `AtomicOptionBox<T>` value is `AtomicBox::new(None)`.
    fn default() -> AtomicOptionBox<T> {
        AtomicOptionBox::new(None)
    }
}

impl<T> Debug for AtomicOptionBox<T> {
    /// The `{:?}` format of an `AtomicOptionBox<T>` looks like
    /// `"AtomicOptionBox(0x12341234)"` or `"AtomicOptionBox(None)"`.
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        let p = self.base.ptr.load(Ordering::Relaxed);
        f.write_str("AtomicOptionBox(")?;
        if p.is_null() {
            f.write_str("None")?;
        } else {
            fmt::Pointer::fmt(&p, f)?;
        }
        f.write_str(")")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::Ordering;

    #[test]
    fn atomic_option_box_swap_works() {
        let b = AtomicOptionBox::new(Some(Box::new("hello world")));
        let bis = Box::new("bis");
        assert_eq!(
            b.swap(None, Ordering::AcqRel),
            Some(Box::new("hello world"))
        );
        assert_eq!(b.swap(Some(bis), Ordering::AcqRel), None);
        assert_eq!(b.swap(None, Ordering::AcqRel), Some(Box::new("bis")));
    }

    #[test]
    fn atomic_option_box_store_works() {
        let b = AtomicOptionBox::new(Some(Box::new("hello world")));
        b.store(None, Ordering::AcqRel);
        assert_eq!(b.into_inner(), None);

        let b = AtomicOptionBox::new(Some(Box::new("hello world")));
        let bis = Box::new("bis");
        b.store(Some(bis), Ordering::AcqRel);
        assert_eq!(b.into_inner(), Some(Box::new("bis")));
    }

    #[test]
    fn atomic_option_box_swap_mut_works() {
        let b = AtomicOptionBox::new(Some(Box::new("hello world")));
        let mut bis = None;
        b.swap_mut(&mut bis, Ordering::AcqRel);
        assert_eq!(bis, Some(Box::new("hello world")));
        bis = Some(Box::new("bis"));
        b.swap_mut(&mut bis, Ordering::AcqRel);
        assert_eq!(bis, None);
        b.swap_mut(&mut bis, Ordering::AcqRel);
        assert_eq!(bis, Some(Box::new("bis")));
    }

    #[test]
    fn atomic_option_box_pointer_identity() {
        let box1 = Box::new(1);
        let p1 = format!("{:p}", box1);
        let atom = AtomicOptionBox::new(Some(box1));

        let box2 = Box::new(2);
        let p2 = format!("{:p}", box2);
        assert!(p2 != p1);

        let box3 = atom.swap(Some(box2), Ordering::AcqRel).unwrap(); // box1 out, box2 in
        let p3 = format!("{:p}", box3);
        assert_eq!(p3, p1); // box3 is box1

        let box4 = atom.swap(None, Ordering::AcqRel).unwrap(); // box2 out, None in
        let p4 = format!("{:p}", box4);
        assert_eq!(p4, p2); // box4 is box2
    }

    #[test]
    fn atomic_box_drops() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::Arc;

        struct K(Arc<AtomicUsize>, usize);

        impl Drop for K {
            fn drop(&mut self) {
                self.0.fetch_add(self.1, Ordering::Relaxed);
            }
        }

        let n = Arc::new(AtomicUsize::new(0));
        {
            let ab = AtomicOptionBox::new(Some(Box::new(K(n.clone(), 5))));
            assert_eq!(n.load(Ordering::Relaxed), 0);
            let first = ab.swap(None, Ordering::AcqRel);
            assert_eq!(n.load(Ordering::Relaxed), 0);
            drop(first);
            assert_eq!(n.load(Ordering::Relaxed), 5);
            let second = ab.swap(Some(Box::new(K(n.clone(), 13))), Ordering::AcqRel);
            assert_eq!(second.is_none(), true);
            assert_eq!(n.load(Ordering::Relaxed), 5);
        }
        assert_eq!(n.load(Ordering::Relaxed), 5 + 13);
    }

    #[test]
    #[should_panic(expected = "invalid ordering for atomic swap")]
    fn cant_use_foolish_swap_ordering_type() {
        let atom = AtomicOptionBox::new(Some(Box::new(0)));
        atom.swap(None, Ordering::Release); // nope
    }

    #[test]
    fn debug_fmt() {
        let my_box = Box::new(32);
        let expected = format!("AtomicOptionBox({:p})", my_box);
        assert_eq!(
            format!("{:?}", AtomicOptionBox::new(Some(my_box))),
            expected
        );
        assert_eq!(
            format!("{:?}", AtomicOptionBox::<String>::new(None)),
            "AtomicOptionBox(None)"
        );
    }
}
