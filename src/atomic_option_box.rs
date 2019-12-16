use std::fmt::{self, Debug, Formatter};
use std::mem::forget;
use std::ptr::{self, null_mut};
use std::sync::atomic::{AtomicPtr, Ordering};

/// A type that holds a single `Option<Box<T>>` value and can be safely shared
/// between threads.
pub struct AtomicOptionBox<T> {
    /// Pointer to a `T` value in the heap, representing `Some(t)`;
    /// or a null pointer for `None`.
    ptr: AtomicPtr<T>,
}

fn into_ptr<T>(value: Option<Box<T>>) -> *mut T {
    match value {
        Some(box_value) => Box::into_raw(box_value),
        None => null_mut(),
    }
}

unsafe fn from_ptr<T>(ptr: *mut T) -> Option<Box<T>> {
    if ptr.is_null() {
        None
    } else {
        Some(Box::from_raw(ptr))
    }
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
    pub fn new(value: Option<Box<T>>) -> AtomicOptionBox<T> {
        let abox = AtomicOptionBox {
            ptr: AtomicPtr::new(null_mut()),
        };
        if let Some(box_value) = value {
            abox.ptr.store(Box::into_raw(box_value), Ordering::Release);
        }
        abox
    }

    /// Creates a new `AtomicOptionBox` with no value.
    ///
    /// Equivalent to `AtomicOptionBox::new(None)`, but can be used in const
    /// context.
    ///
    /// # Examples
    ///
    ///     use atomicbox::AtomicOptionBox;
    ///
    ///     static GLOBAL_BOX: AtomicOptionBox<u32> = AtomicOptionBox::none();
    ///
    pub const fn none() -> Self {
        Self {
            ptr: AtomicPtr::new(null_mut()),
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
    pub fn swap(&self, other: Option<Box<T>>, order: Ordering) -> Option<Box<T>> {
        let mut result = other;
        self.swap_mut(&mut result, order);
        result
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
    pub fn take(&self, order: Ordering) -> Option<Box<T>> {
        self.swap(None, order)
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
    pub fn swap_mut(&self, other: &mut Option<Box<T>>, order: Ordering) {
        match order {
            Ordering::AcqRel | Ordering::SeqCst => {}
            _ => panic!("invalid ordering for atomic swap"),
        }

        let new_ptr = into_ptr(unsafe { ptr::read(other) });
        let old_ptr = self.ptr.swap(new_ptr, order);
        unsafe {
            ptr::write(other, from_ptr(old_ptr));
        }
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
    pub fn into_inner(self) -> Option<Box<T>> {
        let last_ptr = self.ptr.load(Ordering::Acquire);
        forget(self);
        unsafe { from_ptr(last_ptr) }
    }

    /// Returns a mutable reference to the contained value.
    ///
    /// This is safe because it borrows the `AtomicOptionBox` mutably, which
    /// ensures that no other threads can concurrently access either the atomic
    /// pointer field or the boxed data it points to.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        // I have a convoluted theory that Relaxed is good enough here.
        // See comment in AtomicBox::get_mut().
        let ptr = self.ptr.load(Ordering::Relaxed);
        if ptr.is_null() {
            None
        } else {
            Some(unsafe { &mut *ptr })
        }
    }
}

impl<T> Drop for AtomicOptionBox<T> {
    /// Dropping an `AtomicOptionBox<T>` drops the final `Box<T>` value (if
    /// any) stored in it.
    fn drop(&mut self) {
        let ptr = self.ptr.load(Ordering::Acquire);
        unsafe {
            from_ptr(ptr);
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
        let p = self.ptr.load(Ordering::Relaxed);
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
