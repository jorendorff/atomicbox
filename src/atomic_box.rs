use atomic_box_base::{AtomicBoxBase, Handle, HandleReferable, PointerConvertible};
use std::fmt::{self, Debug, Formatter};
use std::sync::atomic::Ordering;

impl<T> PointerConvertible for Box<T> {
    type Target = T;

    fn into_raw(b: Self) -> *mut T {
        Box::into_raw(b)
    }

    unsafe fn from_raw(raw: *mut T) -> Self {
        Box::from_raw(raw)
    }
}

impl<T> HandleReferable for Box<T> {
    type Target = T;

    fn make_handle(&self) -> Handle<T> {
        Handle {
            ptr: &**self as *const T,
        }
    }
}

/// A type that holds a single `Box<T>` value and can be safely shared between
/// threads.
pub struct AtomicBox<T> {
    base: AtomicBoxBase<Box<T>>,
}

impl<T> AtomicBox<T> {
    /// Creates a new `AtomicBox` with the given value.
    ///
    /// # Examples
    ///
    ///     use atomicbox::AtomicBox;
    ///
    ///     let atomic_box = AtomicBox::new(Box::new(0));
    ///
    pub fn new(value: Box<T>) -> AtomicBox<T> {
        AtomicBox {
            base: AtomicBoxBase::new(value),
        }
    }

    /// Atomically set this `AtomicBox` to `other` and return the previous value.
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
    ///     use atomicbox::AtomicBox;
    ///
    ///     let atom = AtomicBox::new(Box::new("one"));
    ///     let prev_value = atom.swap(Box::new("two"), Ordering::AcqRel);
    ///     assert_eq!(*prev_value, "one");
    ///
    pub fn swap(&self, other: Box<T>, order: Ordering) -> Box<T> {
        self.base.swap(other, order)
    }

    /// Atomically set this `AtomicBox` to `other` and drop its previous value.
    ///
    /// The `AtomicBox` takes ownership of `other`.
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
    ///     use atomicbox::AtomicBox;
    ///
    ///     let atom = AtomicBox::new(Box::new("one"));
    ///     atom.store(Box::new("two"), Ordering::AcqRel);
    ///     assert_eq!(atom.into_inner(), Box::new("two"));
    ///
    pub fn store(&self, other: Box<T>, order: Ordering) {
        self.base.store(other, order)
    }

    /// Atomically swaps the contents of this `AtomicBox` with the contents of `other`.
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
    ///     use atomicbox::AtomicBox;
    ///
    ///     let atom = AtomicBox::new(Box::new("one"));
    ///     let mut boxed = Box::new("two");
    ///     atom.swap_mut(&mut boxed, Ordering::AcqRel);
    ///     assert_eq!(*boxed, "one");
    ///
    pub fn swap_mut(&self, other: &mut Box<T>, order: Ordering) {
        self.base.swap_mut(other, order)
    }

    /// Consume this `AtomicBox`, returning the last box value it contained.
    ///
    /// # Examples
    ///
    ///     use atomicbox::AtomicBox;
    ///
    ///     let atom = AtomicBox::new(Box::new("hello"));
    ///     assert_eq!(atom.into_inner(), Box::new("hello"));
    ///
    pub fn into_inner(self) -> Box<T> {
        self.base.into_inner()
    }

    /// Returns a mutable reference to the contained value.
    ///
    /// This is safe because it borrows the `AtomicBox` mutably, which ensures
    /// that no other threads can concurrently access either the atomic pointer field
    /// or the boxed data it points to.
    pub fn get_mut(&mut self) -> &mut T {
        // Relaxed suffices here because this thread must already have
        // rendezvoused with any other thread that's been modifying shared
        // data, and executed an Acquire barrier, in order for the caller to
        // have a `mut` reference.  Symmetrically, no barrier is needed when
        // the reference expires, because this thread must rendezvous with
        // other threads, and execute a Release barrier, before this AtomicBox
        // becomes shared again.
        let ptr = self.base.ptr.load(Ordering::Relaxed);
        unsafe { &mut *(ptr as *mut T) }
    }

    /// Returns a handle that matches the currently held box.
    ///
    /// `load_handle` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. Possible values are [`SeqCst`], [`Acquire`] and [`Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Release`] or [`AcqRel`].
    pub fn load_handle(&self, order: Ordering) -> Handle<T> {
        self.base.load_handle(order)
    }

    /// Returns a pointer to the currently held box.
    ///
    /// Using the pointer is unsafe for all of the usual reasons; e.g., the box might
    /// have been dropped by another thread by the time the pointer is dereferenced.
    ///
    /// `load_pointer` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. Possible values are [`SeqCst`], [`Acquire`] and [`Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Release`] or [`AcqRel`].
    ///
    /// # Examples
    ///
    ///     use atomicbox::AtomicBox;
    ///     use std::sync::atomic::Ordering;
    ///
    ///     let mut box1 = Box::new("goodbye");
    ///     let atom = AtomicBox::new(Box::new("hello"));
    ///     let ptr = &mut *box1 as *mut &str;
    ///
    ///     atom.store(box1, Ordering::SeqCst);
    ///     assert_eq!(atom.load_pointer(Ordering::Relaxed), ptr);
    ///
    pub fn load_pointer(&self, order: Ordering) -> *mut T {
        self.base.load_pointer(order)
    }

    /// Stores `new` into this `AtomicBox` if the currently held value matches the `current` handle.
    ///
    /// The return value is a result indicating whether `new` was written and containing
    /// the previous value. On success the returned handle is guaranteed to match the current value.
    /// On failure the returned value contains the handle that matches the value in this `AtomicBox`
    /// and the given `new`.
    ///
    /// `compare_exchange` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `current` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Acquire`] as success ordering makes the store part
    /// of this operation [`Relaxed`], and using [`Release`] makes the successful load
    /// [`Relaxed`]. The failure ordering can only be [`SeqCst`], [`Acquire`] or [`Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    ///
    /// # Examples
    ///
    ///     use atomicbox::AtomicBox;
    ///     use std::sync::atomic::Ordering;
    ///
    ///     let atom = AtomicBox::new(Box::new("hello"));
    ///     let box1 = Box::new("goodbye");
    ///     let current = atom.load_handle(Ordering::Relaxed);
    ///     let result = atom.compare_exchange(current, box1, Ordering::SeqCst, Ordering::Relaxed);
    ///     assert_eq!(result, Ok(Box::new("hello")));
    ///
    pub fn compare_exchange(
        &self,
        current: Handle<T>,
        new: Box<T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Box<T>, (Handle<T>, Box<T>)> {
        self.base.compare_exchange(current, new, success, failure)
    }

    /// Automatically swaps the contents of this `AtomicBox` and the contents of `new` if the
    /// currently held value matches the `current` handle.
    ///
    /// The return value is a result indicating whether `new` was written and containing
    /// the previous value. On success the returned handle is guaranteed to match the current value.
    /// On failure, the returned value contains the handle that matches the value in this
    /// `AtomicBox`, and `new` isn't mutated.
    ///
    /// `compare_exchange_mut` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `current` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Acquire`] as success ordering makes the store part
    /// of this operation [`Relaxed`], and using [`Release`] makes the successful load
    /// [`Relaxed`]. The failure ordering can only be [`SeqCst`], [`Acquire`] or [`Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    ///
    /// # Examples
    ///
    ///     use atomicbox::AtomicBox;
    ///     use std::sync::atomic::Ordering;
    ///
    ///     let atom = AtomicBox::new(Box::new("hello"));
    ///     let mut box1 = Box::new("goodbye");
    ///     let current = atom.load_handle(Ordering::Relaxed);
    ///     atom.compare_exchange_mut(current, &mut box1, Ordering::SeqCst, Ordering::Relaxed);
    ///     assert_eq!(box1, Box::new("hello"));
    ///
    pub fn compare_exchange_mut(
        &self,
        current: Handle<T>,
        new: &mut Box<T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Handle<T>, Handle<T>> {
        self.base
            .compare_exchange_mut(current, new, success, failure)
    }

    /// Stores `new` into this `AtomicBox` if the currently held value matches the `current` handle.
    ///
    /// Unlike [`AtomicBox::compare_exchange`], this function is allowed to spuriously fail even
    /// when the comparison succeeds, which can result in more efficient code on some platforms.
    /// The return value is a result indicating whether `new` was written and containing
    /// the previous value. On success the returned handle is guaranteed to match the current value.
    /// On failure the returned value contains the handle that matches the value in this `AtomicBox`
    /// and the given `new`.
    ///
    /// `compare_exchange_weak` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `current` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Acquire`] as success ordering makes the store part
    /// of this operation [`Relaxed`], and using [`Release`] makes the successful load
    /// [`Relaxed`]. The failure ordering can only be [`SeqCst`], [`Acquire`] or [`Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    ///
    /// # Examples
    ///
    ///     use atomicbox::AtomicBox;
    ///     use std::sync::atomic::Ordering;
    ///
    ///     let atom = AtomicBox::new(Box::new("hello"));
    ///     let mut box1 = Box::new("goodbye");
    ///     let mut current = atom.load_handle(Ordering::Relaxed);
    ///     box1 = loop {
    ///         match atom.compare_exchange_weak(current, box1, Ordering::SeqCst, Ordering::Relaxed) {
    ///             Ok(b) => break b,
    ///             Err((c, b)) => {
    ///                 current = c;
    ///                 box1 = b;
    ///             }
    ///         }
    ///     };
    ///
    pub fn compare_exchange_weak(
        &self,
        current: Handle<T>,
        new: Box<T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Box<T>, (Handle<T>, Box<T>)> {
        self.base
            .compare_exchange_weak(current, new, success, failure)
    }

    /// Automatically swaps the contents of this `AtomicBox` and the contents of `new` if the
    /// currently held value matches the `current` handle.
    ///
    /// Unlike [`AtomicBox::compare_exchange_weak`], this function is allowed to spuriously fail
    /// even when the comparison succeeds, which can result in more efficient code on some
    /// platforms.
    /// The return value is a result indicating whether `new` was written and containing
    /// the previous value. On success the returned handle is guaranteed to match the current value.
    /// On failure, the returned value contains the handle that matches the value in this
    /// `AtomicBox`, and `new` isn't mutated.rulers
    ///
    /// `compare_exchange_weak_mut` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `current` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Acquire`] as success ordering makes the store part
    /// of this operation [`Relaxed`], and using [`Release`] makes the successful load
    /// [`Relaxed`]. The failure ordering can only be [`SeqCst`], [`Acquire`] or [`Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    ///
    /// # Examples
    ///
    ///     use atomicbox::AtomicBox;
    ///     use std::sync::atomic::Ordering;
    ///
    ///     let atom = AtomicBox::new(Box::new("hello"));
    ///     let mut box1 = Box::new("goodbye");
    ///     let mut current = atom.load_handle(Ordering::Relaxed);
    ///     loop {
    ///         match atom.compare_exchange_weak_mut(current, &mut box1, Ordering::SeqCst, Ordering::Relaxed) {
    ///             Ok(_) => break,
    ///             Err(c) => current = c,
    ///         }
    ///     }
    ///
    pub fn compare_exchange_weak_mut(
        &self,
        current: Handle<T>,
        new: &mut Box<T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Handle<T>, Handle<T>> {
        self.base
            .compare_exchange_weak_mut(current, new, success, failure)
    }
}

impl<T> Default for AtomicBox<T>
where
    Box<T>: Default,
{
    /// The default `AtomicBox<T>` value boxes the default `T` value.
    fn default() -> AtomicBox<T> {
        AtomicBox::new(Default::default())
    }
}

impl<T> Debug for AtomicBox<T> {
    /// The `{:?}` format of an `AtomicBox<T>` looks like `"AtomicBox(0x12341234)"`.
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        let p = self.base.ptr.load(Ordering::Relaxed);
        f.write_str("AtomicBox(")?;
        fmt::Pointer::fmt(&p, f)?;
        f.write_str(")")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Barrier};
    use std::thread::spawn;

    #[test]
    fn atomic_box_swap_works() {
        let b = AtomicBox::new(Box::new("hello world"));
        let bis = Box::new("bis");
        assert_eq!(b.swap(bis, Ordering::AcqRel), Box::new("hello world"));
        assert_eq!(b.swap(Box::new(""), Ordering::AcqRel), Box::new("bis"));
    }

    #[test]
    fn atomic_box_load_handle_works() {
        let box1 = Box::new("hello world");
        let handle1 = box1.make_handle();
        let b = AtomicBox::new(box1);
        let handle2 = b.load_handle(Ordering::Relaxed);
        assert_eq!(handle1, handle2);
    }

    #[test]
    fn atomic_box_compare_exchange_mut_works() {
        let box1 = Box::new("box1");
        let handle1 = box1.make_handle();
        let mut box2 = Box::new("box2");
        let handle2 = box2.make_handle();
        let atom = AtomicBox::new(box1);

        let ok_result =
            atom.compare_exchange_mut(handle1, &mut box2, Ordering::AcqRel, Ordering::Acquire);
        assert_eq!(box2, Box::new("box1"));
        assert_eq!(ok_result, Ok(handle1));
        assert_eq!(atom.load_handle(Ordering::Relaxed), handle2);

        let err_result =
            atom.compare_exchange_mut(handle1, &mut box2, Ordering::AcqRel, Ordering::Acquire);
        assert_eq!(box2, Box::new("box1"));
        assert_eq!(err_result, Err(handle2));
        assert_eq!(atom.load_handle(Ordering::Relaxed), handle2);
    }

    #[test]
    fn atomic_box_compare_exchange_works() {
        let box1 = Box::new("box1");
        let handle1 = box1.make_handle();
        let box2 = Box::new("box2");
        let handle2 = box2.make_handle();
        let atom = AtomicBox::new(box1);

        let ok_result = atom.compare_exchange(handle1, box2, Ordering::AcqRel, Ordering::Acquire);
        let ok_result_box = ok_result.unwrap();
        assert_eq!(ok_result_box, Box::new("box1"));
        assert_eq!(atom.load_handle(Ordering::Relaxed), handle2);

        let err_result =
            atom.compare_exchange(handle1, ok_result_box, Ordering::AcqRel, Ordering::Acquire);
        assert_eq!(err_result, Err((handle2, Box::new("box1"))));
        assert_eq!(atom.load_handle(Ordering::Relaxed), handle2);
    }

    #[test]
    fn atomic_box_compare_exchange_weak_mut_works() {
        let box1 = Box::new("box1");
        let handle1 = box1.make_handle();
        let mut box2 = Box::new("box2");
        let handle2 = box2.make_handle();
        let atom = AtomicBox::new(box1);

        let ok_result = loop {
            let result = atom.compare_exchange_weak_mut(
                handle1,
                &mut box2,
                Ordering::SeqCst,
                Ordering::Relaxed,
            );
            if result.is_ok() {
                break result;
            }
        };
        assert_eq!(box2, Box::new("box1"));
        assert_eq!(ok_result, Ok(handle1));
        assert_eq!(atom.load_handle(Ordering::Relaxed), handle2);

        let err_result =
            atom.compare_exchange_weak_mut(handle1, &mut box2, Ordering::AcqRel, Ordering::Acquire);
        assert_eq!(box2, Box::new("box1"));
        assert_eq!(err_result, Err(handle2));
        assert_eq!(atom.load_handle(Ordering::Relaxed), handle2);
    }

    #[test]
    fn atomic_box_compare_exchange_weak_works() {
        let box1 = Box::new("box1");
        let handle1 = box1.make_handle();
        let mut box2 = Box::new("box2");
        let handle2 = box2.make_handle();
        let atom = AtomicBox::new(box1);

        let old_box = loop {
            let result =
                atom.compare_exchange_weak(handle1, box2, Ordering::SeqCst, Ordering::Relaxed);
            match result {
                Ok(b) => break b,
                Err((_, b)) => box2 = b,
            }
        };

        assert_eq!(old_box, Box::new("box1"));
        assert_eq!(atom.load_handle(Ordering::Relaxed), handle2);

        let err_result =
            atom.compare_exchange_weak(handle1, old_box, Ordering::AcqRel, Ordering::Acquire);
        assert_eq!(err_result, Err((handle2, Box::new("box1"))));
        assert_eq!(atom.load_handle(Ordering::Relaxed), handle2);
    }

    #[test]
    fn atomic_box_store_works() {
        let b = AtomicBox::new(Box::new("hello world"));
        let bis = Box::new("bis");
        b.store(bis, Ordering::AcqRel);
        assert_eq!(b.into_inner(), Box::new("bis"));
    }

    #[test]
    fn atomic_box_swap_mut_works() {
        let b = AtomicBox::new(Box::new("hello world"));
        let mut bis = Box::new("bis");
        b.swap_mut(&mut bis, Ordering::AcqRel);
        assert_eq!(bis, Box::new("hello world"));
        b.swap_mut(&mut bis, Ordering::AcqRel);
        assert_eq!(bis, Box::new("bis"));
    }

    #[test]
    fn atomic_box_pointer_identity() {
        let box1 = Box::new(1);
        let p1 = format!("{:p}", box1);
        let atom = AtomicBox::new(box1);

        let box2 = Box::new(2);
        let p2 = format!("{:p}", box2);
        assert!(p2 != p1);

        let box3 = atom.swap(box2, Ordering::AcqRel); // box1 out, box2 in
        let p3 = format!("{:p}", box3);
        assert_eq!(p3, p1); // box3 is box1

        let box4 = atom.swap(Box::new(5), Ordering::AcqRel); // box2 out, throwaway value in
        let p4 = format!("{:p}", box4);
        assert_eq!(p4, p2); // box4 is box2
    }

    #[test]
    fn atomic_box_drops() {
        use std::sync::atomic::AtomicUsize;

        struct K(Arc<AtomicUsize>, usize);

        impl Drop for K {
            fn drop(&mut self) {
                self.0.fetch_add(self.1, Ordering::Relaxed);
            }
        }

        let n = Arc::new(AtomicUsize::new(0));
        {
            let ab = AtomicBox::new(Box::new(K(n.clone(), 5)));
            assert_eq!(n.load(Ordering::Relaxed), 0);
            let first = ab.swap(Box::new(K(n.clone(), 13)), Ordering::AcqRel);
            assert_eq!(n.load(Ordering::Relaxed), 0);
            drop(first);
            assert_eq!(n.load(Ordering::Relaxed), 5);
        }
        assert_eq!(n.load(Ordering::Relaxed), 5 + 13);
    }

    #[test]
    fn atomic_threads() {
        const NTHREADS: usize = 9;

        let gate = Arc::new(Barrier::new(NTHREADS));
        let abox: Arc<AtomicBox<Vec<u8>>> = Arc::new(Default::default());
        let handles: Vec<_> = (0..NTHREADS as u8)
            .map(|t| {
                let my_gate = gate.clone();
                let my_box = abox.clone();
                spawn(move || {
                    my_gate.wait();
                    let mut my_vec = Box::new(vec![]);
                    for _ in 0..100 {
                        my_vec = my_box.swap(my_vec, Ordering::AcqRel);
                        my_vec.push(t);
                    }
                    my_vec
                })
            })
            .collect();

        let mut counts = [0usize; NTHREADS];
        for h in handles {
            for val in *h.join().unwrap() {
                counts[val as usize] += 1;
            }
        }

        // Don't forget the data still in `abox`!
        // There are NTHREADS+1 vectors in all.
        for val in *abox.swap(Box::new(vec![]), Ordering::AcqRel) {
            counts[val as usize] += 1;
        }

        println!("{:?}", counts);
        for t in 0..NTHREADS {
            assert_eq!(counts[t], 100);
        }
    }

    #[test]
    fn atomic_threads_exchange() {
        const NTHREADS: usize = 9;

        let gate = Arc::new(Barrier::new(NTHREADS));
        let abox: Arc<AtomicBox<Vec<u8>>> = Arc::new(Default::default());
        let shared_box_handle = abox.load_handle(Ordering::Relaxed);
        let handles: Vec<_> = (0..NTHREADS as u8)
            .map(|t| {
                let my_gate = gate.clone();
                let my_box = abox.clone();
                spawn(move || {
                    println!("{:?}", t);
                    my_gate.wait();
                    let mut my_vec = Box::new(vec![]);
                    for _ in 0..100 {
                        loop {
                            let result = my_box.compare_exchange_weak_mut(
                                shared_box_handle,
                                &mut my_vec,
                                Ordering::SeqCst,
                                Ordering::Relaxed,
                            );
                            if result.is_ok() {
                                break;
                            }
                        }
                        my_vec.push(t);

                        my_vec = my_box.swap(my_vec, Ordering::AcqRel);
                    }
                })
            })
            .collect();

        for h in handles {
            h.join().unwrap();
        }

        let mut counts = [0usize; NTHREADS];

        for val in *abox.swap(Box::new(vec![]), Ordering::AcqRel) {
            counts[val as usize] += 1;
        }

        println!("{:?}", counts);
        for t in 0..NTHREADS {
            assert_eq!(counts[t], 100);
        }
    }

    #[test]
    #[should_panic(expected = "invalid ordering for atomic swap")]
    fn cant_use_foolish_swap_ordering_type() {
        let atom = AtomicBox::new(Box::new(0));
        atom.swap(Box::new(44), Ordering::Release); // nope
    }

    #[test]
    fn debug_fmt() {
        let my_box = Box::new(32);
        let expected = format!("AtomicBox({:p})", my_box);
        assert_eq!(format!("{:?}", AtomicBox::new(my_box)), expected);
    }
}
