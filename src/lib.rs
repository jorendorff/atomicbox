//! Safe atomic boxes. 
//!
//! The standard library provides atomic booleans, integers, and pointers.
//! `AtomicPtr` is safe for loading, storing, and so forth; but pointers are
//! unsafe to use.
//!
//! It turns out that a safe atomic `Box` type is possible. Unfortunately, the
//! only operations it supports are `store` and `swap`. Still, this is
//! sufficient for some lock-free data structures, so here it is!

use std::sync::atomic::{AtomicPtr, Ordering};
use std::mem::forget;
use std::ptr::null_mut;

/// A wrapper for a `Box<T>` that can be atomically swapped.
pub struct AtomicBox<T> {
    ptr: AtomicPtr<T>
}

impl<T> AtomicBox<T> {
    pub fn new(value: Box<T>) -> AtomicBox<T> {
        let abox = AtomicBox {
            ptr: AtomicPtr::new(null_mut())
        };
        abox.ptr.store(Box::into_raw(value), Ordering::Release);
        abox
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
    pub fn swap(&self, other: Box<T>, ordering: Ordering) -> Box<T> {
        assert!(match ordering {
            Ordering::AcqRel | Ordering::SeqCst => true,
            _ => false
        });
        let new_ptr = Box::into_raw(other);
        let old_ptr = self.ptr.swap(new_ptr, ordering);
        unsafe {
            Box::from_raw(old_ptr)
        }
    }

    pub fn into_inner(self) -> Box<T> {
        let p = self.ptr.load(Ordering::Acquire);
        forget(self);
        unsafe {
            Box::from_raw(p)
        }
    }

    pub fn get_mut(&mut self) -> &mut T {
        let p = self.ptr.load(Ordering::Acquire);
        unsafe {
            &mut *p
        }
    }
}

impl<T> Drop for AtomicBox<T> {
    fn drop(&mut self) {
        let ptr = self.ptr.load(Ordering::Acquire);
        unsafe {
            Box::from_raw(ptr);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread::spawn;
    use std::sync::{Arc, Barrier};
    use std::sync::atomic::Ordering;
    
    #[test]
    fn atomic_box_works() {
        let b = AtomicBox::new(Box::new("hello world"));
        let bis = Box::new("bis");
        assert_eq!(b.swap(bis, Ordering::AcqRel), Box::new("hello world"));
        assert_eq!(b.swap(Box::new(""), Ordering::AcqRel), Box::new("bis"));
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
        assert_eq!(p3, p1);  // box3 is box1

        let box4 = atom.swap(Box::new(5), Ordering::AcqRel);  // box2 out, throwaway value in
        let p4 = format!("{:p}", box4);
        assert_eq!(p4, p2);  // box4 is box2
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
        let starter: Vec<u8> = vec![];
        let abox = Arc::new(AtomicBox::new(Box::new(starter)));
        let handles: Vec<_> =
            (0 .. NTHREADS as u8)
            .map(|t| {
                let my_gate = gate.clone();
                let my_box = abox.clone();
                spawn(move || {
                    my_gate.wait();
                    let mut my_vec = Box::new(vec![]);
                    for _ in 0 .. 100 {
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
        for t in 0 .. NTHREADS {
            assert_eq!(counts[t], 100);
        }
    }
}
