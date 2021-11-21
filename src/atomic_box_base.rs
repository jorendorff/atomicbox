use std::mem::forget;
use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering};

pub(crate) trait PointerConvertible {
    type Target;

    fn into_raw(b: Self) -> *mut Self::Target;
    unsafe fn from_raw(raw: *mut Self::Target) -> Self;
}

pub(crate) struct AtomicBoxBase<B: PointerConvertible> {
    pub(crate) ptr: AtomicPtr<B::Target>,
}

impl<B: PointerConvertible> AtomicBoxBase<B> {
    pub fn new(value: B) -> AtomicBoxBase<B> {
        let ptr = B::into_raw(value);
        AtomicBoxBase {
            ptr: AtomicPtr::new(ptr),
        }
    }

    pub fn swap(&self, other: B, order: Ordering) -> B {
        let mut result = other;
        self.swap_mut(&mut result, order);
        result
    }

    pub fn store(&self, other: B, order: Ordering) {
        let mut result = other;
        self.swap_mut(&mut result, order);
        drop(result);
    }

    pub fn swap_mut(&self, other: &mut B, order: Ordering) {
        match order {
            Ordering::AcqRel | Ordering::SeqCst => {}
            _ => panic!("invalid ordering for atomic swap"),
        }

        let other_ptr = B::into_raw(unsafe { ptr::read(other) });
        let ptr = self.ptr.swap(other_ptr, order);
        unsafe {
            ptr::write(other, B::from_raw(ptr));
        };
    }

    pub fn into_inner(self) -> B {
        let last_ptr = self.ptr.load(Ordering::Acquire);
        forget(self);
        unsafe { B::from_raw(last_ptr) }
    }

    pub fn load_pointer(&self, order: Ordering) -> *mut B::Target {
        self.ptr.load(order)
    }
}

impl<B: PointerConvertible> Default for AtomicBoxBase<B>
where
    B: Default,
{
    /// The default `AtomicBox<T>` value boxes the default `T` value.
    fn default() -> AtomicBoxBase<B> {
        AtomicBoxBase::new(Default::default())
    }
}

impl<B: PointerConvertible> Drop for AtomicBoxBase<B> {
    /// Dropping an `AtomicBoxBase<T>` drops the final value stored in it.
    fn drop(&mut self) {
        let ptr = self.ptr.load(Ordering::Acquire);
        unsafe {
            B::from_raw(ptr);
        }
    }
}
