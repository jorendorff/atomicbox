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

/// Opaque handle for the atomic box. This allows users to receive handles that
/// represent the value of a box, without leaking pointers that are externally
/// usable.
#[derive(Debug, PartialEq)]
pub struct Handle<T> {
    pub(crate) ptr: *const T,
}

unsafe impl<T> Send for Handle<T> {}
unsafe impl<T> Sync for Handle<T> {}
impl<T> Copy for Handle<T> {}

impl<T> Clone for Handle<T> {
    fn clone(&self) -> Handle<T> {
        *self
    }
}

pub trait HandleReferable {
    type Target;

    fn make_handle(&self) -> Handle<Self::Target>;
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

    pub fn load_handle(&self, order: Ordering) -> Handle<B::Target> {
        Handle {
            ptr: self.load_pointer(order),
        }
    }

    pub fn load_pointer(&self, order: Ordering) -> *mut B::Target {
        self.ptr.load(order)
    }

    pub fn compare_exchange(
        &self,
        current: Handle<B::Target>,
        new: B,
        success: Ordering,
        failure: Ordering,
    ) -> Result<B, (Handle<B::Target>, B)> {
        let mut local_new = new;
        let result = self.compare_exchange_mut(current, &mut local_new, success, failure);

        match result {
            Ok(_) => Ok(local_new),
            Err(previous_ptr) => Err((previous_ptr, local_new)),
        }
    }

    pub fn compare_exchange_mut(
        &self,
        current: Handle<B::Target>,
        new: &mut B,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Handle<B::Target>, Handle<B::Target>> {
        let new_ptr = B::into_raw(unsafe { ptr::read(new) });
        let result =
            self.ptr
                .compare_exchange(current.ptr as *mut B::Target, new_ptr, success, failure);

        match result {
            Ok(previous_ptr) => {
                unsafe {
                    ptr::write(new, B::from_raw(previous_ptr));
                }
                Ok(Handle {
                    ptr: previous_ptr as *const B::Target,
                })
            }
            Err(previous_ptr) => Err(Handle {
                ptr: previous_ptr as *const B::Target,
            }),
        }
    }

    pub fn compare_exchange_weak(
        &self,
        current: Handle<B::Target>,
        new: B,
        success: Ordering,
        failure: Ordering,
    ) -> Result<B, (Handle<B::Target>, B)> {
        let mut local_new = new;
        let result = self.compare_exchange_weak_mut(current, &mut local_new, success, failure);

        match result {
            Ok(_) => Ok(local_new),
            Err(previous_ptr) => Err((previous_ptr, local_new)),
        }
    }

    pub fn compare_exchange_weak_mut(
        &self,
        current: Handle<B::Target>,
        new: &mut B,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Handle<B::Target>, Handle<B::Target>> {
        let new_ptr = B::into_raw(unsafe { ptr::read(new) });
        let result = self.ptr.compare_exchange_weak(
            current.ptr as *mut B::Target,
            new_ptr,
            success,
            failure,
        );

        match result {
            Ok(previous_ptr) => {
                unsafe {
                    ptr::write(new, B::from_raw(previous_ptr));
                }
                Ok(Handle {
                    ptr: previous_ptr as *const B::Target,
                })
            }
            Err(previous_ptr) => Err(Handle {
                ptr: previous_ptr as *const B::Target,
            }),
        }
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
