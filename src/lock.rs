//! Traits for locks that can be used inside a [`WaitList`](crate::WaitList).

/// Associated types of a [`Lock`] with a specific lifetime applied.
pub trait Lifetime<'this, ImplicitBounds: bounds::Sealed = bounds::Bounds<&'this Self>> {
    /// A RAII exclusive guard on the lock; when this type is dropped, the lock must unlock.
    type ExclusiveGuard;

    /// A RAII shared guard on the lock; when this type is dropped, the lock must unlock.
    type SharedGuard;
}

/// A lock.
///
/// # Safety
///
/// This lock must uphold XOR mutability: at any give time either one exclusive guard or
/// multiple shared guards can be handed out.
///
/// Note that the shared implementation does not actually have to be shared; it is just an
/// optimization for implementations that support it.
pub unsafe trait Lock: for<'this> Lifetime<'this> {
    /// Acquire an exclusive lock.
    ///
    /// When called recursively, this function must panic, abort or deadlock.
    ///
    /// If the previous guard was dropped during a panic, this function may or may not panic.
    fn lock_exclusive(&self) -> <Self as Lifetime<'_>>::ExclusiveGuard;

    /// Acquire a shared lock.
    ///
    /// When called recursively, this function may succeed, panic, abort or deadlock.
    ///
    /// If the previous guard was dropped during a panic, this function may or may not panic.
    fn lock_shared(&self) -> <Self as Lifetime<'_>>::SharedGuard;
}

macro_rules! impl_for_wrapper {
    ($($t:ty),*) => { $(
        impl<'this, L: Lock> Lifetime<'this> for $t {
            type ExclusiveGuard = <L as Lifetime<'this>>::ExclusiveGuard;
            type SharedGuard = <L as Lifetime<'this>>::SharedGuard;
        }
        unsafe impl<L: Lock> Lock for $t {
            fn lock_exclusive(&self) -> <Self as Lifetime<'_>>::ExclusiveGuard {
                (**self).lock_exclusive()
            }
            fn lock_shared(&self) -> <Self as Lifetime<'_>>::SharedGuard {
                (**self).lock_shared()
            }
        }
    )* };
}
impl_for_wrapper!(&L, &mut L);

#[cfg(feature = "alloc")]
impl_for_wrapper!(alloc::boxed::Box<L>, alloc::rc::Rc<L>, alloc::sync::Arc<L>);

/// [`Local`] provides a thread-local exclusive-only lock — like [`RefCell`], but it can be smaller
/// and it lacks read support.
///
/// [`RefCell`]: core::cell::RefCell
pub mod local {
    use crate::lock;
    use crate::lock::Lock;
    use core::cell::Cell;
    use core::cell::UnsafeCell;
    use core::ops::Deref;
    use core::ops::DerefMut;

    /// A thread-local implementation of [`Lock`].
    ///
    /// This type is very similar to [`core::cell::RefCell`] but because it only supports
    /// exclusive locking it can be smaller.
    #[derive(Debug)]
    pub struct Local<T> {
        locked: Cell<bool>,
        data: UnsafeCell<T>,
    }

    impl<T> Local<T> {
        /// Create a new local lock around a value.
        #[must_use]
        pub const fn new(value: T) -> Self {
            Self {
                locked: Cell::new(false),
                data: UnsafeCell::new(value),
            }
        }

        /// Get a unique reference to the inner value from a unique reference to the lock.
        #[must_use]
        pub fn get_mut(&mut self) -> &mut T {
            self.data.get_mut()
        }

        /// Consume this lock, returning the inner data.
        #[must_use]
        pub fn into_inner(self) -> T {
            self.data.into_inner()
        }

        /// Check whether the lock is currently locked.
        #[must_use]
        pub fn is_locked(&self) -> bool {
            self.locked.get()
        }
    }

    impl<T: Default> Default for Local<T> {
        fn default() -> Self {
            Self::new(T::default())
        }
    }

    impl<T> From<T> for Local<T> {
        fn from(value: T) -> Self {
            Self::new(value)
        }
    }

    impl<'this, T> lock::Lifetime<'this> for Local<T> {
        type ExclusiveGuard = Guard<'this, T>;
        type SharedGuard = Guard<'this, T>;
    }
    unsafe impl<T> Lock for Local<T> {
        #[track_caller]
        fn lock_exclusive(&self) -> <Self as lock::Lifetime<'_>>::ExclusiveGuard {
            assert!(!self.is_locked(), "Attempted to recursively lock `Local`");
            self.locked.set(true);
            Guard { lock: self }
        }
        fn lock_shared(&self) -> <Self as lock::Lifetime<'_>>::SharedGuard {
            self.lock_exclusive()
        }
    }

    /// The lock guard for [`Local`].
    ///
    /// Because this lock type only supports exclusive locking, the same guard type is used for
    /// both exclusive and shared guards.
    #[derive(Debug)]
    pub struct Guard<'lock, T> {
        lock: &'lock Local<T>,
    }

    impl<T> Deref for Guard<'_, T> {
        type Target = T;
        fn deref(&self) -> &Self::Target {
            unsafe { &*self.lock.data.get() }
        }
    }
    impl<T> DerefMut for Guard<'_, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            unsafe { &mut *self.lock.data.get() }
        }
    }

    impl<T> Drop for Guard<'_, T> {
        fn drop(&mut self) {
            debug_assert!(self.lock.is_locked());
            self.lock.locked.set(false);
        }
    }
}
#[doc(no_inline)]
pub use local::Local;

mod ref_cell {
    use crate::lock;
    use crate::lock::Lock;
    use core::cell;
    use core::cell::RefCell;

    impl<'this, T> lock::Lifetime<'this> for RefCell<T> {
        type ExclusiveGuard = cell::RefMut<'this, T>;
        type SharedGuard = cell::Ref<'this, T>;
    }
    unsafe impl<T> Lock for RefCell<T> {
        fn lock_exclusive(&self) -> <Self as lock::Lifetime<'_>>::ExclusiveGuard {
            self.borrow_mut()
        }
        fn lock_shared(&self) -> <Self as lock::Lifetime<'_>>::SharedGuard {
            self.borrow()
        }
    }
}

#[cfg(feature = "std")]
mod std {
    use crate::lock;
    use crate::lock::Lock;
    use std::sync::Mutex;
    use std::sync::MutexGuard;
    use std::sync::RwLock;
    use std::sync::RwLockReadGuard;
    use std::sync::RwLockWriteGuard;

    #[cfg_attr(doc_nightly, doc(cfg(feature = "std")))]
    impl<'this, T> lock::Lifetime<'this> for Mutex<T> {
        type ExclusiveGuard = MutexGuard<'this, T>;
        type SharedGuard = MutexGuard<'this, T>;
    }
    #[cfg_attr(doc_nightly, doc(cfg(feature = "std")))]
    unsafe impl<T> Lock for Mutex<T> {
        fn lock_exclusive(&self) -> <Self as lock::Lifetime<'_>>::ExclusiveGuard {
            self.lock().unwrap()
        }
        fn lock_shared(&self) -> <Self as lock::Lifetime<'_>>::SharedGuard {
            self.lock_exclusive()
        }
    }

    #[cfg_attr(doc_nightly, doc(cfg(feature = "std")))]
    impl<'this, T> lock::Lifetime<'this> for RwLock<T> {
        type ExclusiveGuard = RwLockWriteGuard<'this, T>;
        type SharedGuard = RwLockReadGuard<'this, T>;
    }
    #[cfg_attr(doc_nightly, doc(cfg(feature = "std")))]
    unsafe impl<T> Lock for RwLock<T> {
        fn lock_exclusive(&self) -> <Self as lock::Lifetime<'_>>::ExclusiveGuard {
            self.write().unwrap()
        }
        fn lock_shared(&self) -> <Self as lock::Lifetime<'_>>::SharedGuard {
            self.read().unwrap()
        }
    }
}

#[cfg(feature = "lock_api_04")]
mod lock_api_04 {
    use crate::lock;
    use crate::lock::Lock;
    use lock_api_04::Mutex;
    use lock_api_04::MutexGuard;
    use lock_api_04::RawMutex;
    use lock_api_04::RawRwLock;
    use lock_api_04::RwLock;
    use lock_api_04::RwLockReadGuard;
    use lock_api_04::RwLockWriteGuard;

    #[cfg_attr(doc_nightly, doc(cfg(feature = "lock_api_04")))]
    impl<'this, R: RawMutex, T> lock::Lifetime<'this> for Mutex<R, T> {
        type ExclusiveGuard = MutexGuard<'this, R, T>;
        type SharedGuard = MutexGuard<'this, R, T>;
    }
    #[cfg_attr(doc_nightly, doc(cfg(feature = "lock_api_04")))]
    unsafe impl<R: RawMutex, T> Lock for Mutex<R, T> {
        fn lock_exclusive(&self) -> <Self as lock::Lifetime<'_>>::ExclusiveGuard {
            self.lock()
        }
        fn lock_shared(&self) -> <Self as lock::Lifetime<'_>>::SharedGuard {
            self.lock_exclusive()
        }
    }

    #[cfg_attr(doc_nightly, doc(cfg(feature = "lock_api_04")))]
    impl<'this, R: RawRwLock, T> lock::Lifetime<'this> for RwLock<R, T> {
        type ExclusiveGuard = RwLockWriteGuard<'this, R, T>;
        type SharedGuard = RwLockReadGuard<'this, R, T>;
    }
    #[cfg_attr(doc_nightly, doc(cfg(feature = "lock_api_04")))]
    unsafe impl<R: RawRwLock, T> Lock for RwLock<R, T> {
        fn lock_exclusive(&self) -> <Self as lock::Lifetime<'_>>::ExclusiveGuard {
            self.write()
        }
        fn lock_shared(&self) -> <Self as lock::Lifetime<'_>>::SharedGuard {
            self.read()
        }
    }
}

#[cfg(feature = "loom_05")]
mod loom_05 {
    use crate::lock;
    use crate::lock::Lock;
    use loom_05_crate::sync::Mutex;
    use loom_05_crate::sync::MutexGuard;
    use loom_05_crate::sync::RwLock;
    use loom_05_crate::sync::RwLockReadGuard;
    use loom_05_crate::sync::RwLockWriteGuard;

    #[cfg_attr(doc_nightly, doc(cfg(feature = "loom")))]
    impl<'this, T> lock::Lifetime<'this> for Mutex<T> {
        type ExclusiveGuard = MutexGuard<'this, T>;
        type SharedGuard = MutexGuard<'this, T>;
    }
    #[cfg_attr(doc_nightly, doc(cfg(feature = "loom")))]
    unsafe impl<T> Lock for Mutex<T> {
        fn lock_exclusive(&self) -> <Self as lock::Lifetime<'_>>::ExclusiveGuard {
            self.lock().unwrap()
        }
        fn lock_shared(&self) -> <Self as lock::Lifetime<'_>>::SharedGuard {
            self.lock_exclusive()
        }
    }

    #[cfg_attr(doc_nightly, doc(cfg(feature = "loom")))]
    impl<'this, T> lock::Lifetime<'this> for RwLock<T> {
        type ExclusiveGuard = RwLockWriteGuard<'this, T>;
        type SharedGuard = RwLockReadGuard<'this, T>;
    }
    #[cfg_attr(doc_nightly, doc(cfg(feature = "loom")))]
    unsafe impl<T> Lock for RwLock<T> {
        fn lock_exclusive(&self) -> <Self as lock::Lifetime<'_>>::ExclusiveGuard {
            self.write().unwrap()
        }
        fn lock_shared(&self) -> <Self as lock::Lifetime<'_>>::SharedGuard {
            self.read().unwrap()
        }
    }
}

mod bounds {
    #[allow(missing_debug_implementations)]
    pub struct Bounds<T>(T);
    pub trait Sealed {}
    impl<T> Sealed for Bounds<T> {}
}
