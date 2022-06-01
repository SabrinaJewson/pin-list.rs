//! Unique IDs.

use crate::util::ConstFnBounds;
use core::fmt::Debug;

/// A marker trait for any type that functions as an ID.
///
/// # Safety
///
/// It must not be possible to create an arbitrary ID that is equal to one that already exists
/// without cloning that exact ID.
pub unsafe trait Id: Sized + Copy + PartialEq + Eq + Debug {}

/// A wrapper around an ID that asserts it is unique.
///
/// This takes away the implementation of [`Copy`] and [`Clone`] for an ID and forbids access to
/// the underlying ID.
#[derive(Debug, PartialEq, Eq)]
pub struct Unique<I: Id> {
    id: I,
}

impl<I> Unique<I>
where
    <I as ConstFnBounds>::Type: Id,
{
    /// Create a new `Unique`, asserting that the given ID contained within is unique.
    ///
    /// # Safety
    ///
    /// The given `id` must be unique at the time of calling this function.
    pub const unsafe fn new(id: I) -> Self {
        Self { id }
    }

    /// Take the inner ID out of this [`Unique`], taking away the uniqueness guarantee.
    #[must_use]
    pub const fn into_inner(self) -> I {
        self.id
    }
}

// SAFETY: `Unique<I>` functions as a `SyncWrapper`
unsafe impl<I: Id> Sync for Unique<I> {}

mod checked {
    use super::Id;
    use super::Unique;
    use core::num::NonZeroU64;
    use core::sync::atomic;
    use core::sync::atomic::AtomicU64;

    /// An allocator of IDs that uses a global atomic `u64` counter.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Checked(NonZeroU64);

    impl Checked {
        /// Allocate a new ID.
        #[must_use]
        pub fn new() -> Unique<Self> {
            static COUNTER: AtomicU64 = AtomicU64::new(1);
            const MAX_ID: u64 = u64::MAX >> 1;

            // Use Relaxed because there is no data that depends on this counter.
            let id = COUNTER.fetch_add(1, atomic::Ordering::Relaxed);

            // Ensure overflows don't happen. Abort instead of panicking so it can't be recovered
            // from.
            if id >= MAX_ID {
                crate::util::abort();
            }

            // SAFETY: `COUNTER` starts at one and the above `assert!` ensures that it never
            // overflows.
            let id = Self(unsafe { NonZeroU64::new_unchecked(id) });

            // SAFETY: The counter only increments and never overflows.
            unsafe { Unique::new(id) }
        }
    }

    // SAFETY: `new` can never return two `u64`s with the same value.
    unsafe impl Id for Checked {}
}
pub use checked::Checked;

mod unchecked {
    use super::Id;
    use super::Unique;

    /// An unchecked ID that leaves all the invariants up to the user. This is zero-cost, but
    /// `unsafe` to use.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[non_exhaustive]
    pub struct Unchecked;

    impl Unchecked {
        /// Create a new [`Unchecked`] ID.
        ///
        /// # Safety
        ///
        /// The returned ID must not be compared against any other `Unchecked` IDs that originated
        /// from a different call to this function.
        #[must_use]
        pub const unsafe fn new() -> Unique<Self> {
            // SAFETY: Ensured by caller
            unsafe { Unique::new(Self) }
        }
    }

    // SAFETY: Ensured by caller in `Unchecked::new`
    unsafe impl Id for Unchecked {}
}
pub use unchecked::Unchecked;

mod debug_checked {
    use super::Id;
    use super::Unique;
    use crate::id;

    /// Equivalent to [`id::Checked`] when `debug_assertions` are enabled, but equivalent to
    /// [`id::Unchecked`] in release.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct DebugChecked {
        #[cfg(debug_assertions)]
        checked: id::Checked,
    }

    impl DebugChecked {
        /// Create a new [`DebugChecked`]. With `debug_assertions` enabled, this will increment a
        /// global atomic counter. In release, this is a no-op.
        ///
        /// # Safety
        ///
        /// The returned ID must not be compared against any other `DebugChecked` IDs that
        /// originated from a different call to this function.
        ///
        /// Note that this function is completely safe to use when `debug_assertions` are enabled,
        /// although it still requires `unsafe` due to the behaviour in release.
        #[must_use]
        pub unsafe fn new() -> Unique<Self> {
            let this = Self {
                #[cfg(debug_assertions)]
                checked: id::Checked::new().into_inner(),
            };
            // SAFETY: Ensured by callera
            unsafe { Unique::new(this) }
        }
    }

    // SAFETY: Ensured by caller in `DebugChecked::new`
    unsafe impl Id for DebugChecked {}
}
pub use debug_checked::DebugChecked;

mod lifetime {
    use super::Id;
    use super::Unique;
    use core::marker::PhantomData;

    /// A fully statically checked ID based on invariant lifetimes and HRTBs.
    ///
    /// This is the same technique as used by `GhostCell`. While theoretically the best option
    /// (being both safe and zero-cost), its infectious nature makes it not very useful in practice.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Lifetime<'id> {
        invariant: PhantomData<fn(&'id ()) -> &'id ()>,
    }

    impl Lifetime<'_> {
        /// Create a new lifetime-based ID usable in a specific scope.
        pub fn scope<O, F>(f: F) -> O
        where
            F: for<'id> FnOnce(Unique<Lifetime<'id>>) -> O,
        {
            f(unsafe {
                Unique::new(Lifetime {
                    invariant: PhantomData,
                })
            })
        }
    }

    unsafe impl Id for Lifetime<'_> {}
}
pub use lifetime::Lifetime;
