//! This crate provides `WaitList`, the most fundamental type for async synchronization. `WaitList`
//! is implemented as an intrusive linked list of futures.
//!
//! # Feature flags
//!
//! - `std`: Implements the `Lock` traits on locks from the standard library.
//! - `lock_api_04`: Implements the `Lock` traits on locks from [`lock_api`] v0.4. This enables
//! integration of crates like [`parking_lot`], [`spin`] and [`usync`].
//! - `loom_05`: Implements the `Lock` traits on locks from [`loom`] v0.5.
//!
//! # Example
//!
//! A thread-safe unfair async mutex.
//!
//! ```
//! use pin_project_lite::pin_project;
//! use std::cell::UnsafeCell;
//! use std::future::Future;
//! use std::ops::Deref;
//! use std::ops::DerefMut;
//! use std::pin::Pin;
//! use std::task;
//! use std::task::Poll;
//! use wait_list::WaitList;
//!
//! pub struct Mutex<T> {
//!     data: UnsafeCell<T>,
//!     waiters: WaitList<std::sync::Mutex<bool>, (), ()>,
//! }
//!
//! unsafe impl<T> Sync for Mutex<T> {}
//!
//! impl<T> Mutex<T> {
//!     pub fn new(data: T) -> Self {
//!         Self {
//!             data: UnsafeCell::new(data),
//!             waiters: WaitList::new(std::sync::Mutex::new(false)),
//!         }
//!     }
//!     pub fn lock(&self) -> Lock<'_, T> {
//!         Lock {
//!             mutex: self,
//!             inner: wait_list::Wait::new(),
//!         }
//!     }
//! }
//!
//! pin_project! {
//!     pub struct Lock<'mutex, T> {
//!         mutex: &'mutex Mutex<T>,
//!         #[pin]
//!         inner: wait_list::Wait<'mutex, std::sync::Mutex<bool>, (), (), TryForward>,
//!     }
//! }
//!
//! impl<'mutex, T> Future for Lock<'mutex, T> {
//!     type Output = Guard<'mutex, T>;
//!     fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
//!         let mut this = self.project();
//!
//!         let mut waiters = if this.inner.as_ref().is_completed() {
//!             // If we haven't initialized the future yet, lock the mutex for the first time
//!             this.mutex.waiters.lock_exclusive()
//!         } else {
//!             // Otherwise, wait for us to be woken
//!             match this.inner.as_mut().poll(cx) {
//!                 Poll::Ready((waiters, ())) => waiters,
//!                 Poll::Pending => return Poll::Pending,
//!             }
//!         };
//!
//!         // If the mutex is unlocked, mark it as locked and return the guard
//!         if !*waiters.guard {
//!             *waiters.guard = true;
//!             return Poll::Ready(Guard { mutex: this.mutex });
//!         }
//!
//!         // Otherwise, re-register ourselves to be woken when the mutex is unlocked again
//!         this.inner.init(cx.waker().clone(), &mut waiters, (), TryForward);
//!         Poll::Pending
//!     }
//! }
//!
//! /// When the future is cancelled before the mutex guard can be taken, wake up the next waiter.
//! struct TryForward;
//! impl<'wait_list> wait_list::CancelCallback<'wait_list, std::sync::Mutex<bool>, (), ()>
//!     for TryForward
//! {
//!     fn on_cancel(
//!         self,
//!         mut list: wait_list::LockedExclusive<'wait_list, std::sync::Mutex<bool>, (), ()>,
//!         output: (),
//!     ) {
//!         let _ = list.wake_one(());
//!     }
//! }
//!
//! pub struct Guard<'mutex, T> {
//!     mutex: &'mutex Mutex<T>,
//! }
//!
//! impl<T> Deref for Guard<'_, T> {
//!     type Target = T;
//!     fn deref(&self) -> &Self::Target {
//!         unsafe { &*self.mutex.data.get() }
//!     }
//! }
//! impl<T> DerefMut for Guard<'_, T> {
//!     fn deref_mut(&mut self) -> &mut Self::Target {
//!         unsafe { &mut *self.mutex.data.get() }
//!     }
//! }
//!
//! impl<T> Drop for Guard<'_, T> {
//!     fn drop(&mut self) {
//!         let mut waiters = self.mutex.waiters.lock_exclusive();
//!         *waiters.guard = false;
//!         let _ = waiters.wake_one(());
//!     }
//! }
//! #
//! # fn assert_send<T: Send>(_: T) {}
//! # let mutex = Mutex::new(());
//! # assert_send(mutex.lock());
//! ```
//!
//! [`lock_api`]: https://docs.rs/lock_api
//! [`parking_lot`]: https://docs.rs/parking_lot
//! [`spin`]: https://docs.rs/spin
//! [`usync`]: https://docs.rs/usync
//! [`loom`]: https://docs.rs/loom
#![warn(
    clippy::pedantic,
    missing_debug_implementations,
    missing_docs,
    noop_method_call,
    trivial_casts,
    trivial_numeric_casts,
    unsafe_op_in_unsafe_fn,
    unused_lifetimes,
    unused_qualifications
)]
#![allow(
    clippy::items_after_statements,
    // `ǃ` (latin letter retroflex click) is used in the tests for a never type
    uncommon_codepoints,
)]
#![no_std]
#![cfg_attr(doc_nightly, feature(doc_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "lock_api_04")]
pub extern crate lock_api_04_crate as lock_api_04;

#[cfg(feature = "loom_05")]
pub extern crate loom_05_crate as loom_05;

use core::cell::UnsafeCell;
use core::fmt;
use core::fmt::Debug;
use core::fmt::Formatter;
use core::future::Future;
use core::mem;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::pin::Pin;
use core::ptr;
use core::ptr::NonNull;
use core::task;
use core::task::Poll;
use pin_project_lite::pin_project;
use pinned_aliasable::Aliasable;

pub mod lock;
#[doc(no_inline)]
pub use lock::Lock;

/// An intrusive linked list of futures.
pub struct WaitList<L: Lock, I, O> {
    /// The lock used by the `WaitList`.
    ///
    /// This is used for internal synchronization, but you can also protect arbitrary state useful
    /// to you in here.
    pub lock: L,

    /// Inner state of the wait list, protected by the above lock.
    inner: UnsafeCell<Inner<I, O>>,
}

unsafe impl<L: Lock, I, O> Send for WaitList<L, I, O>
where
    // - `L` is required to be `Send` because we provide access to it and run its destructor
    // regardless of caller thread.
    // - `L` is not required to be `Sync` because this type holds complete ownership over all `L`s.
    L: Send,
    // - `I` is required to be `Send` because we allow an `&mut Self -> &mut I` conversion, and
    // it's possible to send an `&mut Self` with values inside if a future is leaked.
    // - `I` is not required to be `Sync` because there is no shared access of it between objects.
    I: Send,
    // - `O` is not required to be `Send` because the only situation in which an `O` can be
    // obtained or dropped through this type is in `wait`, which needs multiple shared references
    // to this type to exist.
    // - `O` is not required to be `Sync` because we never deal in `&O`.
    O:,
{
}

unsafe impl<L: Lock, I, O> Sync for WaitList<L, I, O>
where
    // - `L` is not required to be `Send` because we don't allow moving out our `L` from a shared
    // reference.
    // - `L` is required to be `Sync` because we support an `&Self -> &L` conversion: `&self.lock`.
    L: Sync,
    // - `I` is required to be `Send` because its ownership can be transferred between two threads
    // via a `WaitList`, if one thread waits on input and another wakes the first.
    // - `I` is required to be `Sync` because we support an `&Self -> &I` conversion which can be
    // called from multiple threads concurrently (via the shared locks).
    I: Send + Sync,
    // - `O` is required to be `Send` because its ownership can be transferred between threads
    // using an `&Self`.
    // - `O` is not required to be `Sync` because we never deal in `&O`.
    O: Send,
{
}

struct Inner<I, O> {
    /// The head of the queue; the oldest waiter.
    ///
    /// If this is `None`, the list is empty.
    head: Option<NonNull<UnsafeCell<Waiter<I, O>>>>,

    /// The tail of the queue; the newest waiter.
    ///
    /// Whether this is `None` must remain in sync with whether `head` is `None`.
    tail: Option<NonNull<UnsafeCell<Waiter<I, O>>>>,
}

/// A waiter in the above list.
///
/// Each waiter in the list is wrapped in an `UnsafeCell` because there are several places that may
/// hold a reference two it (the linked list and the waiting future). The `UnsafeCell` is guarded
/// by the `WaitList`'s lock.
///
/// Each `Waiter` is stored by its waiting future, and will be automatically removed from the
/// linked list by `dequeue` when the future completes or is cancelled.
struct Waiter<I, O> {
    /// The next waiter in the linked list.
    next: Option<NonNull<UnsafeCell<Waiter<I, O>>>>,

    /// The previous waiter in the linked list.
    prev: Option<NonNull<UnsafeCell<Waiter<I, O>>>>,

    /// The state the waiter is in.
    state: WaiterState<I, O>,
}

enum WaiterState<I, O> {
    /// The waiter has not been woken.
    Waiting { input: I, waker: task::Waker },

    /// The waiter has been woken.
    Woken {
        /// The output value given to `wake_one`. This is `ManuallyDrop` to allow the `Wait` future
        /// to take ownership of it in its destructor.
        output: ManuallyDrop<O>,
    },
}

impl<I, O> Inner<I, O> {
    /// Add a waiter node to the end of this linked list.
    ///
    /// # Safety
    ///
    /// - `waiter` must be the only reference to that object.
    /// - `waiter` must be a valid pointer until it is removed.
    unsafe fn enqueue(&mut self, waiter: &UnsafeCell<Waiter<I, O>>) {
        // Set the previous waiter to the current tail of the queue, if there was one.
        unsafe { &mut *waiter.get() }.prev = self.tail;

        let waiter_ptr = NonNull::from(waiter);

        // Update the old tail's next pointer
        if let Some(prev) = self.tail {
            let prev = unsafe { &mut *prev.as_ref().get() };
            debug_assert_eq!(prev.next, None);
            prev.next = Some(waiter_ptr);
        }

        // Set the waiter as the new tail of the linked list
        self.tail = Some(waiter_ptr);

        // Also set it as the head if there isn't currently a head.
        self.head.get_or_insert(waiter_ptr);
    }

    /// Remove a waiter node from an arbitrary position in the linked list.
    ///
    /// # Safety
    ///
    /// - `waiter` must be a waiter in this queue.
    /// - No other unique references to `waiter` may exist.
    unsafe fn dequeue(&mut self, waiter: &UnsafeCell<Waiter<I, O>>) {
        let waiter_ptr = Some(NonNull::from(waiter));
        let waiter = unsafe { &mut *waiter.get() };

        let prev = waiter.prev;
        let next = waiter.next;

        // Update the pointer of the previous node, or the queue head
        let prev_next_pointer = match waiter.prev {
            Some(prev) => &mut unsafe { &mut *prev.as_ref().get() }.next,
            None => &mut self.head,
        };
        debug_assert_eq!(*prev_next_pointer, waiter_ptr);
        *prev_next_pointer = next;

        // Update the pointer of the next node, or the queue tail
        let next_prev_pointer = match waiter.next {
            Some(next) => &mut unsafe { &mut *next.as_ref().get() }.prev,
            None => &mut self.tail,
        };
        debug_assert_eq!(*next_prev_pointer, waiter_ptr);
        *next_prev_pointer = prev;
    }
}

impl<L, I, O> WaitList<L, I, O>
where
    // workaround for no trait bounds in `const fn`
    <core::iter::Empty<L> as Iterator>::Item: Lock,
{
    /// Create a new empty `WaitList`.
    #[must_use]
    pub const fn new(lock: L) -> Self {
        Self {
            lock,
            inner: UnsafeCell::new(Inner {
                head: None,
                tail: None,
            }),
        }
    }

    /// Take an exclusive lock on the contents of this list.
    ///
    /// This function should not be called recursively as it may deadlock, panic or abort.
    #[must_use]
    pub fn lock_exclusive(&self) -> LockedExclusive<'_, L, I, O> {
        LockedExclusive {
            guard: self.lock.lock_exclusive(),
            common: LockedCommon { wait_list: self },
        }
    }

    /// Take a shared lock on the contents of this list.
    ///
    /// If your chosen lock type only supports exclusive locks, this will take an exclusive lock
    /// instead.
    #[must_use]
    pub fn lock_shared(&self) -> LockedShared<'_, L, I, O> {
        LockedShared {
            guard: self.lock.lock_shared(),
            common: LockedCommon { wait_list: self },
        }
    }
}

impl<L: Lock + Default, I, O> Default for WaitList<L, I, O> {
    fn default() -> Self {
        Self::new(L::default())
    }
}

impl<L: Lock + Debug, I, O> Debug for WaitList<L, I, O> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("WaitList")
            .field("lock", &self.lock)
            .finish()
    }
}

/// An exclusive lock on a [`WaitList`], created by [`WaitList::lock_exclusive`].
pub struct LockedExclusive<'wait_list, L: Lock, I, O> {
    /// The lock guard holding the lock on the `WaitList`.
    ///
    /// You can use this field to access whatever auxiliary locked state you have associated with
    /// the `WaitList`.
    pub guard: <L as lock::Lifetime<'wait_list>>::ExclusiveGuard,

    common: LockedCommon<'wait_list, L, I, O>,
}

impl<'wait_list, L: Lock, I, O> Deref for LockedExclusive<'wait_list, L, I, O> {
    type Target = LockedCommon<'wait_list, L, I, O>;
    fn deref(&self) -> &Self::Target {
        &self.common
    }
}

impl<'wait_list, L: Lock, I, O> LockedExclusive<'wait_list, L, I, O> {
    fn inner_mut(&mut self) -> &mut Inner<I, O> {
        // SAFETY: We have exclusive locked access to the `WaitList`
        unsafe { &mut *self.wait_list.inner.get() }
    }

    /// Retrieve a unique reference to the input given by the head entry in the list, if there is
    /// one.
    #[must_use]
    pub fn head_input_mut(&mut self) -> Option<&mut I> {
        // SAFETY: We have exclusive access, so we can access any entry in the list.
        Some(match unsafe { &mut (*self.head()?.get()).state } {
            WaiterState::Waiting { input, waker: _ } => input,
            WaiterState::Woken { .. } => unreachable!(),
        })
    }

    /// Wait on the list for someone to call [`Self::wake_one`].
    ///
    /// This method takes ownership of `self` so that the lock can be released while the future is
    /// suspended. At the end, ownership of the lock guard is transferred back to the caller.
    ///
    /// A callback must be supplied to call in the event that the future has been woken but was
    /// cancelled before it could complete. You will often want to re-call [`Self::wake_one`] in
    /// this case to pass on the notification to someone else.
    ///
    /// Note that the returned future will not be `Send` if your guard types are `!Send`. To avoid
    /// this problem, use the lower-level [`Wait`] API instead.
    pub fn init_and_wait<OnCancel>(
        self,
        input: I,
        on_cancel: OnCancel,
    ) -> InitAndWait<'wait_list, L, I, O, OnCancel>
    where
        OnCancel: CancelCallback<'wait_list, L, I, O>,
    {
        InitAndWait {
            input: Some(InitAndWaitInput {
                lock: self,
                input,
                on_cancel,
            }),
            inner: Wait::new(),
        }
    }

    /// Pop the first waiter from the front of the queue, if there is one.
    ///
    /// Returns ownership of that waiter's input value and the waker that can be used to wake it.
    ///
    /// It is recommended to only wake the waker when the lock guard is _not_ held, because waking
    /// the waker may attempt to drop the future (if for example the runtime is shutting down)
    /// which would deadlock if the future is registered in `WaitList`.
    ///
    /// # Errors
    ///
    /// Returns an error and gives back the given output when there are no wakers in the list.
    pub fn pop(&mut self, output: O) -> Result<(I, task::Waker), O> {
        let head = match self.inner_mut().head {
            Some(head) => head,
            None => return Err(output),
        };

        let (input, waker) = {
            // SAFETY: We hold an exclusive lock to the list.
            let head_waiter = unsafe { &mut *head.as_ref().get() };

            // Mark the head node's state as done.
            let new_state = WaiterState::Woken {
                output: ManuallyDrop::new(output),
            };
            match mem::replace(&mut head_waiter.state, new_state) {
                WaiterState::Waiting { input, waker } => (input, waker),
                WaiterState::Woken { .. } => unreachable!(),
            }
        };

        // Dequeue the first waiter now that it's not necessary to keep it in the queue.
        unsafe { self.inner_mut().dequeue(head.as_ref()) };

        Ok((input, waker))
    }

    /// Wake and dequeue the first waiter in the queue, if there is one.
    ///
    /// Returns ownership of that waiter's input value.
    ///
    /// This method consumes `self` so we can ensure that the lock guard is freed before calling
    /// `wake` on the waker, to prevent deadlocks.
    ///
    /// # Errors
    ///
    /// Returns an error and gives back the given output when there are no wakers in the list.
    pub fn wake_one(mut self, output: O) -> Result<I, O> {
        let (input, waker) = self.pop(output)?;
        drop(self);
        waker.wake();
        Ok(input)
    }
}

impl<'wait_list, L: Lock + Debug, I, O> Debug for LockedExclusive<'wait_list, L, I, O>
where
    <L as lock::Lifetime<'wait_list>>::ExclusiveGuard: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("LockedExclusive")
            .field("guard", &self.guard)
            .field("common", &self.common)
            .finish()
    }
}

/// A shared lock on a [`WaitList`], created by [`WaitList::lock_shared`].
pub struct LockedShared<'wait_list, L: Lock, I, O> {
    /// The lock guard holding the lock on the `WaitList`.
    pub guard: <L as lock::Lifetime<'wait_list>>::SharedGuard,

    common: LockedCommon<'wait_list, L, I, O>,
}

impl<'wait_list, L: Lock, I, O> Deref for LockedShared<'wait_list, L, I, O> {
    type Target = LockedCommon<'wait_list, L, I, O>;
    fn deref(&self) -> &Self::Target {
        &self.common
    }
}

impl<'wait_list, L: Lock + Debug, I, O> Debug for LockedShared<'wait_list, L, I, O>
where
    <L as lock::Lifetime<'wait_list>>::SharedGuard: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("LockedShared")
            .field("guard", &self.guard)
            .field("common", &self.common)
            .finish()
    }
}

/// Common functions that can work on both exclusive and shared locks.
///
/// You can never create nor hold an instance of this type — it is accessed solely through the
/// `Deref` implementations of [`LockedShared`] and [`LockedExclusive`].
#[non_exhaustive]
pub struct LockedCommon<'wait_list, L: Lock, I, O> {
    /// The list this type locks.
    pub wait_list: &'wait_list WaitList<L, I, O>,
}

impl<'wait_list, L: Lock, I, O> LockedCommon<'wait_list, L, I, O> {
    fn inner(&self) -> &Inner<I, O> {
        // SAFETY: We have at least shared locked access to the `WaitList`
        unsafe { &*self.wait_list.inner.get() }
    }

    fn head(&self) -> Option<&UnsafeCell<Waiter<I, O>>> {
        // SAFETY: The head pointer of the linked list must always be valid.
        Some(unsafe { self.inner().head?.as_ref() })
    }

    /// Check whether there are any futures waiting in this list.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner().head.is_none()
    }

    /// Retrieve a shared reference to the input given by the head entry in the list, if there is
    /// one.
    #[must_use]
    pub fn head_input(&self) -> Option<&I> {
        // SAFETY: We have at least shared locked access, so we can access any entry in the list.
        Some(match unsafe { &(*self.head()?.get()).state } {
            WaiterState::Waiting { input, waker: _ } => input,
            WaiterState::Woken { .. } => unreachable!(),
        })
    }
}

impl<'wait_list, L: Lock + Debug, I, O> Debug for LockedCommon<'wait_list, L, I, O> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("LockedCommon")
            .field("wait_list", &self.wait_list)
            .finish()
    }
}

/// The future of a waiting operation.
///
/// This type provides a lower-level API than [`LockedExclusive::init_and_wait`], but is useful
/// if your guard types are `!Send` but you still want the outer future to remain `Send`.
///
/// Awaiting and polling this future will panic if you have not called [`init`] yet.
///
/// [`init`]: Self::init
#[must_use = "futures do nothing unless you `.await` or poll them"]
pub struct Wait<'wait_list, L: Lock, I, O, OnCancel>
where
    OnCancel: CancelCallback<'wait_list, L, I, O>,
{
    inner: WaitInner<'wait_list, L, I, O, OnCancel>,
}

pin_project! {
    /// `Wait`, but without the bound on `OnCancel` so the `Send` bound doesn't need it. This is
    /// used to work around <https://github.com/rust-lang/rust/issues/96865>.
    struct WaitInner<'wait_list, L: Lock, I, O, OnCancel> {
        #[pin]
        state: WaitState<'wait_list, L, I, O, OnCancel>,
    }
}

unsafe impl<'wait_list, L: Lock, I, O, OnCancel> Send for WaitInner<'wait_list, L, I, O, OnCancel>
where
    // - `L` is not required to be `Send` because we can't move or drop it with just our shared
    // reference to it.
    // - `L` is required to be `Sync` because we access it from a shared reference.
    L: Sync,
    // - `I` is required to be `Send` because we own it and will drop it if we are dropped.
    // - `I` is not required to be `Sync` because we don't ever touch a shared reference to it post
    // placing it in the linked list node; all access to it is done by the `WaitList` itself.
    I: Send,
    // - `O` is required to be `Send` because we can own an instance of it and give back ownership
    // of that instance.
    // - `O` is not required to be `Sync` because we never deal in `&O`.
    O: Send,
    // - `OnCancel` is required to be `Send` because we always own an instance of it.
    // - `OnCancel` is not required to be `Sync` because we never deal in `&OnCancel`.
    OnCancel: Send,
{
}

impl<'wait_list, L: Lock, I, O, OnCancel> Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: CancelCallback<'wait_list, L, I, O>,
{
    /// Manual pin-projection because I need `Drop` and don't want to bring in the full
    /// `pin-project`.
    fn project(self: Pin<&mut Self>) -> Pin<&mut WaitState<'wait_list, L, I, O, OnCancel>> {
        let this = unsafe { Pin::into_inner_unchecked(self) };
        unsafe { Pin::new_unchecked(&mut this.inner) }
            .project()
            .state
    }
}

pin_project! {
    /// The state of a `Wait` future.
    #[project = WaitStateProject]
    #[project_replace = WaitStateProjectReplace]
    enum WaitState<'wait_list, L: Lock, I, O, OnCancel> {
        /// We have been polled at least once and, if we haven't been woken, are still a node in
        /// the linked list.
        Waiting {
            // The list this future is a part of.
            wait_list: &'wait_list WaitList<L, I, O>,

            // The actual alised node in the `WaitList`'s linked list.
            #[pin]
            waiter: Aliasable<UnsafeCell<Waiter<I, O>>>,

            // The callback to be called when the future has been woken but it is cancelled before
            // it could return `Ready`.
            on_cancel: OnCancel,
        },
        /// We are either finished or we haven't been initialized yet.
        Done,
    }
}

impl<'wait_list, L: Lock, I, O, OnCancel> Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: CancelCallback<'wait_list, L, I, O>,
{
    /// Create a new `Wait` future.
    ///
    /// The returned future will be in its "completed" state, so attempting to `.await` it will
    /// panic unless [`init`] is called.
    ///
    /// [`init`]: Self::init
    pub fn new() -> Self {
        Self {
            inner: WaitInner {
                state: WaitState::Done,
            },
        }
    }

    /// Check whether this future is in its completed state or not.
    #[must_use]
    pub fn is_completed(&self) -> bool {
        matches!(self.inner.state, WaitState::Done)
    }

    /// Initialize the future, moving it from a completed to waiting state.
    ///
    /// This function is mostly only useful inside a `poll` function (when you have a `cx`
    /// variable to hand). After calling this, you should return [`Poll::Pending`] as the given
    /// waker has been successfully registered in the wait list.
    ///
    /// A callback must be supplied to call in the event that the future has been woken but was
    /// cancelled before it could complete. You will often want to re-call
    /// [`LockedExclusive::wake_one`] in this case to pass on the notification to someone else.
    ///
    /// # Panics
    ///
    /// Panics if called on a non-completed future.
    pub fn init(
        self: Pin<&mut Self>,
        waker: task::Waker,
        guard: &mut LockedExclusive<'wait_list, L, I, O>,
        input: I,
        on_cancel: OnCancel,
    ) {
        assert!(
            self.as_ref().is_completed(),
            "called `Wait::init` on an incomplete future"
        );

        let mut state = self.project();

        // Construct and set the new `Waiting` state
        let waiter = Aliasable::new(UnsafeCell::new(Waiter {
            next: None,
            prev: None,
            state: WaiterState::Waiting { input, waker },
        }));
        state.set(WaitState::Waiting {
            wait_list: guard.wait_list,
            waiter,
            on_cancel,
        });

        // Take a reference to the waiter and enqueue it in the linked list.
        let waiter = match state.project() {
            WaitStateProject::Waiting { waiter, .. } => waiter,
            WaitStateProject::Done => unreachable!(),
        };
        unsafe { guard.inner_mut().enqueue(waiter.as_ref().get()) };
    }

    /// The same as [`init`] but not requiring a [`task::Waker`], instead substituting in a
    /// temporary no-op waker.
    ///
    /// Using this API is always less efficient than writing a `poll` function manually that calls
    /// [`init`], but it can be useful if you (a) need `Send` futures but have `!Send` mutex guards
    /// and (b) want to stay in an `async` context.
    ///
    /// [`init`]: Self::init
    pub fn init_without_waker(
        self: Pin<&mut Self>,
        guard: &mut LockedExclusive<'wait_list, L, I, O>,
        input: I,
        on_cancel: OnCancel,
    ) {
        self.init(noop_waker(), guard, input, on_cancel);
    }
}

impl<'wait_list, L: Lock, I, O, OnCancel> Future for Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: CancelCallback<'wait_list, L, I, O>,
{
    type Output = (LockedExclusive<'wait_list, L, I, O>, O);

    fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
        let mut state = self.project();

        let (wait_list, waiter) = match state.as_mut().project() {
            WaitStateProject::Waiting {
                wait_list, waiter, ..
            } => (wait_list, waiter),
            WaitStateProject::Done => panic!("`Wait` polled after completion"),
        };

        let lock = wait_list.lock_exclusive();

        // SAFETY: We hold the exclusive lock to the linked list.
        let waiter = unsafe { &mut *waiter.as_ref().get().get() };

        // Check whether we've been woken or not
        match &mut waiter.state {
            // Still waiting, just refresh our waker and pend
            WaiterState::Waiting { waker, .. } => {
                // If necessary, update the waker to the new one.
                if !waker.will_wake(cx.waker()) {
                    *waker = cx.waker().clone();
                }
                Poll::Pending
            }
            // We have been woken! Take the output, set ourselves to the Done state and
            // report that we are ready. Dequeuing has already been managed by the waker.
            WaiterState::Woken { output } => {
                // SAFETY: After this, we set the state to `Done` so that it will never be
                // taken again.
                let output = unsafe { ManuallyDrop::take(output) };
                state.set(WaitState::Done);
                Poll::Ready((lock, output))
            }
        }
    }
}

impl<'wait_list, L: Lock, I, O, OnCancel> Drop for Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: CancelCallback<'wait_list, L, I, O>,
{
    fn drop(&mut self) {
        // This is necessary for soundness since we were pinned before in our `poll` function
        let this = unsafe { Pin::new_unchecked(self) };
        let mut state = this.project();

        match state.as_mut().project() {
            // If we were waiting, we now need to remove ourselves from the linked list so they
            // don't access our freed memory.
            WaitStateProject::Waiting {
                wait_list, waiter, ..
            } => {
                // Set up a guard that panics on drop, in order to cause an abort should
                // `lock_exclusive` panic. This is necessary because we absolutely must remove the
                // waiter from the linked list before returning here otherwise we can cause
                // use-after-frees.
                let abort_on_panic = PanicOnDrop;

                let mut list = wait_list.lock_exclusive();

                let waiter = waiter.as_ref().get();

                // Case 1: We were still waiting before we were cancelled; just remove ourselves
                // from the list and do nothing more.
                if let WaiterState::Waiting { .. } = unsafe { &(*waiter.get()).state } {
                    // Dequeue ourselves so we can safely drop everything while no-one references
                    // it.
                    unsafe { list.inner_mut().dequeue(waiter) };
                }

                // Disarm the guard, we no longer need to abort on a panic.
                mem::forget(abort_on_panic);

                // Case 2: We have been woken but were cancelled before our `poll` could handle
                // the notification. Defer to the user-provided callback to decide what to do.
                if let WaiterState::Woken { output } = unsafe { &mut (*waiter.get()).state } {
                    let output = unsafe { ManuallyDrop::take(output) };

                    let cancel_callback = match state.project_replace(WaitState::Done) {
                        WaitStateProjectReplace::Waiting { on_cancel, .. } => on_cancel,
                        WaitStateProjectReplace::Done => unreachable!(),
                    };
                    cancel_callback.on_cancel(list, output);
                }
            }
            // No need to do anything if we didn't start to run or have completed.
            WaitStateProject::Done => {}
        }
    }
}

impl<'wait_list, L: Lock, I, O, OnCancel> Default for Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: CancelCallback<'wait_list, L, I, O>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<'wait_list, L: Lock, I: Debug, O, OnCancel> Debug for Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: CancelCallback<'wait_list, L, I, O>,
    L: Debug,
    <L as lock::Lifetime<'wait_list>>::ExclusiveGuard: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &self.inner.state {
            WaitState::Waiting { wait_list, .. } => f
                .debug_struct("Wait::Waiting")
                .field("wait_list", wait_list)
                .finish(),
            WaitState::Done => f.pad("Wait::Done"),
        }
    }
}

pin_project! {
    /// A future that both initializes and waits on a [`WaitList`], created by
    /// [`LockedExclusive::init_and_wait`].
    #[must_use = "futures do nothing unless you `.await` or poll them"]
    pub struct InitAndWait<'wait_list, L: Lock, I, O, OnCancel>
    where
        OnCancel: CancelCallback<'wait_list, L, I, O>,
    {
        input: Option<InitAndWaitInput<'wait_list, L, I, O, OnCancel>>,
        #[pin]
        inner: Wait<'wait_list, L, I, O, OnCancel>,
    }
}

impl<'wait_list, L: Lock, I, O, OnCancel> Future for InitAndWait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: CancelCallback<'wait_list, L, I, O>,
{
    type Output = (LockedExclusive<'wait_list, L, I, O>, O);
    fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
        let this = self.project();

        if let Some(InitAndWaitInput {
            mut lock,
            input,
            on_cancel,
        }) = this.input.take()
        {
            this.inner
                .init(cx.waker().clone(), &mut lock, input, on_cancel);
            Poll::Pending
        } else {
            this.inner.poll(cx)
        }
    }
}

impl<'wait_list, L: Lock, I, O, OnCancel> Debug for InitAndWait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: CancelCallback<'wait_list, L, I, O>,
    <L as lock::Lifetime<'wait_list>>::ExclusiveGuard: Debug,
    I: Debug,
    L: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(input) = &self.input {
            f.debug_struct("InitAndWait::Initial")
                .field("lock", &input.lock)
                .field("input", &input.input)
                .finish()
        } else {
            f.debug_struct("InitAndWait::Waiting")
                .field("inner", &self.inner)
                .finish()
        }
    }
}

struct InitAndWaitInput<'wait_list, L: Lock, I, O, OnCancel> {
    lock: LockedExclusive<'wait_list, L, I, O>,
    input: I,
    on_cancel: OnCancel,
}

/// A callback that is called in the event that the future has been woken but was cancelled before
/// it could complete.
///
/// This trait is implemented for all functions and closures that accept a
/// `LockedExclusive<'wait_list, L, I, O>` and an `O`, but is also available as a separate trait so
/// you can implement it on concrete types.
pub trait CancelCallback<'wait_list, L: Lock, I, O>: Sized {
    /// Called when the future has been woken but was cancelled before it could complete.
    ///
    /// It is given an exclusive lock to the associated [`WaitList`] as well as the output value
    /// that was not yielded by the future.
    fn on_cancel(self, list: LockedExclusive<'wait_list, L, I, O>, output: O);
}

impl<'wait_list, L: Lock, I, O, F> CancelCallback<'wait_list, L, I, O> for F
where
    L: 'wait_list,
    I: 'wait_list,
    O: 'wait_list,
    F: FnOnce(LockedExclusive<'wait_list, L, I, O>, O),
{
    fn on_cancel(self, list: LockedExclusive<'wait_list, L, I, O>, output: O) {
        self(list, output);
    }
}

struct PanicOnDrop;
impl Drop for PanicOnDrop {
    fn drop(&mut self) {
        panic!();
    }
}

const fn noop_waker() -> task::Waker {
    const VTABLE: task::RawWakerVTable = task::RawWakerVTable::new(
        // clone
        |_| RAW,
        // wake
        |_| {},
        // wake_by_ref
        |_| {},
        // drop
        |_| {},
    );
    const RAW: task::RawWaker = task::RawWaker::new(ptr::null(), &VTABLE);

    // SAFETY: `Waker` is `#[repr(transparent)]` over `RawWaker`
    unsafe { mem::transmute::<task::RawWaker, task::Waker>(RAW) }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::WaitList;
    use crate::lock;
    use crate::lock::Lock;
    use alloc::boxed::Box;
    use core::future::Future;
    use core::task;
    use core::task::Poll;

    // Never type, but it's actually latin letter retroflex click
    #[derive(Debug, PartialEq)]
    enum ǃ {}

    #[test]
    fn wake_empty() {
        let list = <WaitList<lock::Local<()>, ǃ, Box<u32>>>::default();
        assert_eq!(*list.lock_exclusive().wake_one(Box::new(1)).unwrap_err(), 1);
        assert_eq!(*list.lock_exclusive().wake_one(Box::new(2)).unwrap_err(), 2);
        assert_eq!(list.lock_exclusive().head_input(), None);
        assert_eq!(list.lock_exclusive().head_input_mut(), None);
        assert!(list.lock_shared().is_empty());
    }

    #[test]
    fn cancel() {
        let cx = &mut noop_cx();

        let list = <WaitList<lock::Local<()>, Box<u32>, ǃ>>::default();
        let mut future = Box::pin(list.lock_exclusive().init_and_wait(Box::new(5), no_cancel));
        for _ in 0..10 {
            assert!(future.as_mut().poll(cx).is_pending());
        }
        assert_eq!(**list.lock_exclusive().head_input().unwrap(), 5);
        assert!(!list.lock_shared().is_empty());
        drop(future);
        assert_eq!(list.lock_exclusive().head_input(), None);
        assert!(list.lock_shared().is_empty());
    }

    #[test]
    fn wake_single() {
        let cx = &mut noop_cx();

        let list = <WaitList<lock::Local<()>, Box<u8>, Box<u32>>>::default();

        let mut future = Box::pin(list.lock_exclusive().init_and_wait(Box::new(5), no_cancel));
        assert!(future.as_mut().poll(cx).is_pending());

        assert_eq!(*list.lock_exclusive().wake_one(Box::new(6)).unwrap(), 5);
        assert_eq!(
            future.as_mut().poll(cx).map(|(_, output)| output),
            Poll::Ready(Box::new(6))
        );
        assert!(list.lock_shared().is_empty());
    }

    #[test]
    fn wake_multiple() {
        let cx = &mut noop_cx();

        let list = <WaitList<lock::Local<()>, Box<u8>, Box<u32>>>::default();

        let mut f1 = Box::pin(list.lock_exclusive().init_and_wait(Box::new(1), no_cancel));
        assert!(f1.as_mut().poll(cx).is_pending());

        let mut f2 = Box::pin(list.lock_exclusive().init_and_wait(Box::new(2), no_cancel));
        assert!(f2.as_mut().poll(cx).is_pending());

        assert_eq!(*list.lock_exclusive().wake_one(Box::new(11)).unwrap(), 1);

        let mut f3_out = None;
        let mut f3 = Box::pin(
            list.lock_exclusive()
                .init_and_wait(Box::new(3), |_, out| f3_out = Some(out)),
        );
        assert!(f3.as_mut().poll(cx).is_pending());

        assert_eq!(*list.lock_exclusive().wake_one(Box::new(12)).unwrap(), 2);
        assert_eq!(*list.lock_exclusive().wake_one(Box::new(13)).unwrap(), 3);
        assert_eq!(*list.lock_exclusive().wake_one(Box::new(9)).unwrap_err(), 9);

        assert_eq!(
            f2.as_mut().poll(cx).map(|(_, output)| output),
            Poll::Ready(Box::new(12))
        );
        assert_eq!(
            f1.as_mut().poll(cx).map(|(_, output)| output),
            Poll::Ready(Box::new(11))
        );
        drop(f3);
        assert_eq!(f3_out, Some(Box::new(13)));
    }

    #[test]
    fn drop_in_middle() {
        let cx = &mut noop_cx();

        let list = <WaitList<lock::Local<()>, Box<u32>, ǃ>>::default();

        let mut f1 = Box::pin(list.lock_exclusive().init_and_wait(Box::new(1), no_cancel));
        assert!(f1.as_mut().poll(cx).is_pending());

        let mut f2 = Box::pin(list.lock_exclusive().init_and_wait(Box::new(2), no_cancel));
        assert!(f2.as_mut().poll(cx).is_pending());

        let mut f3 = Box::pin(list.lock_exclusive().init_and_wait(Box::new(3), no_cancel));
        assert!(f3.as_mut().poll(cx).is_pending());

        drop(f2);
        drop(f3);
        drop(f1);

        assert!(list.lock_shared().is_empty());
    }

    #[test]
    fn cancellation_waking_chain() {
        let cx = &mut noop_cx();

        let list = <WaitList<lock::Local<()>, Box<u8>, Box<u32>>>::default();

        let mut f1 = Box::pin(list.lock_exclusive().init_and_wait(
            Box::new(1),
            |list: crate::LockedExclusive<_, Box<u8>, _>, mut output: Box<u32>| {
                *output += 1;
                assert_eq!(*list.wake_one(output).unwrap(), 2);
            },
        ));
        assert!(f1.as_mut().poll(cx).is_pending());

        let mut f2 = Box::pin(list.lock_exclusive().init_and_wait(
            Box::new(2),
            |list: crate::LockedExclusive<_, Box<u8>, _>, mut output: Box<u32>| {
                *output += 1;
                assert_eq!(*list.wake_one(output).unwrap(), 3);
            },
        ));
        assert!(f2.as_mut().poll(cx).is_pending());

        let mut final_output = None;

        let mut f3 = Box::pin(list.lock_exclusive().init_and_wait(
            Box::new(3),
            |list: crate::LockedExclusive<_, Box<u8>, _>, output| {
                assert!(list.is_empty());
                final_output = Some(output);
            },
        ));
        assert!(f3.as_mut().poll(cx).is_pending());

        assert_eq!(*list.lock_exclusive().wake_one(Box::new(12)).unwrap(), 1);

        drop(f1);
        drop(f2);
        drop(f3);

        assert_eq!(final_output, Some(Box::new(14)));
    }

    fn no_cancel<L: Lock, I, O>(_: crate::LockedExclusive<'_, L, I, O>, _: O) {
        panic!("did not expect cancellation")
    }

    fn noop_cx() -> task::Context<'static> {
        static WAKER: task::Waker = crate::noop_waker();
        task::Context::from_waker(&WAKER)
    }
}

#[cfg(test)]
mod test_util {
    pub(crate) trait AssertSend {
        fn assert_send(&self) {}
    }
    impl<T: ?Sized + Send> AssertSend for T {}

    pub(crate) trait AssertNotSend<A> {
        fn assert_not_send(&self) {}
    }
    impl<T: ?Sized> AssertNotSend<()> for T {}
    impl<T: ?Sized + Send> AssertNotSend<u8> for T {}
}
