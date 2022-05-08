//! This crate provides `WaitList`, the most fundamental type for async synchronization. `WaitList`
//! is implemented as an intrusive linked list of futures.
//!
//! # Feature flags
//!
//! - `std`: Implements the `Lock` traits on locks from the standard library.
//! - `lock_api_04`: Implements the `Lock` traits on locks from [`lock_api`] v0.4. This enables
//! integration of crates like [`parking_lot`], [`spin`] and [`usync`].
//!
//! # Example
//!
//! A thread-safe unfair async mutex.
//!
//! ```
//! use std::cell::UnsafeCell;
//! use std::ops::Deref;
//! use std::ops::DerefMut;
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
//!     pub async fn lock(&self) -> Guard<'_, T> {
//!         loop {
//!             wait_list::await_send_after_poll!({
//!                 let mut waiters = self.waiters.lock_exclusive();
//!
//!                 if !*waiters.guard {
//!                     *waiters.guard = true;
//!                     return Guard { mutex: self };
//!                 }
//!
//!                 waiters.wait_hrtb((), |mut list, ()| { let _ = list.wake_one(()); })
//!             });
//!         }
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

use core::cell::UnsafeCell;
use core::fmt;
use core::fmt::Debug;
use core::fmt::Formatter;
use core::future::Future;
use core::mem;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::pin::Pin;
use core::ptr::NonNull;
use core::task;
use core::task::Poll;
use pin_project_lite::pin_project;
use pinned_aliasable::Aliasable;

pub mod lock;
#[doc(no_inline)]
pub use lock::Lock;

mod send_after_poll;
pub use send_after_poll::SendAfterPoll;

// Not public API.
#[doc(hidden)]
pub mod __private {
    pub use crate::send_after_poll::private as send_after_poll;
}

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
    /// If your locks are thread-safe but their guard types are `!Send` (e.g. [`std::sync::Mutex`]
    /// or `parking_lot`'s mutex without the `send_guard` feature) then the returned future will
    /// also not be `Send` because it takes ownership of a mutex guard type. However, you can still
    /// have futures that contain it be `Send`, as long as you await it using the
    /// [`await_send_after_poll!`] macro instead of with `.await`.
    pub fn wait<OnCancel>(
        self,
        input: I,
        on_cancel: OnCancel,
    ) -> Wait<'wait_list, L, I, O, OnCancel>
    where
        OnCancel: FnOnce(LockedExclusive<'wait_list, L, I, O>, O),
    {
        Wait {
            state: WaitState::Initial { guard: self, input },
            on_cancel: ManuallyDrop::new(on_cancel),
        }
    }

    /// The exact same as [`wait`], but with a slightly different bound on `OnCancel` that can work
    /// around compiler errors you might encounter sometimes.
    ///
    /// [`wait`]: Self::wait
    pub fn wait_hrtb<OnCancel>(
        self,
        input: I,
        on_cancel: OnCancel,
    ) -> Wait<'wait_list, L, I, O, OnCancel>
    where
        OnCancel: for<'a> FnOnce(LockedExclusive<'a, L, I, O>, O),
    {
        self.wait(input, on_cancel)
    }

    /// Add a waiter node to the end of this linked list.
    ///
    /// # Safety
    ///
    /// - `waiter` must be the only reference to that object.
    /// - `waiter` must be a valid pointer until it is removed.
    unsafe fn enqueue(&mut self, waiter: &UnsafeCell<Waiter<I, O>>) {
        let inner = self.inner_mut();

        // Set the previous waiter to the current tail of the queue, if there was one.
        unsafe { &mut *waiter.get() }.prev = inner.tail;

        let waiter_ptr = NonNull::from(waiter);

        // Update the old tail's next pointer
        if let Some(prev) = inner.tail {
            let prev = unsafe { &mut *prev.as_ref().get() };
            debug_assert_eq!(prev.next, None);
            prev.next = Some(waiter_ptr);
        }

        // Set the waiter as the new tail of the linked list
        inner.tail = Some(waiter_ptr);

        // Also set it as the head if there isn't currently a head.
        inner.head.get_or_insert(waiter_ptr);
    }

    /// Wake and dequeue the first waiter in the queue, if there is one.
    ///
    /// Returns ownership of that waiter's input value.
    ///
    /// # Errors
    ///
    /// Returns an error and gives back the given output when there are no wakers in the list.
    pub fn wake_one(&mut self, output: O) -> Result<I, O> {
        let head = match self.head() {
            Some(head) => head,
            None => return Err(output),
        };

        let head_waiter = unsafe { &mut *head.get() };

        // Take the `Waker`, both for later waking and to mark it as woken
        let new_state = WaiterState::Woken {
            output: ManuallyDrop::new(output),
        };
        let (input, waker) = match mem::replace(&mut head_waiter.state, new_state) {
            WaiterState::Waiting { input, waker } => (input, waker),
            WaiterState::Woken { .. } => unreachable!(),
        };

        // Extend the lifetime of `head` so the `self` borrow below doesn't conflict with it.
        // SAFETY: The safety contract of `enqueue` ensures the waiter lives long enough.
        let head = unsafe { NonNull::from(head).as_ref() };

        // Dequeue the first waiter now that it's not necessary to keep it in the queue.
        unsafe { self.dequeue(head) };

        // Wake the waker last, to ensure that if this panics nothing goes wrong.
        waker.wake();

        Ok(input)
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
            None => &mut self.inner_mut().head,
        };
        debug_assert_eq!(*prev_next_pointer, waiter_ptr);
        *prev_next_pointer = next;

        // Update the pointer of the next node, or the queue tail
        let next_prev_pointer = match waiter.next {
            Some(next) => &mut unsafe { &mut *next.as_ref().get() }.prev,
            None => &mut self.inner_mut().tail,
        };
        debug_assert_eq!(*next_prev_pointer, waiter_ptr);
        *next_prev_pointer = prev;
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

/// The future of a waiting operation, created by [`LockedExclusive::wait`].
#[must_use = "futures do nothing unless you `.await` or poll them"]
pub struct Wait<'wait_list, L: Lock, I, O, OnCancel>
where
    OnCancel: FnOnce(LockedExclusive<'wait_list, L, I, O>, O),
{
    /// The state enum of the future.
    state: WaitState<'wait_list, L, I, O>,

    /// The callback to be called when the future has been woken but is cancelled before it could
    /// return `Ready`.
    on_cancel: ManuallyDrop<OnCancel>,
}

#[allow(clippy::type_repetition_in_bounds)]
unsafe impl<'wait_list, L: Lock, I, O, OnCancel> SendAfterPoll
    for Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: FnOnce(LockedExclusive<'wait_list, L, I, O>, O),

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

unsafe impl<'wait_list, L: Lock, I, O, OnCancel> Send for Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: FnOnce(LockedExclusive<'wait_list, L, I, O>, O),

    // First of all, inherit all the bounds from when we are `SendAfterPoll`.
    Self: SendAfterPoll,
    // The additional thing we carry before we are polled is the lock guard, so that must be
    // `Send`.
    <L as lock::Lifetime<'wait_list>>::ExclusiveGuard: Send,
{
}

/// Manual pin-projection because I need `Drop` and don't want to bring in the full `pin-project`.
struct WaitProject<'future, 'wait_list, L: Lock, I, O, OnCancel>
where
    OnCancel: FnOnce(LockedExclusive<'wait_list, L, I, O>, O),
{
    state: Pin<&'future mut WaitState<'wait_list, L, I, O>>,
    on_cancel: &'future mut ManuallyDrop<OnCancel>,
}

impl<'wait_list, L: Lock, I, O, OnCancel> Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: FnOnce(LockedExclusive<'wait_list, L, I, O>, O),
{
    fn project(self: Pin<&mut Self>) -> WaitProject<'_, 'wait_list, L, I, O, OnCancel> {
        let this = unsafe { Pin::into_inner_unchecked(self) };
        WaitProject {
            state: unsafe { Pin::new_unchecked(&mut this.state) },
            on_cancel: &mut this.on_cancel,
        }
    }
}

pin_project! {
    /// The state of a `Wait` future.
    #[project = WaitStateProject]
    #[project_replace = WaitStateProjectReplace]
    enum WaitState<'wait_list, L: Lock, I, O> {
        /// The `Wait` has not been polled yet.
        Initial {
            guard: LockedExclusive<'wait_list, L, I, O>,
            input: I,
        },
        /// We have been polled at least once and, if we haven't been woken, are still a node in
        /// the linked list.
        Waiting {
            // The list this future is a part of.
            wait_list: &'wait_list WaitList<L, I, O>,

            // The actual alised node in the `WaitList`'s linked list.
            #[pin]
            waiter: Aliasable<UnsafeCell<Waiter<I, O>>>,
        },
        /// We are finished.
        Done,
    }
}

impl<'wait_list, L: Lock, I, O, OnCancel> Future for Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: FnOnce(LockedExclusive<'wait_list, L, I, O>, O),
{
    type Output = (O, LockedExclusive<'wait_list, L, I, O>);

    fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
        let mut state = self.project().state;

        match state.as_mut().project() {
            WaitStateProject::Initial { .. } => {
                // Temporarily insert the `Done` state so we can use the guard and input
                let (mut guard, input) = match state.as_mut().project_replace(WaitState::Done) {
                    WaitStateProjectReplace::Initial { guard, input } => (guard, input),
                    _ => unreachable!(),
                };

                // Construct the new `Waiting` state
                let wait_list = guard.wait_list;
                let waiter = Aliasable::new(UnsafeCell::new(Waiter {
                    next: None,
                    prev: None,
                    state: WaiterState::Waiting {
                        input,
                        waker: cx.waker().clone(),
                    },
                }));
                state.set(WaitState::Waiting { wait_list, waiter });

                // Take a reference to the waiter and enqueue it in the linked list.
                let waiter = match state.project() {
                    WaitStateProject::Waiting { waiter, .. } => waiter,
                    _ => unreachable!(),
                };
                unsafe { guard.enqueue(waiter.as_ref().get()) };

                // Pend, since we've cloned the waker and added it in the list already
                Poll::Pending
            }
            WaitStateProject::Waiting { wait_list, waiter } => {
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
                        Poll::Ready((output, lock))
                    }
                }
            }
            WaitStateProject::Done => panic!("`Wait` polled after completion"),
        }
    }
}

impl<'wait_list, L: Lock, I, O, OnCancel> Drop for Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: FnOnce(LockedExclusive<'wait_list, L, I, O>, O),
{
    fn drop(&mut self) {
        // This is necessary for soundness since we were pinned before in our `poll` function
        let this = unsafe { Pin::new_unchecked(self) };
        let WaitProject { state, on_cancel } = this.project();

        // SAFETY: This is in the destructor, so it is only called once, and we never call it
        // outside here.
        let on_cancel = unsafe { ManuallyDrop::take(on_cancel) };

        match state.project() {
            // No need to do anything if we didn't start to run or have completed.
            WaitStateProject::Initial { .. } | WaitStateProject::Done => {}
            // If we were waiting, we now need to remove ourselves from the linked list so they
            // don't access our freed memory.
            WaitStateProject::Waiting { wait_list, waiter } => {
                // Set up a guard that panics on drop, in order to cause an abort should
                // `lock_exclusive` panic. This is necessary because we absolutely must remove the
                // waiter from the linked list before returning here otherwise we can cause
                // use-after-frees.
                let abort_on_panic = PanicOnDrop;

                let mut list = wait_list.lock_exclusive();

                let waiter = waiter.as_ref().get();

                if let WaiterState::Waiting { .. } = unsafe { &(*waiter.get()).state } {
                    // Dequeue ourselves so we can safely drop everything while no-one references
                    // it.
                    unsafe { list.dequeue(waiter) };
                }

                // Disarm the guard, we no longer need to abort on a panic.
                mem::forget(abort_on_panic);

                if let WaiterState::Woken { output } = unsafe { &mut (*waiter.get()).state } {
                    // We have been woken but were cancelled before our `poll` could handle the
                    // notification. Defer to the user-provided callback to decide what to do.
                    let output = unsafe { ManuallyDrop::take(output) };
                    on_cancel(list, output);
                }
            }
        }
    }
}

impl<'wait_list, L: Lock, I: Debug, O, OnCancel> Debug for Wait<'wait_list, L, I, O, OnCancel>
where
    OnCancel: FnOnce(LockedExclusive<'wait_list, L, I, O>, O),
    L: Debug,
    <L as lock::Lifetime<'wait_list>>::ExclusiveGuard: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &self.state {
            WaitState::Initial { guard, input } => f
                .debug_struct("Wait::Initial")
                .field("guard", guard)
                .field("input", input)
                .finish(),
            WaitState::Waiting {
                wait_list,
                waiter: _,
            } => f
                .debug_struct("Wait::Waiting")
                .field("wait_list", wait_list)
                .finish(),
            WaitState::Done => f.pad("Wait::Done"),
        }
    }
}

struct PanicOnDrop;
impl Drop for PanicOnDrop {
    fn drop(&mut self) {
        panic!();
    }
}

#[cfg(test)]
#[cfg(feature = "std")]
mod tests {
    use super::await_send_after_poll;
    use super::WaitList;
    use crate::lock;
    use crate::lock::Lock;
    use crate::test_util::AssertNotSend;
    use crate::test_util::AssertSend;
    use alloc::boxed::Box;
    use core::future::Future;
    use core::mem;
    use core::ptr;
    use core::task;
    use core::task::Poll;
    use std::sync::Mutex;

    // Never type, but it's actually latin letter retroflex click
    #[derive(Debug, PartialEq)]
    enum ǃ {}

    #[test]
    fn send_futures() {
        let list = <WaitList<Mutex<()>, (), ǃ>>::default();
        async { await_send_after_poll!(list.lock_exclusive().wait((), no_cancel)) }.assert_send();
        async { list.lock_exclusive().wait((), no_cancel).await }.assert_not_send();
    }

    #[test]
    fn not_send_futures() {
        let list = <WaitList<crate::lock::Local<()>, (), ǃ>>::default();
        async { await_send_after_poll!(list.lock_exclusive().wait((), no_cancel)) }
            .assert_not_send();
    }

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
        let mut future = Box::pin(list.lock_exclusive().wait(Box::new(5), no_cancel));
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

        let mut future = Box::pin(list.lock_exclusive().wait(Box::new(5), no_cancel));
        assert!(future.as_mut().poll(cx).is_pending());

        assert_eq!(*list.lock_exclusive().wake_one(Box::new(6)).unwrap(), 5);
        assert_eq!(
            future.as_mut().poll(cx).map(|(output, _)| output),
            Poll::Ready(Box::new(6))
        );
        assert!(list.lock_shared().is_empty());
    }

    #[test]
    fn wake_multiple() {
        let cx = &mut noop_cx();

        let list = <WaitList<lock::Local<()>, Box<u8>, Box<u32>>>::default();

        let mut f1 = Box::pin(list.lock_exclusive().wait(Box::new(1), no_cancel));
        assert!(f1.as_mut().poll(cx).is_pending());

        let mut f2 = Box::pin(list.lock_exclusive().wait(Box::new(2), no_cancel));
        assert!(f2.as_mut().poll(cx).is_pending());

        assert_eq!(*list.lock_exclusive().wake_one(Box::new(11)).unwrap(), 1);

        let mut f3_out = None;
        let mut f3 = Box::pin(
            list.lock_exclusive()
                .wait(Box::new(3), |_, out| f3_out = Some(out)),
        );
        assert!(f3.as_mut().poll(cx).is_pending());

        let mut list = list.lock_exclusive();
        assert_eq!(*list.wake_one(Box::new(12)).unwrap(), 2);
        assert_eq!(*list.wake_one(Box::new(13)).unwrap(), 3);
        assert_eq!(*list.wake_one(Box::new(99)).unwrap_err(), 99);
        drop(list);

        assert_eq!(
            f2.as_mut().poll(cx).map(|(output, _)| output),
            Poll::Ready(Box::new(12))
        );
        assert_eq!(
            f1.as_mut().poll(cx).map(|(output, _)| output),
            Poll::Ready(Box::new(11))
        );
        drop(f3);
        assert_eq!(f3_out, Some(Box::new(13)));
    }

    #[test]
    fn drop_in_middle() {
        let cx = &mut noop_cx();

        let list = <WaitList<lock::Local<()>, Box<u32>, ǃ>>::default();

        let mut f1 = Box::pin(list.lock_exclusive().wait(Box::new(1), no_cancel));
        assert!(f1.as_mut().poll(cx).is_pending());

        let mut f2 = Box::pin(list.lock_exclusive().wait(Box::new(2), no_cancel));
        assert!(f2.as_mut().poll(cx).is_pending());

        let mut f3 = Box::pin(list.lock_exclusive().wait(Box::new(3), no_cancel));
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

        let mut f1 = Box::pin(
            list.lock_exclusive()
                .wait(Box::new(1), |mut list, mut output| {
                    *output += 1;
                    assert_eq!(*list.wake_one(output).unwrap(), 2);
                }),
        );
        assert!(f1.as_mut().poll(cx).is_pending());

        let mut f2 = Box::pin(
            list.lock_exclusive()
                .wait(Box::new(2), |mut list, mut output| {
                    *output += 1;
                    assert_eq!(*list.wake_one(output).unwrap(), 3);
                }),
        );
        assert!(f2.as_mut().poll(cx).is_pending());

        let mut final_output = None;

        let mut f3 = Box::pin(list.lock_exclusive().wait(Box::new(3), |list, output| {
            assert!(list.is_empty());
            final_output = Some(output);
        }));
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
        static WAKER: task::Waker = unsafe { mem::transmute::<task::RawWaker, task::Waker>(RAW) };

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
