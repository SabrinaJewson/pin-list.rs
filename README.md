# wait-list

This crate has been deprecated in favour of [`pin-list`](https://docs.rs/pin-list)!
If you want to get the crate name for something else, please do not hesitate to [contact me] or
email <help@crates.io>.

[contact me]: https://sabrinajewson.org/

Original readme below:

This crate provides `WaitList`, the most fundamental type for async synchronization. `WaitList`
is implemented as an intrusive linked list of futures.

## Feature flags

- `std`: Implements the `Lock` traits on locks from the standard library.
- `lock_api_04`: Implements the `Lock` traits on locks from [`lock_api`] v0.4. This enables
integration of crates like [`parking_lot`], [`spin`] and [`usync`].
- `loom_05`: Implements the `Lock` traits on locks from [`loom`] v0.5.

## Example

A thread-safe unfair async mutex.

```rust
use pin_project_lite::pin_project;
use std::cell::UnsafeCell;
use std::future::Future;
use std::ops::Deref;
use std::ops::DerefMut;
use std::pin::Pin;
use std::task;
use std::task::Poll;
use wait_list::WaitList;

pub struct Mutex<T> {
    data: UnsafeCell<T>,
    waiters: WaitList<std::sync::Mutex<bool>, (), ()>,
}

unsafe impl<T> Sync for Mutex<T> {}

impl<T> Mutex<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: UnsafeCell::new(data),
            waiters: WaitList::new(std::sync::Mutex::new(false)),
        }
    }
    pub fn lock(&self) -> Lock<'_, T> {
        Lock {
            mutex: self,
            inner: wait_list::Wait::new(),
        }
    }
}

pin_project! {
    pub struct Lock<'mutex, T> {
        mutex: &'mutex Mutex<T>,
        #[pin]
        inner: wait_list::Wait<'mutex, std::sync::Mutex<bool>, (), (), TryForward>,
    }
}

impl<'mutex, T> Future for Lock<'mutex, T> {
    type Output = Guard<'mutex, T>;
    fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
        let mut this = self.project();

        let mut waiters = if this.inner.as_ref().is_completed() {
            // If we haven't initialized the future yet, lock the mutex for the first time
            this.mutex.waiters.lock_exclusive()
        } else {
            // Otherwise, wait for us to be woken
            match this.inner.as_mut().poll(cx) {
                Poll::Ready((waiters, ())) => waiters,
                Poll::Pending => return Poll::Pending,
            }
        };

        // If the mutex is unlocked, mark it as locked and return the guard
        if !*waiters.guard {
            *waiters.guard = true;
            return Poll::Ready(Guard { mutex: this.mutex });
        }

        // Otherwise, re-register ourselves to be woken when the mutex is unlocked again
        this.inner.init(cx.waker().clone(), &mut waiters, (), TryForward);
        Poll::Pending
    }
}

/// When the future is cancelled before the mutex guard can be taken, wake up the next waiter.
struct TryForward;
impl<'wait_list> wait_list::CancelCallback<'wait_list, std::sync::Mutex<bool>, (), ()>
    for TryForward
{
    fn on_cancel(
        self,
        mut list: wait_list::LockedExclusive<'wait_list, std::sync::Mutex<bool>, (), ()>,
        output: (),
    ) {
        let _ = list.wake_one(());
    }
}

pub struct Guard<'mutex, T> {
    mutex: &'mutex Mutex<T>,
}

impl<T> Deref for Guard<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.mutex.data.get() }
    }
}
impl<T> DerefMut for Guard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.mutex.data.get() }
    }
}

impl<T> Drop for Guard<'_, T> {
    fn drop(&mut self) {
        let mut waiters = self.mutex.waiters.lock_exclusive();
        *waiters.guard = false;
        let _ = waiters.wake_one(());
    }
}
#
```

[`lock_api`]: https://docs.rs/lock_api
[`parking_lot`]: https://docs.rs/parking_lot
[`spin`]: https://docs.rs/spin
[`usync`]: https://docs.rs/usync
[`loom`]: https://docs.rs/loom

License: MIT
