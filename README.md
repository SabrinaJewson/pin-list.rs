# pin-list

This crate provides `PinList`, a safe `Pin`-based intrusive doubly linked list.

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
use pin_list::PinList;

type PinListTypes = dyn pin_list::Types<
    Id = pin_list::id::Checked,
    Protected = task::Waker,
    Removed = (),
    Unprotected = (),
>;

pub struct Mutex<T> {
    data: UnsafeCell<T>,
    inner: std::sync::Mutex<Inner>,
}

struct Inner {
    locked: bool,
    waiters: PinList<PinListTypes>,
}

unsafe impl<T> Sync for Mutex<T> {}

impl<T> Mutex<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: UnsafeCell::new(data),
            inner: std::sync::Mutex::new(Inner {
                locked: false,
                waiters: PinList::new(pin_list::id::Checked::new()),
            }),
        }
    }
    pub fn lock(&self) -> Lock<'_, T> {
        Lock {
            mutex: self,
            node: pin_list::Node::new(),
        }
    }
}

pin_project! {
    pub struct Lock<'mutex, T> {
        mutex: &'mutex Mutex<T>,
        #[pin]
        node: pin_list::Node<PinListTypes>,
    }

    impl<T> PinnedDrop for Lock<'_, T> {
        fn drop(this: Pin<&mut Self>) {
            let this = this.project();
            let node = match this.node.initialized_mut() {
                // The future was cancelled before it could complete.
                Some(initialized) => initialized,
                // The future has completed already (or hasn't started); we don't have to do
                // anything.
                None => return,
            };

            let mut inner = this.mutex.inner.lock().unwrap();

            match node.reset(&mut inner.waiters) {
                // If we've cancelled the future like usual, just do that.
                (pin_list::NodeData::Linked(_waker), ()) => {}

                // Otherwise, we have been woken but aren't around to take the lock. To
                // prevent deadlocks, pass the notification on to someone else.
                (pin_list::NodeData::Removed(()), ()) => {
                    if let Ok(waker) = inner.waiters.cursor_front_mut().remove_current(()) {
                        drop(inner);
                        waker.wake();
                    }
                }
            }
        }
    }
}

impl<'mutex, T> Future for Lock<'mutex, T> {
    type Output = Guard<'mutex, T>;
    fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
        let mut this = self.project();

        let mut inner = this.mutex.inner.lock().unwrap();

        if let Some(mut node) = this.node.as_mut().initialized_mut() {
            // Check whether we've been woken up, only continuing if so.
            if let Err(node) = node.take_removed(&inner.waiters) {
                // If we haven't been woken, re-register our waker and pend.
                *node.protected_mut(&mut inner.waiters).unwrap() = cx.waker().clone();
                return Poll::Pending;
            }
        }

        // If the mutex is unlocked, mark it as locked and return the guard
        if !inner.locked {
            inner.locked = true;
            return Poll::Ready(Guard { mutex: this.mutex });
        }

        // Otherwise, re-register ourselves to be woken when the mutex is unlocked again
        inner.waiters.push_back(this.node, cx.waker().clone(), ());

        Poll::Pending
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
        let mut inner = self.mutex.inner.lock().unwrap();
        inner.locked = false;

        if let Ok(waker) = inner.waiters.cursor_front_mut().remove_current(()) {
            drop(inner);
            waker.wake();
        }
    }
}
#
```

License: MIT
