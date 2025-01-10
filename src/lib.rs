//! This crate provides `PinList`, a safe `Pin`-based intrusive doubly linked list.
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
//! use pin_list::PinList;
//!
//! type PinListTypes = dyn pin_list::Types<
//!     Id = pin_list::id::Checked,
//!     Protected = task::Waker,
//!     Removed = (),
//!     Unprotected = (),
//! >;
//!
//! pub struct Mutex<T> {
//!     data: UnsafeCell<T>,
//!     inner: std::sync::Mutex<Inner>,
//! }
//!
//! struct Inner {
//!     locked: bool,
//!     waiters: PinList<PinListTypes>,
//! }
//!
//! unsafe impl<T> Sync for Mutex<T> {}
//!
//! impl<T> Mutex<T> {
//!     pub fn new(data: T) -> Self {
//!         Self {
//!             data: UnsafeCell::new(data),
//!             inner: std::sync::Mutex::new(Inner {
//!                 locked: false,
//!                 waiters: PinList::new(pin_list::id::Checked::new()),
//!             }),
//!         }
//!     }
//!     pub fn lock(&self) -> Lock<'_, T> {
//!         Lock {
//!             mutex: self,
//!             node: pin_list::Node::new(),
//!         }
//!     }
//! }
//!
//! pin_project! {
//!     pub struct Lock<'mutex, T> {
//!         mutex: &'mutex Mutex<T>,
//!         #[pin]
//!         node: pin_list::Node<PinListTypes>,
//!     }
//!
//!     impl<T> PinnedDrop for Lock<'_, T> {
//!         fn drop(this: Pin<&mut Self>) {
//!             let this = this.project();
//!             let node = match this.node.initialized_mut() {
//!                 // The future was cancelled before it could complete.
//!                 Some(initialized) => initialized,
//!                 // The future has completed already (or hasn't started); we don't have to do
//!                 // anything.
//!                 None => return,
//!             };
//!
//!             let mut inner = this.mutex.inner.lock().unwrap();
//!
//!             match node.reset(&mut inner.waiters) {
//!                 // If we've cancelled the future like usual, just do that.
//!                 (pin_list::NodeData::Linked(_waker), ()) => {}
//!
//!                 // Otherwise, we have been woken but aren't around to take the lock. To
//!                 // prevent deadlocks, pass the notification on to someone else.
//!                 (pin_list::NodeData::Removed(()), ()) => {
//!                     if let Ok(waker) = inner.waiters.cursor_front_mut().remove_current(()) {
//!                         drop(inner);
//!                         waker.wake();
//!                     }
//!                 }
//!             }
//!         }
//!     }
//! }
//!
//! impl<'mutex, T> Future for Lock<'mutex, T> {
//!     type Output = Guard<'mutex, T>;
//!     fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
//!         let mut this = self.project();
//!
//!         let mut inner = this.mutex.inner.lock().unwrap();
//!
//!         if let Some(mut node) = this.node.as_mut().initialized_mut() {
//!             // Check whether we've been woken up, only continuing if so.
//!             if let Err(node) = node.take_removed(&inner.waiters) {
//!                 // If we haven't been woken, re-register our waker and pend.
//!                 *node.protected_mut(&mut inner.waiters).unwrap() = cx.waker().clone();
//!                 return Poll::Pending;
//!             }
//!         }
//!
//!         // If the mutex is unlocked, mark it as locked and return the guard
//!         if !inner.locked {
//!             inner.locked = true;
//!             return Poll::Ready(Guard { mutex: this.mutex });
//!         }
//!
//!         // Otherwise, re-register ourselves to be woken when the mutex is unlocked again
//!         inner.waiters.push_back(this.node, cx.waker().clone(), ());
//!
//!         Poll::Pending
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
//!         let mut inner = self.mutex.inner.lock().unwrap();
//!         inner.locked = false;
//!
//!         if let Ok(waker) = inner.waiters.cursor_front_mut().remove_current(()) {
//!             drop(inner);
//!             waker.wake();
//!         }
//!     }
//! }
//! #
//! # fn assert_send<T: Send>(_: T) {}
//! # let mutex = Mutex::new(());
//! # assert_send(mutex.lock());
//! ```
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

    // Repetition is used in `Send`+`Sync` bounds so each one can be individually commented.
    clippy::type_repetition_in_bounds,

    // This is a silly lint; I always turbofish the transmute so it's fine
    clippy::transmute_ptr_to_ptr,

    // Has false positives: https://github.com/rust-lang/rust-clippy/issues/7812
    clippy::redundant_closure,

    // I export all the types at the crate root, so this lint is pointless.
    clippy::module_name_repetitions,
)]
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

pub mod id;
pub use id::Id;

mod list;
pub use list::{Cursor, CursorMut, PinList, Types};

mod node;
pub use node::{InitializedNode, Node, NodeData};

mod util;

#[cfg(all(test, feature = "std"))]
mod tests {
    use crate::id;
    use core::pin::Pin;
    use pin_utils::pin_mut as pin;
    use std::boxed::Box;
    use std::panic;
    use std::process::abort;
    use std::ptr;

    type PinListTypes = dyn crate::Types<
        Id = id::Checked,
        // Use boxes because they better detect double-frees, type mismatches and other errors.
        Protected = Box<u8>,
        Removed = Box<u16>,
        Unprotected = Box<u32>,
    >;
    type PinList = crate::PinList<PinListTypes>;

    #[test]
    fn empty_lists() {
        let mut list = PinList::new(id::Checked::new());
        let list_ptr: *const _ = &list;

        let assert_ghost_cursor = |cursor: crate::Cursor<'_, _>| {
            assert!(ptr::eq(cursor.list(), list_ptr));
            assert_eq!(cursor.protected(), None);
            assert_eq!(cursor.unprotected(), None);
        };
        let assert_ghost_cursor_mut = |mut cursor: crate::CursorMut<'_, _>| {
            assert!(ptr::eq(cursor.list(), list_ptr));
            assert_eq!(cursor.protected(), None);
            assert_eq!(cursor.protected_mut(), None);
            assert_eq!(cursor.unprotected(), None);
            assert_eq!(cursor.remove_current(Box::new(5)), Err(Box::new(5)));
            assert!(!cursor.remove_current_with(|_| abort()));
            assert!(!cursor.remove_current_with_or(|_| abort(), || abort()));
            assert_ghost_cursor(cursor.as_shared());
        };

        assert!(list.is_empty());

        assert_ghost_cursor(list.cursor_ghost());
        assert_ghost_cursor(list.cursor_front());
        assert_ghost_cursor(list.cursor_back());
        assert_ghost_cursor_mut(list.cursor_ghost_mut());
        assert_ghost_cursor_mut(list.cursor_front_mut());
        assert_ghost_cursor_mut(list.cursor_back_mut());
    }

    #[test]
    fn single_node_with_unlink() {
        let mut list = PinList::new(id::Checked::new());

        let node = crate::Node::new();
        pin!(node);
        assert!(node.is_initial());
        assert!(node.initialized().is_none());
        assert!(node.as_mut().initialized_mut().is_none());

        let mut protected = Box::new(0);
        let unprotected = Box::new(1);
        list.push_front(node.as_mut(), protected.clone(), unprotected.clone());

        assert!(!node.is_initial());

        let initialized = node.initialized().unwrap();
        assert_eq!(initialized.unprotected(), &unprotected);
        assert_eq!(initialized.protected(&list), Some(&protected));
        assert_eq!(initialized.protected_mut(&mut list), Some(&mut protected));

        let initialized = node.as_mut().initialized_mut().unwrap();
        assert_eq!(initialized.unprotected(), &unprotected);
        assert_eq!(initialized.protected(&list), Some(&protected));
        assert_eq!(initialized.protected_mut(&mut list), Some(&mut protected));

        assert!(!list.is_empty());

        let check_cursor = |mut cursor: crate::Cursor<'_, _>| {
            assert_eq!(cursor.protected().unwrap(), &protected);
            assert_eq!(cursor.unprotected().unwrap(), &unprotected);
            cursor.move_next();
            assert_eq!(cursor.protected(), None);
            for _ in 0..10 {
                cursor.move_previous();
                assert_eq!(cursor.protected().unwrap(), &protected);
                cursor.move_previous();
                assert_eq!(cursor.protected(), None);
            }
        };
        let check_cursor_mut = |mut cursor: crate::CursorMut<'_, _>| {
            assert_eq!(cursor.protected().unwrap(), &protected);
            assert_eq!(cursor.protected_mut().unwrap(), &protected);
            assert_eq!(cursor.unprotected().unwrap(), &unprotected);
            for _ in 0..7 {
                cursor.move_next();
                assert_eq!(cursor.protected(), None);
                cursor.move_next();
                assert_eq!(cursor.protected().unwrap(), &protected);
            }
            for _ in 0..10 {
                cursor.move_previous();
                assert_eq!(cursor.protected(), None);
                cursor.move_previous();
                assert_eq!(cursor.protected().unwrap(), &protected);
            }
            check_cursor(cursor.as_shared());
            check_cursor(cursor.into_shared());
        };

        check_cursor(list.cursor_front());
        check_cursor(list.cursor_back());
        check_cursor_mut(list.cursor_front_mut());
        check_cursor_mut(list.cursor_back_mut());

        assert_eq!(
            initialized.unlink(&mut list).unwrap(),
            (protected, unprotected)
        );

        assert!(node.is_initial());
        assert!(node.initialized().is_none());
        assert!(node.as_mut().initialized_mut().is_none());

        assert!(list.is_empty());
    }

    #[test]
    fn removal() {
        let mut list = PinList::new(id::Checked::new());

        let node = crate::Node::new();
        pin!(node);

        let protected = Box::new(0);
        let removed = Box::new(1);
        let unprotected = Box::new(2);

        let initialized_node =
            list.push_back(node.as_mut(), protected.clone(), unprotected.clone());

        assert_eq!(
            list.cursor_front_mut()
                .remove_current(removed.clone())
                .unwrap(),
            protected
        );

        assert_eq!(
            initialized_node.take_removed(&list).unwrap(),
            (removed, unprotected)
        );
        assert!(node.is_initial());
        assert!(list.is_empty());
    }

    #[test]
    fn removal_fallback() {
        let mut list = PinList::new(id::Checked::new());

        let node = crate::Node::new();
        pin!(node);

        let protected = Box::new(0);
        let removed = Box::new(1);
        let unprotected = Box::new(2);

        let initialized_node =
            list.push_front(node.as_mut(), protected.clone(), unprotected.clone());

        let mut cursor = list.cursor_front_mut();
        let res = panic::catch_unwind(panic::AssertUnwindSafe(|| {
            cursor.remove_current_with_or(
                |p| {
                    assert_eq!(p, protected);
                    panic::panic_any(491_u32)
                },
                || removed.clone(),
            )
        }));
        assert_eq!(cursor.protected(), None);
        assert_eq!(res.unwrap_err().downcast::<u32>().unwrap(), Box::new(491));

        assert_eq!(
            initialized_node.take_removed(&list).unwrap(),
            (removed, unprotected),
        );
        assert!(node.is_initial());
        assert!(list.is_empty());
    }

    #[test]
    fn multinode() {
        let mut list = PinList::new(id::Checked::new());

        let mut nodes = (0..7)
            .map(|_| Box::pin(crate::Node::new()))
            .collect::<Box<[_]>>();

        fn assert_order<const N: usize>(list: &mut PinList, order: [u8; N]) {
            // Forwards iteration
            let mut cursor = list.cursor_ghost_mut();
            for number in order {
                cursor.move_next();
                assert_eq!(**cursor.protected().unwrap(), number);
                assert_eq!(**cursor.protected_mut().unwrap(), number);
                assert_eq!(**cursor.unprotected().unwrap(), u32::from(number));
            }
            cursor.move_next();
            assert_eq!(cursor.protected(), None);
            assert_eq!(cursor.protected_mut(), None);
            assert_eq!(cursor.unprotected(), None);

            // Reverse iteration
            for number in order.into_iter().rev() {
                cursor.move_previous();
                assert_eq!(**cursor.protected().unwrap(), number);
                assert_eq!(**cursor.protected_mut().unwrap(), number);
                assert_eq!(**cursor.unprotected().unwrap(), u32::from(number));
            }
            cursor.move_previous();
            assert_eq!(cursor.protected(), None);
            assert_eq!(cursor.protected_mut(), None);
            assert_eq!(cursor.unprotected(), None);
        }

        fn cursor(list: &mut PinList, index: usize) -> crate::CursorMut<'_, PinListTypes> {
            let mut cursor = list.cursor_front_mut();
            for _ in 0..index {
                cursor.move_next();
                cursor.protected().unwrap();
            }
            cursor
        }

        // ghost before; ghost after
        list.cursor_ghost_mut()
            .insert_before(nodes[0].as_mut(), Box::new(0), Box::new(0));
        assert_order(&mut list, [0]);

        // ghost before; node after; insert_after
        list.cursor_ghost_mut()
            .insert_after(nodes[1].as_mut(), Box::new(1), Box::new(1));
        assert_order(&mut list, [1, 0]);

        // ghost before; node after; insert_before
        cursor(&mut list, 0).insert_before(nodes[2].as_mut(), Box::new(2), Box::new(2));
        assert_order(&mut list, [2, 1, 0]);

        // node before; ghost after; insert_after
        cursor(&mut list, 2).insert_after(nodes[3].as_mut(), Box::new(3), Box::new(3));
        assert_order(&mut list, [2, 1, 0, 3]);

        // node before; ghost after; insert_before
        list.cursor_ghost_mut()
            .insert_before(nodes[4].as_mut(), Box::new(4), Box::new(4));
        assert_order(&mut list, [2, 1, 0, 3, 4]);

        // node before; node after; insert_after
        cursor(&mut list, 0).insert_after(nodes[5].as_mut(), Box::new(5), Box::new(5));
        assert_order(&mut list, [2, 5, 1, 0, 3, 4]);

        // node before; node after; insert_before
        cursor(&mut list, 1).insert_before(nodes[6].as_mut(), Box::new(6), Box::new(6));
        assert_order(&mut list, [2, 6, 5, 1, 0, 3, 4]);

        fn unlink(
            list: &mut PinList,
            nodes: &mut [Pin<Box<crate::Node<PinListTypes>>>],
            index: u8,
        ) {
            let node = nodes[usize::from(index)].as_mut();
            let node = node.initialized_mut().expect("already unlinked");
            let (protected, unprotected) = node.unlink(list).unwrap();
            assert_eq!(*protected, index);
            assert_eq!(*unprotected, u32::from(index));
        }

        fn remove(
            list: &mut PinList,
            nodes: &mut [Pin<Box<crate::Node<PinListTypes>>>],
            index: u8,
        ) {
            let node = nodes[usize::from(index)].as_mut();
            let node = node.initialized_mut().expect("already unlinked");
            let mut cursor = node.cursor_mut(&mut *list).unwrap();
            let removed = Box::new(u16::from(index));
            assert_eq!(*cursor.remove_current(removed).unwrap(), index);
            let (removed, unprotected) = node.take_removed(&*list).unwrap();
            assert_eq!(*removed, u16::from(index));
            assert_eq!(*unprotected, u32::from(index));
        }

        // node before; node after; unlink
        unlink(&mut list, &mut nodes, 6);
        assert_order(&mut list, [2, 5, 1, 0, 3, 4]);

        // node before; node after; remove
        remove(&mut list, &mut nodes, 5);
        assert_order(&mut list, [2, 1, 0, 3, 4]);

        // node before; ghost after; unlink
        unlink(&mut list, &mut nodes, 4);
        assert_order(&mut list, [2, 1, 0, 3]);

        // node before; ghost after; remove
        remove(&mut list, &mut nodes, 3);
        assert_order(&mut list, [2, 1, 0]);

        // ghost before; node after; unlink
        unlink(&mut list, &mut nodes, 2);
        assert_order(&mut list, [1, 0]);

        // ghost before; node after; remove
        remove(&mut list, &mut nodes, 1);
        assert_order(&mut list, [0]);

        // ghost before; ghost after; unlink
        unlink(&mut list, &mut nodes, 0);
        assert_order(&mut list, []);
    }
}
