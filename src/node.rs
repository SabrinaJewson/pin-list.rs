//! The `Node` type and its related APIs.

use crate::list::NodeLinked;
use crate::list::NodeProtected;
use crate::list::NodeRemoved;
use crate::list::NodeShared;
use crate::util::abort;
use crate::util::debug_unreachable;
use crate::util::unwrap_unchecked;
use crate::util::ConstFnBounds;
use crate::Cursor;
use crate::CursorMut;
use crate::PinList;
use crate::Types;
use core::cell::UnsafeCell;
use core::fmt;
use core::fmt::Debug;
use core::fmt::Formatter;
use core::marker::PhantomData;
use core::mem;
use core::ops::Deref;
use core::pin::Pin;
use core::ptr::NonNull;
use pin_project_lite::pin_project;
use pinned_aliasable::Aliasable;

pin_project! {
    /// A node in a [`PinList`].
    ///
    /// This type is a state machine between three states:
    /// 1. **Initial:**
    ///     The initial state; the node is not registered in any list. This is the only state that
    ///     can be dropped without aborting the process.
    /// 2. **Linked:**
    ///     The node has been linked into a [`PinList`]. It holds a `Protected` and an
    ///     `Unprotected`, of which the former can only be accessed when access to the [`PinList`]
    ///     can be proven. Dropping a node in this state will abort.
    /// 3. **Removed:**
    ///     The node has been removed from a [`PinList`]. It holds a `Removed` and an
    ///     `Unprotected`. Similar to the "linked" state, proof of access to the [`PinList`] is
    ///     required for most operations. Dropping a node in this state will abort.
    pub struct Node<T: ?Sized>
    where
        T: Types,
    {
        // `None` if initial, `Some` if initialized
        #[pin]
        inner: Option<NodeInner<T>>,
    }

    impl<T: ?Sized> PinnedDrop for Node<T>
    where
        T: Types,
    {
        fn drop(this: Pin<&mut Self>) {
            // If we might be linked into a list at this point in time, we have no choice but to
            // abort in order to preserve soundness and prevent use-after-frees.
            if this.inner.is_some() {
                abort();
            }
        }
    }
}

pin_project! {
    struct NodeInner<T: ?Sized>
    where
        T: Types,
    {
        // The ID of the list this node is/was registered in, used for checking whether access to
        // the inner state is valid.
        list_id: T::Id,

        // State that is also accessible by a walker of the list (cursors).
        #[pin]
        shared: Aliasable<NodeShared<T>>,
    }
}

unsafe impl<T: ?Sized + Types> Send for Node<T>
where
    // Required because it is owned by this type and will be dropped by it.
    T::Id: Send,

    // (SAFETY) Not required because the ownership of IDs are not shared.
    /* T::Id: ?Sync, */
    // Required because we can take and return instances of this type by value.
    T::Protected: Send,

    // (SAFETY) Not required because multiple `&PinList`s on different threads are required to
    // access this type in a `Sync`-requiring way, which would need `PinList: Sync` (which does
    // require `T::Protected: Sync`). In other words, `Self: Send` alone only allows exclusive or
    // reentrant access which is OK by `Send + !Sync`.
    /* T::Protected: ?Sync, */
    // Required because we can take and return this type by value.
    T::Removed: Send,

    // (SAFETY) Not required because we never deal in `&T::Removed` — it's always passed by
    // ownership.
    /* T::Removed: ?Sync, */
    // Required because we can take and return this type by value.
    T::Unprotected: Send,

    // Required because values of this type can be shared between this node and its list.
    T::Unprotected: Sync,
{
}

unsafe impl<T: ?Sized + Types> Sync for Node<T>
where
    // (SAFETY) Not required because ownership of IDs can't be obtained from a shared reference.
    /* T::Id: ?Send, */
    // Required because ID comparison code uses its `PartialEq` implementation, which accesses it
    // by shared reference.
    T::Id: Sync,

    // (SAFETY) Not required to be `Send` or `Sync` because the only methods that access it that
    // take `&self` would require the `PinList` to be `Sync` to be called on two threads, which it
    // isn't if `T::Protected: !Send` or `T::Protected: !Sync`.
    /* T::Protected: ?Send + ?Sync, */

    // (SAFETY) Not required because ownership of this type is only passed around when a
    // `Pin<&mut Node<T>>` is the receiver.
    /* T::Removed: ?Send, */

    // (SAFETY) Not required because we never deal in `&T::Removed` — it's always passed by
    // ownership.
    /* T::Removed: ?Sync, */

    // (SAFETY) Not required because ownership of this type is only passed around when a
    // `Pin<&mut Node<T>` is the receiver.
    /* T::Unprotected: ?Send, */
    // Required because shared references to values of this type can be accessed from a shared
    // reference to the node.
    T::Unprotected: Sync,
{
}

impl<T: ?Sized> Node<T>
where
    <T as ConstFnBounds>::Type: Types,
{
    /// Create a new node in its initial state.
    ///
    /// You can move this node into other states by functions like [`PinList::push_front`].
    #[must_use]
    pub const fn new() -> Self {
        Self { inner: None }
    }
}

impl<T: ?Sized + Types> Node<T> {
    /// Check whether the node is in its initial state.
    #[must_use]
    pub fn is_initial(&self) -> bool {
        self.inner.is_none()
    }

    /// Insert this node into the linked list before the given cursor.
    ///
    /// # Panics
    ///
    /// Panics if the node is not in its initial state.
    pub fn insert_before(
        self: Pin<&mut Self>,
        cursor: &mut CursorMut<'_, T>,
        protected: T::Protected,
        unprotected: T::Unprotected,
    ) -> Pin<&mut InitializedNode<'_, T>> {
        let prev = *cursor.prev_mut();

        // Store our own state as linked.
        let node = self.init(NodeInner {
            list_id: cursor.list().id,
            shared: Aliasable::new(NodeShared {
                protected: UnsafeCell::new(NodeProtected::Linked(NodeLinked {
                    prev,
                    next: cursor.current,
                    data: protected,
                })),
                unprotected,
            }),
        });

        // Update the previous node's `next` pointer and the next node's `prev` pointer to both
        // point to us.
        *unsafe { cursor.list.cursor_mut(prev) }.next_mut() = Some(node.shared_ptr());
        *cursor.prev_mut() = Some(node.shared_ptr());

        node
    }

    /// Insert this node into the linked list after the given cursor.
    ///
    /// # Panics
    ///
    /// Panics if the node is not in its initial state.
    pub fn insert_after(
        self: Pin<&mut Self>,
        cursor: &mut CursorMut<'_, T>,
        protected: T::Protected,
        unprotected: T::Unprotected,
    ) -> Pin<&mut InitializedNode<'_, T>> {
        let next = *cursor.next_mut();

        // Store our own state as linked.
        let node = self.init(NodeInner {
            list_id: cursor.list().id,
            shared: Aliasable::new(NodeShared {
                protected: UnsafeCell::new(NodeProtected::Linked(NodeLinked {
                    prev: cursor.current,
                    next,
                    data: protected,
                })),
                unprotected,
            }),
        });

        // Update the previous node's `next` pointer and the next node's `prev` pointer to both
        // point to us.
        *cursor.next_mut() = Some(node.shared_ptr());
        *unsafe { cursor.list.cursor_mut(next) }.prev_mut() = Some(node.shared_ptr());

        node
    }

    fn init(mut self: Pin<&mut Self>, new_inner: NodeInner<T>) -> Pin<&mut InitializedNode<'_, T>> {
        let mut inner = self.as_mut().project().inner;

        assert!(inner.is_none(), "attempted to link an already-linked node");

        inner.set(Some(new_inner));

        // SAFETY: We just set the inner to `Some`.
        unsafe { InitializedNode::new_mut_unchecked(self) }
    }

    /// Borrow the node, if it is initialized (linked or removed).
    ///
    /// Returns [`None`] if the node is in the initial state.
    #[must_use]
    pub fn initialized(&self) -> Option<&InitializedNode<'_, T>> {
        InitializedNode::new_ref(self)
    }

    /// Borrow uniquely the node, if it is initialized (linked or removed).
    ///
    /// Returns [`None`] if the node is in the initial state.
    #[must_use]
    pub fn initialized_mut(self: Pin<&mut Self>) -> Option<Pin<&mut InitializedNode<'_, T>>> {
        InitializedNode::new_mut(self)
    }
}

impl<T: ?Sized + Types> Debug for Node<T>
where
    T::Unprotected: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(initialized) = &self.initialized() {
            f.debug_struct("Node::Initialized")
                .field("list_id", &initialized.inner().list_id)
                .field("unprotected", initialized.unprotected())
                .finish()
        } else {
            f.pad("Node::Initial")
        }
    }
}

/// A [`Node`] which is guaranteed to be initialized, accessed by [`Node::initialized`] and
/// [`Node::initialized_mut`].
///
/// You can never create and will never interact with owned or `&mut` instances of this type — it
/// is accessed solely as `&InitializedNode<'_, T>` or `Pin<&mut InitializedNode<'_, T>>`.
#[repr(transparent)]
pub struct InitializedNode<'node, T: ?Sized + Types> {
    // Hold a `Node<T>` and not a `NodeInner<T>` so we can set its value to `None`.
    node: Node<T>,
    // This `'node` lifetime is used to allow "owned references" to the `InitializedNode`:
    // `Pin<&'node mut InitializedNode<'node, T>>`. Because the unique reference makes the `'node`
    // lifetime invariant, such a type enforces that the reference is not used after that call.
    _lifetime: PhantomData<&'node ()>,
}

impl<T: ?Sized + Types> Deref for InitializedNode<'_, T> {
    type Target = Node<T>;
    fn deref(&self) -> &Self::Target {
        &self.node
    }
}

impl<'node, T: ?Sized + Types> InitializedNode<'node, T> {
    fn new_ref(node: &'node Node<T>) -> Option<&'node Self> {
        node.inner.as_ref()?;
        // SAFETY: We have just asserted that `inner` is `Some` and we are `#[repr(transparent)]`
        // over `Node<T>`.
        Some(unsafe { mem::transmute::<&'node Node<T>, &'node InitializedNode<'node, T>>(node) })
    }

    fn new_mut(node: Pin<&'node mut Node<T>>) -> Option<Pin<&'node mut Self>> {
        node.inner.as_ref()?;
        // SAFETY: We have just asserted that `inner` is `Some`.
        Some(unsafe { Self::new_mut_unchecked(node) })
    }

    unsafe fn new_mut_unchecked(node: Pin<&'node mut Node<T>>) -> Pin<&'node mut Self> {
        // SAFETY: Caller ensures that `inner` is `Some`, and we are `#[repr(transparent)]`
        // over `Node<T>`.
        unsafe {
            mem::transmute::<Pin<&'node mut Node<T>>, Pin<&'node mut InitializedNode<'node, T>>>(
                node,
            )
        }
    }

    fn inner(&self) -> Pin<&NodeInner<T>> {
        // SAFETY: In order for this type to exist, the node must be initialized.
        let inner = unsafe { unwrap_unchecked(self.node.inner.as_ref()) };

        // SAFETY: In order for this state to be created, we must already have been pinned.
        unsafe { Pin::new_unchecked(inner) }
    }

    fn shared(&self) -> &NodeShared<T> {
        self.inner().project_ref().shared.get()
    }

    fn shared_ptr(&self) -> NonNull<NodeShared<T>> {
        NonNull::from(self.shared())
    }

    /// Get a shared reference to the unprotected data of this node.
    #[must_use]
    pub fn unprotected(&self) -> &T::Unprotected {
        &self.shared().unprotected
    }

    /// Get a shared reference to the protected data of this node.
    ///
    /// Returns [`None`] if the node is in its removed state (has been removed from the list).
    ///
    /// # Panics
    ///
    /// Panics if the given list is a different one than this node was registered with.
    #[must_use]
    pub fn protected<'list>(&self, list: &'list PinList<T>) -> Option<&'list T::Protected> {
        assert_eq!(self.inner().list_id, list.id, "incorrect `PinList`");

        // SAFETY: We have shared access to both `self` and our `PinList`, as guaranteed above.
        match unsafe { &*self.shared().protected.get() } {
            NodeProtected::Linked(linked) => Some(&linked.data),
            NodeProtected::Removed(..) => None,
        }
    }

    /// Get a unique reference to the protected data of this node.
    ///
    /// Returns [`None`] if the node is in its removed state (has been removed from the list).
    ///
    /// # Panics
    ///
    /// Panics if the given list is a different one than this node was registered with.
    #[must_use]
    pub fn protected_mut<'list>(
        &self,
        list: &'list mut PinList<T>,
    ) -> Option<&'list mut T::Protected> {
        assert_eq!(self.inner().list_id, list.id, "incorrect `PinList`");

        // Only create a shared reference because we only have a shared reference to `self`. In the
        // `Linked` branch this doesn't end up mattering, but in the `Removed` branch it's possible
        // that a `&NodeRemoved` existed at the time of calling this function.
        match unsafe { &*self.shared().protected.get() } {
            NodeProtected::Linked(..) => {
                // SAFETY: We have unique access to the list, and we have asserted that the node
                // isn't removed.
                Some(match unsafe { &mut *self.shared().protected.get() } {
                    NodeProtected::Linked(linked) => &mut linked.data,
                    NodeProtected::Removed(..) => unsafe { debug_unreachable!() },
                })
            }
            NodeProtected::Removed(..) => None,
        }
    }

    /// Obtain a shared cursor pointing to this node.
    ///
    /// Returns [`None`] if the node was in its removed state (it was removed from the list).
    ///
    /// # Panics
    ///
    /// Panics if the given list is a different one than this node was registered with.
    #[must_use]
    pub fn cursor<'list>(&self, list: &'list PinList<T>) -> Option<Cursor<'list, T>> {
        assert_eq!(self.inner().list_id, list.id, "incorrect `PinList`");

        // SAFETY: We have shared access to both this node and the list.
        match unsafe { &*self.shared().protected.get() } {
            NodeProtected::Linked(..) => {}
            NodeProtected::Removed(..) => return None,
        }

        // SAFETY: We have shared access to the list, and this node is not removed from the list.
        Some(unsafe { list.cursor(Some(self.shared_ptr())) })
    }

    /// Obtain a unique cursor pointing to this node.
    ///
    /// Returns [`None`] if the node was in its removed state (it was removed from the list).
    ///
    /// # Panics
    ///
    /// Panics if the given list is a different one than this node was registered with.
    #[must_use]
    pub fn cursor_mut<'list>(&self, list: &'list mut PinList<T>) -> Option<CursorMut<'list, T>> {
        assert_eq!(self.inner().list_id, list.id, "incorrect `PinList`");

        // Only create a shared reference because we only have a shared reference to `self`. In the
        // `Linked` branch this doesn't end up mattering, but in the `Removed` branch it's possible
        // that a `&NodeRemoved` existed at the time of calling this function.
        match unsafe { &*self.shared().protected.get() } {
            NodeProtected::Linked(..) => {}
            NodeProtected::Removed(..) => return None,
        }

        // SAFETY: We have exclusive access to the list, and this node is not removed from the
        // list.
        Some(unsafe { list.cursor_mut(Some(self.shared_ptr())) })
    }

    /// Remove this node from its containing list and take its data, leaving the node in its
    /// initial state.
    ///
    /// # Errors
    ///
    /// Fails if the node is in its removed state — use [`take_removed`](Self::take_removed) to
    /// handle that case, or call [`reset`](Self::reset) instead.
    ///
    /// # Panics
    ///
    /// Panics if the given list is a different one than this node was registered with.
    // Take `&'node mut Self` instead of `&mut Self` to ensure that this reference is not used
    // after this point.
    pub fn unlink(
        self: Pin<&'node mut Self>,
        list: &mut PinList<T>,
    ) -> Result<(T::Protected, T::Unprotected), Pin<&'node mut Self>> {
        assert_eq!(self.inner().list_id, list.id, "incorrect `PinList`");

        // SAFETY: We have exclusive access to both the node and the list.
        let linked = match unsafe { &mut *self.shared().protected.get() } {
            NodeProtected::Linked(linked) => linked,
            NodeProtected::Removed(..) => return Err(self),
        };

        // Link up the nodes around us to remove ourselves from the list.
        *unsafe { list.cursor_mut(linked.prev) }.next_mut() = linked.next;
        *unsafe { list.cursor_mut(linked.next) }.prev_mut() = linked.prev;

        // SAFETY: We just unlinked ourselves from the list.
        match unsafe { self.take_unchecked() } {
            (NodeData::Linked(linked), unprotected) => Ok((linked, unprotected)),
            // SAFETY: We asserted at the beginning of this function that we were in the linked
            // state.
            (NodeData::Removed(_), _) => unsafe { debug_unreachable!() },
        }
    }

    /// Take the data out of this node if it has been removed from the list, leaving the node in
    /// its initial state.
    ///
    /// # Errors
    ///
    /// Errors if the node was in its "linked" state (it was still part of the list) — use
    /// [`unlink`](Self::unlink) in this case, or call [`reset`](Self::reset) instead.
    ///
    /// # Panics
    ///
    /// Panics if the given list is a different one than this node was registered with.
    // Take `&'node mut Self` instead of `&mut Self` to ensure that this reference is not used
    // after this point.
    pub fn take_removed(
        self: Pin<&'node mut Self>,
        list: &PinList<T>,
    ) -> Result<(T::Removed, T::Unprotected), Pin<&'node mut Self>> {
        assert_eq!(self.inner().list_id, list.id, "incorrect `PinList`");

        // Only create a shared reference because we only have shared access to the `PinList`. In
        // the `Removed` branch this doesn't end up mattering, but in the `Linked` branch it's
        // possible a `&T::Unprotected` existed at the time of calling this function.
        match unsafe { &*self.shared().protected.get() } {
            NodeProtected::Removed(..) => {}
            NodeProtected::Linked(..) => return Err(self),
        }

        // SAFETY: We just asserted that we are in the removed state.
        Ok(unsafe { self.take_removed_unchecked() })
    }

    /// Take the data out of this node, assuming that it has been removed from the list, leaving
    /// the node in its initial state.
    ///
    /// In contrast to [`take_removed`](Self::take_removed), this does not require access to the
    /// [`PinList`].
    ///
    /// # Safety
    ///
    /// The node must not be in its linked state.
    #[must_use]
    // Take `&'node mut Self` instead of `&mut Self` to ensure that this reference is not used
    // after this point.
    pub unsafe fn take_removed_unchecked(
        self: Pin<&'node mut Self>,
    ) -> (T::Removed, T::Unprotected) {
        // SAFETY: Ensured by caller.
        match unsafe { self.take_unchecked() } {
            (NodeData::Linked(_), _) => {
                // oops! the caller has violated the safety invariants of this function. we may
                // have even already caused UB in `take_unchecked`.
                // SAFETY: Ensured by caller.
                unsafe {
                    debug_unreachable!(
                        "called `take_remove_unchecked` on a linked node: this is Undefined Behaviour"
                    )
                }
            }
            (NodeData::Removed(removed), unprotected) => (removed, unprotected),
        }
    }

    /// Take the inner data from this node, leaving it in the initial state.
    ///
    /// # Safety
    ///
    /// The node must have been removed from the list. It can be in either of the `Removed` and
    /// `Linked` states.
    // Take `&'node mut Self` instead of `&mut Self` to ensure that this reference is not used
    // after this point.
    unsafe fn take_unchecked(self: Pin<&'node mut Self>) -> (NodeData<T>, T::Unprotected) {
        // SAFETY: Since the caller asserts that we have been removed, we no longer need to be
        // pinned.
        let this = unsafe { &mut Pin::into_inner_unchecked(self).node };

        let old_node = mem::replace(&mut this.inner, None);
        // SAFETY: In order for this type to exist, the node must be initialized.
        let old_inner = unsafe { unwrap_unchecked(old_node) };
        let old_shared = old_inner.shared.into_inner();
        let data = match old_shared.protected.into_inner() {
            NodeProtected::Linked(NodeLinked { data, .. }) => NodeData::Linked(data),
            NodeProtected::Removed(NodeRemoved { data }) => NodeData::Removed(data),
        };
        (data, old_shared.unprotected)
    }

    /// Reset the node back to its initial state.
    ///
    /// If the node is linked, this will unlink it, and then the node will be moved to the initial
    /// state.
    ///
    /// This can be thought of as a combination of [`unlink`] and [`take_removed`].
    ///
    /// [`unlink`]: Self::unlink
    /// [`take_removed`]: Self::take_removed
    ///
    /// # Panics
    ///
    /// Panics if the given list is a different one than this node was registered with.
    pub fn reset(
        self: Pin<&'node mut Self>,
        list: &mut PinList<T>,
    ) -> (NodeData<T>, T::Unprotected) {
        match self.unlink(list) {
            Ok((protected, unprotected)) => (NodeData::Linked(protected), unprotected),
            Err(this) => {
                // SAFETY: `unlink` only returns `Err` if we have been removed.
                let (removed, unprotected) = unsafe { this.take_removed_unchecked() };
                (NodeData::Removed(removed), unprotected)
            }
        }
    }
}

impl<T: ?Sized + Types> Debug for InitializedNode<'_, T>
where
    T::Unprotected: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("InitializedNode")
            .field("list_id", &self.inner().list_id)
            .field("unprotected", self.unprotected())
            .finish()
    }
}

/// The data stored by a node; either `Protected` or `Removed`. This type is returned by
/// [`InitializedNode::reset`].
pub enum NodeData<T: ?Sized + Types> {
    /// The node was linked in a list.
    Linked(T::Protected),

    /// The node was removed from the list.
    Removed(T::Removed),
}

impl<T: ?Sized + Types> Debug for NodeData<T>
where
    T::Protected: Debug,
    T::Removed: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Linked(protected) => f.debug_tuple("NodeData::Linked").field(protected).finish(),
            Self::Removed(removed) => f.debug_tuple("NodeData::Removed").field(removed).finish(),
        }
    }
}
