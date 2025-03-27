//! The list itself, and its cursor API.

use crate::id;
use crate::util::abort;
use crate::util::debug_unreachable;
use crate::util::run_on_drop;
use crate::util::ConstFnBounds;
use crate::Id;
use crate::InitializedNode;
use crate::Node;
use core::cell::UnsafeCell;
use core::fmt;
use core::fmt::Debug;
use core::fmt::Formatter;
use core::mem;
use core::mem::align_of;
use core::mem::transmute;
use core::pin::Pin;
use core::ptr;
use core::ptr::NonNull;

/// Types used in a [`PinList`]. This trait is used to avoid an excessive number of generic
/// parameters on [`PinList`] and related types.
///
/// Generally you won't want to implement this trait directly — instead you can create ad-hoc
/// implementations by using `dyn Trait` syntax, for example:
///
/// ```
/// type PinListTypes = dyn pin_list::Types<
///     Id = pin_list::id::Checked,
///     Protected = (),
///     Removed = (),
///     Unprotected = (),
/// >;
/// type PinList = pin_list::PinList<PinListTypes>;
/// ```
pub trait Types {
    /// The ID type this list uses to ensure that different [`PinList`]s are not mixed up.
    ///
    /// This crate provides a couple built-in ID types, but you can also define your own:
    /// - [`id::Checked`]:
    ///     IDs are allocated with a single global atomic `u64` counter.
    /// - [`id::Unchecked`]:
    ///     The responsibility is left up to the user to ensure that different [`PinList`]s are not
    ///     incorrectly mixed up. Using this is `unsafe`.
    /// - [`id::DebugChecked`]:
    ///     Equivalent to [`id::Checked`] when `debug_assertions` are enabled, but
    ///     [`id::Unchecked`] in release.
    /// - [`id::Lifetime`]:
    ///     A fully statically checked ID based on invariant lifetimes and HRTBs — this is the same
    ///     technique as used by `GhostCell`. While theoretically the best option, its infectious
    ///     nature makes it not very useful in practice.
    type Id: Id;

    /// Data owned by each node in the list (before it has been removed) and protected by the list.
    /// This is only accessible when the list is.
    ///
    /// When the node is removed from the list, this value is replaced with [`Removed`].
    ///
    /// [`Removed`]: Self::Removed
    type Protected;

    /// Data owned by each node after it has been removed from the list.
    type Removed;

    /// Data owned by each node in the list but not protected by the list.
    ///
    /// This is always accessible by shared reference from the node itself without accessing the
    /// list, and is acessible by shared reference from the [`PinList`].
    type Unprotected;
}

/// An intrusive linked list.
pub struct PinList<T: ?Sized + Types> {
    /// The list's unique ID.
    pub(crate) id: T::Id,

    /// The head of the list.
    ///
    /// If this is `None`, the list is empty.
    head: OptionNodeShared<T>,

    /// The tail of the list.
    ///
    /// Whether this is `None` must remain in sync with whether `head` is `None`.
    tail: OptionNodeShared<T>,
}

/// An optional pointer to a `NodeShared`.
///
/// Unlike `Option<NonNull<NodeShared<T>>>`, this has a niche.
pub(crate) struct OptionNodeShared<T: ?Sized + Types>(NonNull<NodeShared<T>>);

impl<T: ?Sized + Types> OptionNodeShared<T> {
    pub(crate) const NONE: Self = Self(Self::SENTINEL);
    pub(crate) fn some(ptr: NonNull<NodeShared<T>>) -> Self {
        Self(ptr)
    }
    pub(crate) fn get(self) -> Option<NonNull<NodeShared<T>>> {
        (self.0 != Self::SENTINEL).then(|| self.0)
    }
    const SENTINEL: NonNull<NodeShared<T>> = {
        // `NodeShared` indirectly contains pointers, so we know this is true.
        assert!(2 <= align_of::<NodeShared<T>>());

        // We use a value of 1 as the sentinel since it isn’t aligned
        // and thus can’t be mistaken for a valid value.
        //
        // We use a transmute to explicitly polyfill `ptr::without_provenance`.
        #[allow(clippy::useless_transmute)]
        unsafe {
            NonNull::new_unchecked(transmute::<usize, *mut NodeShared<T>>(1))
        }
    };
}

impl<T: ?Sized + Types> Clone for OptionNodeShared<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T: ?Sized + Types> Copy for OptionNodeShared<T> {}

/// The state of a node in a list shared between the node's owner and other types.
///
/// This type is only accessed by shared reference because there are multiple places that need to
/// have non-invalidated pointers to it.
pub(crate) struct NodeShared<T: ?Sized + Types> {
    /// State of this node that is protected by the `PinList`.
    pub(crate) protected: UnsafeCell<NodeProtected<T>>,

    /// State of this node not protected by the `PinList`.
    pub(crate) unprotected: T::Unprotected,
}

pub(crate) enum NodeProtected<T: ?Sized + Types> {
    /// The node is present in the list.
    Linked(NodeLinked<T>),

    /// This node has been removed from the list.
    Removed(NodeRemoved<T>),
}

pub(crate) struct NodeLinked<T: ?Sized + Types> {
    /// The previous node in the linked list.
    pub(crate) prev: OptionNodeShared<T>,

    /// The next node in the linked list.
    pub(crate) next: OptionNodeShared<T>,

    /// Any extra data the user wants to store in this state.
    pub(crate) data: T::Protected,
}

pub(crate) struct NodeRemoved<T: ?Sized + Types> {
    /// Any extra data the user wants to store in this state.
    pub(crate) data: T::Removed,
}

unsafe impl<T: ?Sized + Types> Send for PinList<T>
where
    // Required because it is owned by this type and will be dropped by it.
    T::Id: Send,

    // (SAFETY) Not required because the ownership of IDs are not shared.
    /* T::Id: ?Sync, */
    // Required because we we expose exclusive access to values of this type.
    T::Protected: Send,

    // (SAFETY) Not required because multiple `&PinList`s on different threads are required to
    // access this type in a `Sync`-requiring way, which would need `PinList: Sync` (which does
    // require `T::Protected: Sync`). In other words, `Self: Send` alone only allows exclusive or
    // reentrant access which is OK by `Send + !Sync`.
    /* T::Protected: ?Sync, */
    // Required because ownership can be transferred into the list nodes which may be on a
    // different thread.
    T::Removed: Send,

    // (SAFETY) Not required because we never deal in `&T::Removed` — it's always passed by
    // ownership.
    /* T::Removed: ?Sync, */

    // (SAFETY) Not required because we don't drop it and we only access it by shared reference.
    /* T::Unprotected: ?Send, */
    // Required because values of the type can be shared between this list and its nodes even
    // without the guard held.
    T::Unprotected: Sync,
{
}

unsafe impl<T: ?Sized + Types> Sync for PinList<T>
where
    // (SAFETY) Not required because ownership of IDs can't be obtained from a shared reference.
    /* T::Id: ?Send, */
    // Required because ID comparison code uses its `PartialEq` implementation, which accesses it
    // by shared reference.
    T::Id: Sync,

    // Both `Send` and `Sync` are required because this value can be accessed by both shared
    // and exclusive reference from a shared reference to the list.
    T::Protected: Send + Sync,

    // Required because ownership can be transferred into the list nodes which may be on
    // a different thread.
    T::Removed: Send,

    // (SAFETY) Not required because we never deal in `&T::Removed` — it's always passed by
    // ownership.
    /* T::Removed: ?Sync, */

    // (SAFETY) Not required because we don't drop it and we only access it by shared reference.
    /* T::Unprotected: ?Send, */
    // Required because values of the type can be shared between this list and its nodes.
    T::Unprotected: Sync,
{
}

impl<T: ?Sized> PinList<T>
where
    <T as ConstFnBounds>::Type: Types,
{
    /// Create a new empty `PinList` from a unique ID.
    #[must_use]
    pub const fn new(id: id::Unique<<<T as ConstFnBounds>::Type as Types>::Id>) -> Self {
        Self {
            id: id.into_inner(),
            head: OptionNodeShared::NONE,
            tail: OptionNodeShared::NONE,
        }
    }
}

impl<T: ?Sized + Types> PinList<T> {
    /// Check whether there are any nodes in this list.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        debug_assert_eq!(self.head.get().is_some(), self.tail.get().is_some());
        self.head.get().is_none()
    }

    /// # Safety
    ///
    /// The node must be present in the list.
    pub(crate) unsafe fn cursor(&self, current: OptionNodeShared<T>) -> Cursor<'_, T> {
        Cursor {
            list: self,
            current,
        }
    }

    /// # Safety
    ///
    /// - The node must be present in the list.
    /// - This cursor must not be used to invalidate any other cursors in the list (by e.g.
    ///   removing nodes out from under them).
    pub(crate) unsafe fn cursor_mut(&mut self, current: OptionNodeShared<T>) -> CursorMut<'_, T> {
        CursorMut {
            list: self,
            current,
        }
    }

    /// Obtain a `Cursor` pointing to the "ghost" element of the list.
    #[must_use]
    pub fn cursor_ghost(&self) -> Cursor<'_, T> {
        // SAFETY: The ghost cursor is always in the list.
        unsafe { self.cursor(OptionNodeShared::NONE) }
    }

    /// Obtain a `Cursor` pointing to the first element of the list, or the ghost element if the
    /// list is empty.
    #[must_use]
    pub fn cursor_front(&self) -> Cursor<'_, T> {
        let mut cursor = self.cursor_ghost();
        cursor.move_next();
        cursor
    }

    /// Obtain a `Cursor` pointing to the last element of the list, or the ghost element if the
    /// list is empty.
    #[must_use]
    pub fn cursor_back(&self) -> Cursor<'_, T> {
        let mut cursor = self.cursor_ghost();
        cursor.move_previous();
        cursor
    }

    /// Obtain a `CursorMut` pointing to the "ghost" element of the list.
    #[must_use]
    pub fn cursor_ghost_mut(&mut self) -> CursorMut<'_, T> {
        // SAFETY: The ghost cursor is always in the list, and the `&mut Self` ensures that safe
        // code cannot currently hold a cursor.
        unsafe { self.cursor_mut(OptionNodeShared::NONE) }
    }

    /// Obtain a `CursorMut` pointing to the first element of the list, or the ghost element if the
    /// list is empty.
    #[must_use]
    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T> {
        let mut cursor = self.cursor_ghost_mut();
        cursor.move_next();
        cursor
    }

    /// Obtain a `CursorMut` pointing to the last element of the list, or the ghost element if the
    /// list is empty.
    #[must_use]
    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, T> {
        let mut cursor = self.cursor_ghost_mut();
        cursor.move_previous();
        cursor
    }

    /// Append a node to the front of the list.
    ///
    /// # Panics
    ///
    /// Panics if the node is not in its initial state.
    pub fn push_front<'node>(
        &mut self,
        node: Pin<&'node mut Node<T>>,
        protected: T::Protected,
        unprotected: T::Unprotected,
    ) -> Pin<&'node mut InitializedNode<'node, T>> {
        self.cursor_ghost_mut()
            .insert_after(node, protected, unprotected)
    }

    /// Append a node to the back of the list.
    ///
    /// # Panics
    ///
    /// Panics if the node is not in its initial state.
    pub fn push_back<'node>(
        &mut self,
        node: Pin<&'node mut Node<T>>,
        protected: T::Protected,
        unprotected: T::Unprotected,
    ) -> Pin<&'node mut InitializedNode<'node, T>> {
        self.cursor_ghost_mut()
            .insert_before(node, protected, unprotected)
    }
}

#[allow(clippy::missing_fields_in_debug)]
impl<T: ?Sized + Types> Debug for PinList<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("PinList").field("id", &self.id).finish()
    }
}

/// A shared cursor into a linked list.
///
/// This can be created by methods like [`PinList::cursor_ghost`].
///
/// Each cursor conceptually points to a single item in the list. It can also point to the space
/// between the start and end of the list, in which case it is called the ghost cursor.
///
/// This type is not `Copy` to prevent accidental copies, but its `Clone` implementation is just a
/// bitwise copy — very cheap.
pub struct Cursor<'list, T: ?Sized + Types> {
    list: &'list PinList<T>,
    current: OptionNodeShared<T>,
}

unsafe impl<T: ?Sized + Types> Send for Cursor<'_, T> where
    // (SAFETY) Required because we hold a shared reference to a `PinList`.
    PinList<T>: Sync
{
}

unsafe impl<T: ?Sized + Types> Sync for Cursor<'_, T> where
    // (SAFETY) Required because we hold a shared reference to a `PinList`.
    PinList<T>: Sync
{
}

impl<'list, T: ?Sized + Types> Cursor<'list, T> {
    fn current_shared(&self) -> Option<&'list NodeShared<T>> {
        // SAFETY: A cursor always points to a valid node in the list (ensured by
        // `PinList::cursor`).
        self.current
            .get()
            .map(|current| unsafe { current.as_ref() })
    }
    fn current_protected(&self) -> Option<&'list NodeProtected<T>> {
        // SAFETY: Our shared reference to the list gives us shared access to the protected data of
        // every node in it.
        Some(unsafe { &*self.current_shared()?.protected.get() })
    }
    fn current_linked(&self) -> Option<&'list NodeLinked<T>> {
        match self.current_protected()? {
            NodeProtected::Linked(linked) => Some(linked),
            NodeProtected::Removed(..) => unsafe { debug_unreachable!() },
        }
    }

    /// Move the cursor to the next element in the linked list.
    pub fn move_next(&mut self) {
        self.current = match self.current_linked() {
            Some(linked) => linked.next,
            None => self.list.head,
        };
    }

    /// Move the cursor to the previous element in the linked list.
    pub fn move_previous(&mut self) {
        self.current = match self.current_linked() {
            Some(linked) => linked.prev,
            None => self.list.tail,
        };
    }

    /// Retrieve a shared reference to the list this cursor uses.
    #[must_use]
    pub fn list(&self) -> &'list PinList<T> {
        self.list
    }

    /// Retrieve a shared reference to the protected data of this linked list node.
    ///
    /// Returns [`None`] if the cursor is the ghost cursor.
    #[must_use]
    pub fn protected(&self) -> Option<&'list T::Protected> {
        Some(&self.current_linked()?.data)
    }

    /// Retrieve a shared reference to the unprotected data of this linked list node.
    ///
    /// Returns [`None`] if the cursor is the ghost cursor.
    #[must_use]
    pub fn unprotected(&self) -> Option<&'list T::Unprotected> {
        Some(&self.current_shared()?.unprotected)
    }
}

impl<T: ?Sized + Types> Clone for Cursor<'_, T> {
    fn clone(&self) -> Self {
        Self {
            list: self.list,
            current: self.current,
        }
    }
}

impl<T: ?Sized + Types> Debug for Cursor<'_, T>
where
    T::Unprotected: Debug,
    T::Protected: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("Cursor")
            .field("list", &self.list)
            .field("protected", &self.protected())
            .field("unprotected", &self.unprotected())
            .finish()
    }
}

/// A unique cursor into a linked list.
///
/// This can be created by methods like [`PinList::cursor_ghost_mut`].
///
/// Each cursor conceptually points to a single item in the list. It can also point to the space
/// between the start and end of the list, in which case it is called the ghost cursor.
pub struct CursorMut<'list, T: ?Sized + Types> {
    pub(crate) list: &'list mut PinList<T>,
    pub(crate) current: OptionNodeShared<T>,
}

unsafe impl<T: ?Sized + Types> Send for CursorMut<'_, T> where
    // (SAFETY) Required because we hold a unique reference to a `PinList`.
    PinList<T>: Send
{
}

unsafe impl<T: ?Sized + Types> Sync for CursorMut<'_, T> where
    // (SAFETY) Required because we hold a unique reference to a `PinList`.
    PinList<T>: Sync
{
}

impl<'list, T: ?Sized + Types> CursorMut<'list, T> {
    fn current_shared(&self) -> Option<&NodeShared<T>> {
        // SAFETY: A cursor always points to a valid node in the list (ensured by
        // `PinList::cursor_mut`).
        self.current
            .get()
            .map(|current| unsafe { current.as_ref() })
    }
    fn current_protected(&self) -> Option<&NodeProtected<T>> {
        // SAFETY: Our shared reference to the list gives us shared access to the protected data of
        // every node in it.
        Some(unsafe { &*self.current_shared()?.protected.get() })
    }
    fn current_protected_mut(&mut self) -> Option<&mut NodeProtected<T>> {
        // SAFETY: Our unique reference to the list gives us unique access to the protected data of
        // every node in it.
        Some(unsafe { &mut *self.current_shared()?.protected.get() })
    }
    fn current_linked(&self) -> Option<&NodeLinked<T>> {
        match self.current_protected()? {
            NodeProtected::Linked(linked) => Some(linked),
            NodeProtected::Removed(..) => unsafe { debug_unreachable!() },
        }
    }
    fn current_linked_mut(&mut self) -> Option<&mut NodeLinked<T>> {
        match self.current_protected_mut()? {
            NodeProtected::Linked(linked) => Some(linked),
            NodeProtected::Removed(..) => unsafe { debug_unreachable!() },
        }
    }
    pub(crate) fn prev_mut(&mut self) -> &mut OptionNodeShared<T> {
        match self.current.get() {
            // Unwrap because we don't have polonius
            Some(_) => &mut self.current_linked_mut().unwrap().prev,
            None => &mut self.list.tail,
        }
    }
    pub(crate) fn next_mut(&mut self) -> &mut OptionNodeShared<T> {
        match self.current.get() {
            // Unwrap because we don't have polonius
            Some(_) => &mut self.current_linked_mut().unwrap().next,
            None => &mut self.list.head,
        }
    }

    /// Downgrade this cursor to its shared form.
    #[must_use]
    pub fn into_shared(self) -> Cursor<'list, T> {
        Cursor {
            list: self.list,
            current: self.current,
        }
    }

    /// Reborrow this cursor as its shared form.
    ///
    /// Note that reborrowing this cursor as another `CursorMut` is disallowed because it would
    /// allow invalidating this cursor while it still exists.
    #[must_use]
    pub fn as_shared(&self) -> Cursor<'_, T> {
        Cursor {
            list: self.list,
            current: self.current,
        }
    }

    /// Move the cursor to the next element in the linked list.
    pub fn move_next(&mut self) {
        self.current = *self.next_mut();
    }

    /// Move the cursor to the previous element in the linked list.
    pub fn move_previous(&mut self) {
        self.current = *self.prev_mut();
    }

    /// Retrieve a shared reference to the list this cursor uses.
    #[must_use]
    pub fn list(&self) -> &PinList<T> {
        self.list
    }

    /// Retrieve a shared reference to the protected data of this linked list node.
    ///
    /// Returns [`None`] if the cursor is currently the ghost cursor.
    #[must_use]
    pub fn protected(&self) -> Option<&T::Protected> {
        Some(&self.current_linked()?.data)
    }

    /// Retrieve a unique reference to the protected data of this linked list node.
    ///
    /// Returns [`None`] if the cursor is currently the ghost cursor.
    #[must_use]
    pub fn protected_mut(&mut self) -> Option<&mut T::Protected> {
        Some(&mut self.current_linked_mut()?.data)
    }

    /// Retrieve a shared reference to the unprotected data of this linked list node.
    ///
    /// Returns [`None`] if the cursor is currently the ghost cursor.
    #[must_use]
    pub fn unprotected(&self) -> Option<&T::Unprotected> {
        Some(&self.current_shared()?.unprotected)
    }

    /// Insert a node into the linked list before this one.
    ///
    /// # Panics
    ///
    /// Panics if the node is not in its initial state.
    pub fn insert_before<'node>(
        &mut self,
        node: Pin<&'node mut Node<T>>,
        protected: T::Protected,
        unprotected: T::Unprotected,
    ) -> Pin<&'node mut InitializedNode<'node, T>> {
        node.insert_before(self, protected, unprotected)
    }

    /// Insert a node into the linked list after this one.
    ///
    /// # Panics
    ///
    /// Panics if the node is not in its initial state.
    pub fn insert_after<'node>(
        &mut self,
        node: Pin<&'node mut Node<T>>,
        protected: T::Protected,
        unprotected: T::Unprotected,
    ) -> Pin<&'node mut InitializedNode<'node, T>> {
        node.insert_after(self, protected, unprotected)
    }

    /// Append a node to the front of the list.
    ///
    /// # Panics
    ///
    /// Panics if the node is not in its initial state.
    pub fn push_front<'node>(
        &mut self,
        node: Pin<&'node mut Node<T>>,
        protected: T::Protected,
        unprotected: T::Unprotected,
    ) -> Pin<&'node mut InitializedNode<'node, T>> {
        self.list.push_front(node, protected, unprotected)
    }

    /// Append a node to the back of the list.
    ///
    /// # Panics
    ///
    /// Panics if the node is not in its initial state.
    pub fn push_back<'node>(
        &mut self,
        node: Pin<&'node mut Node<T>>,
        protected: T::Protected,
        unprotected: T::Unprotected,
    ) -> Pin<&'node mut InitializedNode<'node, T>> {
        self.list.push_back(node, protected, unprotected)
    }

    /// Remove this node from the linked list with a given "removed" value.
    ///
    /// The cursor is moved to point to the next element in the linked list.
    ///
    /// # Errors
    ///
    /// Fails if the cursor is currently the ghost cursor (not over an item).
    pub fn remove_current(&mut self, removed: T::Removed) -> Result<T::Protected, T::Removed> {
        let mut res = Err(removed);
        self.remove_current_with(|protected| match mem::replace(&mut res, Ok(protected)) {
            Ok(..) => unsafe { debug_unreachable!() },
            Err(removed) => removed,
        });
        res
    }

    /// Remove this node from the linked list, computing its "removed" value from a closure.
    ///
    /// The cursor is moved to point to the next element in the linked list.
    ///
    /// If the given closure panics, the process will abort.
    ///
    /// Returns whether the operation was successful — it fails if the cursor is currently a ghost
    /// cursor (not over an item).
    pub fn remove_current_with<F>(&mut self, f: F) -> bool
    where
        F: FnOnce(T::Protected) -> T::Removed,
    {
        self.remove_current_with_or(f, || abort())
    }

    /// Remove this node from the linked list, computing its "removed" value from a closure, or
    /// using a secondary closure should the first panic. If the secondary closure panics, the
    /// process will abort.
    ///
    /// The cursor is moved to point to the next element in the linked list.
    ///
    /// Returns whether the operation was successful — it fails if the cursor is currently a ghost
    /// cursor (not over an item).
    pub fn remove_current_with_or<F, Fallback>(&mut self, f: F, fallback: Fallback) -> bool
    where
        F: FnOnce(T::Protected) -> T::Removed,
        Fallback: FnOnce() -> T::Removed,
    {
        let protected: *mut NodeProtected<T> = match self.current_protected_mut() {
            Some(protected) => protected,
            None => return false,
        };

        // Take the protected data so we can do things to it.
        // SAFETY: Control flow cannot exit this function until a value is placed into `protected`
        // by `ptr::write`.
        let old = match unsafe { ptr::read(protected) } {
            NodeProtected::Linked(linked) => linked,
            NodeProtected::Removed(..) => unsafe { debug_unreachable!() },
        };

        // Remove ourselves from the list.
        *unsafe { self.list.cursor_mut(old.prev) }.next_mut() = old.next;
        *unsafe { self.list.cursor_mut(old.next) }.prev_mut() = old.prev;

        // Move the cursor to the next element in the list
        self.current = old.next;

        // This guard makes sure to always set the current node's state to removed even if `f`
        // panics.
        let guard = run_on_drop(|| {
            // Since this only runs when the thread is already panicking, `fallback()` panicking
            // results in a double-panic which leads to an abort.
            let removed = NodeRemoved { data: fallback() };
            unsafe { ptr::write(protected, NodeProtected::Removed(removed)) };
        });

        // Calculate the new user data and set the state to to removed.
        let removed = NodeRemoved { data: f(old.data) };
        unsafe { ptr::write(protected, NodeProtected::Removed(removed)) };

        // Disarm the guard now that `protected` holds a valid value again.
        mem::forget(guard);

        true
    }
}

impl<T: ?Sized + Types> Debug for CursorMut<'_, T>
where
    T::Unprotected: Debug,
    T::Protected: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("CursorMut")
            .field("list", &self.list)
            .field("protected", &self.protected())
            .field("unprotected", &self.unprotected())
            .finish()
    }
}
