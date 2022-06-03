//! Shared internal utilities.

use core::mem::ManuallyDrop;

pub(crate) fn run_on_drop<F: FnOnce()>(f: F) -> impl Drop {
    RunOnDrop(ManuallyDrop::new(f))
}

struct RunOnDrop<F: FnOnce()>(ManuallyDrop<F>);
impl<F: FnOnce()> Drop for RunOnDrop<F> {
    fn drop(&mut self) {
        (unsafe { ManuallyDrop::take(&mut self.0) })();
    }
}

macro_rules! debug_unreachable {
    ($($tt:tt)*) => {
        if cfg!(debug_assertions) {
            unreachable!($($tt)*)
        } else {
            core::hint::unreachable_unchecked()
        }
    }
}
pub(crate) use debug_unreachable;

#[cold]
pub(crate) fn abort() -> ! {
    // When `std` is not available, a double-panic will turn into an abort. Don’t use it always
    // though because it has worse codegen than a plain abort.
    #[cfg(not(feature = "std"))]
    {
        let _guard = run_on_drop(|| panic!());
        panic!();
    }
    #[cfg(feature = "std")]
    std::process::abort();
}

/// A public but not exposed helper trait used to work around the lack of trait bounds in `const
/// fn`s on this crate's MSRV. Instead of writing `T: Bound` which doesn't work, one can write
/// `<T as ConstFnBounds>::Type: Bound` which does work (it was originally an oversight that this
/// was allowed, but in later versions it was stabilized so it's fine to rely on it now).
pub trait ConstFnBounds {
    type Type: ?Sized;
}
impl<T: ?Sized> ConstFnBounds for T {
    type Type = T;
}

/// Polyfill for `Option::unwrap_unchecked`, since this crate's MSRV is older than the
/// stabilization of that function.
pub(crate) unsafe fn unwrap_unchecked<T>(opt: Option<T>) -> T {
    match opt {
        Some(val) => val,
        // SAFETY: The caller ensures the `Option` is not `None`.
        None => unsafe { debug_unreachable!() },
    }
}
