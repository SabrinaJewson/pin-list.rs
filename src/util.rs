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

pub trait ConstFnBounds {
    type Type: ?Sized;
}
impl<T: ?Sized> ConstFnBounds for T {
    type Type = T;
}

// Polyfill for `Option::unwrap_unchecked`
pub(crate) unsafe fn unwrap_unchecked<T>(opt: Option<T>) -> T {
    match opt {
        Some(val) => val,
        None => unsafe { debug_unreachable!() },
    }
}
