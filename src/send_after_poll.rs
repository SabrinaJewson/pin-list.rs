use core::future::Future;

/// A marker trait for a future that can be treated as [`Send`], but only after it has been polled
/// for the first time.
///
/// Any [`Send`] future can implement this trait, so it is mostly useful for futures that would
/// otherwise be totally `!`[`Send`].
///
/// To await a future that implements this trait in a way that means that outer future remains
/// `Send` use the macro [`await_send_after_poll!`].
///
/// # Safety
///
/// Any type implementing this trait must be sendable across a thread boundary after
/// [`Future::poll`] has been called for the first time.
pub unsafe trait SendAfterPoll: Future {}

/// Await a [`SendAfterPoll`] future in such a way that the parent future remains [`Send`].
#[macro_export]
macro_rules! await_send_after_poll {
    ($fut:expr $(,)?) => {{
        // Use a match to avoid expand `$fut` in an `unsafe` context while also avoiding making the
        // outer future `!Send`.
        let future = match $fut {
            // SAFETY: We immediately `.await` the future, leaving no room for it to be sent to
            // another thread.
            future => unsafe { $crate::__private::send_after_poll::PolledImmediately::new(future) },
        };
        future.await
    }};
}

#[doc(hidden)]
pub mod private {
    use super::SendAfterPoll;
    use core::future::Future;
    use core::pin::Pin;
    use core::task;
    use core::task::Poll;
    use pin_project_lite::pin_project;

    pin_project! {
        pub struct PolledImmediately<F> {
            #[pin]
            inner: F,
        }
    }
    impl<F> PolledImmediately<F> {
        /// Assert that a future stays on the same thread before its first poll.
        ///
        /// # Safety
        ///
        /// The future must not be sent to another thread before it polled for the first time.
        pub unsafe fn new(inner: F) -> Self {
            Self { inner }
        }
    }

    // SAFETY: The safety contract of `Self::new` guarantees that we won't actually be sent
    // anywhere before we're polled for the first time.
    unsafe impl<F: SendAfterPoll> Send for PolledImmediately<F> {}

    impl<F: Future> Future for PolledImmediately<F> {
        type Output = F::Output;
        fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
            self.project().inner.poll(cx)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::SendAfterPoll;
    use crate::test_util::AssertNotSend;
    use crate::test_util::AssertSend;
    use core::future::Future;
    use core::marker::PhantomData;
    use core::pin::Pin;
    use core::task;
    use core::task::Poll;

    #[test]
    fn makes_future_send() {
        struct Fut(PhantomData<*mut ()>);
        impl Future for Fut {
            type Output = u32;
            fn poll(self: Pin<&mut Self>, _cx: &mut task::Context<'_>) -> Poll<Self::Output> {
                unreachable!()
            }
        }
        unsafe impl SendAfterPoll for Fut {}

        async { await_send_after_poll!(Fut(PhantomData)) }.assert_send();
        async { Fut(PhantomData).await }.assert_not_send();
    }
}
