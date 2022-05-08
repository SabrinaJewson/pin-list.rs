# wait-list

This crate provides `WaitList`, the most fundamental type for async synchronization. `WaitList`
is implemented as an intrusive linked list of futures.

## Feature flags

- `std`: Implements the `Lock` traits on locks from the standard library.
- `lock_api_04`: Implements the `Lock` traits on locks from [`lock_api`] v0.4. This enables
integration of crates like [`parking_lot`], [`spin`] and [`usync`].

[`lock_api`]: https://docs.rs/lock_api
[`parking_lot`]: https://docs.rs/parking_lot
[`spin`]: https://docs.rs/spin
[`usync`]: https://docs.rs/usync

License: MIT
