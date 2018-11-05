#![cfg_attr(test, deny(warnings))]
#![cfg_attr(test, deny(bad_style))]
#![cfg_attr(test, deny(future_incompatible))]
#![cfg_attr(test, deny(nonstandard_style))]
#![cfg_attr(test, deny(rust_2018_compatibility))]
#![cfg_attr(test, deny(rust_2018_idioms))]

#[allow(unused)]
#[macro_use]
extern crate log;
extern crate crossbeam_epoch as epoch;

#[cfg(any(test, feature = "lock_free_delays"))]
extern crate rand;

#[cfg(any(test, feature = "lock_free_delays"))]
mod debug_delay;

#[cfg(any(test, feature = "lock_free_delays"))]
pub use self::debug_delay::debug_delay;

/// This function is useful for inducing random jitter into our atomic
/// operations, shaking out more possible interleavings quickly. It gets
/// fully elliminated by the compiler in non-test code.
#[cfg(not(any(test, feature = "lock_free_delays")))]
#[inline(always)]
pub fn debug_delay() {}

pub use crate::epoch::{
    pin, unprotected, Atomic, Guard, Owned, Shared,
};

use std::{
    ops::{Deref, DerefMut},
    sync as s,
    sync::atomic as a,
};

macro_rules! new {
    ($name:ident, $outer:ty, $new:expr, $inner:ty) => {
        new!($name, $outer, $new, $inner,);
    };
    ($name:ident, $outer:ty, $new:expr) => {
        impl $outer {
            pub fn new() -> $outer {
                debug_delay();
                $name(($new)())
            }
        }
    };
    ($name:ident, $outer:ty, $new:expr, $inner:ty, $($t:tt),*) => {
        impl<$($t),*> $outer {
            pub fn new(inner: $inner) -> $outer {
                debug_delay();
                $name(($new)(inner))
            }
        }
    };
}

macro_rules! delay {
    ($outer:ty, $inner:ty) => {
        delay!($outer, $inner,);
    };
    ($outer:ty, $inner:ty, $($t:tt),*) => {
        impl<$($t),*> Deref for $outer {
            type Target = $inner;

            #[inline(always)]
            fn deref(&self) -> &Self::Target {
                debug_delay();
                &self.0
            }
        }

        impl<$($t),*> DerefMut for $outer {
            #[inline(always)]
            fn deref_mut(&mut self) -> &mut Self::Target {
                debug_delay();
                &mut self.0
            }
        }

        impl<$($t),*> Drop for $outer {
            #[inline(always)]
            fn drop(&mut self) {
                debug_delay();
            }
        }
    };
}

pub struct Arc<T>(s::Arc<T>);
delay!(Arc<T>, s::Arc<T>, T);
new!(Arc, Arc<T>, s::Arc::new, T, T);

pub struct Mutex<T>(s::Mutex<T>);
delay!(Mutex<T>, s::Mutex<T>, T);
new!(Mutex, Mutex<T>, s::Mutex::new, T, T);

impl<T> Mutex<T> {
    pub fn lock(&self) -> s::LockResult<MutexGuard<'_, T>> {
        self.0.lock().map(|mg| MutexGuard(mg)).map_err(|poisoned| {
            let inner = poisoned.into_inner();
            let wrapped = MutexGuard(inner);
            s::PoisonError::new(wrapped)
        })
    }
}

pub struct MutexGuard<'a, T: 'a>(s::MutexGuard<'a, T>);
delay!(MutexGuard<'a, T>, s::MutexGuard<'a, T>, 'a, T);

pub struct RwLock<T>(s::RwLock<T>);
delay!(RwLock<T>, s::RwLock<T>, T);
new!(RwLock, RwLock<T>, s::RwLock::new, T, T);

pub struct RwLockReadGuard<'a, T: 'a>(s::RwLockReadGuard<'a, T>);
delay!(RwLockReadGuard<'a, T>, s::RwLockReadGuard<'a, T>, 'a, T);

pub struct RwLockWriteGuard<'a, T: 'a>(s::RwLockWriteGuard<'a, T>);
delay!(RwLockWriteGuard<'a, T>, s::RwLockWriteGuard<'a, T>, 'a, T);

pub struct Condvar(s::Condvar);
delay!(Condvar, s::Condvar);
new!(Condvar, Condvar, s::Condvar::new);
pub use crate::a::Ordering;

pub struct AtomicUsize(a::AtomicUsize);
delay!(AtomicUsize, a::AtomicUsize);
new!(AtomicUsize, AtomicUsize, a::AtomicUsize::new, usize);

pub struct AtomicBool(a::AtomicBool);
delay!(AtomicBool, a::AtomicBool);
new!(AtomicBool, AtomicBool, a::AtomicBool::new, bool);

pub struct AtomicIsize(a::AtomicIsize);
delay!(AtomicIsize, a::AtomicIsize);
new!(AtomicIsize, AtomicIsize, a::AtomicIsize::new, isize);

#[cfg(feature = "integer_atomics")]
pub struct AtomicI64(a::AtomicI64);
#[cfg(feature = "integer_atomics")]
delay!(AtomicI64, a::AtomicI64);
#[cfg(feature = "integer_atomics")]
new!(AtomicI64, AtomicI64, a::AtomicI64::new, i64);

#[cfg(feature = "integer_atomics")]
pub struct AtomicU64(a::AtomicU64);
#[cfg(feature = "integer_atomics")]
delay!(AtomicU64, a::AtomicU64);
#[cfg(feature = "integer_atomics")]
new!(AtomicU64, AtomicU64, a::AtomicU64::new, u64);

#[inline(always)]
pub fn spin_loop_hint() {
    a::spin_loop_hint();
}

#[test]
fn works() {
    let a = Arc::new(Mutex::new(0));

    let t = std::thread::spawn({
        let a = a.clone();
        move || {
            let mut am = a.lock().unwrap();
            **am += 1;
        }
    });

    t.join().unwrap();

    let am = a.lock().unwrap();
    assert_eq!(**am, 1);
}
