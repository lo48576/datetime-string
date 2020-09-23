//! Macros for internal use.

/// Asserts that the safe alternative should return `Ok(_)`.
macro_rules! debug_assert_safe_version_ok {
    ($result:expr) => {
        if cfg!(debug_assertions) {
            if let core::result::Result::Err(e) = $result {
                panic!(
                    "Assertion by safe version failed (expr = {}): {}",
                    stringify!($result),
                    e
                );
            }
        }
    };
}

/// Asserts that the expression must return `Ok(_)`.
macro_rules! debug_assert_ok {
    ($result:expr) => {
        if cfg!(debug_assertions) {
            if let core::result::Result::Err(e) = $result {
                panic!("Assertion failed (expr = {}): {}", stringify!($result), e);
            }
        }
    };
    ($result:expr, $($arg:tt)+) => {
        if cfg!(debug_assertions) {
            if let core::result::Result::Err(e) = $result {
                panic!(
                    "Assertion failed: {} (expr = {}): {}",
                    format_args!("{}", $($arg)+),
                    stringify!($result),
                    e
                );
            }
        }
    };
}

/// Asserts that the safe alternative should return `Some(_)`.
macro_rules! debug_assert_safe_version_some {
    ($opt:expr) => {
        if cfg!(debug_assertions) {
            if $opt.is_none() {
                panic!(
                    "Assertion by safe version failed (expr = {}): expected `Some` but got `None`",
                    stringify!($opt)
                );
            }
        }
    };
}

/// Implement `PartialEq` and `Eq` for the given types.
macro_rules! impl_cmp {
    ($ty_common:ty, $ty_lhs:ty, $ty_rhs:ty) => {
        impl PartialEq<$ty_rhs> for $ty_lhs {
            #[inline]
            fn eq(&self, o: &$ty_rhs) -> bool {
                <$ty_common as PartialEq<$ty_common>>::eq(AsRef::as_ref(self), AsRef::as_ref(o))
            }
        }
        impl PartialOrd<$ty_rhs> for $ty_lhs {
            #[inline]
            fn partial_cmp(&self, o: &$ty_rhs) -> Option<core::cmp::Ordering> {
                <$ty_common as PartialOrd<$ty_common>>::partial_cmp(
                    AsRef::as_ref(self),
                    AsRef::as_ref(o),
                )
            }
        }
    };
}

/// Implement `PartialEq` and `Eq` symmetrically for the given types.
macro_rules! impl_cmp_symmetric {
    ($ty_common:ty, $ty_lhs:ty, $ty_rhs:ty) => {
        impl_cmp!($ty_common, $ty_lhs, $ty_rhs);
        impl_cmp!($ty_common, $ty_rhs, $ty_lhs);
    };
}
