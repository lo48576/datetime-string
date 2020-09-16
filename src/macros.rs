//! Macros for internal use.

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
