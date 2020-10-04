//! RFC 3339 [`full-time`] owned string type.
//!
//! [`full-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
#![cfg(feature = "alloc")]

use core::{convert::TryFrom, fmt, ops, str};

use alloc::{string::String, vec::Vec};

#[cfg(feature = "serde")]
use serde::Serialize;

use crate::{ConversionError, Error};

use super::{validate_bytes, FullTimeStr};

/// Owned string for a time in RFC 3339 [`full-time`] format, such as `12:34:56.7890-23:12`.
///
/// Available when `alloc` feature is enabled.
///
/// # Examples
///
/// ```
/// # use datetime_string::rfc3339::FullTimeString;
/// use datetime_string::rfc3339::FullTimeStr;
/// use std::convert::TryFrom;
///
/// let try_from = FullTimeString::try_from("12:34:56.7890-23:12")?;
///
/// let parse = "12:34:56.7890-23:12".parse::<FullTimeString>()?;
/// let parse2: FullTimeString = "12:34:56.7890-23:12".parse()?;
///
/// let to_owned = FullTimeStr::from_str("12:34:56.7890-23:12")?.to_owned();
/// let into: FullTimeString = FullTimeStr::from_str("12:34:56.7890-23:12")?.into();
/// # Ok::<_, datetime_string::Error>(())
/// ```
///
/// [`full-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
// Note that `derive(Serialize)` cannot used here, because it encodes this as
// `Vec<u8>` rather than as a string.
//
// Comparisons implemented for the type are consistent (at least it is intended to be so).
// See <https://github.com/rust-lang/rust-clippy/issues/2025>.
// Note that `clippy::derive_ord_xor_partial_ord` would be introduced since Rust 1.47.0.
#[allow(clippy::derive_hash_xor_eq)]
#[allow(clippy::unknown_clippy_lints, clippy::derive_ord_xor_partial_ord)]
pub struct FullTimeString(Vec<u8>);

impl FullTimeString {
    /// Creates a `FullTimeString` from the given bytes.
    ///
    /// This performs assertion in debug build, but not in release build.
    ///
    /// # Safety
    ///
    /// `validate_bytes(&s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_bytes_maybe_unchecked(s: Vec<u8>) -> Self {
        debug_assert_ok!(validate_bytes(&s));
        Self(s)
    }

    /// Returns a `&FullTimeStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeString;
    /// use datetime_string::rfc3339::FullTimeStr;
    ///
    /// let time = "12:34:56.7890-23:12".parse::<FullTimeString>()?;
    ///
    /// // Usually you don't need to call `as_deref()` explicitly, because
    /// // `Deref<Target = FullTimeStr>` trait is implemented.
    /// let _: &FullTimeStr = time.as_deref();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref(&self) -> &FullTimeStr {
        unsafe {
            // This is safe because `self.0` is valid `full-time` string.
            debug_assert_safe_version_ok!(FullTimeStr::from_bytes(&self.0));
            FullTimeStr::from_bytes_maybe_unchecked(&self.0)
        }
    }

    /// Returns a `&mut FullTimeStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeString;
    /// use datetime_string::rfc3339::FullTimeStr;
    ///
    /// let mut time = "12:34:56.7890-23:12".parse::<FullTimeString>()?;
    ///
    /// // Usually you don't need to call `as_deref_mut()` explicitly, because
    /// // `DerefMut` trait is implemented.
    /// let _: &mut FullTimeStr = time.as_deref_mut();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref_mut(&mut self) -> &mut FullTimeStr {
        unsafe {
            debug_assert_ok!(FullTimeStr::from_bytes(&self.0));
            // This is safe because `self.0` is valid, and `FullTimeStr` ensures
            // that the underlying bytes are ASCII string after modification.
            FullTimeStr::from_bytes_maybe_unchecked_mut(&mut self.0)
        }
    }
}

impl core::borrow::Borrow<FullTimeStr> for FullTimeString {
    #[inline]
    fn borrow(&self) -> &FullTimeStr {
        self.as_deref()
    }
}

impl core::borrow::BorrowMut<FullTimeStr> for FullTimeString {
    #[inline]
    fn borrow_mut(&mut self) -> &mut FullTimeStr {
        self.as_deref_mut()
    }
}

impl alloc::borrow::ToOwned for FullTimeStr {
    type Owned = FullTimeString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for FullTimeString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for FullTimeString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<FullTimeStr> for FullTimeString {
    #[inline]
    fn as_ref(&self) -> &FullTimeStr {
        self
    }
}

impl AsMut<FullTimeStr> for FullTimeString {
    #[inline]
    fn as_mut(&mut self) -> &mut FullTimeStr {
        self
    }
}

impl From<FullTimeString> for Vec<u8> {
    #[inline]
    fn from(v: FullTimeString) -> Vec<u8> {
        v.0
    }
}

impl From<FullTimeString> for String {
    #[inline]
    fn from(v: FullTimeString) -> String {
        unsafe {
            // This is safe because a valid `full-time` string is an ASCII string.
            debug_assert_ok!(str::from_utf8(&v.0));
            String::from_utf8_unchecked(v.0)
        }
    }
}

impl From<&FullTimeStr> for FullTimeString {
    fn from(v: &FullTimeStr) -> Self {
        unsafe {
            // This is safe because the value is already validated.
            Self::from_bytes_maybe_unchecked(v.0.into())
        }
    }
}

impl TryFrom<&[u8]> for FullTimeString {
    type Error = Error;

    #[inline]
    fn try_from(v: &[u8]) -> Result<Self, Self::Error> {
        FullTimeStr::from_bytes(v).map(Into::into)
    }
}

impl TryFrom<&str> for FullTimeString {
    type Error = Error;

    #[inline]
    fn try_from(v: &str) -> Result<Self, Self::Error> {
        FullTimeStr::from_str(v).map(Into::into)
    }
}

impl TryFrom<Vec<u8>> for FullTimeString {
    type Error = ConversionError<Vec<u8>>;

    #[inline]
    fn try_from(v: Vec<u8>) -> Result<Self, Self::Error> {
        match validate_bytes(&v) {
            Ok(_) => Ok(unsafe {
                // This is safe because the value is successfully validated.
                Self::from_bytes_maybe_unchecked(v)
            }),
            Err(e) => Err(ConversionError::new(v, e)),
        }
    }
}

impl TryFrom<String> for FullTimeString {
    type Error = ConversionError<String>;

    #[inline]
    fn try_from(v: String) -> Result<Self, Self::Error> {
        match validate_bytes(v.as_bytes()) {
            Ok(_) => Ok(unsafe {
                // This is safe because the value is successfully validated.
                Self::from_bytes_maybe_unchecked(v.into_bytes())
            }),
            Err(e) => Err(ConversionError::new(v, e)),
        }
    }
}

impl fmt::Display for FullTimeString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_deref().fmt(f)
    }
}

impl ops::Deref for FullTimeString {
    type Target = FullTimeStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_deref()
    }
}

impl ops::DerefMut for FullTimeString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_deref_mut()
    }
}

impl str::FromStr for FullTimeString {
    type Err = Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl_cmp_symmetric!(FullTimeStr, FullTimeString, &FullTimeString);
impl_cmp_symmetric!(FullTimeStr, FullTimeString, FullTimeStr);
impl_cmp_symmetric!(FullTimeStr, FullTimeString, &FullTimeStr);
impl_cmp_symmetric!(str, FullTimeString, str);
impl_cmp_symmetric!(str, FullTimeString, &str);
impl_cmp_symmetric!(str, &FullTimeString, str);
impl_cmp_symmetric!([u8], FullTimeString, [u8]);
impl_cmp_symmetric!([u8], FullTimeString, &[u8]);
impl_cmp_symmetric!([u8], &FullTimeString, [u8]);

#[cfg(feature = "serde")]
impl Serialize for FullTimeString {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

/// Items for serde support.
#[cfg(feature = "serde")]
mod serde_ {
    use super::*;

    use serde::de::{Deserialize, Deserializer, Visitor};

    /// Visitor for `FullTimeString`.
    struct StringVisitor;

    impl<'de> Visitor<'de> for StringVisitor {
        type Value = FullTimeString;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 full-time string")
        }

        #[inline]
        fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            Self::Value::try_from(v).map_err(E::custom)
        }

        #[inline]
        fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            Self::Value::try_from(v).map_err(E::custom)
        }
    }

    impl<'de> Deserialize<'de> for FullTimeString {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_any(StringVisitor)
        }
    }
}

#[cfg(feature = "serde")]
#[cfg(test)]
mod tests {
    use super::*;

    use serde_test::{assert_de_tokens, assert_tokens, Token};

    #[test]
    fn ser_de_string() {
        let raw: &'static str = "12:34:56.7890-23:12";
        assert_tokens(&FullTimeString::try_from(raw).unwrap(), &[Token::Str(raw)]);
    }

    #[test]
    fn de_bytes() {
        let raw: &'static [u8] = b"12:34:56.7890-23:12";
        assert_de_tokens(
            &FullTimeString::try_from(&raw[..]).unwrap(),
            &[Token::Bytes(raw)],
        );
    }
}
