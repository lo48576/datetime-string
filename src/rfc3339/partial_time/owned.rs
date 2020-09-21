//! RFC 3339 [`partial-time`] owned string type.
//!
//! [`partial-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
#![cfg(feature = "alloc")]

use core::{convert::TryFrom, fmt, ops, str};

use alloc::{string::String, vec::Vec};

#[cfg(feature = "serde")]
use serde::Serialize;

use crate::Error;

use super::{validate_bytes, PartialTimeStr};

/// Owned string for a time in RFC 3339 [`partial-time`] format, such as `12:34:56.7890`.
///
/// This is "partial", because it is not associated to a time offset.
///
/// To create a value of this type, use [`str::parse`] method or
/// [`std::convert::TryFrom`] trait, or convert from `&PartialTimeStr`.
///
/// # Examples
///
/// ```
/// # use datetime_string::rfc3339::PartialTimeString;
/// use datetime_string::rfc3339::PartialTimeStr;
/// use std::convert::TryFrom;
///
/// let try_from = PartialTimeString::try_from("12:34:56.7890")?;
///
/// let parse = "12:34:56.7890".parse::<PartialTimeString>()?;
/// let parse2: PartialTimeString = "12:34:56.7890".parse()?;
///
/// let to_owned = PartialTimeStr::from_str("12:34:56.7890")?.to_owned();
/// let into: PartialTimeString = PartialTimeStr::from_str("12:34:56.7890")?.into();
/// # Ok::<_, datetime_string::Error>(())
/// ```
///
/// [`partial-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
// Comparisons implemented for the type are consistent (at least it is intended to be so).
// See <https://github.com/rust-lang/rust-clippy/issues/2025>.
// Note that `clippy::derive_ord_xor_partial_ord` would be introduced since Rust 1.47.0.
#[allow(clippy::derive_hash_xor_eq)]
#[allow(clippy::unknown_clippy_lints, clippy::derive_ord_xor_partial_ord)]
pub struct PartialTimeString(String);

impl PartialTimeString {
    /// Creates a `PartialTimeString` from the given string.
    ///
    /// # Safety
    ///
    /// `validate_bytes(&s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_string_unchecked(s: String) -> Self {
        Self(s)
    }

    /// Creates a `PartialTimeString` from the given bytes.
    ///
    /// # Safety
    ///
    /// `validate_bytes(&s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_bytes_unchecked(s: Vec<u8>) -> Self {
        Self(String::from_utf8_unchecked(s))
    }

    /// Returns a `&PartialTimeStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::PartialTimeString;
    /// use datetime_string::rfc3339::PartialTimeStr;
    ///
    /// let time = "12:34:56.7890".parse::<PartialTimeString>()?;
    ///
    /// // Usually you don't need to call `as_deref()` explicitly, because
    /// // `Deref<Target = PartialTimeStr>` trait is implemented.
    /// let _: &PartialTimeStr = time.as_deref();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref(&self) -> &PartialTimeStr {
        unsafe {
            // This is safe because `self.0` is valid partial-time string.
            PartialTimeStr::from_str_unchecked(&self.0)
        }
    }

    /// Returns a `&mut PartialTimeStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::PartialTimeString;
    /// use datetime_string::rfc3339::PartialTimeStr;
    ///
    /// let mut time = "12:34:56.7890".parse::<PartialTimeString>()?;
    ///
    /// // Usually you don't need to call `as_deref_mut()` explicitly, because
    /// // `DerefMut` trait is implemented.
    /// let _: &mut PartialTimeStr = time.as_deref_mut();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref_mut(&mut self) -> &mut PartialTimeStr {
        unsafe {
            // This is safe because `self.0` is valid partial-time string.
            PartialTimeStr::from_str_unchecked_mut(&mut self.0)
        }
    }
}

impl core::borrow::Borrow<PartialTimeStr> for PartialTimeString {
    #[inline]
    fn borrow(&self) -> &PartialTimeStr {
        self.as_deref()
    }
}

impl core::borrow::BorrowMut<PartialTimeStr> for PartialTimeString {
    #[inline]
    fn borrow_mut(&mut self) -> &mut PartialTimeStr {
        self.as_deref_mut()
    }
}

impl AsRef<[u8]> for PartialTimeString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for PartialTimeString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<PartialTimeStr> for PartialTimeString {
    #[inline]
    fn as_ref(&self) -> &PartialTimeStr {
        self
    }
}

impl From<PartialTimeString> for Vec<u8> {
    #[inline]
    fn from(v: PartialTimeString) -> Vec<u8> {
        v.0.into_bytes()
    }
}

impl From<PartialTimeString> for String {
    #[inline]
    fn from(v: PartialTimeString) -> String {
        v.0
    }
}

impl From<&PartialTimeStr> for PartialTimeString {
    fn from(v: &PartialTimeStr) -> Self {
        unsafe {
            // This is safe because the value is already validated.
            Self::from_string_unchecked(v.as_str().into())
        }
    }
}

impl TryFrom<&[u8]> for PartialTimeString {
    type Error = Error;

    #[inline]
    fn try_from(v: &[u8]) -> Result<Self, Self::Error> {
        PartialTimeStr::from_bytes(v).map(Into::into)
    }
}

impl TryFrom<&str> for PartialTimeString {
    type Error = Error;

    #[inline]
    fn try_from(v: &str) -> Result<Self, Self::Error> {
        PartialTimeStr::from_str(v).map(Into::into)
    }
}

impl TryFrom<Vec<u8>> for PartialTimeString {
    type Error = Error;

    #[inline]
    fn try_from(v: Vec<u8>) -> Result<Self, Self::Error> {
        validate_bytes(&v)?;
        Ok(unsafe {
            // This is safe because the value is successfully validated.
            Self::from_bytes_unchecked(v)
        })
    }
}

impl fmt::Display for PartialTimeString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_deref().fmt(f)
    }
}

impl ops::Deref for PartialTimeString {
    type Target = PartialTimeStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_deref()
    }
}

impl ops::DerefMut for PartialTimeString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_deref_mut()
    }
}

impl str::FromStr for PartialTimeString {
    type Err = Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl_cmp_symmetric!(PartialTimeStr, PartialTimeString, &PartialTimeString);
impl_cmp_symmetric!(PartialTimeStr, PartialTimeString, PartialTimeStr);
impl_cmp_symmetric!(PartialTimeStr, PartialTimeString, &PartialTimeStr);
impl_cmp_symmetric!(str, PartialTimeString, str);
impl_cmp_symmetric!(str, PartialTimeString, &str);
impl_cmp_symmetric!(str, &PartialTimeString, str);
impl_cmp_symmetric!([u8], PartialTimeString, [u8]);
impl_cmp_symmetric!([u8], PartialTimeString, &[u8]);
impl_cmp_symmetric!([u8], &PartialTimeString, [u8]);

/// Items for serde support.
#[cfg(feature = "serde")]
mod serde_ {
    use super::*;

    use serde::de::{Deserialize, Deserializer, Visitor};

    /// Visitor for `PartialTimeString`.
    struct StringVisitor;

    impl<'de> Visitor<'de> for StringVisitor {
        type Value = PartialTimeString;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 partial-time string")
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

    impl<'de> Deserialize<'de> for PartialTimeString {
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
        let raw: &'static str = "12:34:56.7890";
        assert_tokens(
            &PartialTimeString::try_from(raw).unwrap(),
            &[Token::Str(raw)],
        );
    }

    #[test]
    fn de_bytes() {
        let raw: &'static [u8; 13] = b"12:34:56.7890";
        assert_de_tokens(
            &PartialTimeString::try_from(&raw[..]).unwrap(),
            &[Token::Bytes(raw)],
        );
    }
}
