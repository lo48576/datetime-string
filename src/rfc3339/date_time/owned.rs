//! RFC 3339 [`date-time`] owned string type.
//!
//! [`date-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
#![cfg(feature = "alloc")]

use core::{convert::TryFrom, fmt, ops, str};

use alloc::{string::String, vec::Vec};

#[cfg(feature = "serde")]
use serde::Serialize;

use crate::Error;

use super::{validate_bytes, DateTimeStr};

/// Owned string for a datetime in RFC 3339 [`date-time`] format, such as
/// `2001-06-17T12:34:56.7890-23:12`.
///
/// # Examples
///
/// ```
/// # use datetime_string::rfc3339::DateTimeString;
/// use datetime_string::rfc3339::DateTimeStr;
/// use std::convert::TryFrom;
///
/// let try_from = DateTimeString::try_from("2001-06-17T12:34:56.7890-23:12")?;
///
/// let parse = "2001-06-17T12:34:56.7890-23:12".parse::<DateTimeString>()?;
/// let parse2: DateTimeString = "2001-06-17T12:34:56.7890-23:12".parse()?;
///
/// let to_owned = DateTimeStr::from_str("2001-06-17T12:34:56.7890-23:12")?.to_owned();
/// let into: DateTimeString = DateTimeStr::from_str("2001-06-17T12:34:56.7890-23:12")?.into();
/// # Ok::<_, datetime_string::Error>(())
/// ```
///
/// [`date-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
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
pub struct DateTimeString(Vec<u8>);

impl DateTimeString {
    /// Creates a `DateTimeString` from the given bytes.
    ///
    /// # Safety
    ///
    /// `validate_bytes(&s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_bytes_unchecked(s: Vec<u8>) -> Self {
        Self(s)
    }

    /// Returns a `&DateTimeStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeString;
    /// use datetime_string::rfc3339::DateTimeStr;
    ///
    /// let datetime = "2001-06-17T12:34:56.7890-23:12".parse::<DateTimeString>()?;
    ///
    /// // Usually you don't need to call `as_deref()` explicitly, because
    /// // `Deref<Target = DateTimeStr>` trait is implemented.
    /// let _: &DateTimeStr = datetime.as_deref();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref(&self) -> &DateTimeStr {
        unsafe {
            // This is safe because `self.0` is already validated.
            debug_assert_safe_version_ok!(DateTimeStr::from_bytes(&self.0));
            DateTimeStr::from_bytes_unchecked(&self.0)
        }
    }

    /// Returns a `&mut DateTimeStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeString;
    /// use datetime_string::rfc3339::DateTimeStr;
    ///
    /// let mut datetime = "2001-06-17T12:34:56.7890-23:12".parse::<DateTimeString>()?;
    ///
    /// // Usually you don't need to call `as_deref_mut()` explicitly, because
    /// // `DerefMut` trait is implemented.
    /// let _: &mut DateTimeStr = datetime.as_deref_mut();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref_mut(&mut self) -> &mut DateTimeStr {
        unsafe {
            // This is safe because `self.0` is already validated.
            debug_assert_ok!(DateTimeStr::from_bytes(&self.0));
            DateTimeStr::from_bytes_unchecked_mut(&mut self.0)
        }
    }
}

impl core::borrow::Borrow<DateTimeStr> for DateTimeString {
    #[inline]
    fn borrow(&self) -> &DateTimeStr {
        self.as_deref()
    }
}

impl core::borrow::BorrowMut<DateTimeStr> for DateTimeString {
    #[inline]
    fn borrow_mut(&mut self) -> &mut DateTimeStr {
        self.as_deref_mut()
    }
}

impl alloc::borrow::ToOwned for DateTimeStr {
    type Owned = DateTimeString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for DateTimeString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for DateTimeString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<DateTimeStr> for DateTimeString {
    #[inline]
    fn as_ref(&self) -> &DateTimeStr {
        self
    }
}

impl AsMut<DateTimeStr> for DateTimeString {
    #[inline]
    fn as_mut(&mut self) -> &mut DateTimeStr {
        self
    }
}

impl From<DateTimeString> for Vec<u8> {
    #[inline]
    fn from(v: DateTimeString) -> Vec<u8> {
        v.0
    }
}

impl From<DateTimeString> for String {
    #[inline]
    fn from(v: DateTimeString) -> String {
        unsafe {
            // This is safe because a valid `DateTimeString` is an ASCII string.
            debug_assert_ok!(str::from_utf8(&v.0));
            String::from_utf8_unchecked(v.0)
        }
    }
}

impl From<&DateTimeStr> for DateTimeString {
    fn from(v: &DateTimeStr) -> Self {
        debug_assert_ok!(validate_bytes(&v.0));
        unsafe {
            // This is safe because the value is already validated.
            Self::from_bytes_unchecked(v.0.into())
        }
    }
}

impl TryFrom<&[u8]> for DateTimeString {
    type Error = Error;

    #[inline]
    fn try_from(v: &[u8]) -> Result<Self, Self::Error> {
        DateTimeStr::from_bytes(v).map(Into::into)
    }
}

impl TryFrom<&str> for DateTimeString {
    type Error = Error;

    #[inline]
    fn try_from(v: &str) -> Result<Self, Self::Error> {
        DateTimeStr::from_str(v).map(Into::into)
    }
}

impl TryFrom<Vec<u8>> for DateTimeString {
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

impl fmt::Display for DateTimeString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_deref().fmt(f)
    }
}

impl ops::Deref for DateTimeString {
    type Target = DateTimeStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_deref()
    }
}

impl ops::DerefMut for DateTimeString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_deref_mut()
    }
}

impl str::FromStr for DateTimeString {
    type Err = Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl_cmp_symmetric!(DateTimeStr, DateTimeString, &DateTimeString);
impl_cmp_symmetric!(DateTimeStr, DateTimeString, DateTimeStr);
impl_cmp_symmetric!(DateTimeStr, DateTimeString, &DateTimeStr);
impl_cmp_symmetric!(str, DateTimeString, str);
impl_cmp_symmetric!(str, DateTimeString, &str);
impl_cmp_symmetric!(str, &DateTimeString, str);
impl_cmp_symmetric!([u8], DateTimeString, [u8]);
impl_cmp_symmetric!([u8], DateTimeString, &[u8]);
impl_cmp_symmetric!([u8], &DateTimeString, [u8]);

#[cfg(feature = "serde")]
impl Serialize for DateTimeString {
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

    /// Visitor for `DateTimeString`.
    struct StringVisitor;

    impl<'de> Visitor<'de> for StringVisitor {
        type Value = DateTimeString;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 date-time string")
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

    impl<'de> Deserialize<'de> for DateTimeString {
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
        let raw: &'static str = "2001-06-17T12:34:56.7890-23:12";
        assert_tokens(&DateTimeString::try_from(raw).unwrap(), &[Token::Str(raw)]);
    }

    #[test]
    fn de_bytes() {
        let raw: &'static [u8] = b"2001-06-17T12:34:56.7890-23:12";
        assert_de_tokens(
            &DateTimeString::try_from(&raw[..]).unwrap(),
            &[Token::Bytes(raw)],
        );
    }
}
