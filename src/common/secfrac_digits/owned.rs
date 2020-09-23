//! Digits of fractions of a second.
#![cfg(feature = "alloc")]

use core::{convert::TryFrom, fmt, ops, str};

use alloc::{string::String, vec::Vec};

use crate::Error;

use super::{validate_bytes, SecfracDigitsStr};

/// String slice for digits of fractions of a second.
///
/// Note that values of this type cannot be not empty string.
///
/// To create a value of this type, use [`str::parse`] method or
/// [`std::convert::TryFrom`] trait, or convert from `&SecfracDigitsStr`.
///
/// # Examples
///
/// ```
/// # use datetime_string::common::SecfracDigitsString;
/// use datetime_string::common::SecfracDigitsStr;
/// use std::convert::TryFrom;
///
/// let try_from = SecfracDigitsString::try_from("1234")?;
///
/// let parse = "1234".parse::<SecfracDigitsString>()?;
/// let parse2: SecfracDigitsString = "1234".parse()?;
///
/// let to_owned = SecfracDigitsStr::from_str("1234")?.to_owned();
/// let into: SecfracDigitsString = SecfracDigitsStr::from_str("1234")?.into();
/// # Ok::<_, datetime_string::Error>(())
/// ```
///
/// [`time-secfrac`]: https://tools.ietf.org/html/rfc3339#section-5.6
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
// Note that `derive(Serialize)` cannot used here, because it encodes this as
// `[u8; 8]` rather than as a string.
//
// Comparisons implemented for the type are consistent (at least it is intended to be so).
// See <https://github.com/rust-lang/rust-clippy/issues/2025>.
// Note that `clippy::derive_ord_xor_partial_ord` would be introduced since Rust 1.47.0.
#[allow(clippy::derive_hash_xor_eq)]
#[allow(clippy::unknown_clippy_lints, clippy::derive_ord_xor_partial_ord)]
pub struct SecfracDigitsString(Vec<u8>);

impl SecfracDigitsString {
    /// Creates a `SecfracDigitsString` from the given bytes.
    ///
    /// # Safety
    ///
    /// `validate_bytes(&s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_bytes_unchecked(s: Vec<u8>) -> Self {
        Self(s)
    }

    /// Returns a `&SecfracDigitsStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsString;
    /// use datetime_string::common::SecfracDigitsStr;
    ///
    /// let secfrac = "1234".parse::<SecfracDigitsString>()?;
    ///
    /// // Usually you don't need to call `as_deref()` explicitly, because
    /// // `Deref<Target = SecfracDigitsStr>` trait is implemented.
    /// let _: &SecfracDigitsStr = secfrac.as_deref();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref(&self) -> &SecfracDigitsStr {
        unsafe {
            // This is safe because `self.0` is already validated.
            SecfracDigitsStr::from_bytes_unchecked(&self.0)
        }
    }

    /// Returns a `&mut SecfracDigitsStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsString;
    /// use datetime_string::common::SecfracDigitsStr;
    ///
    /// let mut secfrac = "1234".parse::<SecfracDigitsString>()?;
    ///
    /// // Usually you don't need to call `as_deref_mut()` explicitly, because
    /// // `DerefMut` trait is implemented.
    /// let _: &mut SecfracDigitsStr = secfrac.as_deref_mut();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref_mut(&mut self) -> &mut SecfracDigitsStr {
        unsafe {
            // This is safe because `self.0` is already validated.
            SecfracDigitsStr::from_bytes_unchecked_mut(&mut self.0)
        }
    }
}

impl core::borrow::Borrow<SecfracDigitsStr> for SecfracDigitsString {
    #[inline]
    fn borrow(&self) -> &SecfracDigitsStr {
        self.as_deref()
    }
}

impl core::borrow::BorrowMut<SecfracDigitsStr> for SecfracDigitsString {
    #[inline]
    fn borrow_mut(&mut self) -> &mut SecfracDigitsStr {
        self.as_deref_mut()
    }
}

impl alloc::borrow::ToOwned for SecfracDigitsStr {
    type Owned = SecfracDigitsString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for SecfracDigitsString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsRef<str> for SecfracDigitsString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<SecfracDigitsStr> for SecfracDigitsString {
    #[inline]
    fn as_ref(&self) -> &SecfracDigitsStr {
        self
    }
}

impl AsMut<SecfracDigitsStr> for SecfracDigitsString {
    #[inline]
    fn as_mut(&mut self) -> &mut SecfracDigitsStr {
        self
    }
}

impl From<SecfracDigitsString> for Vec<u8> {
    #[inline]
    fn from(v: SecfracDigitsString) -> Vec<u8> {
        v.0
    }
}

impl From<SecfracDigitsString> for String {
    #[inline]
    fn from(v: SecfracDigitsString) -> String {
        unsafe {
            // This is safe because a valid `SecfracDigitsString` is an ASCII string.
            String::from_utf8_unchecked(v.0)
        }
    }
}

impl From<&SecfracDigitsStr> for SecfracDigitsString {
    fn from(v: &SecfracDigitsStr) -> Self {
        unsafe {
            // This is safe because the value is already validated.
            Self::from_bytes_unchecked(v.as_bytes().into())
        }
    }
}

impl TryFrom<&[u8]> for SecfracDigitsString {
    type Error = Error;

    #[inline]
    fn try_from(v: &[u8]) -> Result<Self, Self::Error> {
        SecfracDigitsStr::from_bytes(v).map(Into::into)
    }
}

impl TryFrom<&str> for SecfracDigitsString {
    type Error = Error;

    #[inline]
    fn try_from(v: &str) -> Result<Self, Self::Error> {
        SecfracDigitsStr::from_str(v).map(Into::into)
    }
}

impl TryFrom<Vec<u8>> for SecfracDigitsString {
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

impl fmt::Display for SecfracDigitsString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_deref().fmt(f)
    }
}

impl ops::Deref for SecfracDigitsString {
    type Target = SecfracDigitsStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_deref()
    }
}

impl ops::DerefMut for SecfracDigitsString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_deref_mut()
    }
}

impl str::FromStr for SecfracDigitsString {
    type Err = Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl_cmp_symmetric!(SecfracDigitsStr, SecfracDigitsString, &SecfracDigitsString);
impl_cmp_symmetric!(SecfracDigitsStr, SecfracDigitsString, SecfracDigitsStr);
impl_cmp_symmetric!(SecfracDigitsStr, SecfracDigitsString, &SecfracDigitsStr);
impl_cmp_symmetric!(str, SecfracDigitsString, str);
impl_cmp_symmetric!(str, SecfracDigitsString, &str);
impl_cmp_symmetric!(str, &SecfracDigitsString, str);
impl_cmp_symmetric!([u8], SecfracDigitsString, [u8]);
impl_cmp_symmetric!([u8], SecfracDigitsString, &[u8]);
impl_cmp_symmetric!([u8], &SecfracDigitsString, [u8]);

#[cfg(feature = "serde")]
impl serde::Serialize for SecfracDigitsString {
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

    /// Visitor for `SecfracDigitsString`.
    struct StringVisitor;

    impl<'de> Visitor<'de> for StringVisitor {
        type Value = SecfracDigitsString;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("digits of fractions of a second")
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

    impl<'de> Deserialize<'de> for SecfracDigitsString {
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
        let raw: &'static str = "1234";
        assert_tokens(
            &SecfracDigitsString::try_from(raw).unwrap(),
            &[Token::Str(raw)],
        );
    }

    #[test]
    fn de_bytes() {
        let raw: &'static [u8; 4] = b"1234";
        assert_de_tokens(
            &SecfracDigitsString::try_from(&raw[..]).unwrap(),
            &[Token::Bytes(raw)],
        );
    }
}
