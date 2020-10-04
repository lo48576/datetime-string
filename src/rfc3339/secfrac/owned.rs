//! RFC 3339 [`time-secfrac`] owned string type.
//!
//! [`time-secfrac`]: https://tools.ietf.org/html/rfc3339#section-5.6
#![cfg(feature = "alloc")]

use core::{convert::TryFrom, fmt, ops, str};

use alloc::{string::String, vec::Vec};

use crate::{ConversionError, Error};

use super::{validate_bytes, SecfracStr};

/// Owned string for a time in RFC 3339 [`time-secfrac`] format, such as `.7890`.
///
/// Available when `alloc` feature is enabled.
///
/// To create a value of this type, use [`str::parse`] method or
/// [`std::convert::TryFrom`] trait, or convert from `&SecfracStr`.
///
/// # Examples
///
/// ```
/// # use datetime_string::rfc3339::SecfracString;
/// use datetime_string::rfc3339::SecfracStr;
/// use std::convert::TryFrom;
///
/// let try_from = SecfracString::try_from(".1234")?;
///
/// let parse = ".1234".parse::<SecfracString>()?;
/// let parse2: SecfracString = ".1234".parse()?;
///
/// let to_owned = SecfracStr::from_str(".1234")?.to_owned();
/// let into: SecfracString = SecfracStr::from_str(".1234")?.into();
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
pub struct SecfracString(Vec<u8>);

impl SecfracString {
    /// Creates a `SecfracString` from the given bytes.
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

    /// Returns a `&SecfracStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracString;
    /// use datetime_string::rfc3339::SecfracStr;
    ///
    /// let secfrac = ".1234".parse::<SecfracString>()?;
    ///
    /// // Usually you don't need to call `as_deref()` explicitly, because
    /// // `Deref<Target = SecfracStr>` trait is implemented.
    /// let _: &SecfracStr = secfrac.as_deref();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref(&self) -> &SecfracStr {
        unsafe {
            // This is safe because `self.0` should be already validated.
            debug_assert_safe_version_ok!(SecfracStr::from_bytes(&self.0));
            SecfracStr::from_bytes_maybe_unchecked(&self.0)
        }
    }

    /// Returns a `&mut SecfracStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracString;
    /// use datetime_string::rfc3339::SecfracStr;
    ///
    /// let mut secfrac = ".1234".parse::<SecfracString>()?;
    ///
    /// // Usually you don't need to call `as_deref_mut()` explicitly, because
    /// // `DerefMut` trait is implemented.
    /// let _: &mut SecfracStr = secfrac.as_deref_mut();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref_mut(&mut self) -> &mut SecfracStr {
        unsafe {
            // This is safe because `self.0` should be already validated.
            debug_assert_ok!(SecfracStr::from_bytes(&self.0));
            SecfracStr::from_bytes_maybe_unchecked_mut(&mut self.0)
        }
    }
}

impl core::borrow::Borrow<SecfracStr> for SecfracString {
    #[inline]
    fn borrow(&self) -> &SecfracStr {
        self.as_deref()
    }
}

impl core::borrow::BorrowMut<SecfracStr> for SecfracString {
    #[inline]
    fn borrow_mut(&mut self) -> &mut SecfracStr {
        self.as_deref_mut()
    }
}

impl alloc::borrow::ToOwned for SecfracStr {
    type Owned = SecfracString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for SecfracString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for SecfracString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<SecfracStr> for SecfracString {
    #[inline]
    fn as_ref(&self) -> &SecfracStr {
        self
    }
}

impl AsMut<SecfracStr> for SecfracString {
    #[inline]
    fn as_mut(&mut self) -> &mut SecfracStr {
        self
    }
}

impl From<SecfracString> for Vec<u8> {
    #[inline]
    fn from(v: SecfracString) -> Vec<u8> {
        v.0
    }
}

impl From<SecfracString> for String {
    #[inline]
    fn from(v: SecfracString) -> String {
        unsafe {
            // This is safe because a valid `SecfracDigitsString` is an ASCII string.
            debug_assert_ok!(str::from_utf8(&v.0));
            String::from_utf8_unchecked(v.0)
        }
    }
}

impl From<&SecfracStr> for SecfracString {
    fn from(v: &SecfracStr) -> Self {
        unsafe {
            // This is safe because the value is already validated.
            debug_assert_ok!(validate_bytes(&v.0));
            Self::from_bytes_maybe_unchecked(v.0.into())
        }
    }
}

impl TryFrom<&[u8]> for SecfracString {
    type Error = Error;

    #[inline]
    fn try_from(v: &[u8]) -> Result<Self, Self::Error> {
        SecfracStr::from_bytes(v).map(Into::into)
    }
}

impl TryFrom<&str> for SecfracString {
    type Error = Error;

    #[inline]
    fn try_from(v: &str) -> Result<Self, Self::Error> {
        SecfracStr::from_str(v).map(Into::into)
    }
}

impl TryFrom<Vec<u8>> for SecfracString {
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

impl TryFrom<String> for SecfracString {
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

impl fmt::Display for SecfracString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_deref().fmt(f)
    }
}

impl ops::Deref for SecfracString {
    type Target = SecfracStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_deref()
    }
}

impl ops::DerefMut for SecfracString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_deref_mut()
    }
}

impl str::FromStr for SecfracString {
    type Err = Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl_cmp_symmetric!(SecfracStr, SecfracString, &SecfracString);
impl_cmp_symmetric!(SecfracStr, SecfracString, SecfracStr);
impl_cmp_symmetric!(SecfracStr, SecfracString, &SecfracStr);
impl_cmp_symmetric!(str, SecfracString, str);
impl_cmp_symmetric!(str, SecfracString, &str);
impl_cmp_symmetric!(str, &SecfracString, str);
impl_cmp_symmetric!([u8], SecfracString, [u8]);
impl_cmp_symmetric!([u8], SecfracString, &[u8]);
impl_cmp_symmetric!([u8], &SecfracString, [u8]);

#[cfg(feature = "serde")]
impl serde::Serialize for SecfracString {
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

    /// Visitor for `SecfracString`.
    struct StringVisitor;

    impl<'de> Visitor<'de> for StringVisitor {
        type Value = SecfracString;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 time-secfrac string")
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

    impl<'de> Deserialize<'de> for SecfracString {
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
        let raw: &'static str = ".1234";
        assert_tokens(&SecfracString::try_from(raw).unwrap(), &[Token::Str(raw)]);
    }

    #[test]
    fn de_bytes() {
        let raw: &'static [u8; 5] = b".1234";
        assert_de_tokens(
            &SecfracString::try_from(&raw[..]).unwrap(),
            &[Token::Bytes(raw)],
        );
    }
}
