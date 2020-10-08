//! RFC 3339 [`time-offset`] owned string type.
//!
//! [`time-offset`]: https://tools.ietf.org/html/rfc3339#section-5.6
#![cfg(feature = "alloc")]

use core::{convert::TryFrom, fmt, ops, str};

use alloc::{borrow::ToOwned, string::String, vec::Vec};

use crate::{
    common::{TimeNumOffsetColonStr, TimeNumOffsetColonString, TimeOffsetSign},
    error::{ConversionError, Error},
};

use super::{validate_bytes, TimeOffsetStr};

/// Owned string for a time in RFC 3339 [`time-offset`] format, such as `+09:00`, `-00:00`, and `Z`.
///
/// Available when `alloc` feature is enabled.
///
/// # Examples
///
/// ```
/// # use datetime_string::rfc3339::TimeOffsetString;
/// use datetime_string::rfc3339::TimeOffsetStr;
/// use std::convert::TryFrom;
///
/// let try_from = TimeOffsetString::try_from("-12:34")?;
///
/// let parse = "-12:34".parse::<TimeOffsetString>()?;
/// let parse2: TimeOffsetString = "-12:34".parse()?;
///
/// let to_owned = TimeOffsetStr::from_str("-12:34")?.to_owned();
/// let into: TimeOffsetString = TimeOffsetStr::from_str("-12:34")?.into();
/// # Ok::<_, datetime_string::Error>(())
/// ```
///
/// [`time-offset`]: https://tools.ietf.org/html/rfc3339#section-5.6
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
pub struct TimeOffsetString(Vec<u8>);

impl TimeOffsetString {
    /// Creates a `TimeOffsetString` from the given bytes.
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

    /// Returns `Z`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetString;
    /// let z = TimeOffsetString::z();
    ///
    /// assert_eq!(z.as_str(), "Z");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn z() -> Self {
        let z = *b"Z";
        unsafe {
            // This is safe because `Z` is valid `time-offset` string.
            debug_assert_ok!(validate_bytes(&z));
            Self::from_bytes_maybe_unchecked(z[..].to_owned())
        }
    }

    /// Returns `-00:00`, which is defined in RFC 3339 to indicate "unknown local offset".
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetString;
    /// let unknown_local_offset = TimeOffsetString::unknown_local_offset();
    /// assert_eq!(unknown_local_offset.as_str(), "-00:00");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn unknown_local_offset() -> Self {
        TimeNumOffsetColonString::unknown_local_offset().into()
    }

    /// Creates a new `TimeNumOffsetColonStr` from the given minutes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetString;
    /// let offset = TimeOffsetString::from_minutes(9 * 60)?;
    /// assert_eq!(offset.as_str(), "+09:00");
    ///
    /// assert!(TimeOffsetString::from_minutes(-24 * 60).is_err(), "-24:00 is invaild time");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn from_minutes(minutes: i16) -> Result<Self, Error> {
        TimeNumOffsetColonString::from_minutes(minutes).map(Into::into)
    }

    /// Creates a new `TimeNumOffsetColonStr` from the given minutes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetString;
    /// use datetime_string::common::TimeOffsetSign;
    /// let offset = TimeOffsetString::from_sign_and_hm(TimeOffsetSign::Positive, 9, 30)?;
    /// assert_eq!(offset.as_str(), "+09:30");
    ///
    /// let unknown_local_offset = TimeOffsetString::from_sign_and_hm(TimeOffsetSign::Negative, 0, 0)?;
    /// assert_eq!(unknown_local_offset.as_str(), "-00:00");
    ///
    /// assert!(
    ///     TimeOffsetString::from_sign_and_hm(TimeOffsetSign::Negative, 24, 0).is_err(),
    ///     "-24:00 is invaild time"
    /// );
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn from_sign_and_hm(sign: TimeOffsetSign, hour_abs: u8, minute: u8) -> Result<Self, Error> {
        TimeNumOffsetColonString::from_sign_and_hm(sign, hour_abs, minute).map(Into::into)
    }

    /// Creates a new `TimeNumOffsetColonStr` from the given minutes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetString;
    /// let offset = TimeOffsetString::from_hm_signed(-9, 0)?;
    /// assert_eq!(offset.as_str(), "-09:00");
    ///
    /// let unknown_local_offset = TimeOffsetString::from_hm_signed(0, 0)?;
    /// assert_eq!(unknown_local_offset.as_str(), "+00:00");
    ///
    /// assert!( TimeOffsetString::from_hm_signed(-24, 0).is_err(), "-24:00 is invaild time");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn from_hm_signed(hour: i8, minute: u8) -> Result<Self, Error> {
        TimeNumOffsetColonString::from_hm_signed(hour, minute).map(Into::into)
    }

    /// Returns a `&TimeOffsetStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetString;
    /// use datetime_string::rfc3339::TimeOffsetStr;
    ///
    /// let secfrac = "-12:34".parse::<TimeOffsetString>()?;
    ///
    /// // Usually you don't need to call `as_deref()` explicitly, because
    /// // `Deref<Target = TimeOffsetStr>` trait is implemented.
    /// let _: &TimeOffsetStr = secfrac.as_deref();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref(&self) -> &TimeOffsetStr {
        unsafe {
            // This is safe because a valid `time-offset` string is also an ASCII string.
            debug_assert_safe_version_ok!(TimeOffsetStr::from_bytes(&self.0));
            TimeOffsetStr::from_bytes_maybe_unchecked(&self.0)
        }
    }

    /// Returns a `&mut TimeOffsetStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetString;
    /// use datetime_string::rfc3339::TimeOffsetStr;
    ///
    /// let mut secfrac = "-12:34".parse::<TimeOffsetString>()?;
    ///
    /// // Usually you don't need to call `as_deref_mut()` explicitly, because
    /// // `DerefMut` trait is implemented.
    /// let _: &mut TimeOffsetStr = secfrac.as_deref_mut();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref_mut(&mut self) -> &mut TimeOffsetStr {
        unsafe {
            // This is safe because a valid `time-offset` string is also an
            // ASCII string, and `TimeOffsetStr` ensures that the underlying
            // bytes are ASCII string after modification.
            debug_assert_ok!(TimeOffsetStr::from_bytes(&self.0));
            TimeOffsetStr::from_bytes_maybe_unchecked_mut(&mut self.0)
        }
    }
}

impl core::borrow::Borrow<TimeOffsetStr> for TimeOffsetString {
    #[inline]
    fn borrow(&self) -> &TimeOffsetStr {
        self.as_deref()
    }
}

impl core::borrow::BorrowMut<TimeOffsetStr> for TimeOffsetString {
    #[inline]
    fn borrow_mut(&mut self) -> &mut TimeOffsetStr {
        self.as_deref_mut()
    }
}

impl alloc::borrow::ToOwned for TimeOffsetStr {
    type Owned = TimeOffsetString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for TimeOffsetString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for TimeOffsetString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<TimeOffsetStr> for TimeOffsetString {
    #[inline]
    fn as_ref(&self) -> &TimeOffsetStr {
        self
    }
}

impl AsMut<TimeOffsetStr> for TimeOffsetString {
    #[inline]
    fn as_mut(&mut self) -> &mut TimeOffsetStr {
        self
    }
}

impl From<&TimeNumOffsetColonStr> for TimeOffsetString {
    #[inline]
    fn from(v: &TimeNumOffsetColonStr) -> TimeOffsetString {
        unsafe {
            // This is safe because `TimeNumOffsetColonStr` is subset of `TimeOffsetStr`.
            debug_assert_ok!(validate_bytes(v.as_bytes()));
            Self::from_bytes_maybe_unchecked(v.as_bytes().to_owned())
        }
    }
}

impl From<TimeNumOffsetColonString> for TimeOffsetString {
    #[inline]
    fn from(v: TimeNumOffsetColonString) -> TimeOffsetString {
        unsafe {
            // This is safe because `TimeNumOffsetColonStr` is subset of `TimeOffsetStr`.
            debug_assert_ok!(validate_bytes(v.as_bytes()));
            Self::from_bytes_maybe_unchecked(v.as_bytes().to_owned())
        }
    }
}

impl From<TimeOffsetString> for Vec<u8> {
    #[inline]
    fn from(v: TimeOffsetString) -> Vec<u8> {
        v.0
    }
}

impl From<TimeOffsetString> for String {
    #[inline]
    fn from(v: TimeOffsetString) -> String {
        unsafe {
            // This is safe because a valid `TimeOffsetString` is an ASCII string.
            debug_assert_ok!(str::from_utf8(&v.0));
            String::from_utf8_unchecked(v.0)
        }
    }
}

impl From<&TimeOffsetStr> for TimeOffsetString {
    fn from(v: &TimeOffsetStr) -> Self {
        unsafe {
            // This is safe because the value is already validated.
            debug_assert_ok!(validate_bytes(&v.0));
            Self::from_bytes_maybe_unchecked(v.0.into())
        }
    }
}

impl TryFrom<&[u8]> for TimeOffsetString {
    type Error = Error;

    #[inline]
    fn try_from(v: &[u8]) -> Result<Self, Self::Error> {
        TimeOffsetStr::from_bytes(v).map(Into::into)
    }
}

impl TryFrom<&str> for TimeOffsetString {
    type Error = Error;

    #[inline]
    fn try_from(v: &str) -> Result<Self, Self::Error> {
        TimeOffsetStr::from_str(v).map(Into::into)
    }
}

impl TryFrom<Vec<u8>> for TimeOffsetString {
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

impl TryFrom<String> for TimeOffsetString {
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

impl fmt::Display for TimeOffsetString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_deref().fmt(f)
    }
}

impl ops::Deref for TimeOffsetString {
    type Target = TimeOffsetStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_deref()
    }
}

impl ops::DerefMut for TimeOffsetString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_deref_mut()
    }
}

impl str::FromStr for TimeOffsetString {
    type Err = Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl_cmp_symmetric!(TimeOffsetStr, TimeOffsetString, &TimeOffsetString);
impl_cmp_symmetric!(TimeOffsetStr, TimeOffsetString, TimeOffsetStr);
impl_cmp_symmetric!(TimeOffsetStr, TimeOffsetString, &TimeOffsetStr);
impl_cmp_symmetric!(str, TimeOffsetString, str);
impl_cmp_symmetric!(str, TimeOffsetString, &str);
impl_cmp_symmetric!(str, &TimeOffsetString, str);
impl_cmp_symmetric!([u8], TimeOffsetString, [u8]);
impl_cmp_symmetric!([u8], TimeOffsetString, &[u8]);
impl_cmp_symmetric!([u8], &TimeOffsetString, [u8]);

#[cfg(feature = "serde")]
impl serde::Serialize for TimeOffsetString {
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

    /// Visitor for `TimeOffsetString`.
    struct StringVisitor;

    impl<'de> Visitor<'de> for StringVisitor {
        type Value = TimeOffsetString;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 time-offset string")
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

    impl<'de> Deserialize<'de> for TimeOffsetString {
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
        let raw: &'static str = "-12:34";
        assert_tokens(
            &TimeOffsetString::try_from(raw).unwrap(),
            &[Token::Str(raw)],
        );
    }

    #[test]
    fn de_bytes() {
        let raw: &'static [u8; 6] = b"-12:34";
        assert_de_tokens(
            &TimeOffsetString::try_from(&raw[..]).unwrap(),
            &[Token::Bytes(raw)],
        );
    }
}
