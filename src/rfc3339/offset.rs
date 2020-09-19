//! RFC 3339 [`time-offset`] string types.
//!
//! [`time-offset`]: https://tools.ietf.org/html/rfc3339#section-5.6

use core::{cmp::Ordering, convert::TryFrom, fmt, ops, str};

#[cfg(feature = "serde")]
use serde::Serialize;

use super::{ComponentKind, ErrorKind, TimeNumOffsetStr, TimeOffsetSign, ValidationError};

#[cfg(feature = "alloc")]
pub use self::owned::TimeOffsetString;

#[cfg(feature = "alloc")]
mod owned;

/// Validates the given string as an RFC 3339 [`time-offset`].
///
/// [`time-offset`]: https://tools.ietf.org/html/rfc3339#section-5.6
fn validate_bytes(s: &[u8]) -> Result<(), ValidationError> {
    match s.len().cmp(&1) {
        Ordering::Less => Err(ErrorKind::TooShort.into()),
        Ordering::Equal => {
            if s[0] == b'Z' {
                Ok(())
            } else {
                Err(ErrorKind::InvalidComponentType(ComponentKind::Offset).into())
            }
        }
        Ordering::Greater => TimeNumOffsetStr::from_bytes(s).map(|_| ()),
    }
}

/// RFC 3339 [`time-offset`] string slice.
///
/// [`time-offset`]: https://tools.ietf.org/html/rfc3339#section-5.6
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
// Comparisons implemented for the type are consistent (at least it is intended to be so).
// See <https://github.com/rust-lang/rust-clippy/issues/2025>.
// Note that `clippy::derive_ord_xor_partial_ord` would be introduced since Rust 1.47.0.
#[allow(clippy::derive_hash_xor_eq)]
#[allow(clippy::unknown_clippy_lints, clippy::derive_ord_xor_partial_ord)]
pub struct TimeOffsetStr(str);

impl TimeOffsetStr {
    /// Creates a `&TimeOffsetStr` from the given byte slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_bytes_unchecked(s: &[u8]) -> &Self {
        Self::from_str_unchecked(str::from_utf8_unchecked(s))
    }

    /// Creates a `&mut TimeOffsetStr` from the given mutable byte slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_bytes_unchecked_mut(s: &mut [u8]) -> &mut Self {
        Self::from_str_unchecked_mut(str::from_utf8_unchecked_mut(s))
    }

    /// Creates a `&TimeOffsetStr` from the given string slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const TimeOffsetStr)
    }

    /// Creates a `&mut TimeOffsetStr` from the given mutable string slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_unchecked_mut(s: &mut str) -> &mut Self {
        &mut *(s as *mut str as *mut TimeOffsetStr)
    }

    /// Creates a new `&TimeOffsetStr` from a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetStr;
    /// let time = TimeOffsetStr::from_str("-12:34")?;
    /// assert_eq!(time.as_str(), "-12:34");
    ///
    /// assert!(TimeOffsetStr::from_str("Z").is_ok());
    /// assert!(TimeOffsetStr::from_str("+00:00").is_ok());
    /// assert!(TimeOffsetStr::from_str("+23:59").is_ok());
    /// assert!(TimeOffsetStr::from_str("-00:00").is_ok());
    /// assert!(TimeOffsetStr::from_str("-23:59").is_ok());
    ///
    /// assert!(TimeOffsetStr::from_str("z").is_err(), "lowercase Z is not allowed");
    /// assert!(TimeOffsetStr::from_str("a").is_err(), "Invalid name");
    /// assert!(TimeOffsetStr::from_str("+24:00").is_err(), "Invalid hour");
    /// assert!(TimeOffsetStr::from_str("+00:60").is_err(), "Invalid minute");
    /// assert!(TimeOffsetStr::from_str("-24:00").is_err(), "Invalid hour");
    /// assert!(TimeOffsetStr::from_str("-00:60").is_err(), "Invalid minute");
    /// assert!(TimeOffsetStr::from_str("?00:00").is_err(), "Invalid sign");
    /// assert!(TimeOffsetStr::from_str("00:00").is_err(), "Sign is missing");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    // `FromStr` trait cannot be implemented for a slice.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, ValidationError> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut TimeOffsetStr` from a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetStr;
    /// use datetime_string::rfc3339::TimeOffsetSign;
    /// let mut buf = "-12:34".to_owned();
    /// let offset = TimeOffsetStr::from_mut_str(&mut buf)?;
    /// assert_eq!(offset.as_str(), "-12:34");
    ///
    /// offset.to_numoffset_mut().unwrap().set_sign(TimeOffsetSign::Positive);
    /// assert_eq!(offset.as_str(), "+12:34");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn from_mut_str(s: &mut str) -> Result<&mut Self, ValidationError> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&TimeOffsetStr` from a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetStr;
    /// let time = TimeOffsetStr::from_bytes(b"-12:34")?;
    /// assert_eq!(time.as_str(), "-12:34");
    ///
    /// assert!(TimeOffsetStr::from_bytes(b"Z").is_ok());
    /// assert!(TimeOffsetStr::from_bytes(b"+00:00").is_ok());
    /// assert!(TimeOffsetStr::from_bytes(b"+23:59").is_ok());
    /// assert!(TimeOffsetStr::from_bytes(b"-00:00").is_ok());
    /// assert!(TimeOffsetStr::from_bytes(b"-23:59").is_ok());
    ///
    /// assert!(TimeOffsetStr::from_bytes(b"z").is_err(), "lowercase Z is not allowed");
    /// assert!(TimeOffsetStr::from_bytes(b"a").is_err(), "Invalid name");
    /// assert!(TimeOffsetStr::from_bytes(b"+24:00").is_err(), "Invalid hour");
    /// assert!(TimeOffsetStr::from_bytes(b"+00:60").is_err(), "Invalid minute");
    /// assert!(TimeOffsetStr::from_bytes(b"-24:00").is_err(), "Invalid hour");
    /// assert!(TimeOffsetStr::from_bytes(b"-00:60").is_err(), "Invalid minute");
    /// assert!(TimeOffsetStr::from_bytes(b"?00:00").is_err(), "Invalid sign");
    /// assert!(TimeOffsetStr::from_bytes(b"00:00").is_err(), "Sign is missing");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn from_bytes(s: &[u8]) -> Result<&Self, ValidationError> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut TimeOffsetStr` from a mutable byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetStr;
    /// use datetime_string::rfc3339::TimeOffsetSign;
    /// let mut buf: [u8; 6] = *b"-12:34";
    /// let offset = TimeOffsetStr::from_bytes_mut(&mut buf)?;
    /// assert_eq!(offset.as_str(), "-12:34");
    ///
    /// offset.to_numoffset_mut().unwrap().set_sign(TimeOffsetSign::Positive);
    /// assert_eq!(offset.as_str(), "+12:34");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn from_bytes_mut(s: &mut [u8]) -> Result<&mut Self, ValidationError> {
        TryFrom::try_from(s)
    }

    /// Returns a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetStr;
    /// let time = TimeOffsetStr::from_str("-12:34")?;
    ///
    /// assert_eq!(time.as_str(), "-12:34");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Returns a byte slice.
    ///
    /// If you want to use indexed access, prefer [`as_bytes_fixed_len`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetStr;
    /// let time = TimeOffsetStr::from_str("-12:34")?;
    ///
    /// assert_eq!(time.as_bytes(), b"-12:34");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    ///
    /// [`as_bytes_fixed_len`]: #method.as_bytes_fixed_len
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Returns a sign if available.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeOffsetStr;
    /// use datetime_string::rfc3339::TimeOffsetSign;
    ///
    /// let positive = TimeOffsetStr::from_str("+12:34")?;
    /// assert_eq!(positive.sign(), Some(TimeOffsetSign::Positive));
    ///
    /// let negative = TimeOffsetStr::from_str("-00:00")?;
    /// assert_eq!(negative.sign(), Some(TimeOffsetSign::Negative));
    ///
    /// let zulu = TimeOffsetStr::from_str("Z")?;
    /// assert_eq!(zulu.sign(), None);
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn sign(&self) -> Option<TimeOffsetSign> {
        match self.as_bytes()[0] {
            b'Z' => None,
            b'+' => Some(TimeOffsetSign::Positive),
            v => {
                debug_assert_eq!(v, b'-');
                Some(TimeOffsetSign::Negative)
            }
        }
    }

    /// Returns a `&TimeNumOffsetStr` if the time offset is not `Z`.
    #[inline]
    pub fn to_numoffset(&self) -> Option<&TimeNumOffsetStr> {
        if self.len() == 1 {
            return None;
        }
        Some(unsafe {
            // This is safe because `time-offset` is "Z" or `time-numoffset`.
            TimeNumOffsetStr::from_bytes_unchecked(self.0.as_bytes())
        })
    }

    /// Returns a `&mut TimeNumOffsetStr` if the time offset is not `Z`.
    #[inline]
    // This mimics API of `std::path::Path::to_str(&self) -> Option<&str>`, and
    // `to_*` seems more appropriate than `as_*` (because this method does not
    // return a reference directly).
    #[allow(clippy::wrong_self_convention)]
    pub fn to_numoffset_mut(&mut self) -> Option<&mut TimeNumOffsetStr> {
        if self.len() == 1 {
            return None;
        }
        Some(unsafe {
            // This is safe because `time-offset` is "Z" or `time-numoffset`,
            // and a `time-numoffset` string is also an ASCII string.
            TimeNumOffsetStr::from_bytes_unchecked_mut(self.0.as_bytes_mut())
        })
    }
}

#[cfg(feature = "alloc")]
impl alloc::borrow::ToOwned for TimeOffsetStr {
    type Owned = TimeOffsetString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for TimeOffsetStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for TimeOffsetStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<TimeOffsetStr> for TimeOffsetStr {
    #[inline]
    fn as_ref(&self) -> &TimeOffsetStr {
        self
    }
}

impl<'a> From<&'a TimeOffsetStr> for &'a str {
    #[inline]
    fn from(v: &'a TimeOffsetStr) -> Self {
        v.as_str()
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a TimeOffsetStr {
    type Error = ValidationError;

    #[inline]
    fn try_from(v: &'a [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid `time-offset` string is also an ASCII string.
            TimeOffsetStr::from_bytes_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut TimeOffsetStr {
    type Error = ValidationError;

    #[inline]
    fn try_from(v: &'a mut [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid `time-offset` string is also an ASCII string.
            TimeOffsetStr::from_bytes_unchecked_mut(v)
        })
    }
}

impl<'a> TryFrom<&'a str> for &'a TimeOffsetStr {
    type Error = ValidationError;

    #[inline]
    fn try_from(v: &'a str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because a valid `time-offset` string is also an ASCII string.
            TimeOffsetStr::from_str_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut str> for &'a mut TimeOffsetStr {
    type Error = ValidationError;

    #[inline]
    fn try_from(v: &'a mut str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because a valid `time-offset` string is also an ASCII string.
            TimeOffsetStr::from_str_unchecked_mut(v)
        })
    }
}

impl fmt::Display for TimeOffsetStr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl ops::Deref for TimeOffsetStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl_cmp_symmetric!(str, TimeOffsetStr, &TimeOffsetStr);
impl_cmp_symmetric!([u8], TimeOffsetStr, [u8]);
impl_cmp_symmetric!([u8], TimeOffsetStr, &[u8]);
impl_cmp_symmetric!([u8], &TimeOffsetStr, [u8]);
impl_cmp_symmetric!(str, TimeOffsetStr, str);
impl_cmp_symmetric!(str, TimeOffsetStr, &str);
impl_cmp_symmetric!(str, &TimeOffsetStr, str);

/// Items for serde support.
#[cfg(feature = "serde")]
mod serde_ {
    use super::*;

    use serde::de::{Deserialize, Deserializer, Visitor};

    /// Visitor for `&TimeOffsetStr`.
    struct StrVisitor;

    impl<'de> Visitor<'de> for StrVisitor {
        type Value = &'de TimeOffsetStr;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 time-offset string")
        }

        #[inline]
        fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            Self::Value::try_from(v).map_err(E::custom)
        }

        #[inline]
        fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            Self::Value::try_from(v).map_err(E::custom)
        }
    }

    impl<'de> Deserialize<'de> for &'de TimeOffsetStr {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_any(StrVisitor)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use super::validate_bytes as s_validate;

    #[cfg(feature = "serde")]
    use serde_test::{assert_de_tokens, assert_tokens, Token};

    #[test]
    fn validate_bytes() {
        assert!(s_validate(b"Z").is_ok());
        assert!(s_validate(b"-00:00").is_ok());
        assert!(s_validate(b"-12:30").is_ok());
        assert!(s_validate(b"-23:59").is_ok());
        assert!(s_validate(b"+00:00").is_ok());
        assert!(s_validate(b"+12:30").is_ok());
        assert!(s_validate(b"+23:59").is_ok());

        assert!(TimeOffsetStr::from_str("z").is_err());
        assert!(TimeOffsetStr::from_str("a").is_err());
        assert!(TimeOffsetStr::from_str("+24:00").is_err());
        assert!(TimeOffsetStr::from_str("+00:60").is_err());
        assert!(TimeOffsetStr::from_str("-24:00").is_err());
        assert!(TimeOffsetStr::from_str("-00:60").is_err());
        assert!(TimeOffsetStr::from_str("?00:00").is_err());
        assert!(TimeOffsetStr::from_str("00:00").is_err());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_str() {
        let raw: &'static str = "-12:34";
        assert_tokens(
            &TimeOffsetStr::from_str(raw).unwrap(),
            &[Token::BorrowedStr(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes_slice() {
        let raw: &'static [u8; 6] = b"-12:34";
        assert_de_tokens(
            &TimeOffsetStr::from_bytes(raw).unwrap(),
            &[Token::BorrowedBytes(raw)],
        );
    }
}
