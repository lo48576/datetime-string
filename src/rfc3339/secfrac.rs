//! RFC 3339 [`time-secfrac`] string types.
//!
//! [`time-secfrac`]: https://tools.ietf.org/html/rfc3339#section-5.6

#[cfg(feature = "alloc")]
mod owned;

use core::{convert::TryFrom, fmt, ops, str};

#[cfg(feature = "serde")]
use serde::Serialize;

use crate::error::{ComponentKind, Error, ErrorKind};

#[cfg(feature = "alloc")]
pub use self::owned::SecfracString;

/// Validates the given string as an RFC 3339 [`time-secfrac`] string.
///
/// [`time-secfrac`]: https://tools.ietf.org/html/rfc3339#section-5.6
fn validate_bytes(s: &[u8]) -> Result<(), Error> {
    if s.len() <= 1 {
        return Err(ErrorKind::TooShort.into());
    }

    if s[0] != b'.' {
        return Err(ErrorKind::InvalidSeparator.into());
    }

    let secfrac_s = &s[1..];
    if !secfrac_s.iter().all(u8::is_ascii_digit) {
        return Err(ErrorKind::InvalidComponentType(ComponentKind::Secfrac).into());
    }

    Ok(())
}

/// String slice for a time in RFC 3339 [`time-secfrac`] format, such as `.7890`.
///
/// [`time-secfrac`]: https://tools.ietf.org/html/rfc3339#section-5.6
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
// Comparisons implemented for the type are consistent (at least it is intended to be so).
// See <https://github.com/rust-lang/rust-clippy/issues/2025>.
// Note that `clippy::derive_ord_xor_partial_ord` would be introduced since Rust 1.47.0.
#[allow(clippy::derive_hash_xor_eq)]
#[allow(clippy::unknown_clippy_lints, clippy::derive_ord_xor_partial_ord)]
pub struct SecfracStr(str);

impl SecfracStr {
    /// Creates a `&SecfracStr` from the given byte slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_bytes_unchecked(s: &[u8]) -> &Self {
        Self::from_str_unchecked(str::from_utf8_unchecked(s))
    }

    /// Creates a `&mut SecfracStr` from the given mutable byte slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_bytes_unchecked_mut(s: &mut [u8]) -> &mut Self {
        Self::from_str_unchecked_mut(str::from_utf8_unchecked_mut(s))
    }

    /// Creates a `&SecfracStr` from the given string slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const SecfracStr)
    }

    /// Creates a `&mut SecfracStr` from the given mutable string slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_unchecked_mut(s: &mut str) -> &mut Self {
        &mut *(s as *mut str as *mut SecfracStr)
    }

    /// Creates a new `&SecfracStr` from a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let secfrac = SecfracStr::from_str(".1234")?;
    /// assert_eq!(secfrac.as_str(), ".1234");
    ///
    /// assert!(SecfracStr::from_str(".0").is_ok());
    /// assert!(SecfracStr::from_str(".0000000000").is_ok());
    /// assert!(SecfracStr::from_str(".9999999999").is_ok());
    ///
    /// assert!(SecfracStr::from_str("0").is_err(), "A leading period is required");
    /// assert!(SecfracStr::from_str(".").is_err(), "One or more digits are required");
    ///
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    // `FromStr` trait cannot be implemented for a slice.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut SecfracStr` from a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let mut buf = ".1234".to_owned();
    /// let secfrac = SecfracStr::from_mut_str(&mut buf)?;
    /// assert_eq!(secfrac.as_str(), ".1234");
    ///
    /// secfrac.fill_with_zero();
    /// assert_eq!(secfrac.as_str(), ".0000");
    ///
    /// assert_eq!(buf, ".0000");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_mut_str(s: &mut str) -> Result<&mut Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&SecfracStr` from a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let secfrac = SecfracStr::from_bytes(b".1234")?;
    /// assert_eq!(secfrac.as_str(), ".1234");
    ///
    /// assert!(SecfracStr::from_bytes(b".0").is_ok());
    /// assert!(SecfracStr::from_bytes(b".0000000000").is_ok());
    /// assert!(SecfracStr::from_bytes(b".9999999999").is_ok());
    ///
    /// assert!(SecfracStr::from_bytes(b"0").is_err(), "A leading period is required");
    /// assert!(SecfracStr::from_bytes(b".").is_err(), "One or more digits are required");
    ///
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_bytes(s: &[u8]) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut SecfracStr` from a mutable byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let mut buf: [u8; 5] = *b".1234";
    /// let secfrac = SecfracStr::from_bytes_mut(&mut buf)?;
    /// assert_eq!(secfrac.as_str(), ".1234");
    ///
    /// secfrac.fill_with_zero();
    /// assert_eq!(secfrac.as_str(), ".0000");
    ///
    /// assert_eq!(&buf[..], b".0000");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_bytes_mut(s: &mut [u8]) -> Result<&mut Self, Error> {
        TryFrom::try_from(s)
    }

    /// Returns a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let secfrac = SecfracStr::from_str(".1234")?;
    ///
    /// assert_eq!(secfrac.as_str(), ".1234");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Returns a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let secfrac = SecfracStr::from_str(".1234")?;
    ///
    /// assert_eq!(secfrac.as_str(), ".1234");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Returns the digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let secfrac = SecfracStr::from_str(".1234")?;
    /// assert_eq!(secfrac.digits(), "1234");
    ///
    /// let secfrac2 = SecfracStr::from_str(".012340")?;
    /// assert_eq!(secfrac2.digits(), "012340");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn digits(&self) -> &str {
        &self.0[1..]
    }

    /// Returns a milliseconds precision secfrac if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let not_precise = SecfracStr::from_str(".1")?;
    /// assert_eq!(not_precise.milliseconds_secfrac(), None);
    ///
    /// let expected = SecfracStr::from_str(".012")?;
    /// assert_eq!(expected.milliseconds_secfrac(), Some(expected));
    ///
    /// let more_precise = SecfracStr::from_str(".012345678901")?;
    /// assert_eq!(more_precise.milliseconds_secfrac(), Some(expected));
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn milliseconds_secfrac(&self) -> Option<&SecfracStr> {
        self.as_bytes().get(..4).map(|s| unsafe {
            debug_assert!(validate_bytes(s).is_ok());
            // This is safe because ".NNN" value (where Ns are digits) is a
            // valid time-secfrac string.
            SecfracStr::from_bytes_unchecked(s)
        })
    }

    /// Returns a milliseconds digits as a fixed bytes slice, if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let not_precise = SecfracStr::from_str(".1")?;
    /// assert_eq!(not_precise.milliseconds_bytes_fixed_len(), None);
    ///
    /// let expected = SecfracStr::from_str(".012")?;
    /// assert_eq!(expected.milliseconds_bytes_fixed_len(), Some(b"012"));
    ///
    /// let more_precise = SecfracStr::from_str(".012345678901")?;
    /// assert_eq!(more_precise.milliseconds_bytes_fixed_len(), Some(b"012"));
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn milliseconds_bytes_fixed_len(&self) -> Option<&[u8; 3]> {
        self.as_bytes().get(1..4).map(|s| {
            debug_assert_eq!(s.len(), 3);
            let ptr = s.as_ptr() as *const [u8; 3];
            unsafe {
                // This is always safe because the string is valid `time-secfrac` string.
                &*ptr
            }
        })
    }

    /// Returns a microseconds precision secfrac if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let not_precise = SecfracStr::from_str(".1234")?;
    /// assert_eq!(not_precise.microseconds_secfrac(), None);
    ///
    /// let expected = SecfracStr::from_str(".012345")?;
    /// assert_eq!(expected.microseconds_secfrac(), Some(expected));
    ///
    /// let more_precise = SecfracStr::from_str(".012345678901")?;
    /// assert_eq!(more_precise.microseconds_secfrac(), Some(expected));
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn microseconds_secfrac(&self) -> Option<&SecfracStr> {
        self.as_bytes().get(..7).map(|s| unsafe {
            debug_assert!(validate_bytes(s).is_ok());
            // This is safe because ".NNNNNN" value (where Ns are digits) is a
            // valid time-secfrac string.
            SecfracStr::from_bytes_unchecked(s)
        })
    }

    /// Returns a microseconds digits as a fixed bytes slice, if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let not_precise = SecfracStr::from_str(".1234")?;
    /// assert_eq!(not_precise.microseconds_bytes_fixed_len(), None);
    ///
    /// let expected = SecfracStr::from_str(".012345")?;
    /// assert_eq!(expected.microseconds_bytes_fixed_len(), Some(b"012345"));
    ///
    /// let more_precise = SecfracStr::from_str(".012345678901")?;
    /// assert_eq!(more_precise.microseconds_bytes_fixed_len(), Some(b"012345"));
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn microseconds_bytes_fixed_len(&self) -> Option<&[u8; 6]> {
        self.as_bytes().get(1..7).map(|s| {
            debug_assert_eq!(s.len(), 6);
            let ptr = s.as_ptr() as *const [u8; 6];
            unsafe {
                // This is always safe because the string is valid `time-secfrac` string.
                &*ptr
            }
        })
    }

    /// Returns a nanoseconds precision secfrac if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let not_precise = SecfracStr::from_str(".1234")?;
    /// assert_eq!(not_precise.nanoseconds_secfrac(), None);
    ///
    /// let expected = SecfracStr::from_str(".012345678")?;
    /// assert_eq!(expected.nanoseconds_secfrac(), Some(expected));
    ///
    /// let more_precise = SecfracStr::from_str(".012345678901")?;
    /// assert_eq!(more_precise.nanoseconds_secfrac(), Some(expected));
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn nanoseconds_secfrac(&self) -> Option<&SecfracStr> {
        self.as_bytes().get(..10).map(|s| unsafe {
            debug_assert!(validate_bytes(s).is_ok());
            // This is safe because ".NNNNNNNNN" value (where Ns are digits) is
            // a valid time-secfrac string.
            SecfracStr::from_bytes_unchecked(s)
        })
    }

    /// Returns a nanoseconds digits as a fixed bytes slice, if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let not_precise = SecfracStr::from_str(".1234")?;
    /// assert_eq!(not_precise.nanoseconds_bytes_fixed_len(), None);
    ///
    /// let expected = SecfracStr::from_str(".012345678")?;
    /// assert_eq!(expected.nanoseconds_bytes_fixed_len(), Some(b"012345678"));
    ///
    /// let more_precise = SecfracStr::from_str(".012345678901")?;
    /// assert_eq!(more_precise.nanoseconds_bytes_fixed_len(), Some(b"012345678"));
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn nanoseconds_bytes_fixed_len(&self) -> Option<&[u8; 9]> {
        self.as_bytes().get(1..10).map(|s| {
            debug_assert_eq!(s.len(), 9);
            let ptr = s.as_ptr() as *const [u8; 9];
            unsafe {
                // This is always safe because the string is valid `time-secfrac` string.
                &*ptr
            }
        })
    }

    /// Fills the secfrac part with zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let mut buf = ".1234".to_owned();
    /// let secfrac = SecfracStr::from_mut_str(&mut buf)?;
    /// assert_eq!(secfrac.as_str(), ".1234");
    ///
    /// secfrac.fill_with_zero();
    /// assert_eq!(secfrac.as_str(), ".0000");
    ///
    /// assert_eq!(buf, ".0000");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn fill_with_zero(&mut self) {
        // Use `slice::fill()` once rust-lang/rust#70758 is stabilized.
        // See <https://github.com/rust-lang/rust/issues/70758>.
        unsafe {
            // This is safe because the value after the modification is
            // ".000...00", and it is of course a valid string.
            self.0[1..]
                .as_bytes_mut()
                .iter_mut()
                .for_each(|digit| *digit = b'0');
        }
        debug_assert!(
            validate_bytes(self.as_bytes()).is_ok(),
            "The secfrac string must be valid after the modification"
        );
    }

    /// Fills the secfrac part with zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::SecfracStr;
    /// let mut buf = ".1234".to_owned();
    /// let secfrac = SecfracStr::from_mut_str(&mut buf)?;
    /// assert_eq!(secfrac.as_str(), ".1234");
    ///
    /// secfrac.fill_with_nine();
    /// assert_eq!(secfrac.as_str(), ".9999");
    ///
    /// assert_eq!(buf, ".9999");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn fill_with_nine(&mut self) {
        // Use `slice::fill()` once rust-lang/rust#70758 is stabilized.
        // See <https://github.com/rust-lang/rust/issues/70758>.
        unsafe {
            // This is safe because the value after the modification is
            // ".999...99", and it is of course a valid string.
            self.0[1..]
                .as_bytes_mut()
                .iter_mut()
                .for_each(|digit| *digit = b'9');
        }
        debug_assert!(
            validate_bytes(self.as_bytes()).is_ok(),
            "The secfrac string must be valid after the modification"
        );
    }
}

#[cfg(feature = "alloc")]
impl alloc::borrow::ToOwned for SecfracStr {
    type Owned = SecfracString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for SecfracStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for SecfracStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<SecfracStr> for SecfracStr {
    #[inline]
    fn as_ref(&self) -> &SecfracStr {
        self
    }
}

impl<'a> From<&'a SecfracStr> for &'a str {
    #[inline]
    fn from(v: &'a SecfracStr) -> Self {
        v.as_str()
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a SecfracStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid `time-secfrac` string is also an ASCII string.
            SecfracStr::from_bytes_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut SecfracStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid `time-secfrac` string is also an ASCII string.
            SecfracStr::from_bytes_unchecked_mut(v)
        })
    }
}

impl<'a> TryFrom<&'a str> for &'a SecfracStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because a valid `time-secfrac` string is also an ASCII string.
            SecfracStr::from_str_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut str> for &'a mut SecfracStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because a valid `time-secfrac` string is also an ASCII string.
            SecfracStr::from_str_unchecked_mut(v)
        })
    }
}

impl fmt::Display for SecfracStr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl ops::Deref for SecfracStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl_cmp_symmetric!(str, SecfracStr, &SecfracStr);
impl_cmp_symmetric!([u8], SecfracStr, [u8]);
impl_cmp_symmetric!([u8], SecfracStr, &[u8]);
impl_cmp_symmetric!([u8], &SecfracStr, [u8]);
impl_cmp_symmetric!(str, SecfracStr, str);
impl_cmp_symmetric!(str, SecfracStr, &str);
impl_cmp_symmetric!(str, &SecfracStr, str);

/// Items for serde support.
#[cfg(feature = "serde")]
mod serde_ {
    use super::*;

    use serde::de::{Deserialize, Deserializer, Visitor};

    /// Visitor for `&SecfracStr`.
    struct StrVisitor;

    impl<'de> Visitor<'de> for StrVisitor {
        type Value = &'de SecfracStr;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 time-secfrac string")
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

    impl<'de> Deserialize<'de> for &'de SecfracStr {
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
    #[cfg(feature = "serde")]
    use super::*;

    use super::validate_bytes as s_validate;

    #[cfg(feature = "serde")]
    use serde_test::{assert_de_tokens, assert_tokens, Token};

    #[test]
    fn validate_bytes() {
        assert!(s_validate(b".0").is_ok());
        assert!(s_validate(b".9").is_ok());
        assert!(s_validate(b".1234").is_ok());
        assert!(s_validate(b".001200").is_ok());
        assert!(s_validate(b".0000000").is_ok());
        assert!(s_validate(b".9999999").is_ok());
        assert!(s_validate(b".00000000000000000000000000000000").is_ok());
        assert!(s_validate(b".99999999999999999999999999999999").is_ok());

        assert!(s_validate(b".").is_err());
        assert!(s_validate(b"0").is_err());
        assert!(s_validate(b".+0").is_err());
        assert!(s_validate(b".-0").is_err());
        assert!(s_validate(b".0 ").is_err());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_str() {
        let raw: &'static str = ".1234";
        assert_tokens(
            &SecfracStr::from_str(raw).unwrap(),
            &[Token::BorrowedStr(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes_slice() {
        let raw: &'static [u8; 5] = b".1234";
        assert_de_tokens(
            &SecfracStr::from_bytes(raw).unwrap(),
            &[Token::BorrowedBytes(raw)],
        );
    }
}
