//! Digits of fractions of a second.

#[cfg(feature = "alloc")]
mod owned;

use core::{
    convert::TryFrom,
    fmt,
    ops::{self, RangeTo},
    str,
};

#[cfg(feature = "serde")]
use serde::Serialize;

use crate::error::{ComponentKind, Error, ErrorKind};

#[cfg(feature = "alloc")]
pub use self::owned::SecfracDigitsString;

/// Range of a milliseconds part.
const MILLI_RANGE: RangeTo<usize> = ..3;
/// Range of a microsecodns part.
const MICRO_RANGE: RangeTo<usize> = ..6;
/// Range of a milliseconds part.
const NANO_RANGE: RangeTo<usize> = ..9;

/// Validates the given string as digits of fractions of a second.
///
/// This function ensures that the given bytes is not empty and consists of only ASCII digits.
fn validate_bytes(s: &[u8]) -> Result<(), Error> {
    if s.is_empty() {
        return Err(ErrorKind::TooShort.into());
    }

    if !s.iter().all(u8::is_ascii_digit) {
        return Err(ErrorKind::InvalidComponentType(ComponentKind::Secfrac).into());
    }

    Ok(())
}

/// String slice for digits of fractions of a second.
///
/// Note that values of this type cannot be not empty string.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
// Comparisons implemented for the type are consistent (at least it is intended to be so).
// See <https://github.com/rust-lang/rust-clippy/issues/2025>.
// Note that `clippy::derive_ord_xor_partial_ord` would be introduced since Rust 1.47.0.
#[allow(clippy::derive_hash_xor_eq)]
#[allow(clippy::unknown_clippy_lints, clippy::derive_ord_xor_partial_ord)]
pub struct SecfracDigitsStr(str);

impl SecfracDigitsStr {
    /// Creates a `&SecfracDigitsStr` from the given byte slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_bytes_unchecked(s: &[u8]) -> &Self {
        Self::from_str_unchecked(str::from_utf8_unchecked(s))
    }

    /// Creates a `&mut SecfracDigitsStr` from the given mutable byte slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_bytes_unchecked_mut(s: &mut [u8]) -> &mut Self {
        Self::from_str_unchecked_mut(str::from_utf8_unchecked_mut(s))
    }

    /// Creates a `&SecfracDigitsStr` from the given string slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const SecfracDigitsStr)
    }

    /// Creates a `&mut SecfracDigitsStr` from the given mutable string slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_unchecked_mut(s: &mut str) -> &mut Self {
        &mut *(s as *mut str as *mut SecfracDigitsStr)
    }

    /// Creates a new `&SecfracDigitsStr` from a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let secfrac = SecfracDigitsStr::from_str("1234")?;
    /// assert_eq!(secfrac.as_str(), "1234");
    ///
    /// assert!(SecfracDigitsStr::from_str("0").is_ok());
    /// assert!(SecfracDigitsStr::from_str("0000000000").is_ok());
    /// assert!(SecfracDigitsStr::from_str("9999999999").is_ok());
    ///
    /// assert!(SecfracDigitsStr::from_str("").is_err(), "Fractions should not be empty");
    /// assert!(SecfracDigitsStr::from_str(".0").is_err(), "Only digits are allowed");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    // `FromStr` trait cannot be implemented for a slice.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut SecfracDigitsStr` from a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let mut buf = "1234".to_owned();
    /// let secfrac = SecfracDigitsStr::from_mut_str(&mut buf)?;
    /// assert_eq!(secfrac.as_str(), "1234");
    ///
    /// secfrac.fill_with_zero();
    /// assert_eq!(secfrac.as_str(), "0000");
    ///
    /// assert_eq!(buf, "0000");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_mut_str(s: &mut str) -> Result<&mut Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&SecfracDigitsStr` from a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let secfrac = SecfracDigitsStr::from_str("1234")?;
    /// assert_eq!(secfrac.as_str(), "1234");
    ///
    /// assert!(SecfracDigitsStr::from_str("0").is_ok());
    /// assert!(SecfracDigitsStr::from_str("0000000000").is_ok());
    /// assert!(SecfracDigitsStr::from_str("9999999999").is_ok());
    ///
    /// assert!(SecfracDigitsStr::from_str("").is_err(), "Fractions should not be empty");
    /// assert!(SecfracDigitsStr::from_str(".0").is_err(), "Only digits are allowed");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_bytes(s: &[u8]) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut SecfracDigitsStr` from a mutable byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let mut buf: [u8; 4] = *b"1234";
    /// let secfrac = SecfracDigitsStr::from_bytes_mut(&mut buf)?;
    /// assert_eq!(secfrac.as_str(), "1234");
    ///
    /// secfrac.fill_with_zero();
    /// assert_eq!(secfrac.as_str(), "0000");
    ///
    /// assert_eq!(&buf[..], b"0000");
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
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let secfrac = SecfracDigitsStr::from_str("1234")?;
    ///
    /// assert_eq!(secfrac.as_str(), "1234");
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
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let secfrac = SecfracDigitsStr::from_str("1234")?;
    ///
    /// assert_eq!(secfrac.as_str(), "1234");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Returns a milliseconds precision substring if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let not_precise = SecfracDigitsStr::from_str("1")?;
    /// assert_eq!(not_precise.milliseconds_digits(), None);
    ///
    /// let precise = SecfracDigitsStr::from_str("012")?;
    /// assert_eq!(precise.milliseconds_digits().unwrap(), "012");
    ///
    /// let more_precise = SecfracDigitsStr::from_str("012345678901")?;
    /// assert_eq!(more_precise.milliseconds_digits().unwrap(), "012");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn milliseconds_digits(&self) -> Option<&SecfracDigitsStr> {
        self.0.as_bytes().get(MILLI_RANGE).map(|s| unsafe {
            debug_assert!(validate_bytes(s).is_ok());
            // This is safe because the string consists of only ASCII digits.
            SecfracDigitsStr::from_bytes_unchecked(s)
        })
    }

    /// Returns a milliseconds digits as a fixed bytes slice, if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let not_precise = SecfracDigitsStr::from_str("1")?;
    /// assert_eq!(not_precise.milliseconds_bytes_fixed_len(), None);
    ///
    /// let precise = SecfracDigitsStr::from_str("012")?;
    /// assert_eq!(precise.milliseconds_bytes_fixed_len(), Some(b"012"));
    ///
    /// let more_precise = SecfracDigitsStr::from_str("012345678901")?;
    /// assert_eq!(more_precise.milliseconds_bytes_fixed_len(), Some(b"012"));
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn milliseconds_bytes_fixed_len(&self) -> Option<&[u8; 3]> {
        self.0.as_bytes().get(MILLI_RANGE).map(|s| {
            debug_assert_eq!(s.len(), 3);
            let ptr = s.as_ptr() as *const [u8; 3];
            unsafe {
                // This is safe because the string consists of only ASCII digits.
                &*ptr
            }
        })
    }

    /// Returns a microseconds precision substring if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let not_precise = SecfracDigitsStr::from_str("1234")?;
    /// assert_eq!(not_precise.microseconds_digits(), None);
    ///
    /// let precise = SecfracDigitsStr::from_str("012345")?;
    /// assert_eq!(precise.microseconds_digits().unwrap(), "012345");
    ///
    /// let more_precise = SecfracDigitsStr::from_str("012345678901")?;
    /// assert_eq!(more_precise.microseconds_digits().unwrap(), "012345");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn microseconds_digits(&self) -> Option<&SecfracDigitsStr> {
        self.0.as_bytes().get(MICRO_RANGE).map(|s| unsafe {
            debug_assert!(validate_bytes(s).is_ok());
            // This is safe because the string consists of only ASCII digits.
            SecfracDigitsStr::from_bytes_unchecked(s)
        })
    }

    /// Returns a microseconds digits as a fixed bytes slice, if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let not_precise = SecfracDigitsStr::from_str("1234")?;
    /// assert_eq!(not_precise.microseconds_bytes_fixed_len(), None);
    ///
    /// let precise = SecfracDigitsStr::from_str("012345")?;
    /// assert_eq!(precise.microseconds_bytes_fixed_len(), Some(b"012345"));
    ///
    /// let more_precise = SecfracDigitsStr::from_str("012345678901")?;
    /// assert_eq!(more_precise.microseconds_bytes_fixed_len(), Some(b"012345"));
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn microseconds_bytes_fixed_len(&self) -> Option<&[u8; 6]> {
        self.0.as_bytes().get(MICRO_RANGE).map(|s| {
            debug_assert_eq!(s.len(), 6);
            let ptr = s.as_ptr() as *const [u8; 6];
            unsafe {
                // This is safe because the string consists of only ASCII digits.
                &*ptr
            }
        })
    }

    /// Returns a nanoseconds precision substring if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let not_precise = SecfracDigitsStr::from_str("1234")?;
    /// assert_eq!(not_precise.nanoseconds_digits(), None);
    ///
    /// let precise = SecfracDigitsStr::from_str("012345678")?;
    /// assert_eq!(precise.nanoseconds_digits().unwrap(), "012345678");
    ///
    /// let more_precise = SecfracDigitsStr::from_str("012345678901")?;
    /// assert_eq!(more_precise.nanoseconds_digits().unwrap(), "012345678");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn nanoseconds_digits(&self) -> Option<&SecfracDigitsStr> {
        self.0.as_bytes().get(NANO_RANGE).map(|s| unsafe {
            debug_assert!(validate_bytes(s).is_ok());
            // This is safe because the string consists of only ASCII digits.
            SecfracDigitsStr::from_bytes_unchecked(s)
        })
    }

    /// Returns a nanoseconds digits as a fixed bytes slice, if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let not_precise = SecfracDigitsStr::from_str("1234")?;
    /// assert_eq!(not_precise.nanoseconds_bytes_fixed_len(), None);
    ///
    /// let precise = SecfracDigitsStr::from_str("012345678")?;
    /// assert_eq!(precise.nanoseconds_bytes_fixed_len(), Some(b"012345678"));
    ///
    /// let more_precise = SecfracDigitsStr::from_str("012345678901")?;
    /// assert_eq!(more_precise.nanoseconds_bytes_fixed_len(), Some(b"012345678"));
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn nanoseconds_bytes_fixed_len(&self) -> Option<&[u8; 9]> {
        self.0.as_bytes().get(NANO_RANGE).map(|s| {
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
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let mut buf = "1234".to_owned();
    /// let secfrac = SecfracDigitsStr::from_mut_str(&mut buf)?;
    /// assert_eq!(secfrac.as_str(), "1234");
    ///
    /// secfrac.fill_with_zero();
    /// assert_eq!(secfrac.as_str(), "0000");
    ///
    /// assert_eq!(buf, "0000");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn fill_with_zero(&mut self) {
        // Use `slice::fill()` once rust-lang/rust#70758 is stabilized.
        // See <https://github.com/rust-lang/rust/issues/70758>.
        unsafe {
            // This is safe because the value after the modification is
            // "000...00", and it is of course a valid string because it
            // consists of only ASCII digits.
            self.0
                .as_bytes_mut()
                .iter_mut()
                .for_each(|digit| *digit = b'0');
        }
        debug_assert!(
            validate_bytes(self.as_bytes()).is_ok(),
            "The secfrac digits string must be valid after the modification"
        );
    }

    /// Fills the secfrac part with zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let mut buf = "1234".to_owned();
    /// let secfrac = SecfracDigitsStr::from_mut_str(&mut buf)?;
    /// assert_eq!(secfrac.as_str(), "1234");
    ///
    /// secfrac.fill_with_nine();
    /// assert_eq!(secfrac.as_str(), "9999");
    ///
    /// assert_eq!(buf, "9999");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn fill_with_nine(&mut self) {
        // Use `slice::fill()` once rust-lang/rust#70758 is stabilized.
        // See <https://github.com/rust-lang/rust/issues/70758>.
        unsafe {
            // This is safe because the value after the modification is
            // "999...99", and it is of course a valid string because it
            // consists of only ASCII digits.
            self.0
                .as_bytes_mut()
                .iter_mut()
                .for_each(|digit| *digit = b'9');
        }
        debug_assert!(
            validate_bytes(self.as_bytes()).is_ok(),
            "The secfrac digits string must be valid after the modification"
        );
    }
}

#[cfg(feature = "alloc")]
impl alloc::borrow::ToOwned for SecfracDigitsStr {
    type Owned = SecfracDigitsString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for SecfracDigitsStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for SecfracDigitsStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<SecfracDigitsStr> for SecfracDigitsStr {
    #[inline]
    fn as_ref(&self) -> &SecfracDigitsStr {
        self
    }
}

impl<'a> From<&'a SecfracDigitsStr> for &'a str {
    #[inline]
    fn from(v: &'a SecfracDigitsStr) -> Self {
        v.as_str()
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a SecfracDigitsStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because the string is already validated.
            SecfracDigitsStr::from_bytes_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut SecfracDigitsStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because the string is already validated.
            SecfracDigitsStr::from_bytes_unchecked_mut(v)
        })
    }
}

impl<'a> TryFrom<&'a str> for &'a SecfracDigitsStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because the string is already validated.
            SecfracDigitsStr::from_str_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut str> for &'a mut SecfracDigitsStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because the string is already validated.
            SecfracDigitsStr::from_str_unchecked_mut(v)
        })
    }
}

impl fmt::Display for SecfracDigitsStr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl ops::Deref for SecfracDigitsStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl_cmp_symmetric!(str, SecfracDigitsStr, &SecfracDigitsStr);
impl_cmp_symmetric!([u8], SecfracDigitsStr, [u8]);
impl_cmp_symmetric!([u8], SecfracDigitsStr, &[u8]);
impl_cmp_symmetric!([u8], &SecfracDigitsStr, [u8]);
impl_cmp_symmetric!(str, SecfracDigitsStr, str);
impl_cmp_symmetric!(str, SecfracDigitsStr, &str);
impl_cmp_symmetric!(str, &SecfracDigitsStr, str);

/// Items for serde support.
#[cfg(feature = "serde")]
mod serde_ {
    use super::*;

    use serde::de::{Deserialize, Deserializer, Visitor};

    /// Visitor for `&SecfracDigitsStr`.
    struct StrVisitor;

    impl<'de> Visitor<'de> for StrVisitor {
        type Value = &'de SecfracDigitsStr;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("digits of fractions of a second")
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

    impl<'de> Deserialize<'de> for &'de SecfracDigitsStr {
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
        assert!(s_validate(b"0").is_ok());
        assert!(s_validate(b"9").is_ok());
        assert!(s_validate(b"1234").is_ok());
        assert!(s_validate(b"001200").is_ok());
        assert!(s_validate(b"0000000").is_ok());
        assert!(s_validate(b"9999999").is_ok());
        assert!(s_validate(b"00000000000000000000000000000000").is_ok());
        assert!(s_validate(b"99999999999999999999999999999999").is_ok());

        assert!(s_validate(b"").is_err());
        assert!(s_validate(b".0").is_err());
        assert!(s_validate(b"+0").is_err());
        assert!(s_validate(b"-0").is_err());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_str() {
        let raw: &'static str = "1234";
        assert_tokens(
            &SecfracDigitsStr::from_str(raw).unwrap(),
            &[Token::BorrowedStr(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes_slice() {
        let raw: &'static [u8; 4] = b"1234";
        assert_de_tokens(
            &SecfracDigitsStr::from_bytes(raw).unwrap(),
            &[Token::BorrowedBytes(raw)],
        );
    }
}
