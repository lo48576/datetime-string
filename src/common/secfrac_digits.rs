//! Digits of fractions of a second.

#[cfg(feature = "alloc")]
mod owned;

use core::{
    cmp,
    convert::TryFrom,
    fmt,
    ops::{self, RangeTo},
    str,
};

use crate::{
    error::{ComponentKind, Error, ErrorKind},
    parse::parse_digits8,
};

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
// Note that `derive(Serialize)` cannot used here, because it encodes this as
// `[u8]` rather than as a string.
//
// Comparisons implemented for the type are consistent (at least it is intended to be so).
// See <https://github.com/rust-lang/rust-clippy/issues/2025>.
// Note that `clippy::derive_ord_xor_partial_ord` would be introduced since Rust 1.47.0.
#[allow(clippy::derive_hash_xor_eq)]
#[allow(clippy::unknown_clippy_lints, clippy::derive_ord_xor_partial_ord)]
pub struct SecfracDigitsStr([u8]);

impl SecfracDigitsStr {
    /// Creates a `&SecfracDigitsStr` from the given byte slice.
    ///
    /// This performs assertion in debug build, but not in release build.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_bytes_maybe_unchecked(s: &[u8]) -> &Self {
        debug_assert_ok!(validate_bytes(s));
        &*(s as *const [u8] as *const Self)
    }

    /// Creates a `&mut SecfracDigitsStr` from the given mutable byte slice.
    ///
    /// This performs assertion in debug build, but not in release build.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_bytes_maybe_unchecked_mut(s: &mut [u8]) -> &mut Self {
        debug_assert_ok!(validate_bytes(s));
        &mut *(s as *mut [u8] as *mut Self)
    }

    /// Creates a `&mut SecfracDigitsStr` from the given mutable string slice.
    ///
    /// This performs assertion in debug build, but not in release build.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_maybe_unchecked_mut(s: &mut str) -> &mut Self {
        // This is safe because `SecfracDigitsStr` ensures that the underlying
        // bytes are ASCII string after modification.
        Self::from_bytes_maybe_unchecked_mut(s.as_bytes_mut())
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
        unsafe {
            // This is safe because the `SecfracDigitsStr` ensures that the
            // underlying bytes are ASCII string.
            debug_assert_safe_version_ok!(str::from_utf8(&self.0));
            str::from_utf8_unchecked(&self.0)
        }
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
        &self.0
    }

    /// Retruns a milliseconds value in integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let not_precise = SecfracDigitsStr::from_str("1")?;
    /// assert_eq!(not_precise.milliseconds(), 100);
    ///
    /// let precise = SecfracDigitsStr::from_str("012")?;
    /// assert_eq!(precise.milliseconds(), 12);
    ///
    /// let more_precise = SecfracDigitsStr::from_str("369999")?;
    /// assert_eq!(more_precise.milliseconds(), 369);
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn milliseconds(&self) -> u16 {
        let bytes = &self.0;
        match self.len() {
            1 => (bytes[0] - b'0') as u16 * 100,
            2 => (bytes[0] - b'0') as u16 * 100 + (bytes[1] - b'0') as u16 * 10,
            _ => {
                debug_assert!(self.len() >= 3);
                (bytes[0] - b'0') as u16 * 100
                    + (bytes[1] - b'0') as u16 * 10
                    + (bytes[2] - b'0') as u16
            }
        }
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
        self.0.get(MILLI_RANGE).map(|s| unsafe {
            debug_assert_ok!(validate_bytes(s));
            debug_assert_safe_version_ok!(<&Self>::try_from(s));
            // This is safe because `self.0` consists of only ASCII digits,
            // and so is the substring.
            Self::from_bytes_maybe_unchecked(s)
        })
    }

    /// Returns a milliseconds precision substring if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let mut buf = "012345678901".to_owned();
    /// let digits = SecfracDigitsStr::from_mut_str(&mut buf)?;
    /// assert_eq!(digits.as_str(), "012345678901");
    ///
    /// digits.milliseconds_digits_mut().unwrap().fill_with_zero();
    /// assert_eq!(digits.as_str(), "000345678901");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn milliseconds_digits_mut(&mut self) -> Option<&mut SecfracDigitsStr> {
        self.0.get_mut(MILLI_RANGE).map(|s| {
            unsafe {
                // This is safe because `self.0` consists of only ASCII digits,
                // and so is the substring.
                debug_assert_ok!(Self::from_bytes(s));
                Self::from_bytes_maybe_unchecked_mut(s)
            }
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
        self.0.get(MILLI_RANGE).map(|s| {
            debug_assert_eq!(s.len(), 3);
            debug_assert_safe_version_ok!(<&[u8; 3]>::try_from(s));
            let ptr = s.as_ptr() as *const [u8; 3];
            unsafe {
                // This is safe because the string consists of only ASCII digits.
                &*ptr
            }
        })
    }

    /// Retruns a microseconds value in integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let not_precise = SecfracDigitsStr::from_str("1")?;
    /// assert_eq!(not_precise.microseconds(), 100_000);
    ///
    /// let precise = SecfracDigitsStr::from_str("012345")?;
    /// assert_eq!(precise.microseconds(), 012_345);
    ///
    /// let more_precise = SecfracDigitsStr::from_str("123456999")?;
    /// assert_eq!(more_precise.microseconds(), 123_456);
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn microseconds(&self) -> u32 {
        let bytes = &self.0;
        let len = bytes.len();
        let len6 = cmp::min(6, len);

        let mut buf: [u8; 8] = [b'0'; 8];
        // Note that the first two digits should be `0`.
        buf[2..(2 + len6)].copy_from_slice(&bytes[..len6]);
        parse_digits8(buf)
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
        self.0.get(MICRO_RANGE).map(|s| unsafe {
            debug_assert_safe_version_ok!(Self::from_bytes(s));
            // This is safe because `self.0` consists of only ASCII digits,
            // and so is the substring.
            SecfracDigitsStr::from_bytes_maybe_unchecked(s)
        })
    }

    /// Returns a microseconds precision substring if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let mut buf = "012345678901".to_owned();
    /// let digits = SecfracDigitsStr::from_mut_str(&mut buf)?;
    /// assert_eq!(digits.as_str(), "012345678901");
    ///
    /// digits.microseconds_digits_mut().unwrap().fill_with_zero();
    /// assert_eq!(digits.as_str(), "000000678901");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn microseconds_digits_mut(&mut self) -> Option<&mut SecfracDigitsStr> {
        self.0.get_mut(MICRO_RANGE).map(|s| {
            unsafe {
                // This is safe because `self.0` consists of only ASCII digits,
                // and so is the substring.
                debug_assert_ok!(Self::from_bytes(s));
                SecfracDigitsStr::from_bytes_maybe_unchecked_mut(s)
            }
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
        self.0.get(MICRO_RANGE).map(|s| {
            debug_assert_eq!(s.len(), 6);
            debug_assert_safe_version_ok!(<&[u8; 6]>::try_from(s));
            let ptr = s.as_ptr() as *const [u8; 6];
            unsafe {
                // This is safe because the string consists of only ASCII digits.
                &*ptr
            }
        })
    }

    /// Retruns a nanoseconds value in integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let not_precise = SecfracDigitsStr::from_str("1")?;
    /// assert_eq!(not_precise.nanoseconds(), 100_000_000);
    ///
    /// let precise = SecfracDigitsStr::from_str("012345678")?;
    /// assert_eq!(precise.nanoseconds(), 012_345_678);
    ///
    /// let more_precise = SecfracDigitsStr::from_str("876543210999")?;
    /// assert_eq!(more_precise.nanoseconds(), 876_543_210);
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn nanoseconds(&self) -> u32 {
        let bytes = &self.0;
        let len = bytes.len();
        let len8 = cmp::min(8, len);

        let mut buf: [u8; 8] = [b'0'; 8];
        buf[..len8].copy_from_slice(&bytes[..len8]);
        let upper8 = parse_digits8(buf) * 10;
        if len > 8 {
            upper8 + (bytes[8] - b'0') as u32
        } else {
            upper8
        }
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
        self.0.get(NANO_RANGE).map(|s| unsafe {
            debug_assert_safe_version_ok!(Self::from_bytes(s));
            // This is safe because `self.0` consists of only ASCII digits,
            // and so is the substring.
            SecfracDigitsStr::from_bytes_maybe_unchecked(s)
        })
    }

    /// Returns a nanoseconds precision substring if there are enough digits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::SecfracDigitsStr;
    /// let mut buf = "012345678901".to_owned();
    /// let digits = SecfracDigitsStr::from_mut_str(&mut buf)?;
    /// assert_eq!(digits.as_str(), "012345678901");
    ///
    /// digits.nanoseconds_digits_mut().unwrap().fill_with_zero();
    /// assert_eq!(digits.as_str(), "000000000901");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn nanoseconds_digits_mut(&mut self) -> Option<&mut SecfracDigitsStr> {
        self.0.get_mut(NANO_RANGE).map(|s| {
            unsafe {
                // This is safe because `self.0` consists of only ASCII digits,
                // and so is the substring.
                debug_assert_ok!(Self::from_bytes(s));
                SecfracDigitsStr::from_bytes_maybe_unchecked_mut(s)
            }
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
        self.0.get(NANO_RANGE).map(|s| {
            debug_assert_eq!(s.len(), 9);
            debug_assert_safe_version_ok!(<&[u8; 9]>::try_from(s));
            let ptr = s.as_ptr() as *const [u8; 9];
            unsafe {
                // This is safe because the string consists of only ASCII digits.
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
        self.0.iter_mut().for_each(|digit| *digit = b'0');
        debug_assert!(
            validate_bytes(&self.0).is_ok(),
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
        self.0.iter_mut().for_each(|digit| *digit = b'9');
        debug_assert!(
            validate_bytes(&self.0).is_ok(),
            "The secfrac digits string must be valid after the modification"
        );
    }
}

impl AsRef<[u8]> for SecfracDigitsStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.0
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

impl AsMut<SecfracDigitsStr> for SecfracDigitsStr {
    #[inline]
    fn as_mut(&mut self) -> &mut SecfracDigitsStr {
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
            SecfracDigitsStr::from_bytes_maybe_unchecked(v)
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
            SecfracDigitsStr::from_bytes_maybe_unchecked_mut(v)
        })
    }
}

impl<'a> TryFrom<&'a str> for &'a SecfracDigitsStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a str) -> Result<Self, Self::Error> {
        Self::try_from(v.as_bytes())
    }
}

impl<'a> TryFrom<&'a mut str> for &'a mut SecfracDigitsStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because the string is already validated and
            // `SecfracDigitsStr` ensures that the underlying bytes are ASCII
            // string after modification.
            SecfracDigitsStr::from_str_maybe_unchecked_mut(v)
        })
    }
}

impl fmt::Display for SecfracDigitsStr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl ops::Deref for SecfracDigitsStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl_cmp_symmetric!(str, SecfracDigitsStr, &SecfracDigitsStr);
impl_cmp_symmetric!([u8], SecfracDigitsStr, [u8]);
impl_cmp_symmetric!([u8], SecfracDigitsStr, &[u8]);
impl_cmp_symmetric!([u8], &SecfracDigitsStr, [u8]);
impl_cmp_symmetric!(str, SecfracDigitsStr, str);
impl_cmp_symmetric!(str, SecfracDigitsStr, &str);
impl_cmp_symmetric!(str, &SecfracDigitsStr, str);

#[cfg(feature = "serde")]
impl serde::Serialize for SecfracDigitsStr {
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
