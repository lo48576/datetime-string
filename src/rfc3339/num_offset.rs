//! RFC 3339 [`time-numoffset`] string types.
//!
//! [`time-numoffset`]: https://tools.ietf.org/html/rfc3339#section-5.6

use core::{
    cmp::Ordering,
    convert::TryFrom,
    fmt,
    ops::{self, Range, RangeTo},
    str,
};

use crate::{parse::parse_bcd2, str::write_digit2};

#[cfg(feature = "alloc")]
use alloc::{string::String, vec::Vec};

#[cfg(feature = "serde")]
use serde::Serialize;

use crate::common::TimeOffsetSign;

use super::{ComponentKind, ErrorKind, ValidationError};

/// Length of time-numoffset (e.g. "+12:34").
const NUM_OFFSET_LEN: usize = 6;
/// Range of the absolute hour in the string.
const HOUR_ABS_RANGE: Range<usize> = 1..3;
/// Range of the signed hour in the string.
const HOUR_SIGNED_RANGE: RangeTo<usize> = ..3;
/// Range of the minute in the string.
const MINUTE_RANGE: Range<usize> = 4..6;
/// Maximum value of the hour.
const HOUR_MAX: u8 = 23;
/// Maximum value of the minute.
const MINUTE_MAX: u8 = 59;

/// Validates the given string as an RFC 3339 [`time-numoffset`] string.
///
/// [`time-numoffset`]: https://tools.ietf.org/html/rfc3339#section-5.6
fn validate_bytes(s: &[u8]) -> Result<(), ValidationError> {
    let s: &[u8; NUM_OFFSET_LEN] = match s.len().cmp(&NUM_OFFSET_LEN) {
        Ordering::Greater => return Err(ErrorKind::TooLong.into()),
        Ordering::Less => return Err(ErrorKind::TooShort.into()),
        Ordering::Equal => {
            TryFrom::try_from(s).expect("Should never fail because the length is equal")
        }
    };

    if ((s[0] != b'+') && (s[0] != b'-')) || (s[3] != b':') {
        return Err(ErrorKind::InvalidSeparator.into());
    }

    let hour_s: [u8; 2] = [s[1], s[2]];
    let minute_s: [u8; 2] = [s[4], s[5]];

    if !hour_s.iter().all(u8::is_ascii_digit) {
        return Err(ErrorKind::InvalidComponentType(ComponentKind::OffsetHour).into());
    }
    if !minute_s.iter().all(u8::is_ascii_digit) {
        return Err(ErrorKind::InvalidComponentType(ComponentKind::OffsetMinute).into());
    }

    let hour = parse_bcd2(hour_s);
    if hour > HOUR_MAX {
        return Err(ErrorKind::ComponentOutOfRange(ComponentKind::OffsetHour).into());
    }
    let minute = parse_bcd2(minute_s);
    if minute > MINUTE_MAX {
        return Err(ErrorKind::ComponentOutOfRange(ComponentKind::OffsetMinute).into());
    }

    Ok(())
}

/// RFC 3339 [`time-numoffset`] string slice.
///
/// [`time-numoffset`]: https://tools.ietf.org/html/rfc3339#section-5.6
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
// Comparisons implemented for the type are consistent (at least it is intended to be so).
// See <https://github.com/rust-lang/rust-clippy/issues/2025>.
// Note that `clippy::derive_ord_xor_partial_ord` would be introduced since Rust 1.47.0.
#[allow(clippy::derive_hash_xor_eq)]
#[allow(clippy::unknown_clippy_lints, clippy::derive_ord_xor_partial_ord)]
pub struct TimeNumOffsetStr(str);

impl TimeNumOffsetStr {
    /// Creates a `&TimeNumOffsetStr` from the given byte slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_bytes_unchecked(s: &[u8]) -> &Self {
        Self::from_str_unchecked(str::from_utf8_unchecked(s))
    }

    /// Creates a `&mut TimeNumOffsetStr` from the given mutable byte slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_bytes_unchecked_mut(s: &mut [u8]) -> &mut Self {
        Self::from_str_unchecked_mut(str::from_utf8_unchecked_mut(s))
    }

    /// Creates a `&TimeNumOffsetStr` from the given string slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const TimeNumOffsetStr)
    }

    /// Creates a `&mut TimeNumOffsetStr` from the given mutable string slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_unchecked_mut(s: &mut str) -> &mut Self {
        &mut *(s as *mut str as *mut TimeNumOffsetStr)
    }

    /// Creates a new `&TimeNumOffsetStr` from a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    /// assert_eq!(offset.as_str(), "-12:34");
    ///
    /// assert!(TimeNumOffsetStr::from_str("+00:00").is_ok());
    /// assert!(TimeNumOffsetStr::from_str("+23:59").is_ok());
    /// assert!(TimeNumOffsetStr::from_str("-00:00").is_ok());
    /// assert!(TimeNumOffsetStr::from_str("-23:59").is_ok());
    ///
    /// assert!(TimeNumOffsetStr::from_str("Z").is_err(), "Not time-numoffset");
    /// assert!(TimeNumOffsetStr::from_str("+24:00").is_err(), "Invalid hour");
    /// assert!(TimeNumOffsetStr::from_str("+00:60").is_err(), "Invalid minute");
    /// assert!(TimeNumOffsetStr::from_str("-24:00").is_err(), "Invalid hour");
    /// assert!(TimeNumOffsetStr::from_str("-00:60").is_err(), "Invalid minute");
    /// assert!(TimeNumOffsetStr::from_str("?00:00").is_err(), "Invalid sign");
    /// assert!(TimeNumOffsetStr::from_str("00:00").is_err(), "Sign is missing");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    // `FromStr` trait cannot be implemented for a slice.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, ValidationError> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut TimeNumOffsetStr` from a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// use datetime_string::common::TimeOffsetSign;
    /// let mut buf = "-12:34".to_owned();
    /// let offset = TimeNumOffsetStr::from_mut_str(&mut buf)?;
    /// assert_eq!(offset.as_str(), "-12:34");
    ///
    /// offset.set_sign(TimeOffsetSign::Positive);
    /// assert_eq!(offset.as_str(), "+12:34");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn from_mut_str(s: &mut str) -> Result<&mut Self, ValidationError> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&TimeNumOffsetStr` from a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_bytes(b"-12:34")?;
    /// assert_eq!(offset.as_str(), "-12:34");
    ///
    /// assert!(TimeNumOffsetStr::from_bytes(b"+00:00").is_ok());
    /// assert!(TimeNumOffsetStr::from_bytes(b"+23:59").is_ok());
    /// assert!(TimeNumOffsetStr::from_bytes(b"-00:00").is_ok());
    /// assert!(TimeNumOffsetStr::from_bytes(b"-23:59").is_ok());
    ///
    /// assert!(TimeNumOffsetStr::from_bytes(b"Z").is_err(), "Not time-numoffset");
    /// assert!(TimeNumOffsetStr::from_bytes(b"+24:00").is_err(), "Invalid hour");
    /// assert!(TimeNumOffsetStr::from_bytes(b"+00:60").is_err(), "Invalid minute");
    /// assert!(TimeNumOffsetStr::from_bytes(b"-24:00").is_err(), "Invalid hour");
    /// assert!(TimeNumOffsetStr::from_bytes(b"-00:60").is_err(), "Invalid minute");
    /// assert!(TimeNumOffsetStr::from_bytes(b"?00:00").is_err(), "Invalid sign");
    /// assert!(TimeNumOffsetStr::from_bytes(b"00:00").is_err(), "Sign is missing");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn from_bytes(s: &[u8]) -> Result<&Self, ValidationError> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut TimeNumOffsetStr` from a mutable byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// use datetime_string::common::TimeOffsetSign;
    /// let mut buf: [u8; 6] = *b"-12:34";
    /// let offset = TimeNumOffsetStr::from_bytes_mut(&mut buf)?;
    /// assert_eq!(offset.as_str(), "-12:34");
    ///
    /// offset.set_sign(TimeOffsetSign::Positive);
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
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    ///
    /// assert_eq!(offset.as_str(), "-12:34");
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
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_bytes(b"-12:34")?;
    ///
    /// assert_eq!(offset.as_bytes(), b"-12:34");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    ///
    /// [`as_bytes_fixed_len`]: #method.as_bytes_fixed_len
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Returns a fixed length byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    ///
    /// let fixed_len: &[u8; 6] = offset.as_bytes_fixed_len();
    /// assert_eq!(fixed_len, b"-12:34");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_bytes_fixed_len(&self) -> &[u8; 6] {
        debug_assert_eq!(
            self.len(),
            NUM_OFFSET_LEN,
            "TimeNumOffsetStr must always be 6 bytes"
        );

        let ptr = self.0.as_ptr() as *const [u8; NUM_OFFSET_LEN];
        // This must be always safe because the length is already checked.
        unsafe { &*ptr }
    }

    /// Returns the time offset sign.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// use datetime_string::common::TimeOffsetSign;
    ///
    /// let positive = TimeNumOffsetStr::from_str("+12:34")?;
    /// assert_eq!(positive.sign(), TimeOffsetSign::Positive);
    ///
    /// let negative = TimeNumOffsetStr::from_str("-12:34")?;
    /// assert_eq!(negative.sign(), TimeOffsetSign::Negative);
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    ///
    /// Note that signs are preserved for `+00:00` and `-00:00`.
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// use datetime_string::common::TimeOffsetSign;
    ///
    /// let positive0 = TimeNumOffsetStr::from_str("+00:00")?;
    /// assert_eq!(positive0.sign(), TimeOffsetSign::Positive);
    ///
    /// let negative0 = TimeNumOffsetStr::from_str("-00:00")?;
    /// assert_eq!(negative0.sign(), TimeOffsetSign::Negative);
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn sign(&self) -> TimeOffsetSign {
        if self.as_bytes()[0] == b'+' {
            TimeOffsetSign::Positive
        } else {
            debug_assert_eq!(self.as_bytes()[0], b'-');
            TimeOffsetSign::Negative
        }
    }

    /// Returns a mutable reference to the byte which contains the sign character.
    ///
    /// # Safety
    ///
    /// The returned byte should have `b'+'` or `b'-'`.
    /// If other values are stored, it may lead to undefined behavior.
    #[inline]
    #[must_use]
    unsafe fn sign_byte_mut(&mut self) -> &mut u8 {
        // This must be always safe because a valid time-numoffset string is
        // also a non-empty ASCII string.
        self.0.as_bytes_mut().get_unchecked_mut(0)
    }

    /// Sets the given sign.
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// use datetime_string::common::TimeOffsetSign;
    /// let mut buf = "-12:34".to_owned();
    /// let offset = TimeNumOffsetStr::from_mut_str(&mut buf)?;
    /// assert_eq!(offset.as_str(), "-12:34");
    /// assert_eq!(offset.sign(), TimeOffsetSign::Negative);
    ///
    /// offset.set_sign(TimeOffsetSign::Positive);
    /// assert_eq!(offset.as_str(), "+12:34");
    /// assert_eq!(offset.sign(), TimeOffsetSign::Positive);
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn set_sign(&mut self, sign: TimeOffsetSign) {
        let byte = match sign {
            TimeOffsetSign::Positive => b'+',
            TimeOffsetSign::Negative => b'-',
        };
        unsafe {
            // This is safe because a valid time-numoffset is also an ASCII string,
            // and the substituted value (`byte`) is also an ASCII character.
            *self.sign_byte_mut() = byte;
        }
        debug_assert!(validate_bytes(self.as_bytes()).is_ok());
        debug_assert_eq!(self.sign(), sign);
    }

    /// Returns the absolute hour as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    ///
    /// assert_eq!(offset.hour_abs_str(), "12");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn hour_abs_str(&self) -> &str {
        &self.0[HOUR_ABS_RANGE]
    }

    /// Returns the absolute hour as a fixed length byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    ///
    /// let hour_fixed_len: &[u8; 2] = offset.hour_abs_bytes_fixed_len();
    /// assert_eq!(hour_fixed_len, b"12");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn hour_abs_bytes_fixed_len(&self) -> &[u8; 2] {
        let ptr = self.0[HOUR_ABS_RANGE].as_ptr() as *const [u8; 2];
        // This must be always safe because the string is valid time-numoffset string.
        unsafe { &*ptr }
    }

    /// Returns the absolute hour as a fixed length mutable byte slice.
    ///
    /// # Safety
    ///
    /// The returned slice should have only ASCII digits.
    /// If non-ASCII digits are stored, it may lead to undefined behavior.
    #[inline]
    #[must_use]
    unsafe fn hour_abs_bytes_mut_fixed_len(&mut self) -> &mut [u8; 2] {
        let ptr = self.0[HOUR_ABS_RANGE].as_mut_ptr() as *mut [u8; 2];
        // This must be always safe because the string is valid time-numoffset string.
        &mut *ptr
    }

    /// Returns the absolute hour as an integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    ///
    /// assert_eq!(offset.hour_abs(), 12);
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn hour_abs(&self) -> u8 {
        parse_bcd2(*self.hour_abs_bytes_fixed_len())
    }

    /// Sets the given absolute hour value to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the time after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let mut buf: [u8; 6] = *b"-12:34";
    /// let time = TimeNumOffsetStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "-12:34");
    ///
    /// time.set_hour_abs(0)?;
    /// assert_eq!(time.as_str(), "-00:34");
    ///
    /// assert!(time.set_hour_abs(24).is_err(), "-24:34 is invalid");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn set_hour_abs(&mut self, hour_abs: u8) -> Result<(), ValidationError> {
        if hour_abs > HOUR_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::OffsetHour).into());
        }
        unsafe {
            // This is safe because `write_digit2()` fills the slice with ASCII digits.
            write_digit2(self.hour_abs_bytes_mut_fixed_len(), hour_abs);
        }
        debug_assert!(validate_bytes(self.as_bytes()).is_ok());

        Ok(())
    }

    /// Returns the signed hour as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    ///
    /// assert_eq!(offset.hour_signed_str(), "-12");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn hour_signed_str(&self) -> &str {
        &self.0[HOUR_SIGNED_RANGE]
    }

    /// Returns the signed hour as a fixed length byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    ///
    /// let hour_fixed_len: &[u8; 3] = offset.hour_signed_bytes_fixed_len();
    /// assert_eq!(hour_fixed_len, b"-12");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn hour_signed_bytes_fixed_len(&self) -> &[u8; 3] {
        let ptr = self.0[HOUR_SIGNED_RANGE].as_ptr() as *const [u8; 3];
        // This must be always safe because the string is valid time-numoffset string.
        unsafe { &*ptr }
    }

    /// Returns the signed hour as an integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    ///
    /// assert_eq!(offset.hour_signed(), -12);
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    ///
    /// Note that both `+00` and `-00` are treaded as the same 0.
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let positive = TimeNumOffsetStr::from_str("+00:59")?;
    /// assert_eq!(positive.hour_signed(), 0);
    ///
    /// let negative = TimeNumOffsetStr::from_str("-00:59")?;
    /// assert_eq!(negative.hour_signed(), 0);
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn hour_signed(&self) -> i8 {
        let abs = self.hour_abs() as i8;
        match self.sign() {
            TimeOffsetSign::Positive => abs,
            TimeOffsetSign::Negative => -abs,
        }
    }

    /// Sets the given absolute hour value and sign to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the time after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// use datetime_string::common::TimeOffsetSign;
    /// let mut buf: [u8; 6] = *b"-12:34";
    /// let time = TimeNumOffsetStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "-12:34");
    ///
    /// time.set_sign_and_hour_abs(TimeOffsetSign::Positive, 23)?;
    /// assert_eq!(time.as_str(), "+23:34");
    ///
    /// assert!(time.set_sign_and_hour_abs(TimeOffsetSign::Negative, 24).is_err(), "-24:34 is invalid");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn set_sign_and_hour_abs(
        &mut self,
        sign: TimeOffsetSign,
        hour_abs: u8,
    ) -> Result<(), ValidationError> {
        self.set_hour_abs(hour_abs)?;
        self.set_sign(sign);
        debug_assert!(validate_bytes(self.as_bytes()).is_ok());

        Ok(())
    }

    /// Sets the given signed hour value to the string.
    ///
    /// If `0` is passed, it is always considered as positive 0.
    ///
    /// # Failures
    ///
    /// * Fails if the time after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// use datetime_string::common::TimeOffsetSign;
    /// let mut buf: [u8; 6] = *b"-12:34";
    /// let time = TimeNumOffsetStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "-12:34");
    ///
    /// time.set_hour_signed(0)?;
    /// assert_eq!(time.as_str(), "+00:34");
    ///
    /// time.set_hour_signed(-1)?;
    /// assert_eq!(time.as_str(), "-01:34");
    ///
    /// assert!(time.set_hour_signed(24).is_err(), "+24:34 is invalid");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn set_hour_signed(&mut self, hour: i8) -> Result<(), ValidationError> {
        let sign = if hour >= 0 {
            TimeOffsetSign::Positive
        } else {
            TimeOffsetSign::Negative
        };
        let hour_abs = hour.wrapping_abs() as u8;

        self.set_sign_and_hour_abs(sign, hour_abs)
    }

    /// Returns the minute as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    ///
    /// assert_eq!(offset.minute_str(), "34");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn minute_str(&self) -> &str {
        &self.0[MINUTE_RANGE]
    }

    /// Returns the minute as a fixed length byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    ///
    /// let minute_fixed_len: &[u8; 2] = offset.minute_bytes_fixed_len();
    /// assert_eq!(minute_fixed_len, b"34");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn minute_bytes_fixed_len(&self) -> &[u8; 2] {
        let ptr = self.0[MINUTE_RANGE].as_ptr() as *const [u8; 2];
        // This must be always safe because the string is valid time-numoffset string.
        unsafe { &*ptr }
    }

    /// Returns the minute as a fixed length mutable byte slice.
    ///
    /// # Safety
    ///
    /// The returned slice should have only ASCII digits.
    /// If non-ASCII digits are stored, it may lead to undefined behavior.
    #[inline]
    #[must_use]
    unsafe fn minute_bytes_mut_fixed_len(&mut self) -> &mut [u8; 2] {
        let ptr = self.0[MINUTE_RANGE].as_mut_ptr() as *mut [u8; 2];
        // This must be always safe because the string is valid time-numoffset string.
        &mut *ptr
    }

    /// Returns the minute as an integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = TimeNumOffsetStr::from_str("-12:34")?;
    ///
    /// assert_eq!(offset.minute(), 34);
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn minute(&self) -> u8 {
        parse_bcd2(*self.minute_bytes_fixed_len())
    }

    /// Sets the given minute value to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the time after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let mut buf: [u8; 6] = *b"-12:34";
    /// let time = TimeNumOffsetStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "-12:34");
    ///
    /// time.set_minute(01)?;
    /// assert_eq!(time.as_str(), "-12:01");
    ///
    /// assert!(time.set_minute(60).is_err(), "-12:60 is invalid");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn set_minute(&mut self, minute: u8) -> Result<(), ValidationError> {
        if minute > MINUTE_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::OffsetMinute).into());
        }
        unsafe {
            // This is safe because `write_digit2()` fills the slice with ASCII digits.
            write_digit2(self.minute_bytes_mut_fixed_len(), minute);
        }
        debug_assert!(validate_bytes(self.as_bytes()).is_ok());

        Ok(())
    }

    /// Sets the given signed hour and minute value to the string.
    ///
    /// If `0` is passed, it is always considered as positive 0.
    ///
    /// # Failures
    ///
    /// * Fails if the time after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// use datetime_string::common::TimeOffsetSign;
    /// let mut buf: [u8; 6] = *b"-12:34";
    /// let time = TimeNumOffsetStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "-12:34");
    ///
    /// time.set_time_signed(0, 56)?;
    /// assert_eq!(time.as_str(), "+00:56");
    ///
    /// time.set_time_signed(-1, 23)?;
    /// assert_eq!(time.as_str(), "-01:23");
    ///
    /// assert!(time.set_time_signed(24, 00).is_err(), "+24:00 is invalid");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    pub fn set_time_signed(&mut self, hour: i8, minute: u8) -> Result<(), ValidationError> {
        let hour_abs = hour.wrapping_abs() as u8;
        let sign = if hour >= 0 {
            TimeOffsetSign::Positive
        } else {
            TimeOffsetSign::Negative
        };

        self.set_sign_and_time(sign, hour_abs, minute)
    }

    /// Sets the given sign, absolute hour, and minute value to the string.
    ///
    /// If `0` is passed, it is always considered as positive 0.
    ///
    /// # Failures
    ///
    /// * Fails if the time after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetStr;
    /// use datetime_string::common::TimeOffsetSign;
    /// let mut buf: [u8; 6] = *b"-12:34";
    /// let time = TimeNumOffsetStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "-12:34");
    ///
    /// time.set_sign_and_time(TimeOffsetSign::Negative, 0, 56)?;
    /// assert_eq!(time.as_str(), "-00:56");
    ///
    /// time.set_sign_and_time(TimeOffsetSign::Positive, 1, 23)?;
    /// assert_eq!(time.as_str(), "+01:23");
    ///
    /// assert!(time.set_sign_and_time(TimeOffsetSign::Positive, 24, 00).is_err(), "+24:00 is invalid");
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    pub fn set_sign_and_time(
        &mut self,
        sign: TimeOffsetSign,
        hour_abs: u8,
        minute: u8,
    ) -> Result<(), ValidationError> {
        if hour_abs > HOUR_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::OffsetHour).into());
        }
        if minute > MINUTE_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::OffsetMinute).into());
        }

        self.set_sign(sign);
        unsafe {
            // This is safe because `write_digit2()` fills the slice with ASCII digits.
            write_digit2(self.hour_abs_bytes_mut_fixed_len(), hour_abs);
            write_digit2(self.minute_bytes_mut_fixed_len(), minute);
        }
        debug_assert!(validate_bytes(self.as_bytes()).is_ok());

        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl alloc::borrow::ToOwned for TimeNumOffsetStr {
    type Owned = TimeNumOffsetString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for TimeNumOffsetStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for TimeNumOffsetStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<TimeNumOffsetStr> for TimeNumOffsetStr {
    #[inline]
    fn as_ref(&self) -> &TimeNumOffsetStr {
        self
    }
}

impl<'a> From<&'a TimeNumOffsetStr> for &'a str {
    #[inline]
    fn from(v: &'a TimeNumOffsetStr) -> Self {
        v.as_str()
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a TimeNumOffsetStr {
    type Error = ValidationError;

    #[inline]
    fn try_from(v: &'a [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid time-numoffset string is also an ASCII string.
            TimeNumOffsetStr::from_bytes_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut TimeNumOffsetStr {
    type Error = ValidationError;

    #[inline]
    fn try_from(v: &'a mut [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid time-numoffset string is also an ASCII string.
            TimeNumOffsetStr::from_bytes_unchecked_mut(v)
        })
    }
}

impl<'a> TryFrom<&'a str> for &'a TimeNumOffsetStr {
    type Error = ValidationError;

    #[inline]
    fn try_from(v: &'a str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because a valid time-numoffset string is also an ASCII string.
            TimeNumOffsetStr::from_str_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut str> for &'a mut TimeNumOffsetStr {
    type Error = ValidationError;

    #[inline]
    fn try_from(v: &'a mut str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because a valid time-numoffset string is also an ASCII string.
            TimeNumOffsetStr::from_str_unchecked_mut(v)
        })
    }
}

impl fmt::Display for TimeNumOffsetStr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl ops::Deref for TimeNumOffsetStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl_cmp_symmetric!(str, TimeNumOffsetStr, &TimeNumOffsetStr);
impl_cmp_symmetric!([u8], TimeNumOffsetStr, [u8]);
impl_cmp_symmetric!([u8], TimeNumOffsetStr, &[u8]);
impl_cmp_symmetric!([u8], &TimeNumOffsetStr, [u8]);
impl_cmp_symmetric!(str, TimeNumOffsetStr, str);
impl_cmp_symmetric!(str, TimeNumOffsetStr, &str);
impl_cmp_symmetric!(str, &TimeNumOffsetStr, str);

/// RFC 3339 [`time-numoffset`] string slice.
///
/// This is a fixed length string, and implements [`Copy`] trait.
///
/// To create a value of this type, use [`<str>::parse()`] method or
/// [`std::convert::TryFrom`] trait, or convert from `&TimeNumOffsetStr`.
///
/// # Examples
///
/// ```
/// # use datetime_string::rfc3339::TimeNumOffsetString;
/// use datetime_string::rfc3339::TimeNumOffsetStr;
/// use std::convert::TryFrom;
///
/// let try_from = TimeNumOffsetString::try_from("-12:34")?;
///
/// let parse = "-12:34".parse::<TimeNumOffsetString>()?;
/// let parse2: TimeNumOffsetString = "-12:34".parse()?;
///
/// let to_owned = TimeNumOffsetStr::from_str("-12:34")?.to_owned();
/// let into: TimeNumOffsetString = TimeNumOffsetStr::from_str("-12:34")?.into();
/// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
/// ```
///
/// [`time-numoffset`]: https://tools.ietf.org/html/rfc3339#section-5.6
// Note that `derive(Serialize)` cannot used here, because it encodes this as
// `[u8; 6]` rather than as a string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
// Comparisons implemented for the type are consistent (at least it is intended to be so).
// See <https://github.com/rust-lang/rust-clippy/issues/2025>.
// Note that `clippy::derive_ord_xor_partial_ord` would be introduced since Rust 1.47.0.
#[allow(clippy::derive_hash_xor_eq)]
#[allow(clippy::unknown_clippy_lints, clippy::derive_ord_xor_partial_ord)]
pub struct TimeNumOffsetString([u8; NUM_OFFSET_LEN]);

impl TimeNumOffsetString {
    /// Creates a `TimeNumOffsetString` from the given bytes.
    ///
    /// # Safety
    ///
    /// `validate_bytes(&s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn new_unchecked(s: [u8; 6]) -> Self {
        Self(s)
    }

    /// Returns a `&TimeNumOffsetStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetString;
    /// use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let offset = "-12:34".parse::<TimeNumOffsetString>()?;
    ///
    /// // Usually you don't need to call `as_deref()` explicitly, because
    /// // `Deref<Target = TimeNumOffsetStr>` trait is implemented.
    /// let _: &TimeNumOffsetStr = offset.as_deref();
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref(&self) -> &TimeNumOffsetStr {
        unsafe {
            // This is safe because `self.0` is valid time-numoffset string.
            TimeNumOffsetStr::from_bytes_unchecked(&self.0)
        }
    }

    /// Returns a `&mut TimeNumOffsetStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::TimeNumOffsetString;
    /// use datetime_string::rfc3339::TimeNumOffsetStr;
    /// let mut offset = "-12:34".parse::<TimeNumOffsetString>()?;
    ///
    /// // Usually you don't need to call `as_deref_mut()` explicitly, because
    /// // `DerefMut` trait is implemented.
    /// let _: &mut TimeNumOffsetStr = offset.as_deref_mut();
    /// # Ok::<_, datetime_string::rfc3339::ValidationError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref_mut(&mut self) -> &mut TimeNumOffsetStr {
        unsafe {
            // This is safe because `self.0` is valid time-numoffset string.
            TimeNumOffsetStr::from_bytes_unchecked_mut(&mut self.0)
        }
    }
}

impl core::borrow::Borrow<TimeNumOffsetStr> for TimeNumOffsetString {
    #[inline]
    fn borrow(&self) -> &TimeNumOffsetStr {
        self.as_deref()
    }
}

impl core::borrow::BorrowMut<TimeNumOffsetStr> for TimeNumOffsetString {
    #[inline]
    fn borrow_mut(&mut self) -> &mut TimeNumOffsetStr {
        self.as_deref_mut()
    }
}

impl AsRef<[u8]> for TimeNumOffsetString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for TimeNumOffsetString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<TimeNumOffsetStr> for TimeNumOffsetString {
    #[inline]
    fn as_ref(&self) -> &TimeNumOffsetStr {
        self
    }
}

#[cfg(feature = "alloc")]
impl From<TimeNumOffsetString> for Vec<u8> {
    #[inline]
    fn from(v: TimeNumOffsetString) -> Vec<u8> {
        (*v.as_bytes_fixed_len()).into()
    }
}

#[cfg(feature = "alloc")]
impl From<TimeNumOffsetString> for String {
    #[inline]
    fn from(v: TimeNumOffsetString) -> String {
        let vec: Vec<u8> = (*v.as_bytes_fixed_len()).into();
        unsafe {
            // This is safe because a valid time-numoffset string is also an ASCII string.
            String::from_utf8_unchecked(vec)
        }
    }
}

impl From<&TimeNumOffsetStr> for TimeNumOffsetString {
    fn from(v: &TimeNumOffsetStr) -> Self {
        unsafe {
            // This is safe because the value is already validated.
            Self::new_unchecked(*v.as_bytes_fixed_len())
        }
    }
}

impl TryFrom<&[u8]> for TimeNumOffsetString {
    type Error = ValidationError;

    #[inline]
    fn try_from(v: &[u8]) -> Result<Self, Self::Error> {
        TimeNumOffsetStr::from_bytes(v).map(Into::into)
    }
}

impl TryFrom<&str> for TimeNumOffsetString {
    type Error = ValidationError;

    #[inline]
    fn try_from(v: &str) -> Result<Self, Self::Error> {
        TimeNumOffsetStr::from_str(v).map(Into::into)
    }
}

impl TryFrom<[u8; 6]> for TimeNumOffsetString {
    type Error = ValidationError;

    #[inline]
    fn try_from(v: [u8; 6]) -> Result<Self, Self::Error> {
        validate_bytes(&v)?;
        Ok(unsafe {
            // This is safe because the value is successfully validated.
            Self::new_unchecked(v)
        })
    }
}

impl fmt::Display for TimeNumOffsetString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_deref().fmt(f)
    }
}

impl ops::Deref for TimeNumOffsetString {
    type Target = TimeNumOffsetStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_deref()
    }
}

impl ops::DerefMut for TimeNumOffsetString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_deref_mut()
    }
}

impl str::FromStr for TimeNumOffsetString {
    type Err = ValidationError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl_cmp_symmetric!(TimeNumOffsetStr, TimeNumOffsetString, &TimeNumOffsetString);
impl_cmp_symmetric!(TimeNumOffsetStr, TimeNumOffsetString, TimeNumOffsetStr);
impl_cmp_symmetric!(TimeNumOffsetStr, TimeNumOffsetString, &TimeNumOffsetStr);
impl_cmp_symmetric!(str, TimeNumOffsetString, str);
impl_cmp_symmetric!(str, TimeNumOffsetString, &str);
impl_cmp_symmetric!(str, &TimeNumOffsetString, str);
impl_cmp_symmetric!([u8], TimeNumOffsetString, [u8]);
impl_cmp_symmetric!([u8], TimeNumOffsetString, &[u8]);
impl_cmp_symmetric!([u8], &TimeNumOffsetString, [u8]);

#[cfg(feature = "serde")]
impl Serialize for TimeNumOffsetString {
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

    /// Visitor for `&TimeNumOffsetStr`.
    struct StrVisitor;

    impl<'de> Visitor<'de> for StrVisitor {
        type Value = &'de TimeNumOffsetStr;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 time-numoffset time string")
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

    impl<'de> Deserialize<'de> for &'de TimeNumOffsetStr {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_any(StrVisitor)
        }
    }

    /// Visitor for `TimeNumOffsetString`.
    struct StringVisitor;

    impl<'de> Visitor<'de> for StringVisitor {
        type Value = TimeNumOffsetString;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 time-numoffset time string")
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

    impl<'de> Deserialize<'de> for TimeNumOffsetString {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_any(StringVisitor)
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
        assert!(s_validate(b"+00:00").is_ok());
        assert!(s_validate(b"+00:30").is_ok());
        assert!(s_validate(b"+00:59").is_ok());
        assert!(s_validate(b"+12:00").is_ok());
        assert!(s_validate(b"+12:30").is_ok());
        assert!(s_validate(b"+12:59").is_ok());
        assert!(s_validate(b"+23:00").is_ok());
        assert!(s_validate(b"+23:30").is_ok());
        assert!(s_validate(b"+23:59").is_ok());
        assert!(s_validate(b"-00:00").is_ok());
        assert!(s_validate(b"-00:30").is_ok());
        assert!(s_validate(b"-00:59").is_ok());
        assert!(s_validate(b"-12:00").is_ok());
        assert!(s_validate(b"-12:30").is_ok());
        assert!(s_validate(b"-12:59").is_ok());
        assert!(s_validate(b"-23:00").is_ok());
        assert!(s_validate(b"-23:30").is_ok());
        assert!(s_validate(b"-23:59").is_ok());

        assert!(s_validate(b"Z").is_err());
        assert!(s_validate(b"+24:00").is_err());
        assert!(s_validate(b"-24:00").is_err());
        assert!(s_validate(b"+23:60").is_err());
        assert!(s_validate(b"-23:60").is_err());
        assert!(s_validate(b"00:00").is_err());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_str() {
        let raw: &'static str = "-12:34";
        assert_tokens(
            &TimeNumOffsetStr::from_str(raw).unwrap(),
            &[Token::BorrowedStr(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_string() {
        let raw: &'static str = "-12:34";
        assert_tokens(
            &TimeNumOffsetString::try_from(raw).unwrap(),
            &[Token::Str(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes_slice() {
        let raw: &'static [u8; 6] = b"-12:34";
        assert_de_tokens(
            &TimeNumOffsetStr::from_bytes(raw).unwrap(),
            &[Token::BorrowedBytes(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes() {
        let raw: &'static [u8; 6] = b"-12:34";
        assert_de_tokens(
            &TimeNumOffsetString::try_from(&raw[..]).unwrap(),
            &[Token::Bytes(raw)],
        );
    }
}
