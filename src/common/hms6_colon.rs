//! Time string in `%H:%M:%S` (`hh:mm:ss`) format.
//!
//! This is also an RFC 3339 [`partial-time`] string without `secfrac` part.
//!
//! [`partial-time`]: https://tools.ietf.org/html/rfc3339#section-5.6

use core::{
    cmp::Ordering,
    convert::TryFrom,
    fmt,
    ops::{self, Range},
    str,
};

use crate::{parse::parse_digits2, str::write_digit2};

#[cfg(feature = "alloc")]
use alloc::{string::String, vec::Vec};

use crate::error::{ComponentKind, Error, ErrorKind};

/// Length of `hh:mm:ss` string.
const HMS_LEN: usize = 8;
/// Range of the hour in the string.
const HOUR_RANGE: Range<usize> = 0..2;
/// Range of the minute in the string.
const MINUTE_RANGE: Range<usize> = 3..5;
/// Range of the second in the string.
const SECOND_RANGE: Range<usize> = 6..8;
/// Maximum value of the hour.
const HOUR_MAX: u8 = 23;
/// Maximum value of the minute.
const MINUTE_MAX: u8 = 59;
/// Maximum value of the second.
///
/// Note that a leap second is always allowed.
const SECOND_MAX: u8 = 60;

/// Validates the given `%H:%M:%S` string.
///
/// In other words, this string can contain an RFC 3339 [`partial-time`] string without `secfrac` part.
///
/// This type allows leap seconds unconditionally, because leap seconds are
/// irregular and cannot predict, and date and timezone is also necessary to
/// check if a leap second really happened or will happen.
/// It is user's responsibility to validate a leap second really happened or
/// will happen, if the "second" component is 60.
///
/// [`partial-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
fn validate_bytes(s: &[u8]) -> Result<(), Error> {
    let s: &[u8; HMS_LEN] = match s.len().cmp(&HMS_LEN) {
        Ordering::Greater => return Err(ErrorKind::TooLong.into()),
        Ordering::Less => return Err(ErrorKind::TooShort.into()),
        Ordering::Equal => {
            TryFrom::try_from(s).expect("Should never fail because the length is equal")
        }
    };

    if (s[2] != b':') || (s[5] != b':') {
        return Err(ErrorKind::InvalidSeparator.into());
    }

    let hour_s: [u8; 2] = [s[0], s[1]];
    let minute_s: [u8; 2] = [s[3], s[4]];
    let second_s: [u8; 2] = [s[6], s[7]];

    if !hour_s.iter().all(u8::is_ascii_digit) {
        return Err(ErrorKind::InvalidComponentType(ComponentKind::Hour).into());
    }
    if !minute_s.iter().all(u8::is_ascii_digit) {
        return Err(ErrorKind::InvalidComponentType(ComponentKind::Minute).into());
    }
    if !second_s.iter().all(u8::is_ascii_digit) {
        return Err(ErrorKind::InvalidComponentType(ComponentKind::Second).into());
    }

    let hour = parse_digits2(hour_s);
    if hour > HOUR_MAX {
        return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Hour).into());
    }
    let minute = parse_digits2(minute_s);
    if minute > MINUTE_MAX {
        return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Minute).into());
    }
    let second = parse_digits2(second_s);
    // Leap second is always allowed for this type. See the documentation for the types.
    if second > SECOND_MAX {
        return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Minute).into());
    }

    Ok(())
}

/// String slice for a time in `%H:%M:%S` (`hh:mm:ss`) format, such as `01:23:45`.
///
/// This is also an RFC 3339 [`partial-time`] string without `secfrac` part.
///
/// [`partial-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
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
pub struct Hms6ColonStr([u8]);

impl Hms6ColonStr {
    /// Creates a `&Hms6ColonStr` from the given byte slice.
    ///
    /// This performs assertion in debug build, but not in release build.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_bytes_maybe_unchecked(v: &[u8]) -> &Self {
        debug_assert_ok!(validate_bytes(v));
        &*(v as *const [u8] as *const Self)
    }

    /// Creates a `&mut Hms6ColonStr` from the given mutable byte slice.
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

    /// Creates a `&mut Hms6ColonStr` from the given mutable string slice.
    ///
    /// This performs assertion in debug build, but not in release build.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_maybe_unchecked_mut(s: &mut str) -> &mut Self {
        // This is safe because `Hms6ColonStr` ensures that the underlying bytes
        // are ASCII string after modification.
        Self::from_bytes_maybe_unchecked_mut(s.as_bytes_mut())
    }

    /// Creates a new `&Hms6ColonStr` from a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    /// assert_eq!(time.as_str(), "12:34:56");
    ///
    /// assert!(Hms6ColonStr::from_str("00:00:00").is_ok());
    /// assert!(Hms6ColonStr::from_str("23:59:59").is_ok());
    /// assert!(Hms6ColonStr::from_str("23:59:60").is_ok(), "Leap second is always allowed");
    ///
    /// assert!(Hms6ColonStr::from_str("24:00:00").is_err(), "Invalid hour");
    /// assert!(Hms6ColonStr::from_str("00:60:00").is_err(), "Invalid minute");
    /// assert!(Hms6ColonStr::from_str("00:00:61").is_err(), "Invalid second");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    // `FromStr` trait cannot be implemented for a slice.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut Hms6ColonStr` from a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let mut buf = "12:34:56".to_owned();
    /// let time = Hms6ColonStr::from_mut_str(&mut buf)?;
    /// assert_eq!(time.as_str(), "12:34:56");
    ///
    /// time.set_hour(0)?;
    /// assert_eq!(time.as_str(), "00:34:56");
    ///
    /// assert_eq!(buf, "00:34:56");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_mut_str(s: &mut str) -> Result<&mut Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&Hms6ColonStr` from a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_bytes(b"12:34:56")?;
    /// assert_eq!(time.as_str(), "12:34:56");
    ///
    /// assert!(Hms6ColonStr::from_bytes(b"00:00:00").is_ok());
    /// assert!(Hms6ColonStr::from_bytes(b"23:59:59").is_ok());
    /// assert!(Hms6ColonStr::from_bytes(b"23:59:60").is_ok(), "Leap second is always allowed");
    ///
    /// assert!(Hms6ColonStr::from_bytes(b"24:00:00").is_err(), "Invalid hour");
    /// assert!(Hms6ColonStr::from_bytes(b"00:60:00").is_err(), "Invalid minute");
    /// assert!(Hms6ColonStr::from_bytes(b"00:00:61").is_err(), "Invalid second");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_bytes(s: &[u8]) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut Hms6ColonStr` from a mutable byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let mut buf: [u8; 8] = *b"12:34:56";
    /// let time = Hms6ColonStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "12:34:56");
    ///
    /// time.set_hour(0)?;
    /// assert_eq!(time.as_str(), "00:34:56");
    ///
    /// assert_eq!(&buf[..], b"00:34:56");
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
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    ///
    /// assert_eq!(time.as_str(), "12:34:56");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        unsafe {
            // This is safe because the `Hms6ColonStr` ensures that the
            // underlying bytes are ASCII string.
            debug_assert_safe_version_ok!(str::from_utf8(&self.0));
            str::from_utf8_unchecked(&self.0)
        }
    }

    /// Returns a byte slice.
    ///
    /// If you want to use indexed access, prefer [`as_bytes_fixed_len`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_bytes(b"12:34:56")?;
    ///
    /// assert_eq!(time.as_bytes(), b"12:34:56");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    ///
    /// [`as_bytes_fixed_len`]: #method.as_bytes_fixed_len
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Returns a fixed length byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    ///
    /// let fixed_len: &[u8; 8] = time.as_bytes_fixed_len();
    /// assert_eq!(fixed_len, b"12:34:56");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_bytes_fixed_len(&self) -> &[u8; 8] {
        debug_assert_eq!(self.len(), HMS_LEN, "Hms6ColonStr must always be 8 bytes");

        debug_assert_safe_version_ok!(<&[u8; 8]>::try_from(&self.0[..HMS_LEN]));
        let ptr = self.0.as_ptr() as *const [u8; HMS_LEN];
        // This must be always safe because the length is already checked.
        unsafe { &*ptr }
    }

    /// Returns the hour as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    ///
    /// assert_eq!(time.hour_str(), "12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn hour_str(&self) -> &str {
        unsafe {
            // This is safe because the string is ASCII string and `HOUR_RANGE`
            // is always inside the string.
            debug_assert_safe_version_ok!(str::from_utf8(&self.0[HOUR_RANGE]));
            str::from_utf8_unchecked(self.0.get_unchecked(HOUR_RANGE))
        }
    }

    /// Returns the hour as a fixed length byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    ///
    /// let hour_fixed_len: &[u8; 2] = time.hour_bytes_fixed_len();
    /// assert_eq!(hour_fixed_len, b"12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn hour_bytes_fixed_len(&self) -> &[u8; 2] {
        unsafe {
            // This is safe because `HOUR_RANGE` fits inside the string.
            debug_assert_safe_version_ok!(<&[u8; 2]>::try_from(&self.0[HOUR_RANGE]));
            let ptr = self.0.as_ptr().add(HOUR_RANGE.start) as *const [u8; 2];
            &*ptr
        }
    }

    /// Returns the hour as a fixed length mutable byte slice.
    ///
    /// # Safety
    ///
    /// The returned slice should have only ASCII digits.
    /// If non-ASCII digits are stored, it may lead to undefined behavior.
    #[inline]
    #[must_use]
    unsafe fn hour_bytes_mut_fixed_len(&mut self) -> &mut [u8; 2] {
        // This is safe because `HOUR_RANGE` fits inside the string.
        debug_assert_safe_version_ok!(<&mut [u8; 2]>::try_from(&mut self.0[HOUR_RANGE]));
        let ptr = self.0.as_mut_ptr().add(HOUR_RANGE.start) as *mut [u8; 2];
        &mut *ptr
    }

    /// Returns the hour as an integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    ///
    /// assert_eq!(time.hour(), 12);
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn hour(&self) -> u8 {
        parse_digits2(*self.hour_bytes_fixed_len())
    }

    /// Returns the minute as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    ///
    /// assert_eq!(time.minute_str(), "34");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn minute_str(&self) -> &str {
        unsafe {
            // This is safe because the string is ASCII string and `MINUTE_RANGE`
            // is always inside the string.
            debug_assert_safe_version_ok!(str::from_utf8(&self.0[MINUTE_RANGE]));
            str::from_utf8_unchecked(self.0.get_unchecked(MINUTE_RANGE))
        }
    }

    /// Returns the minute as a fixed length byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    ///
    /// let minute_fixed_len: &[u8; 2] = time.minute_bytes_fixed_len();
    /// assert_eq!(minute_fixed_len, b"34");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn minute_bytes_fixed_len(&self) -> &[u8; 2] {
        unsafe {
            // This is safe because `MINUTE_RANGE` fits inside the string.
            debug_assert_safe_version_ok!(<&[u8; 2]>::try_from(&self.0[MINUTE_RANGE]));
            let ptr = self.0.as_ptr().add(MINUTE_RANGE.start) as *const [u8; 2];
            &*ptr
        }
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
        // This is safe because `MINUTE_RANGE` fits inside the string.
        debug_assert_safe_version_ok!(<&mut [u8; 2]>::try_from(&mut self.0[MINUTE_RANGE]));
        let ptr = self.0.as_mut_ptr().add(MINUTE_RANGE.start) as *mut [u8; 2];
        &mut *ptr
    }

    /// Returns the minute as an integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    ///
    /// assert_eq!(time.minute(), 34);
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn minute(&self) -> u8 {
        parse_digits2(*self.minute_bytes_fixed_len())
    }

    /// Returns the second as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    ///
    /// assert_eq!(time.second_str(), "56");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn second_str(&self) -> &str {
        unsafe {
            // This is safe because the string is ASCII string and `SECOND_RANGE`
            // is always inside the string.
            debug_assert_safe_version_ok!(str::from_utf8(&self.0[SECOND_RANGE]));
            str::from_utf8_unchecked(self.0.get_unchecked(SECOND_RANGE))
        }
    }

    /// Returns the second as a fixed length byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    ///
    /// let second_fixed_len: &[u8; 2] = time.second_bytes_fixed_len();
    /// assert_eq!(second_fixed_len, b"56");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn second_bytes_fixed_len(&self) -> &[u8; 2] {
        unsafe {
            // This is safe because `SECOND_RANGE` fits inside the string.
            debug_assert_safe_version_ok!(<&[u8; 2]>::try_from(&self.0[SECOND_RANGE]));
            let ptr = self.0.as_ptr().add(SECOND_RANGE.start) as *const [u8; 2];
            &*ptr
        }
    }

    /// Returns the second as a fixed length mutable byte slice.
    ///
    /// # Safety
    ///
    /// The returned slice should have only ASCII digits.
    /// If non-ASCII digits are stored, it may lead to undefined behavior.
    #[inline]
    #[must_use]
    unsafe fn second_bytes_mut_fixed_len(&mut self) -> &mut [u8; 2] {
        // This is safe because `SECOND_RANGE` fits inside the string.
        debug_assert_safe_version_ok!(<&mut [u8; 2]>::try_from(&mut self.0[SECOND_RANGE]));
        let ptr = self.0.as_mut_ptr().add(SECOND_RANGE.start) as *mut [u8; 2];
        &mut *ptr
    }

    /// Returns the second as an integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let time = Hms6ColonStr::from_str("12:34:56")?;
    ///
    /// assert_eq!(time.second(), 56);
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn second(&self) -> u8 {
        parse_digits2(*self.second_bytes_fixed_len())
    }

    /// Sets the given hour value to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the time after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let mut buf: [u8; 8] = *b"12:34:56";
    /// let time = Hms6ColonStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "12:34:56");
    ///
    /// time.set_hour(0)?;
    /// assert_eq!(time.as_str(), "00:34:56");
    ///
    /// assert!(time.set_hour(24).is_err(), "24:34:56 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_hour(&mut self, hour: u8) -> Result<(), Error> {
        if hour > HOUR_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Hour).into());
        }
        unsafe {
            // This is safe because `write_digit2()` fills the slice with ASCII digits.
            write_digit2(self.hour_bytes_mut_fixed_len(), hour);
        }
        debug_assert_ok!(validate_bytes(&self.0));

        Ok(())
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
    /// # use datetime_string::common::Hms6ColonStr;
    /// let mut buf: [u8; 8] = *b"12:34:56";
    /// let time = Hms6ColonStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "12:34:56");
    ///
    /// time.set_minute(0)?;
    /// assert_eq!(time.as_str(), "12:00:56");
    ///
    /// assert!(time.set_minute(60).is_err(), "24:60:56 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_minute(&mut self, minute: u8) -> Result<(), Error> {
        if minute > MINUTE_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Minute).into());
        }
        unsafe {
            // This is safe because `write_digit2()` fills the slice with ASCII digits.
            write_digit2(self.minute_bytes_mut_fixed_len(), minute);
        }
        debug_assert_ok!(validate_bytes(&self.0));

        Ok(())
    }

    /// Sets the given second value to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the time after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let mut buf: [u8; 8] = *b"12:34:56";
    /// let time = Hms6ColonStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "12:34:56");
    ///
    /// time.set_second(0)?;
    /// assert_eq!(time.as_str(), "12:34:00");
    ///
    /// assert!(time.set_second(61).is_err(), "24:34:61 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_second(&mut self, second: u8) -> Result<(), Error> {
        if second > SECOND_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Second).into());
        }
        unsafe {
            // This is safe because `write_digit2()` fills the slice with ASCII digits.
            write_digit2(self.second_bytes_mut_fixed_len(), second);
        }
        debug_assert_ok!(validate_bytes(&self.0));

        Ok(())
    }

    /// Sets the given hour and minute values to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the time after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let mut buf: [u8; 8] = *b"12:34:56";
    /// let time = Hms6ColonStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "12:34:56");
    ///
    /// time.set_hour_minute(21, 10)?;
    /// assert_eq!(time.as_str(), "21:10:56");
    ///
    /// assert!(time.set_hour_minute(23, 60).is_err(), "23:60:56 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_hour_minute(&mut self, hour: u8, minute: u8) -> Result<(), Error> {
        if hour > HOUR_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Hour).into());
        }
        if minute > MINUTE_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Minute).into());
        }
        unsafe {
            // These are safe because `write_digit2()` fills the slice with ASCII digits.
            write_digit2(self.hour_bytes_mut_fixed_len(), hour);
            write_digit2(self.minute_bytes_mut_fixed_len(), minute);
        }
        debug_assert_ok!(validate_bytes(&self.0));

        Ok(())
    }

    /// Sets the given minute and second values to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the time after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let mut buf: [u8; 8] = *b"12:34:56";
    /// let time = Hms6ColonStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "12:34:56");
    ///
    /// time.set_minute_second(54, 32)?;
    /// assert_eq!(time.as_str(), "12:54:32");
    ///
    /// assert!(time.set_minute_second(60, 59).is_err(), "12:60:59 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_minute_second(&mut self, minute: u8, second: u8) -> Result<(), Error> {
        if minute > MINUTE_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Minute).into());
        }
        if second > SECOND_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Second).into());
        }
        unsafe {
            // These are safe because `write_digit2()` fills the slice with ASCII digits.
            write_digit2(self.minute_bytes_mut_fixed_len(), minute);
            write_digit2(self.second_bytes_mut_fixed_len(), second);
        }
        debug_assert_ok!(validate_bytes(&self.0));

        Ok(())
    }

    /// Sets the given hour, minute, and second values to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the time after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonStr;
    /// let mut buf: [u8; 8] = *b"12:34:56";
    /// let time = Hms6ColonStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "12:34:56");
    ///
    /// time.set_time(23, 12, 1)?;
    /// assert_eq!(time.as_str(), "23:12:01");
    ///
    /// assert!(time.set_time(24, 0, 0).is_err(), "24:00:00 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_time(&mut self, hour: u8, minute: u8, second: u8) -> Result<(), Error> {
        if hour > HOUR_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Hour).into());
        }
        if minute > MINUTE_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Minute).into());
        }
        if second > SECOND_MAX {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Second).into());
        }
        unsafe {
            // These are safe because `write_digit2()` fills the slice with ASCII digits.
            write_digit2(self.hour_bytes_mut_fixed_len(), hour);
            write_digit2(self.minute_bytes_mut_fixed_len(), minute);
            write_digit2(self.second_bytes_mut_fixed_len(), second);
        }
        debug_assert_ok!(validate_bytes(&self.0));

        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl alloc::borrow::ToOwned for Hms6ColonStr {
    type Owned = Hms6ColonString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for Hms6ColonStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for Hms6ColonStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<Hms6ColonStr> for Hms6ColonStr {
    #[inline]
    fn as_ref(&self) -> &Hms6ColonStr {
        self
    }
}

impl AsMut<Hms6ColonStr> for Hms6ColonStr {
    #[inline]
    fn as_mut(&mut self) -> &mut Hms6ColonStr {
        self
    }
}

impl<'a> From<&'a Hms6ColonStr> for &'a str {
    #[inline]
    fn from(v: &'a Hms6ColonStr) -> Self {
        v.as_str()
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a Hms6ColonStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because the value is successfully validated.
            Hms6ColonStr::from_bytes_maybe_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut Hms6ColonStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because the value is successfully validated.
            Hms6ColonStr::from_bytes_maybe_unchecked_mut(v)
        })
    }
}

impl<'a> TryFrom<&'a str> for &'a Hms6ColonStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a str) -> Result<Self, Self::Error> {
        TryFrom::try_from(v.as_bytes())
    }
}

impl<'a> TryFrom<&'a mut str> for &'a mut Hms6ColonStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because the value is successfully validated, and
            // `Hms6ColonStr` ensures the value after modification is an ASCII string.
            Hms6ColonStr::from_str_maybe_unchecked_mut(v)
        })
    }
}

impl fmt::Display for Hms6ColonStr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl ops::Deref for Hms6ColonStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl_cmp_symmetric!(str, Hms6ColonStr, &Hms6ColonStr);
impl_cmp_symmetric!([u8], Hms6ColonStr, [u8]);
impl_cmp_symmetric!([u8], Hms6ColonStr, &[u8]);
impl_cmp_symmetric!([u8], &Hms6ColonStr, [u8]);
impl_cmp_symmetric!(str, Hms6ColonStr, str);
impl_cmp_symmetric!(str, Hms6ColonStr, &str);
impl_cmp_symmetric!(str, &Hms6ColonStr, str);

#[cfg(feature = "serde")]
impl serde::Serialize for Hms6ColonStr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

/// Owned string for a time in `%H:%M:%S` (`hh:mm:ss`) format, such as `01:23:45`.
///
/// This is also an RFC 3339 [`partial-time`] string without `secfrac` part.
///
/// This is a fixed length string, and implements [`Copy`] trait.
///
/// To create a value of this type, use [`str::parse`] method or
/// [`std::convert::TryFrom`] trait, or convert from `&Hms6ColonStr`.
///
/// # Examples
///
/// ```
/// # use datetime_string::common::Hms6ColonString;
/// use datetime_string::common::Hms6ColonStr;
/// use std::convert::TryFrom;
///
/// let try_from = Hms6ColonString::try_from("12:34:56")?;
///
/// let parse = "12:34:56".parse::<Hms6ColonString>()?;
/// let parse2: Hms6ColonString = "12:34:56".parse()?;
///
/// let to_owned = Hms6ColonStr::from_str("12:34:56")?.to_owned();
/// let into: Hms6ColonString = Hms6ColonStr::from_str("12:34:56")?.into();
/// # Ok::<_, datetime_string::Error>(())
/// ```
///
/// [`partial-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
// Note that `derive(Serialize)` cannot used here, because it encodes this as
// `[u8; 8]` rather than as a string.
//
// Comparisons implemented for the type are consistent (at least it is intended to be so).
// See <https://github.com/rust-lang/rust-clippy/issues/2025>.
// Note that `clippy::derive_ord_xor_partial_ord` would be introduced since Rust 1.47.0.
#[allow(clippy::derive_hash_xor_eq)]
#[allow(clippy::unknown_clippy_lints, clippy::derive_ord_xor_partial_ord)]
pub struct Hms6ColonString([u8; HMS_LEN]);

impl Hms6ColonString {
    /// Creates a `Hms6ColonString` from the given bytes.
    ///
    /// # Safety
    ///
    /// `validate_bytes(&s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn new_maybe_unchecked(s: [u8; 8]) -> Self {
        debug_assert_ok!(validate_bytes(&s));
        Self(s)
    }

    /// Returns a `&Hms6ColonStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonString;
    /// use datetime_string::common::Hms6ColonStr;
    /// let time = "12:34:56".parse::<Hms6ColonString>()?;
    ///
    /// // Usually you don't need to call `as_deref()` explicitly, because
    /// // `Deref<Target = Hms6ColonStr>` trait is implemented.
    /// let _: &Hms6ColonStr = time.as_deref();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref(&self) -> &Hms6ColonStr {
        unsafe {
            // This is safe because the string is already validated.
            debug_assert_safe_version_ok!(Hms6ColonStr::from_bytes(&self.0));
            Hms6ColonStr::from_bytes_maybe_unchecked(&self.0)
        }
    }

    /// Returns a `&mut Hms6ColonStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Hms6ColonString;
    /// use datetime_string::common::Hms6ColonStr;
    /// let mut time = "12:34:56".parse::<Hms6ColonString>()?;
    ///
    /// // Usually you don't need to call `as_deref_mut()` explicitly, because
    /// // `DerefMut` trait is implemented.
    /// let _: &mut Hms6ColonStr = time.as_deref_mut();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref_mut(&mut self) -> &mut Hms6ColonStr {
        unsafe {
            // This is safe because the string is already validated.
            debug_assert_ok!(Hms6ColonStr::from_bytes(&self.0));
            Hms6ColonStr::from_bytes_maybe_unchecked_mut(&mut self.0)
        }
    }
}

impl core::borrow::Borrow<Hms6ColonStr> for Hms6ColonString {
    #[inline]
    fn borrow(&self) -> &Hms6ColonStr {
        self.as_deref()
    }
}

impl core::borrow::BorrowMut<Hms6ColonStr> for Hms6ColonString {
    #[inline]
    fn borrow_mut(&mut self) -> &mut Hms6ColonStr {
        self.as_deref_mut()
    }
}

impl AsRef<[u8]> for Hms6ColonString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for Hms6ColonString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<Hms6ColonStr> for Hms6ColonString {
    #[inline]
    fn as_ref(&self) -> &Hms6ColonStr {
        self
    }
}

impl AsMut<Hms6ColonStr> for Hms6ColonString {
    #[inline]
    fn as_mut(&mut self) -> &mut Hms6ColonStr {
        self
    }
}

#[cfg(feature = "alloc")]
impl From<Hms6ColonString> for Vec<u8> {
    #[inline]
    fn from(v: Hms6ColonString) -> Vec<u8> {
        (*v.as_bytes_fixed_len()).into()
    }
}

#[cfg(feature = "alloc")]
impl From<Hms6ColonString> for String {
    #[inline]
    fn from(v: Hms6ColonString) -> String {
        let vec: Vec<u8> = (*v.as_bytes_fixed_len()).into();
        unsafe {
            // This is safe because a valid `hh:mm:ss` string is also an ASCII string.
            String::from_utf8_unchecked(vec)
        }
    }
}

impl From<&Hms6ColonStr> for Hms6ColonString {
    fn from(v: &Hms6ColonStr) -> Self {
        unsafe {
            // This is safe because the value is already validated.
            Self::new_maybe_unchecked(*v.as_bytes_fixed_len())
        }
    }
}

impl TryFrom<&[u8]> for Hms6ColonString {
    type Error = Error;

    #[inline]
    fn try_from(v: &[u8]) -> Result<Self, Self::Error> {
        Hms6ColonStr::from_bytes(v).map(Into::into)
    }
}

impl TryFrom<&str> for Hms6ColonString {
    type Error = Error;

    #[inline]
    fn try_from(v: &str) -> Result<Self, Self::Error> {
        Hms6ColonStr::from_str(v).map(Into::into)
    }
}

impl TryFrom<[u8; 8]> for Hms6ColonString {
    type Error = Error;

    #[inline]
    fn try_from(v: [u8; 8]) -> Result<Self, Self::Error> {
        validate_bytes(&v)?;
        Ok(unsafe {
            // This is safe because the value is successfully validated.
            Self::new_maybe_unchecked(v)
        })
    }
}

impl fmt::Display for Hms6ColonString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_deref().fmt(f)
    }
}

impl ops::Deref for Hms6ColonString {
    type Target = Hms6ColonStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_deref()
    }
}

impl ops::DerefMut for Hms6ColonString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_deref_mut()
    }
}

impl str::FromStr for Hms6ColonString {
    type Err = Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl_cmp_symmetric!(Hms6ColonStr, Hms6ColonString, &Hms6ColonString);
impl_cmp_symmetric!(Hms6ColonStr, Hms6ColonString, Hms6ColonStr);
impl_cmp_symmetric!(Hms6ColonStr, Hms6ColonString, &Hms6ColonStr);
impl_cmp_symmetric!(str, Hms6ColonString, str);
impl_cmp_symmetric!(str, Hms6ColonString, &str);
impl_cmp_symmetric!(str, &Hms6ColonString, str);
impl_cmp_symmetric!([u8], Hms6ColonString, [u8]);
impl_cmp_symmetric!([u8], Hms6ColonString, &[u8]);
impl_cmp_symmetric!([u8], &Hms6ColonString, [u8]);

#[cfg(feature = "serde")]
impl serde::Serialize for Hms6ColonString {
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

    /// Visitor for `&Hms6ColonStr`.
    struct StrVisitor;

    impl<'de> Visitor<'de> for StrVisitor {
        type Value = &'de Hms6ColonStr;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("hh:mm:ss time string")
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

    impl<'de> Deserialize<'de> for &'de Hms6ColonStr {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_any(StrVisitor)
        }
    }

    /// Visitor for `Hms6ColonString`.
    struct StringVisitor;

    impl<'de> Visitor<'de> for StringVisitor {
        type Value = Hms6ColonString;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("hh:mm:ss time string")
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

    impl<'de> Deserialize<'de> for Hms6ColonString {
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
        assert!(s_validate(b"00:00:00").is_ok());
        assert!(s_validate(b"00:00:30").is_ok());
        assert!(s_validate(b"00:00:59").is_ok());
        assert!(s_validate(b"00:00:60").is_ok());
        assert!(s_validate(b"00:30:00").is_ok());
        assert!(s_validate(b"00:59:00").is_ok());
        assert!(s_validate(b"12:00:00").is_ok());
        assert!(s_validate(b"23:00:00").is_ok());

        assert!(s_validate(b"00:00:61").is_err());
        assert!(s_validate(b"00:00:99").is_err());
        assert!(s_validate(b"00:60:00").is_err());
        assert!(s_validate(b"00:99:00").is_err());
        assert!(s_validate(b"24:00:00").is_err());
        assert!(s_validate(b"99:00:00").is_err());

        assert!(s_validate(b"+0:00:00").is_err());
        assert!(s_validate(b"-0:00:00").is_err());
        assert!(s_validate(b"00:+0:00").is_err());
        assert!(s_validate(b"00:-0:00").is_err());
        assert!(s_validate(b"00:00:+0").is_err());
        assert!(s_validate(b"00:00:-0").is_err());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_str() {
        let raw: &'static str = "12:34:56";
        assert_tokens(
            &Hms6ColonStr::from_str(raw).unwrap(),
            &[Token::BorrowedStr(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_string() {
        let raw: &'static str = "12:34:56";
        assert_tokens(&Hms6ColonString::try_from(raw).unwrap(), &[Token::Str(raw)]);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes_slice() {
        let raw: &'static [u8; 8] = b"12:34:56";
        assert_de_tokens(
            &Hms6ColonStr::from_bytes(raw).unwrap(),
            &[Token::BorrowedBytes(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes() {
        let raw: &'static [u8; 8] = b"12:34:56";
        assert_de_tokens(
            &Hms6ColonString::try_from(&raw[..]).unwrap(),
            &[Token::Bytes(raw)],
        );
    }
}
