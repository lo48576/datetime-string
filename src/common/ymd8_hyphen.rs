//! Date string in `%Y-%m-%d` (`YYYY-MM-DD`) format.
//!
//! This is also an RFC 3339 [`full-date`] string.
//!
//! [`full-date`]: https://tools.ietf.org/html/rfc3339#section-5.6

use core::{
    cmp::Ordering,
    convert::TryFrom,
    fmt,
    ops::{self, Range},
    str,
};

use crate::{
    datetime::{validate_ym0d, validate_ym1d},
    parse::{parse_digits2, parse_digits4},
    str::{write_digit2, write_digit4},
};

#[cfg(feature = "alloc")]
use alloc::{string::String, vec::Vec};

use crate::error::{ComponentKind, Error, ErrorKind};

/// Length of RFC 3339 `full-date` string (i.e. length of `YYYY-MM-DD`).
const FULL_DATE_LEN: usize = 10;
/// Range of the year in the string.
const YEAR_RANGE: Range<usize> = 0..4;
/// Range of the month in the string.
const MONTH_RANGE: Range<usize> = 5..7;
/// Range of the day of month in the string.
const MDAY_RANGE: Range<usize> = 8..10;

/// Validates the given string as an RFC 3339 [`full-date`] string.
///
/// [`full-date`]: https://tools.ietf.org/html/rfc3339#section-5.6
fn validate_bytes(s: &[u8]) -> Result<(), Error> {
    let s: &[u8; FULL_DATE_LEN] = match s.len().cmp(&FULL_DATE_LEN) {
        Ordering::Greater => return Err(ErrorKind::TooLong.into()),
        Ordering::Less => return Err(ErrorKind::TooShort.into()),
        Ordering::Equal => {
            TryFrom::try_from(s).expect("Should never fail because the length is equal")
        }
    };

    if (s[4] != b'-') || (s[7] != b'-') {
        return Err(ErrorKind::InvalidSeparator.into());
    }

    let year_s: [u8; 4] = [s[0], s[1], s[2], s[3]];
    let month_s: [u8; 2] = [s[5], s[6]];
    let mday_s: [u8; 2] = [s[8], s[9]];

    if !year_s.iter().all(u8::is_ascii_digit) {
        return Err(ErrorKind::InvalidComponentType(ComponentKind::Year).into());
    }
    if !month_s.iter().all(u8::is_ascii_digit) {
        return Err(ErrorKind::InvalidComponentType(ComponentKind::Month).into());
    }
    if !mday_s.iter().all(u8::is_ascii_digit) {
        return Err(ErrorKind::InvalidComponentType(ComponentKind::Mday).into());
    }

    let month1 = parse_digits2(month_s);
    if (month1 < 1) || (month1 > 12) {
        return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Month).into());
    }
    let mday = parse_digits2(mday_s);
    if mday < 1 {
        return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Mday).into());
    }
    let year = parse_digits4(year_s);

    validate_ym1d(year, month1, mday).map_err(Into::into)
}

/// String slice for a date in `YYYY-MM-DD` format, such as `2001-12-31`.
///
/// This is also an RFC 3339 [`full-date`] string.
///
/// [`full-date`]: https://tools.ietf.org/html/rfc3339#section-5.6
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
pub struct Ymd8HyphenStr([u8]);

impl Ymd8HyphenStr {
    /// Creates a `&Ymd8HyphenStr` from the given byte slice.
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

    /// Creates a `&mut Ymd8HyphenStr` from the given mutable byte slice.
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

    /// Creates a `&mut Ymd8HyphenStr` from the given mutable string slice.
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

    /// Creates a new `&Ymd8HyphenStr` from a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    /// assert_eq!(date.as_str(), "2001-12-31");
    ///
    /// assert!(Ymd8HyphenStr::from_str("0000-01-01").is_ok());
    /// assert!(Ymd8HyphenStr::from_str("9999-12-31").is_ok());
    ///
    /// assert!(Ymd8HyphenStr::from_str("2004-02-29").is_ok(), "2004 is a leap year");
    /// assert!(Ymd8HyphenStr::from_str("2100-02-29").is_err(), "2100 is NOT a leap year");
    /// assert!(Ymd8HyphenStr::from_str("2000-02-29").is_ok(), "2000 is a leap year");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    // `FromStr` trait cannot be implemented for a slice.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut Ymd8HyphenStr` from a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let mut buf = "2001-12-31".to_owned();
    /// let date = Ymd8HyphenStr::from_mut_str(&mut buf)?;
    /// assert_eq!(date.as_str(), "2001-12-31");
    ///
    /// date.set_year(1999)?;
    /// assert_eq!(date.as_str(), "1999-12-31");
    ///
    /// assert_eq!(buf, "1999-12-31");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_mut_str(s: &mut str) -> Result<&mut Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&Ymd8HyphenStr` from a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_bytes(b"2001-12-31")?;
    /// assert_eq!(date.as_str(), "2001-12-31");
    ///
    /// assert!(Ymd8HyphenStr::from_bytes(b"0000-01-01").is_ok());
    /// assert!(Ymd8HyphenStr::from_bytes(b"9999-12-31").is_ok());
    ///
    /// assert!(Ymd8HyphenStr::from_bytes(b"2004-02-29").is_ok(), "2004 is a leap year");
    /// assert!(Ymd8HyphenStr::from_bytes(b"2100-02-29").is_err(), "2100 is NOT a leap year");
    /// assert!(Ymd8HyphenStr::from_bytes(b"2000-02-29").is_ok(), "2000 is a leap year");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_bytes(s: &[u8]) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut Ymd8HyphenStr` from a mutable byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let mut buf: [u8; 10] = *b"2001-12-31";
    /// let date = Ymd8HyphenStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(date.as_str(), "2001-12-31");
    ///
    /// date.set_year(1999)?;
    /// assert_eq!(date.as_str(), "1999-12-31");
    ///
    /// assert_eq!(&buf[..], b"1999-12-31");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_bytes_mut(s: &mut [u8]) -> Result<&mut Self, Error> {
        TryFrom::try_from(s)
    }

    /// Assigns the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let mut buf: [u8; 10] = *b"1999-12-31";
    /// let date = Ymd8HyphenStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(date.as_str(), "1999-12-31");
    ///
    /// let newdate = Ymd8HyphenStr::from_str("2000-01-01")?;
    ///
    /// date.assign(newdate);
    /// assert_eq!(date.as_str(), "2000-01-01");
    /// assert_eq!(buf, *b"2000-01-01");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn assign(&mut self, v: &Self) {
        debug_assert_eq!(self.0.len(), v.0.len());
        self.0.copy_from_slice(&v.0);
    }

    /// Returns a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// assert_eq!(date.as_str(), "2001-12-31");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        unsafe {
            // This is safe because the `Ymd8HyphenStr` ensures that the
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
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// assert_eq!(date.as_bytes(), b"2001-12-31");
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
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// let fixed_len: &[u8; 10] = date.as_bytes_fixed_len();
    /// assert_eq!(fixed_len, b"2001-12-31");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_bytes_fixed_len(&self) -> &[u8; 10] {
        debug_assert_eq!(
            self.len(),
            FULL_DATE_LEN,
            "Ymd8HyphenStr must always be 10 bytes"
        );

        debug_assert_safe_version_ok!(<&[u8; FULL_DATE_LEN]>::try_from(&self.0));
        let ptr = self.0.as_ptr() as *const [u8; FULL_DATE_LEN];
        // This must be always safe because the length is already checked.
        unsafe { &*ptr }
    }

    /// Returns the year as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// assert_eq!(date.year_str(), "2001");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn year_str(&self) -> &str {
        unsafe {
            // This is safe because the string is ASCII string and `YEAR_RANGE`
            // is always inside the string.
            debug_assert_safe_version_ok!(str::from_utf8(&self.0[YEAR_RANGE]));
            str::from_utf8_unchecked(self.0.get_unchecked(YEAR_RANGE))
        }
    }

    /// Returns the year as a fixed length byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// let year_fixed_len: &[u8; 4] = date.year_bytes_fixed_len();
    /// assert_eq!(year_fixed_len, b"2001");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn year_bytes_fixed_len(&self) -> &[u8; 4] {
        unsafe {
            // This is safe because `YEAR_RANGE` fits inside the string.
            debug_assert_safe_version_ok!(<&[u8; 4]>::try_from(&self.0[YEAR_RANGE]));
            let ptr = self.0.as_ptr().add(YEAR_RANGE.start) as *const [u8; 4];
            &*ptr
        }
    }

    /// Returns the year as a fixed length mutable byte slice.
    ///
    /// # Safety
    ///
    /// The returned slice should have only ASCII digits.
    /// If non-ASCII digits are stored, it may lead to undefined behavior.
    #[inline]
    #[must_use]
    unsafe fn year_bytes_mut_fixed_len(&mut self) -> &mut [u8; 4] {
        // This is safe because `YEAR_RANGE` fits inside the string.
        debug_assert_ok!(<&[u8; 4]>::try_from(&self.0[YEAR_RANGE]));
        let ptr = self.0.as_mut_ptr().add(YEAR_RANGE.start) as *mut [u8; 4];
        &mut *ptr
    }

    /// Returns the year as an integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// assert_eq!(date.year(), 2001);
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn year(&self) -> u16 {
        parse_digits4(*self.year_bytes_fixed_len())
    }

    /// Returns the month as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// assert_eq!(date.month_str(), "12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn month_str(&self) -> &str {
        unsafe {
            // This is safe because the string is ASCII string and `MONTH_RANGE`
            // is always inside the string.
            debug_assert_safe_version_ok!(str::from_utf8(&self.0[MONTH_RANGE]));
            str::from_utf8_unchecked(self.0.get_unchecked(MONTH_RANGE))
        }
    }

    /// Returns the month as a fixed length byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// let month_fixed_len: &[u8; 2] = date.month_bytes_fixed_len();
    /// assert_eq!(month_fixed_len, b"12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn month_bytes_fixed_len(&self) -> &[u8; 2] {
        unsafe {
            // This is safe because `MONTH_RANGE` fits inside the string.
            debug_assert_safe_version_ok!(<&[u8; 2]>::try_from(&self.0[MONTH_RANGE]));
            let ptr = self.0.as_ptr().add(MONTH_RANGE.start) as *const [u8; 2];
            &*ptr
        }
    }

    /// Returns the month as a fixed length mutable byte slice.
    ///
    /// # Safety
    ///
    /// The returned slice should have only ASCII digits.
    /// If non-ASCII digits are stored, it may lead to undefined behavior.
    #[inline]
    #[must_use]
    unsafe fn month_bytes_mut_fixed_len(&mut self) -> &mut [u8; 2] {
        // This is safe because `MONTH_RANGE` fits inside the string.
        debug_assert_ok!(<&[u8; 2]>::try_from(&self.0[MONTH_RANGE]));
        let ptr = self.0.as_mut_ptr().add(MONTH_RANGE.start) as *mut [u8; 2];
        &mut *ptr
    }

    /// Returns the 1-based month as an integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// assert_eq!(date.month1(), 12);
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn month1(&self) -> u8 {
        parse_digits2(*self.month_bytes_fixed_len())
    }

    /// Returns the 0-based month as an integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// assert_eq!(date.month0(), 11);
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn month0(&self) -> u8 {
        parse_digits2(*self.month_bytes_fixed_len()).wrapping_sub(1)
    }

    /// Returns the day of month as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// assert_eq!(date.mday_str(), "31");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn mday_str(&self) -> &str {
        unsafe {
            // This is safe because the string is ASCII string and `MDAY_RANGE`
            // is always inside the string.
            debug_assert_safe_version_ok!(str::from_utf8(&self.0[MDAY_RANGE]));
            str::from_utf8_unchecked(self.0.get_unchecked(MDAY_RANGE))
        }
    }

    /// Returns the day of month as a fixed length byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// let mday_fixed_len: &[u8; 2] = date.mday_bytes_fixed_len();
    /// assert_eq!(mday_fixed_len, b"31");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn mday_bytes_fixed_len(&self) -> &[u8; 2] {
        unsafe {
            // This is safe because `MDAY_RANGE` fits inside the string.
            debug_assert_safe_version_ok!(<&[u8; 2]>::try_from(&self.0[MDAY_RANGE]));
            let ptr = self.0.as_ptr().add(MDAY_RANGE.start) as *const [u8; 2];
            &*ptr
        }
    }

    /// Returns the day of month as a fixed length mutable byte slice.
    ///
    /// # Safety
    ///
    /// The returned slice should have only ASCII digits.
    /// If non-ASCII digits are stored, it may lead to undefined behavior.
    #[inline]
    #[must_use]
    unsafe fn mday_bytes_mut_fixed_len(&mut self) -> &mut [u8; 2] {
        // This is safe because `MDAY_RANGE` fits inside the string.
        debug_assert_ok!(<&[u8; 2]>::try_from(&self.0[MDAY_RANGE]));
        let ptr = self.0.as_mut_ptr().add(MDAY_RANGE.start) as *mut [u8; 2];
        &mut *ptr
    }

    /// Returns the day of month as an integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let date = Ymd8HyphenStr::from_str("2001-12-31")?;
    ///
    /// assert_eq!(date.mday(), 31);
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn mday(&self) -> u8 {
        parse_digits2(*self.mday_bytes_fixed_len())
    }

    /// Sets the given year to the string.
    ///
    /// # Failures
    ///
    /// * Fails if `year` is greater than 9999.
    /// * Fails if the datetime after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let mut buf: [u8; 10] = *b"2000-02-29";
    /// let date = Ymd8HyphenStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(date.as_str(), "2000-02-29");
    ///
    /// date.set_year(2004)?;
    /// assert_eq!(date.as_str(), "2004-02-29");
    ///
    /// assert!(date.set_year(2001).is_err(), "2001-02-29 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_year(&mut self, year: u16) -> Result<(), Error> {
        if year > 9999 {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Year).into());
        }
        validate_ym1d(year, self.month1(), self.mday())?;
        unsafe {
            // This is safe because `write_digit4()` fills the slice with ASCII digits.
            write_digit4(self.year_bytes_mut_fixed_len(), year);
        }

        debug_assert_ok!(validate_bytes(&self.0));
        debug_assert_ok!(
            validate_ym1d(self.year(), self.month1(), self.mday()),
            "Date should be valid after modification"
        );
        Ok(())
    }

    /// Sets the given 0-based month value to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the datetime after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let mut buf: [u8; 10] = *b"2001-12-31";
    /// let date = Ymd8HyphenStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(date.as_str(), "2001-12-31");
    ///
    /// date.set_month0(7)?;
    /// assert_eq!(date.as_str(), "2001-08-31");
    ///
    /// assert!(date.set_month0(8).is_err(), "2001-09-31 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_month0(&mut self, month0: u8) -> Result<(), Error> {
        if month0 >= 12 {
            return Err(ErrorKind::ComponentOutOfRange(ComponentKind::Month).into());
        }
        validate_ym0d(self.year(), month0, self.mday())?;
        unsafe {
            // This is safe because `write_digit2()` fills the slice with ASCII digits.
            write_digit2(self.month_bytes_mut_fixed_len(), month0.wrapping_add(1));
        }

        debug_assert_ok!(validate_bytes(&self.0));
        debug_assert_ok!(
            validate_ym1d(self.year(), self.month1(), self.mday()),
            "Date should be valid after modification"
        );
        Ok(())
    }

    /// Sets the given 1-based month value to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the datetime after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let mut buf: [u8; 10] = *b"2001-12-31";
    /// let date = Ymd8HyphenStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(date.as_str(), "2001-12-31");
    ///
    /// date.set_month1(8)?;
    /// assert_eq!(date.as_str(), "2001-08-31");
    ///
    /// assert!(date.set_month1(9).is_err(), "2001-09-31 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn set_month1(&mut self, month1: u8) -> Result<(), Error> {
        self.set_month0(month1.wrapping_sub(1))
    }

    /// Sets the given day of month value to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the datetime after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let mut buf: [u8; 10] = *b"2001-02-28";
    /// let date = Ymd8HyphenStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(date.as_str(), "2001-02-28");
    ///
    /// date.set_mday(3)?;
    /// assert_eq!(date.as_str(), "2001-02-03");
    ///
    /// assert!(date.set_mday(29).is_err(), "2001-02-29 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_mday(&mut self, mday: u8) -> Result<(), Error> {
        validate_ym1d(self.year(), self.month1(), mday)?;
        unsafe {
            // This is safe because `write_digit2()` fills the slice with ASCII digits.
            write_digit2(self.mday_bytes_mut_fixed_len(), mday);
        }

        debug_assert_ok!(validate_bytes(&self.0));
        debug_assert_ok!(
            validate_ym1d(self.year(), self.month1(), self.mday()),
            "Date should be valid after modification"
        );
        Ok(())
    }

    /// Sets the given 0-based month and 1-based day of month values to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the datetime after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let mut buf: [u8; 10] = *b"2001-02-28";
    /// let date = Ymd8HyphenStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(date.as_str(), "2001-02-28");
    ///
    /// date.set_month0_mday(3, 23)?;
    /// assert_eq!(date.as_str(), "2001-04-23");
    ///
    /// assert!(date.set_month0_mday(1, 29).is_err(), "2001-02-29 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_month0_mday(&mut self, month0: u8, mday: u8) -> Result<(), Error> {
        validate_ym0d(self.year(), month0, mday)?;
        unsafe {
            // This is safe because `write_digit2()` fills the slices with ASCII digits.
            write_digit2(self.month_bytes_mut_fixed_len(), month0.wrapping_add(1));
            write_digit2(self.mday_bytes_mut_fixed_len(), mday);
        }

        debug_assert_ok!(validate_bytes(&self.0));
        debug_assert_ok!(
            validate_ym1d(self.year(), self.month1(), self.mday()),
            "Date should be valid after modification"
        );
        Ok(())
    }

    /// Sets the given 1-based month and day of month values to the string.
    ///
    /// # Failures
    ///
    /// * Fails if the datetime after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let mut buf: [u8; 10] = *b"2001-02-28";
    /// let date = Ymd8HyphenStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(date.as_str(), "2001-02-28");
    ///
    /// date.set_month1_mday(4, 23)?;
    /// assert_eq!(date.as_str(), "2001-04-23");
    ///
    /// assert!(date.set_month1_mday(2, 29).is_err(), "2001-02-29 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_month1_mday(&mut self, month1: u8, mday: u8) -> Result<(), Error> {
        validate_ym1d(self.year(), month1, mday)?;
        unsafe {
            // This is safe because `write_digit2()` fills the slices with ASCII digits.
            write_digit2(self.month_bytes_mut_fixed_len(), month1);
            write_digit2(self.mday_bytes_mut_fixed_len(), mday);
        }

        debug_assert_ok!(validate_bytes(&self.0));
        debug_assert_ok!(
            validate_ym1d(self.year(), self.month1(), self.mday()),
            "Date should be valid after modification"
        );
        Ok(())
    }

    /// Sets the given 1-based year, 0-based month, and 1-based day of month values to the string.
    ///
    /// # Failures
    ///
    /// * Fails if `year` is greater than 9999.
    /// * Fails if the datetime after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let mut buf: [u8; 10] = *b"2001-02-28";
    /// let date = Ymd8HyphenStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(date.as_str(), "2001-02-28");
    ///
    /// date.set_ym0d(1999, 3, 23)?;
    /// assert_eq!(date.as_str(), "1999-04-23");
    ///
    /// assert!(date.set_ym0d(1999, 1, 29).is_err(), "1999-02-29 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    pub fn set_ym0d(&mut self, year: u16, month0: u8, mday: u8) -> Result<(), Error> {
        validate_ym0d(year, month0, mday)?;
        unsafe {
            // This is safe because `write_digit2()` and `write_digit4()` fill
            // the slices with ASCII digits.
            write_digit4(self.year_bytes_mut_fixed_len(), year);
            write_digit2(self.month_bytes_mut_fixed_len(), month0.wrapping_add(1));
            write_digit2(self.mday_bytes_mut_fixed_len(), mday);
        }

        debug_assert_ok!(validate_bytes(&self.0));
        debug_assert_ok!(
            validate_ym1d(self.year(), self.month1(), self.mday()),
            "Date should be valid after modification"
        );
        Ok(())
    }

    /// Sets the given 1-based year, month, and day of month values to the string.
    ///
    /// # Failures
    ///
    /// * Fails if `year` is greater than 9999.
    /// * Fails if the datetime after modification is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenStr;
    /// let mut buf: [u8; 10] = *b"2001-02-28";
    /// let date = Ymd8HyphenStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(date.as_str(), "2001-02-28");
    ///
    /// date.set_ym1d(1999, 4, 23)?;
    /// assert_eq!(date.as_str(), "1999-04-23");
    ///
    /// assert!(date.set_ym1d(1999, 2, 29).is_err(), "1999-02-29 is invalid");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn set_ym1d(&mut self, year: u16, month1: u8, mday: u8) -> Result<(), Error> {
        self.set_ym0d(year, month1.wrapping_sub(1), mday)
    }
}

#[cfg(feature = "alloc")]
impl alloc::borrow::ToOwned for Ymd8HyphenStr {
    type Owned = Ymd8HyphenString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for Ymd8HyphenStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for Ymd8HyphenStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<Ymd8HyphenStr> for Ymd8HyphenStr {
    #[inline]
    fn as_ref(&self) -> &Ymd8HyphenStr {
        self
    }
}

impl AsMut<Ymd8HyphenStr> for Ymd8HyphenStr {
    #[inline]
    fn as_mut(&mut self) -> &mut Ymd8HyphenStr {
        self
    }
}

impl<'a> From<&'a Ymd8HyphenStr> for &'a str {
    #[inline]
    fn from(v: &'a Ymd8HyphenStr) -> Self {
        v.as_str()
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a Ymd8HyphenStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid RFC 3339 `full-date` string is also an ASCII string.
            Ymd8HyphenStr::from_bytes_maybe_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut Ymd8HyphenStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid RFC 3339 `full-date` string is also an ASCII string.
            Ymd8HyphenStr::from_bytes_maybe_unchecked_mut(v)
        })
    }
}

impl<'a> TryFrom<&'a str> for &'a Ymd8HyphenStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a str) -> Result<Self, Self::Error> {
        TryFrom::try_from(v.as_bytes())
    }
}

impl<'a> TryFrom<&'a mut str> for &'a mut Ymd8HyphenStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because the value is successfully validated, and
            // `Ymd8HyphenStr` ensures the value after modification is an ASCII string.
            Ymd8HyphenStr::from_str_maybe_unchecked_mut(v)
        })
    }
}

impl fmt::Display for Ymd8HyphenStr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl ops::Deref for Ymd8HyphenStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl_cmp_symmetric!(str, Ymd8HyphenStr, &Ymd8HyphenStr);
impl_cmp_symmetric!([u8], Ymd8HyphenStr, [u8]);
impl_cmp_symmetric!([u8], Ymd8HyphenStr, &[u8]);
impl_cmp_symmetric!([u8], &Ymd8HyphenStr, [u8]);
impl_cmp_symmetric!(str, Ymd8HyphenStr, str);
impl_cmp_symmetric!(str, Ymd8HyphenStr, &str);
impl_cmp_symmetric!(str, &Ymd8HyphenStr, str);

#[cfg(feature = "serde")]
impl serde::Serialize for Ymd8HyphenStr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

/// Owned string for a date in `YYYY-MM-DD` format, such as `2001-12-31`.
///
/// This is also an RFC 3339 [`full-date`] string.
///
/// This is a fixed length string, and implements [`Copy`] trait.
///
/// To create a value of this type, use [`str::parse`] method or
/// [`std::convert::TryFrom`] trait, or convert from `&Ymd8HyphenStr`.
///
/// # Examples
///
/// ```
/// # use datetime_string::common::Ymd8HyphenString;
/// use datetime_string::common::Ymd8HyphenStr;
/// use std::convert::TryFrom;
///
/// let try_from = Ymd8HyphenString::try_from("2001-12-31")?;
///
/// let parse = "2001-12-31".parse::<Ymd8HyphenString>()?;
/// let parse2: Ymd8HyphenString = "2001-12-31".parse()?;
///
/// let to_owned = Ymd8HyphenStr::from_str("2001-12-31")?.to_owned();
/// let into: Ymd8HyphenString = Ymd8HyphenStr::from_str("2001-12-31")?.into();
/// # Ok::<_, datetime_string::Error>(())
/// ```
///
/// [`full-date`]: https://tools.ietf.org/html/rfc3339#section-5.6
// Note that `derive(Serialize)` cannot used here, because it encodes this as
// `[u8; 10]` rather than as a string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
// Comparisons implemented for the type are consistent (at least it is intended to be so).
// See <https://github.com/rust-lang/rust-clippy/issues/2025>.
// Note that `clippy::derive_ord_xor_partial_ord` would be introduced since Rust 1.47.0.
#[allow(clippy::derive_hash_xor_eq)]
#[allow(clippy::unknown_clippy_lints, clippy::derive_ord_xor_partial_ord)]
pub struct Ymd8HyphenString([u8; FULL_DATE_LEN]);

impl Ymd8HyphenString {
    /// Creates a `Ymd8HyphenString` from the given bytes.
    ///
    /// # Safety
    ///
    /// `validate_bytes(&s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn new_maybe_unchecked(s: [u8; 10]) -> Self {
        debug_assert_ok!(validate_bytes(&s));
        Self(s)
    }

    /// Returns a `&Ymd8HyphenStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenString;
    /// use datetime_string::common::Ymd8HyphenStr;
    ///
    /// let date = "2001-12-31".parse::<Ymd8HyphenString>()?;
    ///
    /// // Usually you don't need to call `as_deref()` explicitly, because
    /// // `Deref<Target = Ymd8HyphenStr>` trait is implemented.
    /// let _: &Ymd8HyphenStr = date.as_deref();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref(&self) -> &Ymd8HyphenStr {
        unsafe {
            // This is safe because `self.0` is valid RFC 3339 `full-date` string.
            debug_assert_ok!(Ymd8HyphenStr::from_bytes(&self.0));
            Ymd8HyphenStr::from_bytes_maybe_unchecked(&self.0)
        }
    }

    /// Returns a `&mut Ymd8HyphenStr` for the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::common::Ymd8HyphenString;
    /// use datetime_string::common::Ymd8HyphenStr;
    ///
    /// let mut date = "2001-12-31".parse::<Ymd8HyphenString>()?;
    ///
    /// // Usually you don't need to call `as_deref_mut()` explicitly, because
    /// // `DerefMut` trait is implemented.
    /// let _: &mut Ymd8HyphenStr = date.as_deref_mut();
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_deref_mut(&mut self) -> &mut Ymd8HyphenStr {
        unsafe {
            // This is safe because `self.0` is valid RFC 3339 `full-date` string.
            debug_assert_ok!(Ymd8HyphenStr::from_bytes(&self.0));
            Ymd8HyphenStr::from_bytes_maybe_unchecked_mut(&mut self.0)
        }
    }
}

impl core::borrow::Borrow<Ymd8HyphenStr> for Ymd8HyphenString {
    #[inline]
    fn borrow(&self) -> &Ymd8HyphenStr {
        self.as_deref()
    }
}

impl core::borrow::BorrowMut<Ymd8HyphenStr> for Ymd8HyphenString {
    #[inline]
    fn borrow_mut(&mut self) -> &mut Ymd8HyphenStr {
        self.as_deref_mut()
    }
}

impl AsRef<[u8]> for Ymd8HyphenString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for Ymd8HyphenString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<Ymd8HyphenStr> for Ymd8HyphenString {
    #[inline]
    fn as_ref(&self) -> &Ymd8HyphenStr {
        self
    }
}

impl AsMut<Ymd8HyphenStr> for Ymd8HyphenString {
    #[inline]
    fn as_mut(&mut self) -> &mut Ymd8HyphenStr {
        self
    }
}

#[cfg(feature = "alloc")]
impl From<Ymd8HyphenString> for Vec<u8> {
    #[inline]
    fn from(v: Ymd8HyphenString) -> Vec<u8> {
        (*v.as_bytes_fixed_len()).into()
    }
}

#[cfg(feature = "alloc")]
impl From<Ymd8HyphenString> for String {
    #[inline]
    fn from(v: Ymd8HyphenString) -> String {
        let vec: Vec<u8> = (*v.as_bytes_fixed_len()).into();
        unsafe {
            // This is safe because a valid RFC 3339 `full-date` string is also an ASCII string.
            String::from_utf8_unchecked(vec)
        }
    }
}

impl From<&Ymd8HyphenStr> for Ymd8HyphenString {
    fn from(v: &Ymd8HyphenStr) -> Self {
        unsafe {
            // This is safe because the value is already validated.
            Self::new_maybe_unchecked(*v.as_bytes_fixed_len())
        }
    }
}

impl TryFrom<&[u8]> for Ymd8HyphenString {
    type Error = Error;

    #[inline]
    fn try_from(v: &[u8]) -> Result<Self, Self::Error> {
        Ymd8HyphenStr::from_bytes(v).map(Into::into)
    }
}

impl TryFrom<&str> for Ymd8HyphenString {
    type Error = Error;

    #[inline]
    fn try_from(v: &str) -> Result<Self, Self::Error> {
        Ymd8HyphenStr::from_str(v).map(Into::into)
    }
}

impl TryFrom<[u8; 10]> for Ymd8HyphenString {
    type Error = Error;

    #[inline]
    fn try_from(v: [u8; 10]) -> Result<Self, Self::Error> {
        validate_bytes(&v)?;
        Ok(unsafe {
            // This is safe because the value is successfully validated.
            Self::new_maybe_unchecked(v)
        })
    }
}

impl fmt::Display for Ymd8HyphenString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_deref().fmt(f)
    }
}

impl ops::Deref for Ymd8HyphenString {
    type Target = Ymd8HyphenStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_deref()
    }
}

impl ops::DerefMut for Ymd8HyphenString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_deref_mut()
    }
}

impl str::FromStr for Ymd8HyphenString {
    type Err = Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl_cmp_symmetric!(Ymd8HyphenStr, Ymd8HyphenString, &Ymd8HyphenString);
impl_cmp_symmetric!(Ymd8HyphenStr, Ymd8HyphenString, Ymd8HyphenStr);
impl_cmp_symmetric!(Ymd8HyphenStr, Ymd8HyphenString, &Ymd8HyphenStr);
impl_cmp_symmetric!(str, Ymd8HyphenString, str);
impl_cmp_symmetric!(str, Ymd8HyphenString, &str);
impl_cmp_symmetric!(str, &Ymd8HyphenString, str);
impl_cmp_symmetric!([u8], Ymd8HyphenString, [u8]);
impl_cmp_symmetric!([u8], Ymd8HyphenString, &[u8]);
impl_cmp_symmetric!([u8], &Ymd8HyphenString, [u8]);

#[cfg(feature = "serde")]
impl serde::Serialize for Ymd8HyphenString {
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

    /// Visitor for `&Ymd8HyphenStr`.
    struct StrVisitor;

    impl<'de> Visitor<'de> for StrVisitor {
        type Value = &'de Ymd8HyphenStr;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("YYYY-MM-DD date string")
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

    impl<'de> Deserialize<'de> for &'de Ymd8HyphenStr {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_any(StrVisitor)
        }
    }

    /// Visitor for `Ymd8HyphenString`.
    struct StringVisitor;

    impl<'de> Visitor<'de> for StringVisitor {
        type Value = Ymd8HyphenString;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("YYYY-MM-DD date string")
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

    impl<'de> Deserialize<'de> for Ymd8HyphenString {
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
        assert!(s_validate(b"0000-01-01").is_ok());
        assert!(s_validate(b"9999-12-31").is_ok());

        assert!(s_validate(b"2001-01-01").is_ok());
        assert!(s_validate(b"2001-01-31").is_ok());
        assert!(s_validate(b"2001-03-31").is_ok());
        assert!(s_validate(b"2001-04-30").is_ok());
        assert!(s_validate(b"2001-05-31").is_ok());
        assert!(s_validate(b"2001-06-30").is_ok());
        assert!(s_validate(b"2001-07-31").is_ok());
        assert!(s_validate(b"2001-08-31").is_ok());
        assert!(s_validate(b"2001-09-30").is_ok());
        assert!(s_validate(b"2001-10-31").is_ok());
        assert!(s_validate(b"2001-11-30").is_ok());
        assert!(s_validate(b"2001-12-31").is_ok());

        assert!(s_validate(b"2001-00-01").is_err());
        assert!(s_validate(b"2001-13-01").is_err());
        assert!(s_validate(b"2001-01-00").is_err());
        assert!(s_validate(b"2001-01-32").is_err());
        assert!(s_validate(b"2001-03-32").is_err());
        assert!(s_validate(b"2001-04-31").is_err());
        assert!(s_validate(b"2001-05-32").is_err());
        assert!(s_validate(b"2001-06-31").is_err());
        assert!(s_validate(b"2001-07-32").is_err());
        assert!(s_validate(b"2001-08-32").is_err());
        assert!(s_validate(b"2001-09-31").is_err());
        assert!(s_validate(b"2001-10-32").is_err());
        assert!(s_validate(b"2001-11-31").is_err());
        assert!(s_validate(b"2001-12-32").is_err());

        // 2001 is not a leap year.
        assert!(s_validate(b"2001-02-28").is_ok());
        assert!(s_validate(b"2001-02-29").is_err());
        // 2000 is a leap year.
        assert!(s_validate(b"2000-02-28").is_ok());
        assert!(s_validate(b"2000-02-29").is_ok());
        assert!(s_validate(b"2000-02-30").is_err());
        // 2004 is a leap year.
        assert!(s_validate(b"2004-02-28").is_ok());
        assert!(s_validate(b"2004-02-29").is_ok());
        assert!(s_validate(b"2004-02-30").is_err());
        // 2100 is not a leap year.
        assert!(s_validate(b"2100-02-28").is_ok());
        assert!(s_validate(b"2100-02-29").is_err());

        assert!(s_validate(b"2001+01-01").is_err());
        assert!(s_validate(b"2001-01+01").is_err());
        assert!(s_validate(b"01-01-01").is_err());
        assert!(s_validate(b"+001-01-01").is_err());
        assert!(s_validate(b"-001-01-01").is_err());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_str() {
        let raw: &'static str = "2001-12-31";
        assert_tokens(
            &Ymd8HyphenStr::from_str(raw).unwrap(),
            &[Token::BorrowedStr(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_string() {
        let raw: &'static str = "2001-12-31";
        assert_tokens(
            &Ymd8HyphenString::try_from(raw).unwrap(),
            &[Token::Str(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes_slice() {
        let raw: &'static [u8; 10] = b"2001-12-31";
        assert_de_tokens(
            &Ymd8HyphenStr::from_bytes(raw).unwrap(),
            &[Token::BorrowedBytes(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes() {
        let raw: &'static [u8; 10] = b"2001-12-31";
        assert_de_tokens(
            &Ymd8HyphenString::try_from(&raw[..]).unwrap(),
            &[Token::Bytes(raw)],
        );
    }
}
