//! RFC 3339 [`date-time`] string types.
//!
//! [`date-time`]: https://tools.ietf.org/html/rfc3339#section-5.6

#[cfg(feature = "alloc")]
mod owned;

use core::{
    convert::TryFrom,
    fmt,
    ops::{self, RangeFrom, RangeTo},
    str,
};

#[cfg(feature = "serde")]
use serde::Serialize;

use crate::error::{Error, ErrorKind};

use super::{FullDateStr, FullTimeStr};

#[cfg(feature = "alloc")]
pub use self::owned::DateTimeString;

/// Minimum length of the `date-time` string.
///
/// This is a length of `YYYY-MM-DDThh:mm:ssZ`.
const DATETIME_LEN_MIN: usize = 20;
/// Position of separator "T".
const T_POS: usize = 10;
/// Range of the date in a string.
///
/// This is always valid range for `full-date` string.
const DATE_RANGE: RangeTo<usize> = ..T_POS;
/// Range of the time in a string.
///
/// This is always valid range for `full-date` string.
const TIME_RANGE: RangeFrom<usize> = (T_POS + 1)..;

/// Validates the given string as an RFC 3339 [`date-time`].
///
/// [`date-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
fn validate_bytes(s: &[u8]) -> Result<(), Error> {
    if s.len() < DATETIME_LEN_MIN {
        return Err(ErrorKind::TooShort.into());
    }

    if s[T_POS] != b'T' {
        return Err(ErrorKind::InvalidSeparator.into());
    }

    FullDateStr::from_bytes(&s[DATE_RANGE])?;
    FullTimeStr::from_bytes(&s[TIME_RANGE])?;

    Ok(())
}

/// String slice for a datetime in RFC 3339 [`date-time`] format, such as
/// `2001-06-17T12:34:56.7890-23:12`.
///
/// [`date-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
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
pub struct DateTimeStr([u8]);

impl DateTimeStr {
    /// Creates a `&DateTimeStr` from the given byte slice.
    ///
    /// This performs assertion in debug build, but not in release build.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_bytes_maybe_unchecked(s: &[u8]) -> &Self {
        debug_assert_ok!(validate_bytes(s));
        &*(s as *const [u8] as *const Self)
    }

    /// Creates a `&mut DateTimeStr` from the given mutable byte slice.
    ///
    /// This performs assertion in debug build, but not in release build.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_bytes_maybe_unchecked_mut(s: &mut [u8]) -> &mut Self {
        debug_assert_ok!(validate_bytes(s));
        &mut *(s as *mut [u8] as *mut Self)
    }

    /// Creates a `&mut DateTimeStr` from the given mutable string slice.
    ///
    /// This performs assertion in debug build, but not in release build.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_maybe_unchecked_mut(s: &mut str) -> &mut Self {
        // This is safe because `DateTimeStr` ensures that the underlying
        // bytes are ASCII string after modification.
        Self::from_bytes_maybe_unchecked_mut(s.as_bytes_mut())
    }

    /// Creates a new `&DateTimeStr` from a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// let datetime = DateTimeStr::from_str("2001-06-17T12:34:56.7890-23:12")?;
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.7890-23:12");
    ///
    /// assert!(DateTimeStr::from_str("2000-02-29T12:34:56Z").is_ok());
    /// assert!(DateTimeStr::from_str("9999-12-31T23:59:59+23:59").is_ok());
    /// assert!(DateTimeStr::from_str("0000-01-01T00:00:00.0-00:00").is_ok());
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    // `FromStr` trait cannot be implemented for a slice.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut DateTimeStr` from a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// let mut buf = "2001-06-17T12:34:56.7890-23:12".to_owned();
    /// let datetime = DateTimeStr::from_mut_str(&mut buf)?;
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.7890-23:12");
    ///
    /// datetime.date_mut().set_year(1999);
    /// assert_eq!(datetime.as_str(), "1999-06-17T12:34:56.7890-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_mut_str(s: &mut str) -> Result<&mut Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&DateTimeStr` from a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// let datetime = DateTimeStr::from_bytes(b"2001-06-17T12:34:56.7890-23:12")?;
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.7890-23:12");
    ///
    /// assert!(DateTimeStr::from_bytes(b"2001-06-17T12:34:56Z").is_ok());
    /// assert!(DateTimeStr::from_bytes(b"9999-12-31T23:59:59+23:59").is_ok());
    /// assert!(DateTimeStr::from_bytes(b"0000-01-01T00:00:00.0-00:00").is_ok());
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_bytes(s: &[u8]) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut DateTimeStr` from a mutable byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// let mut buf = b"2001-06-17T12:34:56.7890-23:12".to_owned();
    /// let datetime = DateTimeStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.7890-23:12");
    ///
    /// datetime.date_mut().set_year(1999);
    /// assert_eq!(datetime.as_str(), "1999-06-17T12:34:56.7890-23:12");
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
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// let datetime = DateTimeStr::from_str("2001-06-17T12:34:56.7890-23:12")?;
    ///
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.7890-23:12");
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
    /// If you want to use indexed access, prefer [`as_bytes_fixed_len`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// let datetime = DateTimeStr::from_str("2001-06-17T12:34:56.7890-23:12")?;
    ///
    /// assert_eq!(datetime.as_bytes(), b"2001-06-17T12:34:56.7890-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    ///
    /// [`as_bytes_fixed_len`]: #method.as_bytes_fixed_len
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Decomposes the string into `&FullDateStr` and `&FullTimeStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// let datetime = DateTimeStr::from_str("2001-06-17T12:34:56.7890-23:12")?;
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.7890-23:12");
    ///
    /// let (date, time) = datetime.decompose();
    /// assert_eq!(date.as_str(), "2001-06-17");
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn decompose(&self) -> (&FullDateStr, &FullTimeStr) {
        let date = unsafe {
            // This is safe because `DATE_RANGE` fits inside the string, and a
            // `date-time` string has a `full-date` followed by 'T' and `full-time`.
            debug_assert_safe_version_ok!(<FullDateStr>::from_bytes(&self.0[DATE_RANGE]));
            FullDateStr::from_bytes_maybe_unchecked(self.0.get_unchecked(DATE_RANGE))
        };
        let time = unsafe {
            // This is safe because `TIME_RANGE` fits inside the string, and a
            // `date-time` string has a `full-time` suffix following `full-date`
            // and 'T'.
            debug_assert_safe_version_ok!(<FullTimeStr>::from_bytes(&self.0[TIME_RANGE]));
            FullTimeStr::from_bytes_maybe_unchecked(self.0.get_unchecked(TIME_RANGE))
        };

        (date, time)
    }

    /// Decomposes the string into `&mut FullDateStr` and `&mut FullTimeStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// use datetime_string::common::TimeOffsetSign;
    ///
    /// let mut buf = "2001-06-17T12:34:56.7890-23:12".to_owned();
    /// let datetime = DateTimeStr::from_mut_str(&mut buf)?;
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.7890-23:12");
    ///
    /// let (date, time) = datetime.decompose_mut();
    /// assert_eq!(date.as_str(), "2001-06-17");
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// date.set_year(1999)?;
    /// time.partial_time_mut().secfrac_mut().unwrap().digits_mut().fill_with_zero();
    /// assert_eq!(datetime.as_str(), "1999-06-17T12:34:56.0000-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn decompose_mut(&mut self) -> (&mut FullDateStr, &mut FullTimeStr) {
        debug_assert_ok!(<FullDateStr>::from_bytes(&self.0[..T_POS]));
        debug_assert_ok!(<FullTimeStr>::from_bytes(&self.0[(T_POS + 1)..]));

        unsafe {
            let (date, t_time) = self.0.split_at_mut(T_POS);
            // Note that `t_time` contains the separator "T" as a prefix.
            let time = t_time.get_unchecked_mut(1..);

            // This is safe because a `date-time` string has a `full-date`
            // followed by 'T' and `full-time`, and `FullDateStr` ensures that
            // the underlying bytes are ASCII string after modification.
            let date = FullDateStr::from_bytes_maybe_unchecked_mut(date);
            // This is safe because a `date-time` string has a `full-time`
            // suffix following `full-date` and 'T', and `FullTimeStr` ensures
            // that the underlying bytes are ASCII string after modification.
            let time = FullTimeStr::from_bytes_maybe_unchecked_mut(time);

            (date, time)
        }
    }

    /// Returns a `&FullDateStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// let datetime = DateTimeStr::from_str("2001-06-17T12:34:56.7890-23:12")?;
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.7890-23:12");
    ///
    /// let date = datetime.date();
    /// assert_eq!(date.as_str(), "2001-06-17");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn date(&self) -> &FullDateStr {
        unsafe {
            debug_assert_safe_version_ok!(FullDateStr::from_bytes(&self.0[DATE_RANGE]));
            // This is safe because the range is valid for the shortest possible string.
            let s = self.0.get_unchecked(DATE_RANGE);
            // This is safe because a `date-time` string has a `full-date` before "T".
            FullDateStr::from_bytes_maybe_unchecked(s)
        }
    }

    /// Returns a `&mut FullDateStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// let mut buf = "2001-06-17T12:34:56.7890-23:12".to_owned();
    /// let datetime = DateTimeStr::from_mut_str(&mut buf)?;
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.7890-23:12");
    ///
    /// let date = datetime.date_mut();
    /// assert_eq!(date.as_str(), "2001-06-17");
    ///
    /// date.set_year(1999)?;
    /// assert_eq!(datetime.as_str(), "1999-06-17T12:34:56.7890-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn date_mut(&mut self) -> &mut FullDateStr {
        unsafe {
            debug_assert_ok!(FullDateStr::from_bytes(&self.0[DATE_RANGE]));
            // This is safe because the range is valid for the shortest possible
            // string, and `FullDateStr` ensures that the underlying bytes are
            // ASCII string after modification.
            let s = self.0.get_unchecked_mut(DATE_RANGE);
            // This is safe because a `date-time` string has a `partial-time` before "T".
            FullDateStr::from_bytes_maybe_unchecked_mut(s)
        }
    }

    /// Returns a `&FullTimeStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// let datetime = DateTimeStr::from_str("2001-06-17T12:34:56.7890-23:12")?;
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.7890-23:12");
    ///
    /// let time = datetime.time();
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn time(&self) -> &FullTimeStr {
        unsafe {
            debug_assert_safe_version_ok!(FullTimeStr::from_bytes(&self.0[TIME_RANGE]));
            // This is safe because the range is valid for the shortest possible string.
            let s = self.0.get_unchecked(TIME_RANGE);
            // This is safe because a `date-time` string has a `time-offset` right after "T".
            FullTimeStr::from_bytes_maybe_unchecked(s)
        }
    }

    /// Returns a `&mut FullTimeStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// use datetime_string::common::TimeOffsetSign;
    ///
    /// let mut buf = "2001-06-17T12:34:56.7890-23:12".to_owned();
    /// let datetime = DateTimeStr::from_mut_str(&mut buf)?;
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.7890-23:12");
    ///
    /// let time = datetime.time_mut();
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// time.partial_time_mut().secfrac_mut().unwrap().digits_mut().fill_with_zero();
    /// assert_eq!(datetime.as_str(), "2001-06-17T12:34:56.0000-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn time_mut(&mut self) -> &mut FullTimeStr {
        unsafe {
            debug_assert_ok!(FullTimeStr::from_bytes(&self.0[TIME_RANGE]));
            // This is safe because the range is valid for the shortest possible
            // string, and `FullTimeStr` ensures that the underlying bytes are
            // ASCII string after modification.
            let s = self.0.get_unchecked_mut(TIME_RANGE);
            // This is safe because a `date-time` string has a `time-offset` right after "T".
            FullTimeStr::from_bytes_maybe_unchecked_mut(s)
        }
    }

    /// Converts the time to [`chrono::DateTime<FixedOffset>`][`chrono04::DateTime`].
    ///
    /// Note that this truncates subnanosecond secfrac.
    ///
    /// Enabled by `chrono04` feature.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::DateTimeStr;
    /// use chrono04::{FixedOffset, TimeZone};
    ///
    /// let datetime = DateTimeStr::from_str("1999-12-31T12:34:56.01234567899999+09:00")?;
    /// assert_eq!(
    ///     datetime.to_chrono_date_time(),
    ///     FixedOffset::east(9 * 60 * 60).ymd(1999, 12, 31).and_hms_nano(12, 34, 56, 12_345_678)
    /// );
    ///
    /// let leap = DateTimeStr::from_str("2001-12-31T23:59:60.876543210999-00:00")?;
    /// assert_eq!(
    ///     leap.to_chrono_date_time(),
    ///     FixedOffset::east(0).ymd(2001, 12, 31).and_hms_nano(23, 59, 59, 1_876_543_210)
    /// );
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[cfg(feature = "chrono04")]
    pub fn to_chrono_date_time(&self) -> chrono04::DateTime<chrono04::FixedOffset> {
        use chrono04::TimeZone;

        let (date_s, time_s) = self.decompose();
        let date: chrono04::NaiveDate = date_s.into();
        let time: chrono04::NaiveTime = time_s.partial_time().to_chrono_naive_time();
        let offset: chrono04::FixedOffset = time_s.offset().into();

        offset
            .from_local_datetime(&date.and_time(time))
            .single()
            .expect("Should never fail: fixed time offset is not affected by summer time")
    }
}

impl AsRef<[u8]> for DateTimeStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsRef<str> for DateTimeStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<DateTimeStr> for DateTimeStr {
    #[inline]
    fn as_ref(&self) -> &DateTimeStr {
        self
    }
}

impl AsMut<DateTimeStr> for DateTimeStr {
    #[inline]
    fn as_mut(&mut self) -> &mut DateTimeStr {
        self
    }
}

impl<'a> From<&'a DateTimeStr> for &'a str {
    #[inline]
    fn from(v: &'a DateTimeStr) -> Self {
        v.as_str()
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a DateTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid `date-time` string is also an ASCII string.
            DateTimeStr::from_bytes_maybe_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut DateTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid `date-time` string is also an ASCII string.
            DateTimeStr::from_bytes_maybe_unchecked_mut(v)
        })
    }
}

impl<'a> TryFrom<&'a str> for &'a DateTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a str) -> Result<Self, Self::Error> {
        Self::try_from(v.as_bytes())
    }
}

impl<'a> TryFrom<&'a mut str> for &'a mut DateTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because the string is already validated and
            // `DateTimeStr` ensures that the underlying bytes are ASCII
            // string after modification.
            DateTimeStr::from_str_maybe_unchecked_mut(v)
        })
    }
}

impl fmt::Display for DateTimeStr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl ops::Deref for DateTimeStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl_cmp_symmetric!(str, DateTimeStr, &DateTimeStr);
impl_cmp_symmetric!([u8], DateTimeStr, [u8]);
impl_cmp_symmetric!([u8], DateTimeStr, &[u8]);
impl_cmp_symmetric!([u8], &DateTimeStr, [u8]);
impl_cmp_symmetric!(str, DateTimeStr, str);
impl_cmp_symmetric!(str, DateTimeStr, &str);
impl_cmp_symmetric!(str, &DateTimeStr, str);

#[cfg(feature = "serde")]
impl Serialize for DateTimeStr {
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

    /// Visitor for `&DateTimeStr`.
    struct StrVisitor;

    impl<'de> Visitor<'de> for StrVisitor {
        type Value = &'de DateTimeStr;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 date-time string")
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

    impl<'de> Deserialize<'de> for &'de DateTimeStr {
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
        assert!(s_validate(b"2001-06-17T12:34:56Z").is_ok());
        assert!(s_validate(b"2001-06-17T12:34:56-00:00").is_ok());
        assert!(s_validate(b"2001-06-17T12:34:56-12:30").is_ok());
        assert!(s_validate(b"2001-06-17T12:34:56-23:59").is_ok());
        assert!(s_validate(b"2001-06-17T12:34:56+00:00").is_ok());
        assert!(s_validate(b"2001-06-17T12:34:56+12:30").is_ok());
        assert!(s_validate(b"2001-06-17T12:34:56+23:59").is_ok());

        assert!(s_validate(b"2001-06-17T00:00:00-00:00").is_ok());
        assert!(s_validate(b"2001-06-17T23:59:59-00:00").is_ok());

        assert!(s_validate(b"2001-06-17T12:34:56.7890Z").is_ok());
        assert!(s_validate(b"2001-06-17T12:34:56.7890-00:00").is_ok());
        assert!(s_validate(b"2001-06-17T12:34:56.7890+00:00").is_ok());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_str() {
        let raw: &'static str = "2001-06-17T12:34:56.7890-23:12";
        assert_tokens(
            &DateTimeStr::from_str(raw).unwrap(),
            &[Token::BorrowedStr(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes_slice() {
        let raw: &'static [u8] = b"2001-06-17T12:34:56.7890-23:12";
        assert_de_tokens(
            &DateTimeStr::from_bytes(raw).unwrap(),
            &[Token::BorrowedBytes(raw)],
        );
    }
}
