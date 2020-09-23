//! RFC 3339 [`full-time`] string types.
//!
//! [`full-time`]: https://tools.ietf.org/html/rfc3339#section-5.6

#[cfg(feature = "alloc")]
mod owned;

use core::{convert::TryFrom, fmt, ops, str};

#[cfg(feature = "serde")]
use serde::Serialize;

use crate::Error;

use super::{PartialTimeStr, TimeNumOffsetStr, TimeOffsetStr};

#[cfg(feature = "alloc")]
pub use self::owned::FullTimeString;

/// Validates the given string as an RFC 3339 [`full-time`].
///
/// [`full-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
fn validate_bytes(s: &[u8]) -> Result<(), Error> {
    let len = s.len();
    let len_1 = len - 1;
    if s[len_1] == b'Z' {
        return PartialTimeStr::from_bytes(&s[..len_1]).map(|_| ());
    }

    // 6: Length of `+hh:mm`.
    let (partial_time, num_offset) = s.split_at(len - 6);
    PartialTimeStr::from_bytes(partial_time)?;
    // `time-offset` follows `partial-time`, but `time-offset` is already checked to not being `Z`.
    // Then the offset should be `time-numoffset`.
    TimeNumOffsetStr::from_bytes(num_offset)?;

    Ok(())
}

/// String slice for a time in RFC 3339 [`full-time`] format, such as `12:34:56.7890-23:12`.
///
/// [`full-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
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
pub struct FullTimeStr([u8]);

impl FullTimeStr {
    /// Creates a `&FullTimeStr` from the given byte slice.
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

    /// Creates a `&mut FullTimeStr` from the given mutable byte slice.
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

    /// Creates a `&mut FullTimeStr` from the given mutable string slice.
    ///
    /// This performs assertion in debug build, but not in release build.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_maybe_unchecked_mut(s: &mut str) -> &mut Self {
        // This is safe because `FullTimeStr` ensures that the underlying
        // bytes are ASCII string after modification.
        Self::from_bytes_maybe_unchecked_mut(s.as_bytes_mut())
    }

    /// Creates a new `&FullTimeStr` from a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// let time = FullTimeStr::from_str("12:34:56.7890-23:12")?;
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// assert!(FullTimeStr::from_str("12:34:56Z").is_ok());
    /// assert!(FullTimeStr::from_str("23:59:59+23:59").is_ok());
    /// assert!(FullTimeStr::from_str("00:00:00.0-00:00").is_ok());
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    // `FromStr` trait cannot be implemented for a slice.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut FullTimeStr` from a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// let mut buf = "12:34:56.7890-23:12".to_owned();
    /// let time = FullTimeStr::from_mut_str(&mut buf)?;
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// time.partial_time_mut().hms_mut().set_time(0, 22, 44)?;
    /// assert_eq!(time.as_str(), "00:22:44.7890-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_mut_str(s: &mut str) -> Result<&mut Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&FullTimeStr` from a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// let time = FullTimeStr::from_bytes(b"12:34:56.7890-23:12")?;
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// assert!(FullTimeStr::from_bytes(b"12:34:56Z").is_ok());
    /// assert!(FullTimeStr::from_bytes(b"23:59:59+23:59").is_ok());
    /// assert!(FullTimeStr::from_bytes(b"00:00:00.0-00:00").is_ok());
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_bytes(s: &[u8]) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut FullTimeStr` from a mutable byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// let mut buf = b"12:34:56.7890-23:12".to_owned();
    /// let time = FullTimeStr::from_bytes_mut(&mut buf[..])?;
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// time.partial_time_mut().hms_mut().set_time(0, 22, 44)?;
    /// assert_eq!(time.as_str(), "00:22:44.7890-23:12");
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
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// let time = FullTimeStr::from_str("12:34:56.7890-23:12")?;
    ///
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        unsafe {
            // This is safe because the `FullTimeStr` ensures that the
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
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// let time = FullTimeStr::from_str("12:34:56.7890-23:12")?;
    ///
    /// assert_eq!(time.as_bytes(), b"12:34:56.7890-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    ///
    /// [`as_bytes_fixed_len`]: #method.as_bytes_fixed_len
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Returns the beginning position of the time offset substring.
    #[inline]
    #[must_use]
    fn offset_start_pos(&self) -> usize {
        let len = self.0.len();
        let len_1 = len - 1;
        if self.0[len_1] == b'Z' {
            // Time offset is 'Z', which is 1 bytes.
            len_1
        } else {
            // Time offset is `time-numoffset` format, which is 6 bytes.
            len - 6
        }
    }

    /// Decomposes the string into `&PartialTimeStr` and `&TimeOffsetStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// let time = FullTimeStr::from_str("12:34:56.7890-23:12")?;
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// let (partial_time, offset) = time.decompose();
    /// assert_eq!(partial_time.as_str(), "12:34:56.7890");
    /// assert_eq!(offset.as_str(), "-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn decompose(&self) -> (&PartialTimeStr, &TimeOffsetStr) {
        let offset_start_pos = self.offset_start_pos();
        debug_assert!(
            offset_start_pos < self.len(),
            "Time offset should not be empty"
        );
        let (partial_time, offset) = self.0.split_at(offset_start_pos);

        let partial_time = unsafe {
            // This is safe because a `full-time` string has a `partial-time`
            // followed by `time-offset`.
            debug_assert_safe_version_ok!(PartialTimeStr::from_bytes(partial_time));
            PartialTimeStr::from_bytes_maybe_unchecked(partial_time)
        };
        let offset = unsafe {
            // This is safe because a `full-time` string has a `time-offset`
            // suffix following `partial-time`.
            debug_assert_safe_version_ok!(TimeOffsetStr::from_bytes(offset));
            TimeOffsetStr::from_bytes_maybe_unchecked(offset)
        };

        (partial_time, offset)
    }

    /// Decomposes the string into `&mut PartialTimeStr` and `&mut TimeOffsetStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// use datetime_string::common::TimeOffsetSign;
    ///
    /// let mut buf = "12:34:56.7890-23:12".to_owned();
    /// let time = FullTimeStr::from_mut_str(&mut buf)?;
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// let (partial_time, offset) = time.decompose_mut();
    /// assert_eq!(partial_time.as_str(), "12:34:56.7890");
    /// assert_eq!(offset.as_str(), "-23:12");
    ///
    /// partial_time.secfrac_mut().unwrap().digits_mut().fill_with_zero();
    /// offset.to_numoffset_mut().unwrap().set_sign(TimeOffsetSign::Positive);
    /// assert_eq!(time.as_str(), "12:34:56.0000+23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn decompose_mut(&mut self) -> (&mut PartialTimeStr, &mut TimeOffsetStr) {
        let offset_start_pos = self.offset_start_pos();
        debug_assert!(
            offset_start_pos < self.len(),
            "Time offset should not be empty"
        );
        debug_assert_ok!(PartialTimeStr::from_bytes(&self.0[..offset_start_pos]));
        debug_assert_ok!(TimeOffsetStr::from_bytes(&self.0[offset_start_pos..]));
        let (partial_time, offset) = self.0.split_at_mut(offset_start_pos);

        unsafe {
            // This is safe because a `full-time` string has a `partial-time`
            // followed by `time-offset`, and `PartialTimeStr` ensures that the
            // underlying bytes are ASCII string after modification.
            let partial_time = PartialTimeStr::from_bytes_maybe_unchecked_mut(partial_time);
            // This is safe because a `full-time` string has a `time-offset`
            // suffix following `partial-time`, and `TimeOffsetStr` ensures
            // that the underlying bytes are ASCII string after modification.
            let offset = TimeOffsetStr::from_bytes_maybe_unchecked_mut(offset);

            (partial_time, offset)
        }
    }

    /// Returns a `&PartialTimeStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// let time = FullTimeStr::from_str("12:34:56.7890-23:12")?;
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// let partial_time = time.partial_time();
    /// assert_eq!(partial_time.as_str(), "12:34:56.7890");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn partial_time(&self) -> &PartialTimeStr {
        let offset_start_pos = self.offset_start_pos();
        debug_assert!(offset_start_pos < self.0.len());
        unsafe {
            debug_assert_safe_version_ok!(PartialTimeStr::from_bytes(&self.0[..offset_start_pos]));
            // This is safe because `offset_start_pos` is always less than the string length.
            let s = self.0.get_unchecked(..offset_start_pos);
            // This is safe because a `full-time` string has a `partial-time`
            // followed by `time-offset`.
            PartialTimeStr::from_bytes_maybe_unchecked(s)
        }
    }

    /// Returns a `&mut PartialTimeStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// use datetime_string::common::TimeOffsetSign;
    ///
    /// let mut buf = "12:34:56.7890-23:12".to_owned();
    /// let time = FullTimeStr::from_mut_str(&mut buf)?;
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// let partial_time = time.partial_time_mut();
    /// assert_eq!(partial_time.as_str(), "12:34:56.7890");
    ///
    /// partial_time.secfrac_mut().unwrap().digits_mut().fill_with_zero();
    /// assert_eq!(time.as_str(), "12:34:56.0000-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn partial_time_mut(&mut self) -> &mut PartialTimeStr {
        let offset_start_pos = self.offset_start_pos();
        debug_assert!(offset_start_pos < self.0.len());
        unsafe {
            debug_assert_ok!(PartialTimeStr::from_bytes(&self.0[..offset_start_pos]));
            // This is safe because `offset_start_pos` is always less than the string length.
            let s = self.0.get_unchecked_mut(..offset_start_pos);
            // This is safe because a `full-time` string has a `partial-time`
            // followed by `time-offset`, and `PartialTimeStr` ensures that the
            // underlying bytes are ASCII string after modification.
            PartialTimeStr::from_bytes_maybe_unchecked_mut(s)
        }
    }

    /// Returns a `&TimeOffsetStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// let time = FullTimeStr::from_str("12:34:56.7890-23:12")?;
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// let offset = time.offset();
    /// assert_eq!(offset.as_str(), "-23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn offset(&self) -> &TimeOffsetStr {
        let offset_start_pos = self.offset_start_pos();
        debug_assert!(offset_start_pos < self.0.len());
        unsafe {
            debug_assert_safe_version_ok!(TimeOffsetStr::from_bytes(&self.0[offset_start_pos..]));
            // This is safe because `offset_start_pos` is always less than the string length.
            let s = self.0.get_unchecked(offset_start_pos..);
            // This is safe because a `full-time` string has a `time-offset`
            // suffix following `partial-time`.
            TimeOffsetStr::from_bytes_maybe_unchecked(s)
        }
    }

    /// Returns a `&mut PartialTimeStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::FullTimeStr;
    /// use datetime_string::common::TimeOffsetSign;
    ///
    /// let mut buf = "12:34:56.7890-23:12".to_owned();
    /// let time = FullTimeStr::from_mut_str(&mut buf)?;
    /// assert_eq!(time.as_str(), "12:34:56.7890-23:12");
    ///
    /// let offset = time.offset_mut();
    /// assert_eq!(offset.as_str(), "-23:12");
    ///
    /// offset.to_numoffset_mut().unwrap().set_sign(TimeOffsetSign::Positive);
    /// assert_eq!(time.as_str(), "12:34:56.7890+23:12");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn offset_mut(&mut self) -> &mut TimeOffsetStr {
        let offset_start_pos = self.offset_start_pos();
        debug_assert!(offset_start_pos < self.0.len());
        unsafe {
            debug_assert_ok!(TimeOffsetStr::from_bytes(&self.0[offset_start_pos..]));
            // This is safe because `offset_start_pos` is always less than the string length.
            let s = self.0.get_unchecked_mut(offset_start_pos..);
            // This is safe because a `full-time` string has a `time-offset`
            // suffix following `partial-time`, and `TimeOffsetStr` ensures
            // that the underlying bytes are ASCII string after modification.
            TimeOffsetStr::from_bytes_maybe_unchecked_mut(s)
        }
    }
}

impl AsRef<[u8]> for FullTimeStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for FullTimeStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<FullTimeStr> for FullTimeStr {
    #[inline]
    fn as_ref(&self) -> &FullTimeStr {
        self
    }
}

impl AsMut<FullTimeStr> for FullTimeStr {
    #[inline]
    fn as_mut(&mut self) -> &mut FullTimeStr {
        self
    }
}

impl<'a> From<&'a FullTimeStr> for &'a str {
    #[inline]
    fn from(v: &'a FullTimeStr) -> Self {
        v.as_str()
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a FullTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid `full-time` string is also an ASCII string.
            FullTimeStr::from_bytes_maybe_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut FullTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid `full-time` string is also an ASCII string.
            FullTimeStr::from_bytes_maybe_unchecked_mut(v)
        })
    }
}

impl<'a> TryFrom<&'a str> for &'a FullTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a str) -> Result<Self, Self::Error> {
        Self::try_from(v.as_bytes())
    }
}

impl<'a> TryFrom<&'a mut str> for &'a mut FullTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because a valid `full-time` string is also an ASCII
            // string, and `FullTimeStr` ensures that the value after
            // modification is still an ASCII string.
            FullTimeStr::from_str_maybe_unchecked_mut(v)
        })
    }
}

impl fmt::Display for FullTimeStr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl ops::Deref for FullTimeStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl_cmp_symmetric!(str, FullTimeStr, &FullTimeStr);
impl_cmp_symmetric!([u8], FullTimeStr, [u8]);
impl_cmp_symmetric!([u8], FullTimeStr, &[u8]);
impl_cmp_symmetric!([u8], &FullTimeStr, [u8]);
impl_cmp_symmetric!(str, FullTimeStr, str);
impl_cmp_symmetric!(str, FullTimeStr, &str);
impl_cmp_symmetric!(str, &FullTimeStr, str);

#[cfg(feature = "serde")]
impl Serialize for FullTimeStr {
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

    /// Visitor for `&FullTimeStr`.
    struct StrVisitor;

    impl<'de> Visitor<'de> for StrVisitor {
        type Value = &'de FullTimeStr;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 full-time string")
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

    impl<'de> Deserialize<'de> for &'de FullTimeStr {
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
        assert!(s_validate(b"12:34:56Z").is_ok());
        assert!(s_validate(b"12:34:56-00:00").is_ok());
        assert!(s_validate(b"12:34:56-12:30").is_ok());
        assert!(s_validate(b"12:34:56-23:59").is_ok());
        assert!(s_validate(b"12:34:56+00:00").is_ok());
        assert!(s_validate(b"12:34:56+12:30").is_ok());
        assert!(s_validate(b"12:34:56+23:59").is_ok());

        assert!(s_validate(b"00:00:00-00:00").is_ok());
        assert!(s_validate(b"23:59:59-00:00").is_ok());

        assert!(s_validate(b"12:34:56.7890Z").is_ok());
        assert!(s_validate(b"12:34:56.7890-00:00").is_ok());
        assert!(s_validate(b"12:34:56.7890+00:00").is_ok());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_str() {
        let raw: &'static str = "12:34:56.7890-23:12";
        assert_tokens(
            &FullTimeStr::from_str(raw).unwrap(),
            &[Token::BorrowedStr(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes_slice() {
        let raw: &'static [u8] = b"12:34:56.7890-23:12";
        assert_de_tokens(
            &FullTimeStr::from_bytes(raw).unwrap(),
            &[Token::BorrowedBytes(raw)],
        );
    }
}
