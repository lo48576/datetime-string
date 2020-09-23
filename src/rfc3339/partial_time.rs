//! RFC 3339 [`partial-time`] string types.
//!
//! [`partial-time`]: https://tools.ietf.org/html/rfc3339#section-5.6

#[cfg(feature = "alloc")]
mod owned;

use core::{cmp::Ordering, convert::TryFrom, fmt, ops, str};

use crate::{
    common::Hms6ColonStr,
    error::{Error, ErrorKind},
    rfc3339::SecfracStr,
};

#[cfg(feature = "alloc")]
pub use self::owned::PartialTimeString;

/// Minimum length of `partial-time` string (i.e. length of `hh:mm:ss`).
const PARTIAL_TIME_LEN_MIN: usize = 8;

/// Validates the given string as an RFC 3339 [`partial-time`] string.
///
/// [`partial-time`]: https://tools.ietf.org/html/rfc3339#section-5.6
fn validate_bytes(s: &[u8]) -> Result<(), Error> {
    let (hms, dotfrac) = match s.len().cmp(&PARTIAL_TIME_LEN_MIN) {
        Ordering::Greater => s.split_at(PARTIAL_TIME_LEN_MIN),
        Ordering::Less => return Err(ErrorKind::TooShort.into()),
        Ordering::Equal => return Hms6ColonStr::from_bytes(s).map(|_| ()),
    };
    debug_assert!(
        !dotfrac.is_empty(),
        "If `dotfrac` component is available, it should be non-empty string"
    );

    Hms6ColonStr::from_bytes(hms)?;
    SecfracStr::from_bytes(dotfrac)?;

    Ok(())
}

/// String slice for a time in RFC 3339 [`partial-time`] format, such as `12:34:56.7890`.
///
/// This is "partial", because it is not associated to a time offset.
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
pub struct PartialTimeStr([u8]);

impl PartialTimeStr {
    /// Creates a `&PartialTimeStr` from the given byte slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_bytes_unchecked(s: &[u8]) -> &Self {
        &*(s as *const [u8] as *const Self)
    }

    /// Creates a `&mut PartialTimeStr` from the given mutable byte slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s)` should return `Ok(())`.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_bytes_unchecked_mut(s: &mut [u8]) -> &mut Self {
        &mut *(s as *mut [u8] as *mut Self)
    }

    /// Creates a `&mut PartialTimeStr` from the given mutable string slice.
    ///
    /// # Safety
    ///
    /// `validate_bytes(s.as_bytes())` should return `Ok(())`.
    #[inline]
    #[must_use]
    unsafe fn from_str_unchecked_mut(s: &mut str) -> &mut Self {
        // This is safe because `PartialTimeStr` ensures that the underlying
        // bytes are ASCII string after modification.
        Self::from_bytes_unchecked_mut(s.as_bytes_mut())
    }

    /// Creates a new `&PartialTimeStr` from a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::PartialTimeStr;
    /// let time = PartialTimeStr::from_str("12:34:56.7890")?;
    /// assert_eq!(time.as_str(), "12:34:56.7890");
    ///
    /// assert!(PartialTimeStr::from_str("12:34:56").is_ok());
    /// assert!(PartialTimeStr::from_str("12:34:56.0").is_ok());
    /// assert!(PartialTimeStr::from_str("12:34:56.01234567890").is_ok());
    ///
    /// assert!(PartialTimeStr::from_str("12:34:56.").is_err());
    /// assert!(PartialTimeStr::from_str(".").is_err());
    /// assert!(PartialTimeStr::from_str("12:34.56").is_err());
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    // `FromStr` trait cannot be implemented for a slice.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut PartialTimeStr` from a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::PartialTimeStr;
    /// let mut buf = "12:34:56.7890".to_owned();
    /// let time = PartialTimeStr::from_mut_str(&mut buf)?;
    /// assert_eq!(time.as_str(), "12:34:56.7890");
    ///
    /// time.hms_mut().set_time(23, 12, 01);
    /// time.secfrac_mut().unwrap().digits_mut().fill_with_zero();
    /// assert_eq!(time.as_str(), "23:12:01.0000");
    ///
    /// assert_eq!(buf, "23:12:01.0000");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_mut_str(s: &mut str) -> Result<&mut Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&PartialTimeStr` from a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::PartialTimeStr;
    /// let time = PartialTimeStr::from_bytes(b"12:34:56.7890")?;
    /// assert_eq!(time.as_str(), "12:34:56.7890");
    ///
    /// assert!(PartialTimeStr::from_bytes(b"12:34:56").is_ok());
    /// assert!(PartialTimeStr::from_bytes(b"12:34:56.0").is_ok());
    /// assert!(PartialTimeStr::from_bytes(b"12:34:56.01234567890").is_ok());
    ///
    /// assert!(PartialTimeStr::from_bytes(b"12:34:56.").is_err());
    /// assert!(PartialTimeStr::from_bytes(b".").is_err());
    /// assert!(PartialTimeStr::from_bytes(b"12:34.56").is_err());
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    pub fn from_bytes(s: &[u8]) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&mut PartialTimeStr` from a mutable byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::PartialTimeStr;
    /// let mut buf: [u8; 13] = *b"12:34:56.7890";
    /// let time = PartialTimeStr::from_bytes_mut(&mut buf)?;
    /// assert_eq!(time.as_str(), "12:34:56.7890");
    ///
    /// time.hms_mut().set_time(23, 12, 01);
    /// time.secfrac_mut().unwrap().digits_mut().fill_with_zero();
    /// assert_eq!(time.as_str(), "23:12:01.0000");
    ///
    /// assert_eq!(&buf[..], b"23:12:01.0000");
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
    /// # use datetime_string::rfc3339::PartialTimeStr;
    /// let time = PartialTimeStr::from_str("12:34:56.7890")?;
    ///
    /// assert_eq!(time.as_str(), "12:34:56.7890");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        unsafe {
            // This is safe because the `PartialTimeStr` ensures that the
            // underlying bytes are ASCII string.
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
    /// # use datetime_string::rfc3339::PartialTimeStr;
    /// let time = PartialTimeStr::from_str("12:34:56.7890")?;
    ///
    /// assert_eq!(time.as_str(), "12:34:56.7890");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    ///
    /// [`as_bytes_fixed_len`]: #method.as_bytes_fixed_len
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Returns a `hh:mm:ss` substring.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::PartialTimeStr;
    /// let time = PartialTimeStr::from_str("12:34:56.7890")?;
    ///
    /// assert_eq!(time.hms(), "12:34:56");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn hms(&self) -> &Hms6ColonStr {
        unsafe {
            // This is safe because a valid partial-time string has `hh:mm:ss` as a prefix.
            Hms6ColonStr::from_bytes_unchecked(self.0.get_unchecked(..PARTIAL_TIME_LEN_MIN))
        }
    }

    /// Returns a mutable `hh:mm:ss` substring.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::PartialTimeStr;
    /// let mut buf = "12:34:56.7890".to_owned();
    /// let time = PartialTimeStr::from_mut_str(&mut buf)?;
    /// assert_eq!(time.as_str(), "12:34:56.7890");
    ///
    /// time.hms_mut().set_time(23, 12, 1);
    /// assert_eq!(time.as_str(), "23:12:01.7890");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn hms_mut(&mut self) -> &mut Hms6ColonStr {
        unsafe {
            // This is safe because a valid partial-time string has `hh:mm:ss`
            // as a prefix, and `Hms6ColonStr` ensures that the underlying bytes
            // are ASCII string after modification.
            Hms6ColonStr::from_bytes_unchecked_mut(self.0.get_unchecked_mut(..PARTIAL_TIME_LEN_MIN))
        }
    }

    /// Returns [`time-secfrac`] substring.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::PartialTimeStr;
    /// let time = PartialTimeStr::from_str("12:34:56.7890")?;
    ///
    /// assert_eq!(time.secfrac().unwrap(), ".7890");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    ///
    /// [`time-secfrac`]: https://tools.ietf.org/html/rfc3339#section-5.6
    #[inline]
    #[must_use]
    pub fn secfrac(&self) -> Option<&SecfracStr> {
        self.0.get(PARTIAL_TIME_LEN_MIN..).map(|v| {
            unsafe {
                // This is safe because a valid partial-time string which is longer than
                // PARTIAL_TIME_LEN_MIN (== "hh:mm:ss".len()) has time-secfrac as a prefix.
                SecfracStr::from_bytes_unchecked(v)
            }
        })
    }

    /// Returns a mutable [`time-secfrac`] substring.
    ///
    /// # Examples
    ///
    /// ```
    /// # use datetime_string::rfc3339::PartialTimeStr;
    /// let mut buf = "12:34:56.7890".to_owned();
    /// let time = PartialTimeStr::from_mut_str(&mut buf)?;
    /// assert_eq!(time.as_str(), "12:34:56.7890");
    ///
    /// time.hms_mut().set_time(23, 12, 1);
    /// assert_eq!(time.as_str(), "23:12:01.7890");
    /// # Ok::<_, datetime_string::Error>(())
    /// ```
    ///
    /// [`time-secfrac`]: https://tools.ietf.org/html/rfc3339#section-5.6
    #[inline]
    #[must_use]
    pub fn secfrac_mut(&mut self) -> Option<&mut SecfracStr> {
        unsafe {
            // This is safe because a valid partial-time string which is longer than
            // PARTIAL_TIME_LEN_MIN (== "hh:mm:ss".len()) has time-secfrac as a prefix,
            // and `SecfracStr` ensures that the underlying bytes are ASCII string
            // after modification.
            self.0
                .get_mut(PARTIAL_TIME_LEN_MIN..)
                .map(|v| SecfracStr::from_bytes_unchecked_mut(v))
        }
    }
}

#[cfg(feature = "alloc")]
impl alloc::borrow::ToOwned for PartialTimeStr {
    type Owned = PartialTimeString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl AsRef<[u8]> for PartialTimeStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsRef<str> for PartialTimeStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<PartialTimeStr> for PartialTimeStr {
    #[inline]
    fn as_ref(&self) -> &PartialTimeStr {
        self
    }
}

impl AsMut<PartialTimeStr> for PartialTimeStr {
    #[inline]
    fn as_mut(&mut self) -> &mut PartialTimeStr {
        self
    }
}

impl<'a> From<&'a PartialTimeStr> for &'a str {
    #[inline]
    fn from(v: &'a PartialTimeStr) -> Self {
        v.as_str()
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a PartialTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid `partial-time` string is also an ASCII string.
            PartialTimeStr::from_bytes_unchecked(v)
        })
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut PartialTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut [u8]) -> Result<Self, Self::Error> {
        validate_bytes(v)?;
        Ok(unsafe {
            // This is safe because a valid `partial-time` string is also an ASCII string.
            PartialTimeStr::from_bytes_unchecked_mut(v)
        })
    }
}

impl<'a> TryFrom<&'a str> for &'a PartialTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a str) -> Result<Self, Self::Error> {
        Self::try_from(v.as_bytes())
    }
}

impl<'a> TryFrom<&'a mut str> for &'a mut PartialTimeStr {
    type Error = Error;

    #[inline]
    fn try_from(v: &'a mut str) -> Result<Self, Self::Error> {
        validate_bytes(v.as_bytes())?;
        Ok(unsafe {
            // This is safe because the string is already validated and
            // `PartialTimeStr` ensures that the underlying bytes are ASCII
            // string after modification.
            PartialTimeStr::from_str_unchecked_mut(v)
        })
    }
}

impl fmt::Display for PartialTimeStr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl ops::Deref for PartialTimeStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl_cmp_symmetric!(str, PartialTimeStr, &PartialTimeStr);
impl_cmp_symmetric!([u8], PartialTimeStr, [u8]);
impl_cmp_symmetric!([u8], PartialTimeStr, &[u8]);
impl_cmp_symmetric!([u8], &PartialTimeStr, [u8]);
impl_cmp_symmetric!(str, PartialTimeStr, str);
impl_cmp_symmetric!(str, PartialTimeStr, &str);
impl_cmp_symmetric!(str, &PartialTimeStr, str);

#[cfg(feature = "serde")]
impl serde::Serialize for PartialTimeStr {
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

    /// Visitor for `&PartialTimeStr`.
    struct StrVisitor;

    impl<'de> Visitor<'de> for StrVisitor {
        type Value = &'de PartialTimeStr;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("RFC 3339 partial-time string")
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

    impl<'de> Deserialize<'de> for &'de PartialTimeStr {
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
        assert!(s_validate(b"00:00:00").is_ok());
        assert!(s_validate(b"00:00:00.0000").is_ok());
        assert!(s_validate(b"00:00:00.00000000000").is_ok());
        assert!(s_validate(b"12:34:56.7890").is_ok());
        assert!(s_validate(b"23:59:60").is_ok());
        assert!(s_validate(b"23:59:60.9999").is_ok());
        assert!(s_validate(b"23:59:60.01234567890").is_ok());
        assert!(s_validate(b"23:59:60.99999999999").is_ok());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn ser_de_str() {
        let raw: &'static str = "12:34:56.7890";
        assert_tokens(
            &PartialTimeStr::from_str(raw).unwrap(),
            &[Token::BorrowedStr(raw)],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn de_bytes_slice() {
        let raw: &'static [u8; 13] = b"12:34:56.7890";
        assert_de_tokens(
            &PartialTimeStr::from_bytes(raw).unwrap(),
            &[Token::BorrowedBytes(raw)],
        );
    }
}
