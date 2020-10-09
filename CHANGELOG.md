# Change Log

## [Unreleased]


## [0.2.1]

* Added `chrono` v0.4 integration.
    + Enabled by `chrono04` feature.

### Added

* Added `chrono` v0.4 integration (31f6771961a60834643ee356b6a0cead6fa45677).
    + Enabled by `chrono04` feature.
    + Note that some conversions are lossy (truncates subnanosecond for example).
    + `common::Hms6ColonStr{,ing}` and `chrono::NaiveTime`
        - `From<&common::Hms6ColonStr> for chrono::NaiveTime`
        - `From<&chrono::NaiveTime> for common::Hms6ColonString`
    + `common::TimeNumOffsetColonStr{,ing}` and `chrono::FixedOffset`
        - `From<&common::TimeNumOffsetColonStr> for chrono::FixedOffset`
        - `TryFrom<&chrono::FixedOffset> for common::TimeNumOffsetColonStr`
            * Note that `chrono::FixedOffset` can have non-zero seconds (such as `+01:23:45`),
              but this is not allowed for `common::TimeNumOffsetColonStr{,ing}`.
    + `common::Ymd8HyphenStr{,ing}` and `chrono::NaiveDate`
        - `From<&common::Ymd8HyphenStr> for chrono::NaiveDate`
        - `TryFrom<&chrono::NaiveDate> for common::Ymd8HyphenString`
            * Note that `chrono::NaiveDate` can have year which is less than
              zero or larger than 9999, but this is not allowed for
              `common::Ymd8HyphenStr{,ing}`.
    + `rfc3339::DateTimeStr` and `chrono::DateTime<chrono::FixedOffset>`
        - `rfc3339::DateTimeStr::to_chrono_date_time(&self) -> chrono::DateTime<chrono::FixedOffset>`
    + `rfc3339::TimeOffsetStr` and `chrono::FixedOffset`
        - `From<&rfc3339::TimeOffsetStr> for chrono::FixedOffset`
    + `rfc3339::PartialTimeStr` and `chrono::NaiveTime`
        - `rfc3339::PartialTimeStr::to_chrono_naive_time(&self) -> chrono::NaiveTime`


## [0.2.0]

* Now `TryFrom<Vec<u8>> for {OwnedString}` impls uses `ConversionError<Vec<u8>>`
  as an error type, instead of `Error` (4353b833860cbbf92e708cf9ddf55103ab059386).
* `TryFrom<String> for {VariableLengthOwnedString}` impls are added.
* Added `assign` method to fixed length string slice types
  (`common::{Hms6ColonStr, TimeNumOffsetColonStr, Ymd8HyphenStr}`)
  (d4de91e7abbad0cd13a45da48efe698c1b2e5d57).
* Added `Hms6ColonStr::to_seconds` method (66448be35bf51bc37589855dc2084cf706e69a03).
* Added `Ymd8HyphenStr::{days_since_epoch, yday0, yday1}` methods
  (66448be35bf51bc37589855dc2084cf706e69a03).
* Added value creation methods and trait impls (6feb20ae2c9efebb34ccf18a5ce333383fa768f0).
* Improve doc comments.

### Added

* `TryFrom<String> for {VariableLengthOwnedString}` impls are added.
* Added `assign` method to fixed length string slice types
  (`common::{Hms6ColonStr, TimeNumOffsetColonStr, Ymd8HyphenStr}`).
* Added `Hms6ColonStr::to_seconds` method.
* Added `Ymd8HyphenStr::{days_since_epoch, yday0, yday1}` methods.
* Added value creation methods and trait impls.
    + `common::Hms6ColonString`
        - `from_hms()`
    + `common::Ymd8HyphenString`
        - `from_ym0d()`, `from_ym1d()`
    + `common::TimeNumOffsetColonString`
        - `utc()`, `unknown_local_offset()`, `from_minutes()`,
          `from_sign_and_hm()`, `from_hm_signed()`
    + `rfc3339::TimeOffsetString`
        - `z()`, `unknown_local_offset()`, `from_minutes()`,
          `from_sign_and_hm()`, `from_hm_signed()`
        - `From<&common::TimeNumOffsetColonStr{,ing}> for rfc3339::TimeOffsetString`

### Breaking changes

* Now `TryFrom<Vec<u8>> for {OwnedString}` impls uses `ConversionError<Vec<u8>>`
  as an error type, instead of `Error`.
    + A pair of `Error` and `ConversionError<T>` is quite similar to
      `std::str::Utf8Error` and `std::string::FromUtf8Error`.
      `ConversionError<T>` allows users to get the value back without extra
      allocation overhead, when it is not convertible to the target type.


## [0.1.0]

Initial release.

Mainly RFC 3339 datetime types are supported.


[Unreleased]: <https://github.com/lo48576/fbxcel/compare/v0.2.1...develop>
[0.2.1]: <https://github.com/lo48576/fbxcel/releases/tag/v0.2.1>
[0.2.0]: <https://github.com/lo48576/fbxcel/releases/tag/v0.2.0>
[0.1.0]: <https://github.com/lo48576/fbxcel/releases/tag/v0.1.0>
