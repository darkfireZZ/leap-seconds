//! Contains all error-related functionality of the crate.

use {
    crate::{DataComponent, DateTime, Sha1Hash},
    core::fmt::{self, Display},
    std::io,
    thiserror::Error,
};

#[derive(Debug, Error)]
pub enum ParseFileError {
    #[error(transparent)]
    IoError(#[from] io::Error),
    #[error(transparent)]
    ParseLineError(#[from] ParseLineError),
    #[error("incorrect hash: calculated = {calculated}, found = {found}")]
    InvalidHash {
        calculated: Sha1Hash,
        found: Sha1Hash,
    },
    #[error("missing data: {0}")]
    MissingData(DataComponent),
    #[error("duplicate data on lines {line1} and {line2}: {data_component}")]
    DuplicateData {
        data_component: DataComponent,
        line1: usize,
        line2: usize,
    },
}

/// Indicates an attempt to create an invalid [`Date`](crate::Date).
///
/// ```
/// use leap_seconds::{Date, InvalidDate};
///
/// // November only has 30 days
/// let error = Date::new(2000, 11, 31);
///
/// assert_eq!(error, Err(InvalidDate::DayOutOfRange(31)));
/// ```
#[derive(Clone, Debug, Error, Eq, PartialEq)]
pub enum InvalidDate {
    /// Indicates that the day was out of range.
    #[error("day out of range: {0}")]
    MonthOutOfRange(u8),
    /// Indicates that the month was out of range.
    #[error("month out of range: {0}")]
    DayOutOfRange(u8),
}

/// Indicates and attempt to create an invalid [`Time`](crate::Time).
///
/// ```
/// use leap_seconds::{Time, InvalidTime};
///
/// // A time with 60 seconds is invalid
/// let error = Time::new(18, 42, 60);
///
/// assert_eq!(error, Err(InvalidTime::SecondsOutOfRange(60)));
/// ```
#[derive(Clone, Copy, Debug, Error, Eq, PartialEq)]
pub enum InvalidTime {
    /// Indicates that the hours were out of range.
    #[error("hours out of range: {0}")]
    HoursOutOfRange(u8),
    /// Indicates that the minutes were out of range.
    #[error("minutes out of range: {0}")]
    MinutesOutOfRange(u8),
    /// Indicates that the seconds were out of range.
    #[error("seconds out of range: {0}")]
    SecondsOutOfRange(u8),
}

/// Occurs if a [`DateTime`] is not representable as a [`Timestamp`].
///
/// See [`Timestamp::MAX_REPRESENTABLE_DATE_TIME`] and [`Timestamp::MIN_REPRESENTABLE_DATE_TIME`]
/// for the latest and the earliest [`DateTime`] respectively that can be represented as a
/// [`Timestamp`].
///
/// ```
/// # use std::error::Error;
/// use leap_seconds::{
///     Date, DateTime, Time, Timestamp,
///     errors::DateTimeNotRepresentable,
/// };
///
/// let date_time = DateTime {
///     date: Date::new(1234, 5, 6)?,
///     time: Time::new(7, 8, 9)?,
/// };
///
/// let error: DateTimeNotRepresentable = Timestamp::from_date_time(date_time).unwrap_err();
/// assert_eq!(error.date_time(), date_time);
/// #
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// [`Timestamp`]: crate::Timestamp
/// [`Timestamp::MAX_REPRESENTABLE_DATE_TIME`]: crate::Timestamp::MAX_REPRESENTABLE_DATE_TIME
/// [`Timestamp::MIN_REPRESENTABLE_DATE_TIME`]: crate::Timestamp::MIN_REPRESENTABLE_DATE_TIME
#[derive(Clone, Debug, Error, Eq, PartialEq)]
pub struct DateTimeNotRepresentable {
    pub(crate) date_time: DateTime,
}

impl DateTimeNotRepresentable {
    /// Gets the [`DateTime`] that could not be represented as a [`Timestamp`].
    ///
    /// [`Timestamp`]: crate::Timestamp
    #[must_use]
    pub const fn date_time(self) -> DateTime {
        self.date_time
    }
}

impl Display for DateTimeNotRepresentable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DateTime is not representable as 64-bit timestamp")
    }
}

#[derive(Debug, Error)]
pub struct ParseLineError {
    pub(crate) kind: ParseLineErrorKind,
    pub(crate) line: String,
    pub(crate) line_number: usize,
}

impl Display for ParseLineError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} on line {}: \"{}\"",
            self.kind, self.line_number, self.line
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ParseLineErrorKind {
    InvalidTimestamp,
    InvalidLeapSecondLine,
    InvalidTaiDiff,
    InvalidHash,
}

impl Display for ParseLineErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let output = match self {
            Self::InvalidTimestamp => "invalid timestamp",
            Self::InvalidLeapSecondLine => "invalid leapsecond line",
            Self::InvalidTaiDiff => "invalid TAI difference",
            Self::InvalidHash => "invalid hash",
        };

        write!(f, "{output}")
    }
}
