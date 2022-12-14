//! Contains all error-related functionality of the crate.

use {
    crate::{DateTime, Sha1Hash},
    core::fmt::{self, Display},
    std::io,
    thiserror::Error,
};

/// Data that is required to exist exactly once in a `leap-seconds.list` file.
///
/// If that is not the case, an attempt to parse the file will result in a [`ParseFileError`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DataComponent {
    /// A line containing a timestamp when the file was updated last.
    LastUpdate,

    /// A timestamp at which the data in the file expires.
    ExpirationDate,

    /// A hash of the data contained in the file.
    Hash,
}

impl Display for DataComponent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let result = match self {
            Self::LastUpdate => "last update",
            Self::ExpirationDate => "expiration date",
            Self::Hash => "hash",
        };

        write!(f, "{result}")
    }
}

/// Indicates that a `leap-seconds.list` file could not be parsed successfully.
#[derive(Debug, Error)]
pub enum ParseFileError {
    /// An IO error occurred in the underlying stream.
    #[error(transparent)]
    IoError(#[from] io::Error),

    /// A line in the file could not be parsed successfully.
    ///
    /// See [`ParseLineError`] for further information.
    #[error(transparent)]
    ParseLineError(#[from] ParseLineError),

    /// The hash that was calculated did not match the one that was found in the file.
    #[error("incorrect hash: calculated = {calculated}, found = {found}")]
    InvalidHash {
        /// The hash that was calculated from the contents of the file.
        calculated: Sha1Hash,
        /// The hash that was found in the file.
        found: Sha1Hash,
    },

    /// The given file is incomplete. Required data could not be found in the file.
    #[error("missing data: {0}")]
    MissingData(DataComponent),

    /// The file contains duplicate data.
    #[error("duplicate data on lines {line1} and {line2}: {data_component}")]
    DuplicateData {
        /// The type of data that was found twice.
        data_component: DataComponent,
        /// The first line the data was found on.
        line1: usize,
        /// The second line the data was found on.
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

/// The error that occurs when a line of a `leap-seconds.list` file could not be parsed.
#[derive(Debug, Error)]
pub struct ParseLineError {
    pub(crate) cause: ParseLineErrorKind,
    pub(crate) line: String,
    pub(crate) line_number: usize,
}

impl ParseLineError {
    /// Gets what caused this error.
    #[must_use]
    pub const fn cause(&self) -> ParseLineErrorKind {
        self.cause
    }

    /// Gets the line that caused this error.
    #[must_use]
    pub fn line(&self) -> &str {
        &self.line
    }

    /// Gets the line number at which this error occured.
    #[must_use]
    pub const fn line_number(&self) -> usize {
        self.line_number
    }
}

impl Display for ParseLineError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} on line {}: \"{}\"",
            self.cause, self.line_number, self.line
        )
    }
}

/// Reasons that could cause a line to not be parsed successfully.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ParseLineErrorKind {
    /// A timestamp is incorrectly formatted.
    InvalidTimestamp,

    /// A line describing a leap second is incorrectly formatted.
    InvalidLeapSecondLine,

    /// The [TAI]-[UTC] difference on a line describing a leap second is incorrectly formatted.
    ///
    /// [TAI]: https://en.wikipedia.org/wiki/International_Atomic_Time
    /// [UTC]: https://en.wikipedia.org/wiki/Coordinated_Universal_Time
    InvalidTaiDiff,

    /// The line containing the hash of the data is incorrectly formatted.
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
