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

#[derive(Clone, Debug, Error, Eq, PartialEq)]
pub enum InvalidDate {
    #[error("day out of range: {0}")]
    MonthOutOfRange(u8),
    #[error("month out of range: {0}")]
    DayOutOfRange(u8),
}

#[derive(Clone, Copy, Debug, Error, Eq, PartialEq)]
pub enum InvalidTime {
    #[error("hours out of range: {0}")]
    HoursOutOfRange(u8),
    #[error("minutes out of range: {0}")]
    MinutesOutOfRange(u8),
    #[error("seconds out of range: {0}")]
    SecondsOutOfRange(u8),
}

#[derive(Clone, Debug, Error, Eq, PartialEq)]
pub struct DateTimeNotRepresentable(pub(crate) DateTime);

impl DateTimeNotRepresentable {
    #[must_use]
    pub fn date_time(self) -> DateTime {
        self.0
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
