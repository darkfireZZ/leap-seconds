use {
    std::{num::IntErrorKind, str::FromStr},
    thiserror::Error,
};

pub enum Line {
    Comment(Comment),
    LeapSecondInfo(LeapSecondInfo),
}

impl FromStr for Line {
    type Err = ParseTzdbError;
    fn from_str(line: &str) -> Result<Self, Self::Err> {
        match line.parse::<Comment>() {
            Ok(line) => return Ok(Self::Comment(line)),
            Err(ParseLineError::ParseFailure) => (),
            Err(ParseLineError::BadFormat(_err)) => return Err(ParseTzdbError::Failed),
        }

        match line.parse::<LeapSecondInfo>() {
            Ok(line) => return Ok(Self::LeapSecondInfo(line)),
            Err(ParseLineError::ParseFailure) => (),
            Err(ParseLineError::BadFormat(_err)) => return Err(ParseTzdbError::Failed),
        }

        Err(ParseTzdbError::Failed)
    }
}

impl From<LeapSecondInfo> for Line {
    fn from(leap_second_info: LeapSecondInfo) -> Self {
        Self::LeapSecondInfo(leap_second_info)
    }
}

impl From<Comment> for Line {
    fn from(comment: Comment) -> Self {
        Self::Comment(comment)
    }
}

pub struct LeapSecondInfo {
    // TODO make private again
    // timestamp (in seconds since 1900-01-01)
    pub timestamp: u64,
    pub tai_diff: u16,
}

impl FromStr for LeapSecondInfo {
    type Err = ParseLineError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let splits = s.split_whitespace().collect::<Vec<_>>();

        if splits.len() < 2 {
            return Err(ParseLineError::BadFormat(
                BadFormatError::InvalidLeapSecondInfo,
            ));
        }

        let timestamp = splits[0].parse::<u64>().map_err(|err| {
            if err.kind() == &IntErrorKind::PosOverflow {
                BadFormatError::TimestampOutOfRange
            } else {
                BadFormatError::InvalidLeapSecondInfo
            }
        })?;
        let tai_diff = splits[1].parse::<u16>().map_err(|err| {
            if err.kind() == &IntErrorKind::PosOverflow {
                BadFormatError::TaiDiffOutOfRange
            } else {
                BadFormatError::InvalidLeapSecondInfo
            }
        })?;

        // TODO also validate the rest is valid

        Ok(Self {
            timestamp,
            tai_diff,
        })
    }
}

pub struct Comment {
    text: String,
}

impl FromStr for Comment {
    type Err = ParseLineError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("#") {
            Ok(Comment {
                text: s.get(2..).unwrap_or("").to_owned(),
            })
        } else {
            Err(ParseLineError::ParseFailure)
        }
    }
}

#[derive(Debug, Error)]
pub enum ParseTzdbError {
    #[error("failed to parse leap-seconds.list")]
    Failed,
}

// TODO make private
#[derive(Debug, Error)]
pub enum ParseLineError {
    // TODO better message
    #[error("failed to parse correctly")]
    ParseFailure,
    #[error(transparent)]
    BadFormat(#[from] BadFormatError),
}

// TODO make private
#[derive(Debug, Error)]
pub enum BadFormatError {
    #[error("badly formatted leap second info line")]
    InvalidLeapSecondInfo,
    #[error("timestamp out of range")]
    TimestampOutOfRange,
    #[error("TAI difference out of range")]
    TaiDiffOutOfRange,
}
