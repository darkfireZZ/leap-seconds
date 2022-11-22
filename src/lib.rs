use {
    core::fmt::{self, Display},
    sha1::{Digest, Sha1},
    std::io::{self, BufRead},
    thiserror::Error,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DataComponent {
    LastUpdate,
    ExpirationDate,
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

const SECONDS_PER_MINUTE: u64 = 60;
const MINUTES_PER_HOUR: u64 = 60;
const HOURS_PER_DAY: u64 = 24;

const SECONDS_PER_HOUR: u64 = MINUTES_PER_HOUR * SECONDS_PER_MINUTE;
const SECONDS_PER_DAY: u64 = HOURS_PER_DAY * SECONDS_PER_HOUR;

const JANUARY: u64 = 1;
const FEBRUARY: u64 = 2;
const MARCH: u64 = 3;
const APRIL: u64 = 4;
const MAY: u64 = 5;
const JUNE: u64 = 6;
const JULY: u64 = 7;
const AUGUST: u64 = 8;
const SEPTEMBER: u64 = 9;
const OCTOBER: u64 = 10;
const NOVEMBER: u64 = 11;
const DECEMBER: u64 = 12;

/// A date and time represented as seconds since 1900-01-01 00:00:00.
///
/// [`Timestamp`] is a simple wrapper around a [`u64`] with a couple of convenience functions.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Timestamp {
    value: u64,
}

impl Timestamp {
    /// Creates a new [`Timestamp`] from a [`u64`].
    pub fn from_u64(value: u64) -> Self {
        Self { value }
    }

    /// Get the integer representation of this [`Timestamp`].
    pub fn as_u64(&self) -> u64 {
        self.value
    }

    /// Extracts the seconds from this [`Timestamp`].
    pub fn seconds(&self) -> u64 {
        self.total_seconds() % SECONDS_PER_MINUTE
    }

    /// Extracts the minutes from this [`Timestamp`].
    pub fn minutes(&self) -> u64 {
        self.total_minutes() % MINUTES_PER_HOUR
    }

    /// Extracts the hours from this [`Timestamp`].
    pub fn hours(&self) -> u64 {
        self.total_hours() % HOURS_PER_DAY
    }

    /// Extracts which day of the year it is from this [`Timestamp`].
    pub fn day_of_year(&self) -> u64 {
        self.year_and_day().1
    }

    /// Extracts the year from this [`Timestamp`].
    pub fn year(&self) -> u64 {
        self.year_and_day().0
    }

    /// Extracts the month from this [`Timestamp`].
    pub fn month(&self) -> u64 {
        self.month_and_day().0
    }

    /// Extracts which day of the month it is from this [`Timestamp`].
    pub fn day_of_month(&self) -> u64 {
        self.month_and_day().1
    }

    fn total_seconds(&self) -> u64 {
        self.value
    }

    fn total_minutes(&self) -> u64 {
        self.value / SECONDS_PER_MINUTE
    }

    fn total_hours(&self) -> u64 {
        self.value / SECONDS_PER_HOUR
    }

    fn total_days(&self) -> u64 {
        self.value / SECONDS_PER_DAY
    }

    fn is_leap_year(year: u64) -> bool {
        (year % 4) == 0 && (year % 100 != 0 || year % 400 == 0)
    }

    fn days_in_year(year: u64) -> u64 {
        if Self::is_leap_year(year) {
            366
        } else {
            365
        }
    }

    fn year_and_day(&self) -> (u64, u64) {
        let mut days = self.total_days();
        let mut year = 1900;

        loop {
            let days_in_year = Self::days_in_year(year);

            if days_in_year > days {
                return (year, days + 1);
            }

            days -= days_in_year;
            year += 1;
        }
    }

    fn days_in_month(month: u64, year: u64) -> u64 {
        match month {
            JANUARY => 31,
            FEBRUARY => {
                if Self::is_leap_year(year) {
                    29
                } else {
                    28
                }
            }
            MARCH => 31,
            APRIL => 30,
            MAY => 31,
            JUNE => 30,
            JULY => 31,
            AUGUST => 31,
            SEPTEMBER => 30,
            OCTOBER => 31,
            NOVEMBER => 30,
            DECEMBER => 31,
            _ => unreachable!("invalid month"),
        }
    }

    fn month_and_day(&self) -> (u64, u64) {
        let (year, mut days) = self.year_and_day();
        days -= 1;
        let mut month = JANUARY;

        loop {
            let days_in_month = Self::days_in_month(month, year);

            if days_in_month > days {
                return (month, days + 1);
            }

            days -= days_in_month;
            month += 1;
        }
    }
}

impl Display for Timestamp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl From<u64> for Timestamp {
    fn from(timestamp: u64) -> Timestamp {
        Self::from_u64(timestamp)
    }
}

impl From<Timestamp> for u64 {
    fn from(timestamp: Timestamp) -> u64 {
        timestamp.as_u64()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LeapSecond {
    timestamp: Timestamp,
    tai_diff: u16,
}

#[derive(Debug, Error)]
pub struct ParseLineError {
    kind: ParseLineErrorKind,
    line: String,
    line_number: usize,
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

#[derive(Clone, Debug)]
struct Line {
    content: String,
    number: usize,
}

impl Line {
    fn kind(&self) -> LineType {
        if self.content.starts_with('#') {
            match self.content[1..].chars().next() {
                Some('$') => LineType::LastUpdate,
                Some('@') => LineType::ExpirationDate,
                Some('h') => LineType::Hash,
                _ => LineType::Comment,
            }
        } else {
            LineType::LeapSecond
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LineType {
    Comment,
    LastUpdate,
    ExpirationDate,
    LeapSecond,
    Hash,
}

#[derive(Clone, Copy, Debug)]
struct LineBorrow<'a> {
    content: &'a str,
    number: usize,
}

fn extract_content<'a>(line: &'a Line) -> LineBorrow<'a> {
    LineBorrow {
        content: line.content[2..].trim(),
        number: line.number,
    }
}

fn parse_timestamp<'a>(timestamp: LineBorrow<'a>) -> Result<Timestamp, ParseLineError> {
    let timestamp = timestamp
        .content
        .parse::<u64>()
        .map_err(|_| ParseLineError {
            kind: ParseLineErrorKind::InvalidTimestamp,
            line: timestamp.content.to_owned(),
            line_number: timestamp.number,
        })?;

    Ok(Timestamp::from_u64(timestamp))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sha1Hash {
    value: [u8; 20],
}

impl Sha1Hash {
    fn from_array(array: [u8; 20]) -> Self {
        Self { value: array }
    }
}

impl Display for Sha1Hash {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let to_string = self
            .value
            .iter()
            .map(|byte| format!("{:0>2x}", byte))
            .collect::<String>();
        write!(f, "{to_string}")
    }
}

fn parse_hash(hash: LineBorrow) -> Result<Sha1Hash, ParseLineError> {
    let hash_vec = hash
        .content
        .split_ascii_whitespace()
        .map(|word| {
            u32::from_str_radix(word, 16).map_err(|_| ParseLineError {
                kind: ParseLineErrorKind::InvalidHash,
                line: hash.content.to_owned(),
                line_number: hash.number,
            })
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flat_map(|word| word.to_be_bytes())
        .collect::<Vec<_>>();

    let hash = TryInto::<[u8; 20]>::try_into(hash_vec).map_err(|_| ParseLineError {
        kind: ParseLineErrorKind::InvalidHash,
        line: hash.content.to_owned(),
        line_number: hash.number,
    })?;

    Ok(Sha1Hash::from_array(hash))
}

fn parse_leap_second_lines<'a>(
    lines: &'a [Line],
) -> Result<Vec<(LineBorrow<'a>, LineBorrow<'a>)>, ParseLineError> {
    lines
        .into_iter()
        .map(|line| {
            let mut leap_second = line.content.as_str();
            if let Some(start_of_comment) = leap_second.find('#') {
                leap_second = &leap_second[..start_of_comment];
            }
            let leap_second = leap_second.trim();

            let leap_second = leap_second
                .split_once(|c: char| c.is_ascii_whitespace())
                .ok_or_else(|| ParseLineError {
                    kind: ParseLineErrorKind::InvalidLeapSecondLine,
                    line: line.content.to_owned(),
                    line_number: line.number,
                })?;

            Ok((
                LineBorrow {
                    content: leap_second.0,
                    number: line.number,
                },
                LineBorrow {
                    content: leap_second.1,
                    number: line.number,
                },
            ))
        })
        .collect::<Result<Vec<_>, _>>()
}

fn calculate_hash<'a>(
    last_update: LineBorrow<'a>,
    expiration_date: LineBorrow<'a>,
    leap_seconds: &'a [(LineBorrow<'a>, LineBorrow<'a>)],
) -> Sha1Hash {
    let mut hasher = Sha1::new();

    hasher.update(last_update.content.as_bytes());
    hasher.update(expiration_date.content.as_bytes());

    for chunk in leap_seconds.into_iter().flat_map(|(s1, s2)| [s1, s2]) {
        hasher.update(chunk.content.as_bytes());
    }

    Sha1Hash::from_array(hasher.finalize().into())
}

fn parse_tai_diff<'a>(tai_diff: LineBorrow<'a>) -> Result<u16, ParseLineError> {
    tai_diff.content.parse::<u16>().map_err(|_| ParseLineError {
        kind: ParseLineErrorKind::InvalidTaiDiff,
        line: tai_diff.content.to_owned(),
        line_number: tai_diff.number,
    })
}

fn parse_leap_seconds<'a>(
    leap_second_lines: &[(LineBorrow<'a>, LineBorrow<'a>)],
) -> Result<Vec<LeapSecond>, ParseLineError> {
    leap_second_lines
        .into_iter()
        .map(|(timestamp, tai_diff)| {
            Ok(LeapSecond {
                timestamp: parse_timestamp(*timestamp)?,
                tai_diff: parse_tai_diff(*tai_diff)?,
            })
        })
        .collect()
}

// TODO choose better names for everything in this function
fn set_option(
    option: &Option<Line>,
    to: Line,
    data_component: DataComponent,
) -> Result<Line, ParseFileError> {
    if let Some(line) = option {
        Err(ParseFileError::DuplicateData {
            data_component,
            line1: line.number,
            line2: to.number,
        })
    } else {
        Ok(to)
    }
}

fn extract_content_lines<R: BufRead>(file: R) -> Result<ContentLines, ParseFileError> {
    let mut last_update = None;
    let mut expiration_date = None;
    let mut leap_seconds = Vec::new();
    let mut hash = None;

    let lines = file
        .lines()
        .enumerate()
        .map(|(number, line)| line.map(|content| Line { content, number }));

    for line in lines {
        let line = line?;
        match line.kind() {
            LineType::Comment => continue,
            LineType::LeapSecond => leap_seconds.push(line),
            LineType::LastUpdate => {
                last_update = Some(set_option(&last_update, line, DataComponent::LastUpdate)?);
            }
            LineType::ExpirationDate => {
                expiration_date = Some(set_option(
                    &expiration_date,
                    line,
                    DataComponent::ExpirationDate,
                )?);
            }
            LineType::Hash => {
                hash = Some(set_option(&hash, line, DataComponent::Hash)?);
            }
        }
    }

    let last_update =
        last_update.ok_or_else(|| ParseFileError::MissingData(DataComponent::LastUpdate))?;
    let expiration_date = expiration_date
        .ok_or_else(|| ParseFileError::MissingData(DataComponent::ExpirationDate))?;
    let hash = hash.ok_or_else(|| ParseFileError::MissingData(DataComponent::Hash))?;

    Ok(ContentLines {
        last_update,
        expiration_date,
        leap_seconds,
        hash,
    })
}

#[derive(Clone, Debug)]
struct ContentLines {
    last_update: Line,
    expiration_date: Line,
    hash: Line,
    leap_seconds: Vec<Line>,
}

impl ContentLines {
    fn last_update<'a>(&'a self) -> LineBorrow<'a> {
        extract_content(&self.last_update)
    }

    fn expiration_date<'a>(&'a self) -> LineBorrow<'a> {
        extract_content(&self.expiration_date)
    }

    fn hash<'a>(&'a self) -> LineBorrow<'a> {
        extract_content(&self.hash)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Data {
    last_update: Timestamp,
    expiration_date: Timestamp,
    leap_seconds: Vec<LeapSecond>,
}

pub fn parse_file<R: BufRead>(file: R) -> Result<Data, ParseFileError> {
    let content_lines = extract_content_lines(file)?;

    let last_update = content_lines.last_update();
    let expiration_date = content_lines.expiration_date();
    let hash = content_lines.hash();

    let leap_second_lines = parse_leap_second_lines(&content_lines.leap_seconds)?;

    let calculated_hash = calculate_hash(last_update, expiration_date, &leap_second_lines);

    let last_update = parse_timestamp(last_update)?;
    let expiration_date = parse_timestamp(expiration_date)?;
    let hash_from_file = parse_hash(hash)?;

    let leap_seconds = parse_leap_seconds(&leap_second_lines)?;

    if calculated_hash != hash_from_file {
        return Err(ParseFileError::InvalidHash {
            calculated: calculated_hash,
            found: hash_from_file,
        });
    }

    Ok(Data {
        last_update,
        expiration_date,
        leap_seconds,
    })
}

#[cfg(test)]
mod tests {
    mod timestamp {
        use crate::Timestamp;

        #[test]
        fn from_and_as_u64() {
            let original = 123456780987654;
            let result = Timestamp::from_u64(original).as_u64();

            assert_eq!(result, original);
        }

        #[test]
        fn test_1900_01_01() {
            let timestamp = Timestamp::from_u64(0);

            assert_eq!(timestamp.year(), 1900);
            assert_eq!(timestamp.month(), 1);
            assert_eq!(timestamp.day_of_month(), 1);
            assert_eq!(timestamp.hours(), 0);
            assert_eq!(timestamp.minutes(), 0);
            assert_eq!(timestamp.seconds(), 0);

            assert_eq!(timestamp.day_of_year(), 1);
        }

        #[test]
        fn test_1901_01_07_19_45_33() {
            let year = 1 * 365 * 24 * 60 * 60;
            let day = 6 * 24 * 60 * 60;
            let hours = 19 * 60 * 60;
            let minutes = 45 * 60;
            let seconds = 33;

            let timestamp = Timestamp::from_u64(year + day + hours + minutes + seconds);

            assert_eq!(timestamp.year(), 1901);
            assert_eq!(timestamp.month(), 1);
            assert_eq!(timestamp.day_of_month(), 7);
            assert_eq!(timestamp.hours(), 19);
            assert_eq!(timestamp.minutes(), 45);
            assert_eq!(timestamp.seconds(), 33);

            assert_eq!(timestamp.day_of_year(), 7);
        }

        #[test]
        fn test_1904_02_29_23_59_59() {
            let year = 4 * 365 * 24 * 60 * 60;
            let month = 31 * 24 * 60 * 60;
            let day = 28 * 24 * 60 * 60;
            let hours = 23 * 60 * 60;
            let minutes = 59 * 60;
            let seconds = 59;

            let timestamp = Timestamp::from_u64(year + month + day + hours + minutes + seconds);

            assert_eq!(timestamp.year(), 1904);
            assert_eq!(timestamp.month(), 2);
            assert_eq!(timestamp.day_of_month(), 29);
            assert_eq!(timestamp.hours(), 23);
            assert_eq!(timestamp.minutes(), 59);
            assert_eq!(timestamp.seconds(), 59);

            assert_eq!(timestamp.day_of_year(), 60);

            let next_timestamp = Timestamp::from_u64(timestamp.as_u64() + 1);

            assert_eq!(next_timestamp.year(), 1904);
            assert_eq!(next_timestamp.month(), 3);
            assert_eq!(next_timestamp.day_of_month(), 1);
            assert_eq!(next_timestamp.hours(), 0);
            assert_eq!(next_timestamp.minutes(), 0);
            assert_eq!(next_timestamp.seconds(), 0);

            assert_eq!(next_timestamp.day_of_year(), 61);
        }

        #[test]
        fn test_2023_06_28() {
            let timestamp = Timestamp::from_u64(3896899200);

            assert_eq!(timestamp.year(), 2023);
            assert_eq!(timestamp.month(), 6);
            assert_eq!(timestamp.day_of_month(), 28);
            assert_eq!(timestamp.hours(), 0);
            assert_eq!(timestamp.minutes(), 0);
            assert_eq!(timestamp.seconds(), 0);
        }

        #[test]
        fn test_1985_07_01() {
            let timestamp = Timestamp::from_u64(2698012800);

            assert_eq!(timestamp.year(), 1985);
            assert_eq!(timestamp.month(), 7);
            assert_eq!(timestamp.day_of_month(), 1);
            assert_eq!(timestamp.hours(), 0);
            assert_eq!(timestamp.minutes(), 0);
            assert_eq!(timestamp.seconds(), 0);
        }

        #[test]
        fn test_2017_01_01() {
            let timestamp = Timestamp::from_u64(3692217600);

            assert_eq!(timestamp.year(), 2017);
            assert_eq!(timestamp.month(), 1);
            assert_eq!(timestamp.day_of_month(), 1);
            assert_eq!(timestamp.hours(), 0);
            assert_eq!(timestamp.minutes(), 0);
            assert_eq!(timestamp.seconds(), 0);

            assert_eq!(timestamp.day_of_year(), 1);
        }
    }
}
