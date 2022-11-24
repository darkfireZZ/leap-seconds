// TODO add module-level documentation
//! ```
//! use leap_seconds::LeapSecondsList;
//! use std::io::BufReader;
//!
//! let file = reqwest::blocking::get("https://data.iana.org/time-zones/tzdb/leap-seconds.list")
//!         .unwrap();
//! let file = BufReader::new(file);
//! let leap_seconds_list = LeapSecondsList::from_file(file).unwrap();
//!
//! # use leap_seconds::Timestamp;
//! #
//! # let min_expiration_date = Timestamp::from_u64(3896899200);
//! # assert!(leap_seconds_list.expiration_date() >= min_expiration_date);
//! #
//! # let min_last_update = Timestamp::from_u64(3676924800);
//! # assert!(leap_seconds_list.last_update() >= min_last_update);
//! #
//! # let first_leap_second = &leap_seconds_list.leap_seconds()[0];
//! # let expected_timestamp = Timestamp::from_u64(2272060800);
//! # let expected_tai_diff = 10;
//! # assert_eq!(first_leap_second.timestamp(), expected_timestamp);
//! # assert_eq!(first_leap_second.tai_diff(), expected_tai_diff);
//! ```

#![deny(clippy::all)]
#![warn(clippy::pedantic)]
// TODO disallow these lints
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_lossless)]
// TODO enable these lints
// #![warn(clippy::cargo)]
// #![warn(missing_docs)]

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

const JANUARY: u8 = 1;
const FEBRUARY: u8 = 2;
const MARCH: u8 = 3;
const APRIL: u8 = 4;
const MAY: u8 = 5;
const JUNE: u8 = 6;
const JULY: u8 = 7;
const AUGUST: u8 = 8;
const SEPTEMBER: u8 = 9;
const OCTOBER: u8 = 10;
const NOVEMBER: u8 = 11;
const DECEMBER: u8 = 12;

#[derive(Clone, Debug, Error, Eq, PartialEq)]
pub enum InvalidDate {
    #[error("day out of range: {0}")]
    MonthOutOfRange(u8),
    #[error("month out of range: {0}")]
    DayOutOfRange(u8),
}

/// A date.
///
/// Is limited to years `>= 0`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Date {
    year: u64,
    month: u8,
    day: u8,
}

impl Date {
    /// Creates a new [`Date`].
    ///
    /// ```
    /// # use leap_seconds::{Date, InvalidDate};
    /// #
    /// let _ = Date::new(2003, 03, 30)?;
    /// #
    /// # Ok::<(), InvalidDate>(())
    /// ```
    ///
    /// # Errors
    ///
    /// Fails if the given date is invalid.
    ///
    /// ```
    /// # use leap_seconds::Date;
    /// #
    /// // The year 7_777_777 is not a leap year
    /// let error = Date::new(7_777_777, 2, 29);
    /// assert!(error.is_err());
    /// ```
    pub fn new(year: u64, month: u8, day: u8) -> Result<Self, InvalidDate> {
        if !(1..=12).contains(&month) {
            Err(InvalidDate::MonthOutOfRange(month))
        } else if day < 1 || day > days_in_month(month, year) {
            Err(InvalidDate::DayOutOfRange(day))
        } else {
            Ok(Date { year, month, day })
        }
    }

    /// Gets the day of this [`Date`].
    ///
    /// ```
    /// # use leap_seconds::{Date, InvalidDate};
    /// #
    /// let date = Date::new(1977, 5, 25)?;
    /// assert_eq!(date.day(), 25);
    /// #
    /// # Ok::<(), InvalidDate>(())
    /// ```
    #[must_use]
    pub const fn day(self) -> u8 {
        self.day
    }

    /// Gets the month of this [`Date`].
    ///
    /// ```
    /// # use leap_seconds::{Date, InvalidDate};
    /// #
    /// let date = Date::new(1980, 5, 21)?;
    /// assert_eq!(date.month(), 5);
    /// #
    /// # Ok::<(), InvalidDate>(())
    /// ```
    #[must_use]
    pub const fn month(self) -> u8 {
        self.month
    }

    /// Gets the year of this [`Date`].
    ///
    /// ```
    /// # use leap_seconds::{Date, InvalidDate};
    /// #
    /// let date = Date::new(1983, 5, 25)?;
    /// assert_eq!(date.year(), 1983);
    /// #
    /// # Ok::<(), InvalidDate>(())
    /// ```
    #[must_use]
    pub const fn year(self) -> u64 {
        self.year
    }

    fn seconds_since_1900(self) -> u64 {
        let mut days = self.day as u64 - 1;

        for month in JANUARY..self.month {
            days += days_in_month(month, self.year) as u64;
        }

        for year in 1900..self.year {
            days += days_in_year(year);
        }

        days * SECONDS_PER_DAY
    }
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

/// A time.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Time {
    hours: u8,
    minutes: u8,
    seconds: u8,
}

impl Time {
    /// Create a new [`Time`].
    ///
    /// ```
    /// # use leap_seconds::{InvalidTime, Time};
    /// #
    /// // 15:03:42
    /// let _ = Time::new(15, 3, 42)?;
    /// #
    /// # Ok::<(), InvalidTime>(())
    /// ```
    ///
    /// # Errors
    ///
    /// Fails if the given time is invalid.
    ///
    /// ```
    /// # use leap_seconds::Time;
    /// #
    /// let error = Time::new(23, 60, 15);
    /// assert!(error.is_err());
    /// ```
    pub fn new(hours: u8, minutes: u8, seconds: u8) -> Result<Self, InvalidTime> {
        if hours >= (HOURS_PER_DAY as u8) {
            Err(InvalidTime::HoursOutOfRange(hours))
        } else if minutes >= (MINUTES_PER_HOUR as u8) {
            Err(InvalidTime::MinutesOutOfRange(minutes))
        } else if seconds >= (SECONDS_PER_MINUTE as u8) {
            Err(InvalidTime::SecondsOutOfRange(seconds))
        } else {
            Ok(Time {
                hours,
                minutes,
                seconds,
            })
        }
    }

    /// Gets the hours of this [`Time`].
    ///
    /// ```
    /// # use leap_seconds::{InvalidTime, Time};
    /// #
    /// let time = Time::new(13, 17, 29)?;
    /// assert_eq!(time.hours(), 13);
    /// #
    /// # Ok::<(), InvalidTime>(())
    /// ```
    #[must_use]
    pub const fn hours(self) -> u8 {
        self.hours
    }

    /// Gets the minutes of this [`Time`].
    ///
    /// ```
    /// # use leap_seconds::{InvalidTime, Time};
    /// #
    /// let time = Time::new(13, 17, 29)?;
    /// assert_eq!(time.minutes(), 17);
    /// #
    /// # Ok::<(), InvalidTime>(())
    /// ```
    #[must_use]
    pub const fn minutes(self) -> u8 {
        self.minutes
    }

    /// Gets the seconds of this [`Time`].
    ///
    /// ```
    /// # use leap_seconds::{InvalidTime, Time};
    /// #
    /// let time = Time::new(13, 17, 29)?;
    /// assert_eq!(time.seconds(), 29);
    /// #
    /// # Ok::<(), InvalidTime>(())
    /// ```
    #[must_use]
    pub const fn seconds(self) -> u8 {
        self.seconds
    }

    const fn total_seconds(self) -> u64 {
        (self.hours as u64) * SECONDS_PER_HOUR
            + (self.minutes as u64) * SECONDS_PER_MINUTE
            + (self.seconds as u64)
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DateTime {
    pub date: Date,
    pub time: Time,
}

const fn is_leap_year(year: u64) -> bool {
    (year % 4 == 0) && ((year % 100 != 0) || (year % 400 == 0))
}

const fn days_in_year(year: u64) -> u64 {
    if is_leap_year(year) {
        366
    } else {
        365
    }
}

const fn days_in_month(month: u8, year: u64) -> u8 {
    match month {
        JANUARY | MARCH | MAY | JULY | AUGUST | OCTOBER | DECEMBER => 31,
        APRIL | JUNE | SEPTEMBER | NOVEMBER => 30,
        FEBRUARY => {
            if is_leap_year(year) {
                29
            } else {
                28
            }
        }
        // TODO this is terrible code, improve this
        _ => u8::MAX, // _ => unreachable!("invalid month")
    }
}

#[derive(Clone, Debug, Error, Eq, PartialEq)]
pub struct DateTimeNotRepresentable(DateTime);

impl Display for DateTimeNotRepresentable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DateTime is not representable as 64-bit timestamp")
    }
}

/// A date and time represented as seconds since 1900-01-01 00:00:00.
///
/// [`Timestamp`] is a simple wrapper around a [`u64`] with a couple of convenience functions.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Timestamp {
    value: u64,
}

impl Timestamp {
    pub const MAX_REPRESENTABLE_DATE_TIME: DateTime = Self::from_u64(u64::MAX).date_time();
    pub const MIN_REPRESENTABLE_DATE_TIME: DateTime = Self::from_u64(0).date_time();

    /// Creates a new [`Timestamp`] from a [`DateTime`].
    ///
    /// # Errors
    ///
    /// Fails if the [`DateTime`] is not representable as a [`Timestamp`].
    ///
    /// ```
    /// use leap_seconds::{Date, DateTime, Time, Timestamp};
    ///
    /// let error = Timestamp::from_date_time(DateTime {
    ///     date: Date::new(1899, 1, 1).expect("valid date"),
    ///     time: Time::new(12, 0, 0).expect("valid time"),
    /// });
    ///
    /// assert!(error.is_err());
    /// ```
    pub fn from_date_time(date_time: DateTime) -> Result<Self, DateTimeNotRepresentable> {
        if (date_time >= Self::MIN_REPRESENTABLE_DATE_TIME)
            && (date_time <= Self::MAX_REPRESENTABLE_DATE_TIME)
        {
            Ok(Timestamp::from_u64(
                date_time.date.seconds_since_1900() + date_time.time.total_seconds(),
            ))
        } else {
            Err(DateTimeNotRepresentable(date_time))
        }
    }

    /// Creates a new [`Timestamp`] from a [`u64`].
    #[must_use]
    pub const fn from_u64(value: u64) -> Self {
        Self { value }
    }

    /// Gets the integer representation of this [`Timestamp`].
    #[must_use]
    pub const fn as_u64(self) -> u64 {
        self.value
    }

    /// Gets the date and time of this [`Timestamp`].
    #[must_use]
    pub const fn date_time(self) -> DateTime {
        DateTime {
            date: self.date(),
            time: self.time(),
        }
    }

    /// Gets the time of this [`Timestamp`].
    #[must_use]
    pub const fn time(self) -> Time {
        Time {
            hours: self.hours(),
            minutes: self.minutes(),
            seconds: self.seconds(),
        }
    }

    /// Gets the date of this [`Timestamp`].
    #[must_use]
    pub const fn date(self) -> Date {
        // Credits to Howard Hinnant for the algorithm:
        // https://howardhinnant.github.io/date_algorithms.html (last accessed 2022-11-24)

        const DAYS_PER_ERA: u64 = 365 * 400 + 100 - 4 + 1;
        const REF_YEAR: u64 = 1900;
        const DIFF: u64 =
            REF_YEAR * 365 + (REF_YEAR / 400) - (REF_YEAR / 100) + (REF_YEAR / 4) + 1 - 60; // 719468

        let days_since_1900_01_01 = self.total_days();

        let days_since_0000_03_01 = days_since_1900_01_01 + DIFF;
        let era = days_since_0000_03_01 / DAYS_PER_ERA;
        let day_of_era = days_since_0000_03_01 % DAYS_PER_ERA; // [0, 146096]
        let year_of_era =
            (day_of_era - day_of_era / 1460 + day_of_era / 36524 - day_of_era / 146_096) / 365; // [0, 399]
        let year = year_of_era + era * 400;
        let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100); // [0, 365]

        let mp = (5 * day_of_year + 2) / 153; // [0, 11]
        let day = (day_of_year - (153 * mp + 2) / 5 + 1) as u8; // [1, 31]
        let month = (mp % 12) as u8; // [1, 12]
        let year = year + (month <= 2) as u64;

        Date { year, month, day }
    }

    const fn hours(self) -> u8 {
        (self.total_hours() % HOURS_PER_DAY) as u8
    }

    const fn minutes(self) -> u8 {
        (self.total_minutes() % MINUTES_PER_HOUR) as u8
    }

    const fn seconds(self) -> u8 {
        (self.total_seconds() % SECONDS_PER_MINUTE) as u8
    }

    const fn total_seconds(self) -> u64 {
        self.value
    }

    const fn total_minutes(self) -> u64 {
        self.value / SECONDS_PER_MINUTE
    }

    const fn total_hours(self) -> u64 {
        self.value / SECONDS_PER_HOUR
    }

    const fn total_days(self) -> u64 {
        self.value / SECONDS_PER_DAY
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LeapSecond {
    timestamp: Timestamp,
    tai_diff: u16,
}

impl LeapSecond {
    #[must_use]
    pub const fn timestamp(self) -> Timestamp {
        self.timestamp
    }

    #[must_use]
    pub const fn tai_diff(self) -> u16 {
        self.tai_diff
    }
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

fn extract_content(line: &Line) -> LineBorrow<'_> {
    LineBorrow {
        content: line.content[2..].trim(),
        number: line.number,
    }
}

fn parse_timestamp(timestamp: LineBorrow<'_>) -> Result<Timestamp, ParseLineError> {
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
            .map(|byte| format!("{byte:0>2x}"))
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
        .flat_map(u32::to_be_bytes)
        .collect::<Vec<_>>();

    let hash = TryInto::<[u8; 20]>::try_into(hash_vec).map_err(|_| ParseLineError {
        kind: ParseLineErrorKind::InvalidHash,
        line: hash.content.to_owned(),
        line_number: hash.number,
    })?;

    Ok(Sha1Hash::from_array(hash))
}

fn parse_leap_second_lines(
    lines: &[Line],
) -> Result<Vec<(LineBorrow<'_>, LineBorrow<'_>)>, ParseLineError> {
    lines
        .iter()
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
                    line: line.content.clone(),
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

    for chunk in leap_seconds.iter().flat_map(|(s1, s2)| [s1, s2]) {
        hasher.update(chunk.content.as_bytes());
    }

    Sha1Hash::from_array(hasher.finalize().into())
}

fn parse_tai_diff(tai_diff: LineBorrow<'_>) -> Result<u16, ParseLineError> {
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
        .iter()
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
        hash,
        leap_seconds,
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
    fn last_update(&self) -> LineBorrow<'_> {
        extract_content(&self.last_update)
    }

    fn expiration_date(&self) -> LineBorrow<'_> {
        extract_content(&self.expiration_date)
    }

    fn hash(&self) -> LineBorrow<'_> {
        extract_content(&self.hash)
    }
}

/// Provides access to the data in `leap-seconds.list`.
///
/// See the [crate-level documentation](crate) for examples.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeapSecondsList {
    last_update: Timestamp,
    expiration_date: Timestamp,
    leap_seconds: Vec<LeapSecond>,
}

impl LeapSecondsList {
    /// Parse a `leap-seconds.list` file.
    ///
    /// # Errors
    ///
    /// If the given `leap-seconds.list` could not be parsed successfully.
    ///
    /// See [`ParseFileError`] for more information on what each error variant means.
    pub fn from_file<R: BufRead>(file: R) -> Result<Self, ParseFileError> {
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

        Ok(LeapSecondsList {
            last_update,
            expiration_date,
            leap_seconds,
        })
    }

    /// Gets the last time the file was updated.
    #[must_use]
    pub fn last_update(&self) -> Timestamp {
        self.last_update
    }

    /// Gets the expiration date of the file.
    #[must_use]
    pub fn expiration_date(&self) -> Timestamp {
        self.expiration_date
    }

    /// Gets the leap second list from the file.
    #[must_use]
    pub fn leap_seconds(&self) -> &[LeapSecond] {
        &self.leap_seconds
    }

    /// Gets the leap second list from the file.
    #[must_use]
    pub fn into_leap_seconds(self) -> Vec<LeapSecond> {
        self.leap_seconds
    }
}

#[cfg(test)]
mod tests {
    mod timestamp {
        use crate::{Date, DateTime, Time, Timestamp};

        #[test]
        fn from_and_as_u64() {
            let original = 123456780987654;
            let result = Timestamp::from_u64(original).as_u64();

            assert_eq!(result, original);
        }

        #[test]
        fn test_1900_01_01() {
            let expected = Timestamp::from_date_time(DateTime {
                date: Date::new(1900, 1, 1).unwrap(),
                time: Time::new(0, 0, 0).unwrap(),
            })
            .unwrap();
            let actual = Timestamp::from_u64(0);

            assert_eq!(actual, expected);
        }

        #[test]
        fn test_1901_01_07_19_45_33() {
            let year = 1 * 365 * 24 * 60 * 60;
            let day = 6 * 24 * 60 * 60;
            let hours = 19 * 60 * 60;
            let minutes = 45 * 60;
            let seconds = 33;

            let expected = Timestamp::from_date_time(DateTime {
                date: Date::new(1901, 1, 7).unwrap(),
                time: Time::new(19, 45, 33).unwrap(),
            })
            .unwrap();
            let actual = Timestamp::from_u64(year + day + hours + minutes + seconds);

            assert_eq!(actual, expected);
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
            let expected = Timestamp::from_date_time(DateTime {
                date: Date::new(1904, 2, 29).unwrap(),
                time: Time::new(23, 59, 59).unwrap(),
            })
            .unwrap();

            assert_eq!(timestamp, expected);

            let next_timestamp = Timestamp::from_u64(timestamp.as_u64() + 1);
            let next_expected = Timestamp::from_date_time(DateTime {
                date: Date::new(1904, 3, 1).unwrap(),
                time: Time::new(0, 0, 0).unwrap(),
            })
            .unwrap();

            assert_eq!(next_timestamp, next_expected);

            assert!(next_timestamp > timestamp);
        }

        #[test]
        fn test_2023_06_28() {
            let expected = Timestamp::from_date_time(DateTime {
                date: Date::new(2023, 6, 28).unwrap(),
                time: Time::new(0, 0, 0).unwrap(),
            })
            .unwrap();
            let actual = Timestamp::from_u64(3896899200);

            assert_eq!(actual, expected);
        }

        #[test]
        fn test_1985_07_01() {
            let expected = Timestamp::from_date_time(DateTime {
                date: Date::new(1985, 7, 1).unwrap(),
                time: Time::new(0, 0, 0).unwrap(),
            })
            .unwrap();
            let actual = Timestamp::from_u64(2698012800);

            assert_eq!(actual, expected);
        }

        #[test]
        fn test_2017_01_01() {
            let expected = Timestamp::from_date_time(DateTime {
                date: Date::new(2017, 1, 1).unwrap(),
                time: Time::new(0, 0, 0).unwrap(),
            })
            .unwrap();
            let actual = Timestamp::from_u64(3692217600);

            assert_eq!(actual, expected);
        }
    }
}
