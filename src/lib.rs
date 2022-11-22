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

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Timestamp {
    value: u64,
}

impl Timestamp {
    pub fn from_u64(value: u64) -> Self {
        Self { value }
    }

    pub fn as_u64(&self) -> u64 {
        self.value
    }
}

impl Display for Timestamp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
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

impl ParseLineError {
    fn new<'a>(kind: ParseLineErrorKind, line: LineBorrow<'a>) -> Self {
        Self {
            kind,
            line: line.content.to_owned(),
            line_number: line.number,
        }
    }
}

impl Display for ParseLineError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} on line {}: \"{}\"", self.kind, self.line_number, self.line)
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

impl<'a> From<&'a Line> for LineBorrow<'a> {
    fn from(line: &'a Line) -> LineBorrow<'a> {
        LineBorrow {
            content: &line.content,
            number: line.number,
        }
    }
}

fn extract_content<'a>(line: &'a Line) -> LineBorrow<'a> {
    LineBorrow {
        content: line.content[2..].trim(),
        number: line.number,
    }
}

fn parse_timestamp<'a>(timestamp: LineBorrow<'a>) -> Result<Timestamp, ParseLineError> {
    let timestamp = timestamp.content.parse::<u64>()
        .map_err(|_| ParseLineError::new(ParseLineErrorKind::InvalidTimestamp, timestamp))?;

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
    let hash_vec = hash.content
        .split_ascii_whitespace()
        .map(|word| {
            u32::from_str_radix(word, 16)
                .map_err(|_| ParseLineError::new(ParseLineErrorKind::InvalidHash, hash))
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flat_map(|word| word.to_be_bytes())
        .collect::<Vec<_>>();

    let hash = TryInto::<[u8; 20]>::try_into(hash_vec)
        .map_err(|_| ParseLineError::new(ParseLineErrorKind::InvalidHash, hash))?;

    Ok(Sha1Hash::from_array(hash))
}

fn parse_leap_second_lines<'a>(lines: &'a [Line]) -> Result<Vec<(LineBorrow<'a>, LineBorrow<'a>)>, ParseLineError> {
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
                .ok_or_else(|| ParseLineError::new(ParseLineErrorKind::InvalidLeapSecondLine, line.into()))?;

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
    tai_diff.content
        .parse::<u16>()
        .map_err(|_| ParseLineError::new(ParseLineErrorKind::InvalidTaiDiff, tai_diff))
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
