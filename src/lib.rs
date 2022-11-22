use {
    core::fmt::{self, Display},
    sha1::{Digest, Sha1},
    std::io::{self, BufRead},
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
pub enum ParseLineError {
    #[error("unexpected start of line: expected \"{expected}\", found \"{found}\" on line #{line_number}")]
    UnexpectedStartOfLine {
        expected: &'static str,
        found: String,
        line_number: usize,
    },
    #[error("invalid timestamp: \"{timestamp}\" on line #{line_number}")]
    InvalidTimestamp {
        timestamp: String,
        line_number: usize,
    },
    #[error("invalid hash: \"{0}\"")]
    InvalidHash(String),
    #[error("invalid content line: \"{content_line}\" on line #{line_number}")]
    InvalidContentLine {
        content_line: String,
        line_number: usize,
    },
    #[error("invalid TAI difference: \"{0}\"")]
    InvalidTaiDiff(String),
}

#[derive(Clone, Debug)]
struct Line {
    content: String,
    number: usize,
}

impl Line {
    fn is_comment(&self) -> bool {
        self.content.starts_with('#')
            && (self.content[1..].starts_with(|c: char| c.is_ascii_whitespace())
                || self.content.len() == 1)
    }
}

fn validate_start_of_line(
    line: &Line,
    expected_start_of_line: &'static str,
) -> Result<(), ParseLineError> {
    if line.content.starts_with(expected_start_of_line) {
        Ok(())
    } else {
        Err(ParseLineError::UnexpectedStartOfLine {
            expected: expected_start_of_line,
            found: line
                .content
                .get(0..2)
                .or_else(|| line.content.get(0..1))
                .unwrap_or_else(|| "")
                .to_owned(),
            line_number: line.number,
        })
    }
}

fn extract_content<'a>(
    line: &'a Line,
    expected_start_of_line: &'static str,
) -> Result<&'a str, ParseLineError> {
    validate_start_of_line(line, expected_start_of_line)?;

    Ok(&line.content[2..].trim())
}

const LAST_UPDATE_LINE_START: &'static str = "#$";
const EXPIRE_DATE_LINE_START: &'static str = "#@";
const HASH_LINE_START: &'static str = "#h";

fn parse_timestamp(timestamp: &str) -> Result<Timestamp, ParseLineError> {
    let timestamp = timestamp
        .parse::<u64>()
        .map_err(|_| ParseLineError::InvalidTimestamp {
            timestamp: timestamp.to_owned(),
            line_number: todo!(),
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

fn parse_hash(hash: &str) -> Result<Sha1Hash, ParseLineError> {
    let hash_str = hash;

    let hash = hash
        .split_ascii_whitespace()
        .map(|word| {
            u32::from_str_radix(word, 16)
                .map_err(|_| ParseLineError::InvalidHash(hash_str.to_owned()))
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flat_map(|word| word.to_be_bytes())
        .collect::<Vec<_>>();

    let hash = TryInto::<[u8; 20]>::try_into(hash)
        .map_err(|_| ParseLineError::InvalidHash(hash_str.to_owned()))?;

    Ok(Sha1Hash::from_array(hash))
}

fn parse_content_lines(lines: &[Line]) -> Result<Vec<(&str, &str)>, ParseLineError> {
    lines
        .into_iter()
        .map(|line| {
            let mut content = line.content.as_str();
            if let Some(start_of_comment) = content.find('#') {
                content = &content[..start_of_comment];
            }
            let content = content.trim();

            content
                .split_once(|c: char| c.is_ascii_whitespace())
                .ok_or_else(|| ParseLineError::InvalidContentLine {
                    content_line: line.content.clone(),
                    line_number: line.number,
                })
        })
        .collect::<Result<Vec<_>, _>>()
}

fn calculate_hash<'a>(
    last_updated: &'a str,
    expiration_date: &'a str,
    content: &'a [(&'a str, &'a str)],
) -> Sha1Hash {
    let mut hasher = Sha1::new();

    hasher.update(last_updated.as_bytes());
    hasher.update(expiration_date.as_bytes());

    for chunk in content.into_iter().flat_map(|(s1, s2)| [s1, s2]) {
        hasher.update(chunk.as_bytes());
    }

    Sha1Hash::from_array(hasher.finalize().into())
}

fn parse_tai_diff(tai_diff: &str) -> Result<u16, ParseLineError> {
    tai_diff
        .parse::<u16>()
        .map_err(|_| ParseLineError::InvalidTaiDiff(tai_diff.to_owned()))
}

fn parse_leap_seconds(content_lines: &[(&str, &str)]) -> Result<Vec<LeapSecond>, ParseLineError> {
    content_lines
        .into_iter()
        .map(|(timestamp, tai_diff)| {
            Ok(LeapSecond {
                timestamp: parse_timestamp(timestamp)?,
                tai_diff: parse_tai_diff(tai_diff)?,
            })
        })
        .collect()
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Data {
    last_updated: Timestamp,
    expiration_date: Timestamp,
    leap_seconds: Vec<LeapSecond>,
}

pub fn parse_file<R: BufRead>(file: R) -> Result<Data, ParseFileError> {
    let lines = file
        .lines()
        .enumerate()
        .map(|(number, line)| line.map(|content| Line { content, number }))
        .filter(|line| match line {
            Ok(line) => !line.is_comment(),
            Err(_) => true,
        })
        .collect::<io::Result<Vec<_>>>()?;

    let num_lines = lines.len();

    if num_lines < 3 {
        todo!("error");
    }

    let last_updated_line = &lines[0];
    let expiration_date_line = &lines[1];
    let content_lines = &lines[2..num_lines - 1];
    let hash_line = &lines[num_lines - 1];

    let last_updated = extract_content(last_updated_line, LAST_UPDATE_LINE_START)?;
    let expiration_date = extract_content(expiration_date_line, EXPIRE_DATE_LINE_START)?;
    let hash = extract_content(hash_line, HASH_LINE_START)?;
    let content_lines = parse_content_lines(content_lines)?;

    let calculated_hash = calculate_hash(last_updated, expiration_date, &content_lines);

    let last_updated = parse_timestamp(&last_updated)?;
    let expiration_date = parse_timestamp(&expiration_date)?;
    let hash_from_file = parse_hash(&hash)?;

    let leap_seconds = parse_leap_seconds(&content_lines)?;

    if calculated_hash != hash_from_file {
        return Err(ParseFileError::InvalidHash {
            calculated: calculated_hash,
            found: hash_from_file,
        });
    }

    Ok(Data {
        last_updated,
        expiration_date,
        leap_seconds,
    })
}
