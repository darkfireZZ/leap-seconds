use {
    flate2::read::GzDecoder,
    leap_seconds::Line,
    std::{
        fs::File,
        io::{BufRead, BufReader, Write},
        path::Path,
    },
    tar::Archive,
};

fn main() {
    let tar_gz =
        reqwest::blocking::get("https://data.iana.org/time-zones/releases/tzdata2022f.tar.gz")
            .unwrap();
    let tar = GzDecoder::new(tar_gz);
    let mut archive = Archive::new(tar);

    let file_search = archive.entries().unwrap().find(|entry| {
        entry.as_ref().unwrap().path().unwrap().to_str().unwrap() == "leap-seconds.list"
    });
    let leap_seconds = file_search.unwrap().unwrap();
    let buf_read = BufReader::new(leap_seconds);
    let test = buf_read
        .lines()
        .map(|line| line.unwrap().parse::<Line>().unwrap())
        .filter_map(|line| {
            if let Line::LeapSecondInfo(line) = line {
                Some(line)
            } else {
                None
            }
        })
        .map(|line| {
            let mut s = String::new();

            s.push_str(&line.timestamp.to_string());
            s.push(' ');
            s.push_str(&line.tai_diff.to_string());
            s.push('\n');

            s
        })
        .collect::<String>();

    let file_path = Path::new(&".").join("leap-seconds.list");
    let mut f = File::create(file_path).unwrap();

    f.write_all(test.as_bytes()).unwrap();
}
