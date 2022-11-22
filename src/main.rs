use {
    flate2::read::GzDecoder,
    std::io::BufReader,
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
    let data = leap_seconds::parse_file(buf_read).unwrap();

    println!("{:#?}", data);
}
