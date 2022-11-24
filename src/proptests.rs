mod timestamp {
    use crate::Timestamp;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn from_and_to_date_time(timestamp in 0..u64::MAX) {
            let timestamp = Timestamp::from_u64(timestamp);
            let date_time = timestamp.date_time();

            let timestamp_again = Timestamp::from_date_time(date_time).expect("should always be valid");
            assert_eq!(timestamp_again, timestamp);

            let date_time_again = timestamp_again.date_time();
            assert_eq!(date_time_again, date_time);
        }
    }
}
