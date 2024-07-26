use std::collections::HashMap;

use chrono::{DateTime, Duration, Utc};

use super::{
    category::CategoriesTable,
    event::{EventSetData, EventSetId},
};

#[derive(Debug, Default)]
pub struct Database {
    manifest: DatabaseManifest,
    categories: CategoriesTable,
    segments: Vec<Segment>,
    event_sets: HashMap<EventSetId, EventSetData>,
}

#[derive(Debug)]
struct DatabaseManifest {
    /// The next ID to be assigned to an event set.
    next_event_set_id: EventSetId,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Segment {
    /// The start of the time interval that this segment represents. The end
    /// of the interval is the start of the next segment, or none if the
    /// next segment does not exist.
    start: DateTime<Utc>,
    events: Vec<EventSetId>,
}

const DEFAULT_SEGMENT_SIZE: Duration = Duration::weeks(69);

impl Database {
    pub fn new() -> Self {
        Database::default()
    }

    // Returns a unique `EventSetId` and marks that ID as used. Panics if the ID
    // space for this database is exhausted. (Technically, panics *right before*
    // the ID space is exhausted, such that call that would have returned the
    // last valid ID panics instead.)
    fn gen_unique_event_set_id(&mut self) -> EventSetId {
        let id = self.manifest.next_event_set_id;
        self.manifest.next_event_set_id = EventSetId(id.0.checked_add(1).unwrap());
        id
    }

    // Adds an event set to the database, returning the ID under which it was
    // stored.
    pub fn add_event_set(&mut self, event_set: EventSetData) -> EventSetId {
        let id = self.gen_unique_event_set_id();

        let (earliest, latest) = event_set.pessimistic_boundaries();
        self.event_sets.insert(id, event_set);

        self.ensure_segments_back_to(earliest);

        // add the event set to all segments for which it is pertinent
        for segment in self.segments.iter_mut().rev() {
            // if the segment starts after the latest possible instance of the
            // event set, this condition will return false and this segment
            // cannot be included, but do check for earlier segments (later in
            // the iteration)
            if !latest.is_some_and(|latest| latest < segment.start) {
                // the segment starts before or equal to the latest possible
                // instance of the event set, so some events instances might be
                // within the segment
                segment.events.push(id);

                if segment.start <= earliest {
                    // the segment starts before or equal to the earliest
                    // possible instance of the event set, so the predecessor
                    // segment cannot possibly contain any instances of the
                    // event set
                    break;
                }
            }
        }

        id
    }

    /// Ensures that there exist segments covering date-times as far back as the
    /// specified date-time. Employs an opaque strategy for deciding how to
    /// divide up the segments. Returns whether any segments were successfully
    /// added
    fn ensure_segments_back_to(&mut self, earliest: DateTime<Utc>) -> bool {
        if let Some(segment) = self.segments.first() {
            // calculate the segments that we will need to add
            let mut first_start_time = segment.start;
            let mut num_additional_segments = 0;
            while first_start_time > earliest {
                first_start_time -= DEFAULT_SEGMENT_SIZE;
                num_additional_segments += 1;
            }
            if num_additional_segments == 0 {
                return false;
            }
            self.segments.splice(
                0..0,
                (0..num_additional_segments).map(|i| Segment {
                    start: first_start_time + DEFAULT_SEGMENT_SIZE * i,
                    events: Vec::new(),
                }),
            );
            true
        } else {
            self.segments.push(Segment { start: earliest, events: Vec::new() });
            true
        }
    }

    /// Prepends a segment starting at the specified date-time to the sequence
    /// of segments. Fails if there is already a segment that includes the
    /// specified date-time. Returns whether a segment was successfully
    /// prepended.
    pub fn prepend_segment(&mut self, start: DateTime<Utc>) -> bool {
        if let Some(segment) = self.segments.first() {
            if segment.start <= start {
                // there is already a segment that includes the specified
                // date-time
                return false;
            }
        }

        self.segments.insert(0, Segment { start, events: Vec::new() });
        true
    }

    pub fn get_segment_by_dt(&self, dt: DateTime<Utc>) -> Option<&Segment> {
        // look backwards because it is more likely that we are looking for more
        // recent segments
        self.segments.iter().rev().filter(|&segment| segment.start <= dt).next()
    }

    pub fn segments(&self) -> impl Iterator<Item = &Segment> {
        self.segments.iter()
    }

    pub fn get_segments_in_interval(&self, start: DateTime<Utc>, end: DateTime<Utc>) -> &[Segment] {
        let mut iter = self.segments.iter().enumerate().rev();

        // get the index of the latest segment that overlaps with the interval
        let Some(last_index) =
            iter.find_map(|(index, segment)| if segment.start < end { Some(index) } else { None })
        else {
            // the interval ends before the earliest segment begins
            return &[];
        };

        // get the index of the earliest segment that overlaps with the interval
        let first_index = iter
            .filter_map(|(index, segment)| if segment.start <= start { Some(index) } else { None })
            .last()
            .unwrap_or(last_index);

        &self.segments[first_index..=last_index]
    }

    pub fn get_event_set(&self, id: &EventSetId) -> Option<&EventSetData> {
        self.event_sets.get(id)
    }
}

impl Default for DatabaseManifest {
    fn default() -> Self {
        DatabaseManifest { next_event_set_id: EventSetId(0) }
    }
}

#[cfg(test)]
mod test {
    use super::super::event::{EnumeratedInstances, EventDataTimeless};
    use super::super::time::Period;
    use chrono::TimeZone as _;

    use super::*;

    #[test]
    fn db_seed_segments() {
        let dt = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();

        let mut db = Database::new();
        assert!(db.prepend_segment(dt));
        assert_eq!(
            db.segments().collect::<Vec<_>>(),
            vec![&Segment { start: dt, events: Vec::new() },]
        );
    }

    #[test]
    fn db_ensure_segments_back_to() {
        let mut db = Database::new();

        let dt = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
        assert!(db.ensure_segments_back_to(dt));
        assert_eq!(
            db.segments().collect::<Vec<_>>(),
            vec![&Segment { start: dt, events: Vec::new() },]
        );

        let dt2 = Utc.with_ymd_and_hms(2023, 12, 31, 0, 0, 0).unwrap();
        assert!(db.ensure_segments_back_to(dt2));
        assert_eq!(
            db.segments().collect::<Vec<_>>(),
            vec![
                &Segment { start: dt - DEFAULT_SEGMENT_SIZE, events: Vec::new() },
                &Segment { start: dt, events: Vec::new() },
            ]
        );

        // dt3 is already included, so it should not add any other segments
        let dt3 = Utc.with_ymd_and_hms(2022, 12, 30, 0, 0, 0).unwrap();
        assert!(!db.ensure_segments_back_to(dt3));

        let dt4 = Utc.with_ymd_and_hms(2022, 1, 30, 0, 0, 0).unwrap();
        assert!(db.ensure_segments_back_to(dt4));
        assert_eq!(
            db.segments().collect::<Vec<_>>(),
            vec![
                &Segment { start: dt - DEFAULT_SEGMENT_SIZE * 2, events: Vec::new() },
                &Segment { start: dt - DEFAULT_SEGMENT_SIZE, events: Vec::new() },
                &Segment { start: dt, events: Vec::new() },
            ]
        );
    }

    #[test]
    fn db_add_event_set_to_empty() {
        let a = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
        let b = Utc.with_ymd_and_hms(2024, 1, 1, 1, 0, 0).unwrap();

        let mut db = Database::new();

        let event_set = EventSetData {
            enumerated_instances: vec![EnumeratedInstances {
                periods: vec![Period::DateTimeInterval { start: a, end: b }],
                event_data: EventDataTimeless::default(),
            }],
            ..Default::default()
        };

        let id = db.add_event_set(event_set.clone());
        assert_eq!(
            db.segments().collect::<Vec<_>>(),
            vec![&Segment { start: a, events: vec![id] },]
        );
        assert_eq!(db.get_event_set(&id), Some(&event_set));
    }

    #[test]
    fn db_add_event_sets_to_existing_segments() {
        fn gen_dt(offset_days: i64) -> DateTime<Utc> {
            let reference = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
            reference + Duration::days(offset_days)
        }
        fn gen_event_set(start_offset_days: i64, end_offset_days: i64) -> EventSetData {
            let a = gen_dt(start_offset_days);
            let b = gen_dt(end_offset_days);
            EventSetData {
                enumerated_instances: vec![EnumeratedInstances {
                    periods: vec![Period::DateTimeInterval { start: a, end: b }],
                    event_data: EventDataTimeless::default(),
                }],
                ..Default::default()
            }
        }

        let mut db = Database::new();
        assert!(db.prepend_segment(gen_dt(500)));
        assert!(db.prepend_segment(gen_dt(400)));
        assert!(db.prepend_segment(gen_dt(300)));
        assert!(db.prepend_segment(gen_dt(200)));
        assert!(db.prepend_segment(gen_dt(100)));
        assert!(db.prepend_segment(gen_dt(0)));
        assert_eq!(
            db.segments().collect::<Vec<_>>(),
            vec![
                &Segment { start: gen_dt(0), events: Vec::new() },
                &Segment { start: gen_dt(100), events: Vec::new() },
                &Segment { start: gen_dt(200), events: Vec::new() },
                &Segment { start: gen_dt(300), events: Vec::new() },
                &Segment { start: gen_dt(400), events: Vec::new() },
                &Segment { start: gen_dt(500), events: Vec::new() },
            ]
        );

        let id_a = db.add_event_set(gen_event_set(150, 350));
        let id_b = db.add_event_set(gen_event_set(250, 251));
        let id_c = db.add_event_set(gen_event_set(300, 450));
        let id_d = db.add_event_set(gen_event_set(350, 500));
        let id_e = db.add_event_set(gen_event_set(450, 550));
        assert_eq!(
            db.segments().collect::<Vec<_>>(),
            vec![
                &Segment { start: gen_dt(0), events: vec![] },
                &Segment { start: gen_dt(100), events: vec![id_a] },
                &Segment { start: gen_dt(200), events: vec![id_a, id_b] },
                &Segment { start: gen_dt(300), events: vec![id_a, id_c, id_d] },
                &Segment { start: gen_dt(400), events: vec![id_c, id_d, id_e] },
                &Segment { start: gen_dt(500), events: vec![id_d, id_e] },
            ]
        );

        let id_f = db.add_event_set(gen_event_set(-1, 50));
        assert_eq!(
            db.segments().collect::<Vec<_>>(),
            vec![
                &Segment { start: gen_dt(0) - DEFAULT_SEGMENT_SIZE, events: vec![id_f] },
                &Segment { start: gen_dt(0), events: vec![id_f] },
                &Segment { start: gen_dt(100), events: vec![id_a] },
                &Segment { start: gen_dt(200), events: vec![id_a, id_b] },
                &Segment { start: gen_dt(300), events: vec![id_a, id_c, id_d] },
                &Segment { start: gen_dt(400), events: vec![id_c, id_d, id_e] },
                &Segment { start: gen_dt(500), events: vec![id_d, id_e] },
            ]
        );
    }
}
