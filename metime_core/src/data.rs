use std::collections::HashMap;

use chrono::{DateTime, Days, Duration, NaiveDate, NaiveTime, TimeZone, Utc};

use rrule::RRule;

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

/// A unique ID that can used to refer to an event set.
///
/// Event sets that are similar in time should have similar IDs, but there are
/// no guarantees.
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct EventSetId(u64);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct EventSetData {
    records: Vec<EventRecord>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum EventRecord {
    /// Enumerates a finite set of instances in the event set.
    EnumeratedInstances {
        /// The periods of the instances of the event. The start times of the
        /// periods must be monotonically increasing. Must be non-empty.
        periods: Vec<Period>,
        event_data: EventDataTimeless,
    },
    /// Defines a possibly infinite set of instances in the event set based on
    /// an iCalendar (RFC 5545) recurrence rule.
    IcalRecurringInstances {
        reccurence_desc: IcalRecurrenceDesc,
        event_data: EventDataTimeless,
    },
    /// Overrides an existing instancein the event set possibly rescheduling or
    /// deleting them. May also edit the data of the overrided instance.
    OverrideInstance {
        /// The target instance to override. Must refer to an existing instance
        /// of an event in the event set; cannot refer to the result of
        /// overriding an instance.
        target: Moment,
        /// The new period of the overriden instance. If this is None, the
        /// instance is deleted.
        new_period: Option<Period>,
        /// The new data of the overriden instance. If this is None, the
        /// instance retains its original data. Meaningless if new_period is
        /// None.
        event_data: Option<EventDataTimeless>,
    },
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct EventDataTimeless {
    /// The categories to which this event belongs.
    categories: Vec<CategoryId>,
    /// A short description of the event, e.g. "weekly meeting with John".
    summary: String,
    /// A longer description of the event.
    description: String,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Moment {
    DateTime(DateTime<Utc>),
    Date(NaiveDate),
}

/// Represents a period in time that an event can take up. This can be a
/// precisely defined interval/point of date-time(s), or an imprecise
/// interval of dates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Period {
    /// A precise interval of date-times, including the start and excluding the
    /// end.
    DateTimeInterval { start: DateTime<Utc>, end: DateTime<Utc> },
    /// A single date-time, representing an instantaneous event.
    DateTime(DateTime<Utc>),
    /// An interval of dates. The additional days represents the number of days
    /// after the start date that are also included in the interval. For example,
    /// if the start date is 2024-01-01 and there are 2 additional days, the
    /// last day of the period will *include* 2024-01-03, for 3 days in total.
    DateInterval { start: NaiveDate, additional: Days },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IcalRecurrenceDesc {
    // TODO allow a time zone to be attached; this is to allow stuff like "3pm
    // in this time zone" even when daylight savings happens
    initial_recurrence: Period,
    rrule: RRule,
}

#[derive(Debug, Default, PartialEq, Eq)]
struct CategoriesTable {
    categories: HashMap<CategoryId, CategoryData>,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct CategoryId(u64);

#[derive(Debug, PartialEq, Eq)]
pub struct CategoryData {
    /// A short description of the category, e.g. "work"
    summary: String,
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
            self.segments.splice(0..0, (0..num_additional_segments).map(|i| Segment {
                start: first_start_time + DEFAULT_SEGMENT_SIZE * i,
                events: Vec::new(),
            }));
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
        let Some(last_index) = iter.find_map(|(index, segment)| {
            if segment.start < end { Some(index) } else { None }
        }) else {
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

impl EventSetData {
    /// Returns a date-time before which it is guaranteed that there are no
    /// instances of the event set, and a date-time after which it is guaranteed
    /// that there are no instances of the event set. This includes the end
    /// times of event instances.
    fn pessimistic_boundaries(&self) -> (DateTime<Utc>, Option<DateTime<Utc>>) {
        // None means there have been no instances yet to set any of the limits.
        // Some(limit) means that `limit` is the latest time that an instance of
        // this event set can occur. For `latest`, Some(None) means that the
        // current latest is a point infinitely far in the future, so it can't
        // get any later.
        let mut earliest: Option<DateTime<Utc>> = None;
        let mut latest: Option<Option<DateTime<Utc>>> = None;
        fn expand_limits(
            current_earliest: &mut Option<DateTime<Utc>>,
            current_latest: &mut Option<Option<DateTime<Utc>>>,
            start: DateTime<Utc>,
            end: Option<DateTime<Utc>>,
        ) {
            *current_earliest = Some(current_earliest.map_or(start, |e| e.min(start)));
            *current_latest = match *current_latest {
                // None means there have been no instances yet, so set the
                // current latest to the end of this instance
                None => Some(end),
                // Some(Some(_)) means that the current latest is a specific
                // time, so set the boundary to the later time between the
                // current latest and the end of this instance
                Some(Some(l)) => match end {
                    // set the boundary to the later time between the current
                    Some(e) => Some(Some(l.max(e))),
                    // if the end is None, that means the end limit is a point
                    // infinitely far in the future, so it can't get any later
                    None => Some(None),
                },
                // Some(None) means that the current latest is a time
                // infinitly far in the future, so it can't get any later. keep
                // as-is.
                Some(None) => None,
            };
        }

        'record_loop: for record in &self.records {
            match record {
                EventRecord::EnumeratedInstances { periods, .. } => {
                    for period in periods {
                        let (start, end) = period.pessimistic_boundaries();
                        expand_limits(&mut earliest, &mut latest, start, Some(end));
                    }
                }
                EventRecord::IcalRecurringInstances { reccurence_desc, .. } => {
                    let IcalRecurrenceDesc { initial_recurrence, rrule } = reccurence_desc;

                    // find the start point of the recurrence
                    let start = initial_recurrence.pessimistic_boundaries().0;

                    // find the end point of the recurrence
                    let end = if let Some(until) = rrule.get_until() {
                        // the recurrence rule defines a set end point
                        let last = initial_recurrence.shift_start_coerce(until.to_utc());
                        Some(last.pessimistic_boundaries().1)
                    } else if rrule.get_count().is_some() {
                        // the recurrence rule defines a set number of instances
                        let Some(end) = reccurence_desc.into_iter().last().map(|last| last.pessimistic_boundaries().1) else {
                            // the recurrence rule defines no instances
                            continue 'record_loop;
                        };
                        Some(end)
                    } else {
                        // the recurrence rule defines no end to instances
                        None
                    };

                    expand_limits(&mut earliest, &mut latest, start, end);
                }
                EventRecord::OverrideInstance { new_period, .. } => {
                    if let Some(new_period) = new_period {
                        let (start, end) = new_period.pessimistic_boundaries();
                        expand_limits(&mut earliest, &mut latest, start, Some(end));
                    }
                }
            }
        }

        (
            earliest.expect("should be at least one record in the event set"),
            latest.expect("shoudl be at least one record in the event set"),
        )
    }
}

impl Period {
    /// Returns the earliest and latest date-times that are in the period. For
    /// periods without a specific time, this pessimistically returns the
    /// earliest and latest date-times for which it is that naive date in *some*
    /// time zone.
    fn pessimistic_boundaries(&self) -> (DateTime<Utc>, DateTime<Utc>) {
        match self {
            &Period::DateTimeInterval { start, end } => (start, end),
            &Period::DateTime(dt) => (dt, dt),
            &Period::DateInterval { start, additional } => {
                let start_point = Utc.from_utc_datetime(&start.and_time(NaiveTime::MIN));
                let end_point = Utc.from_utc_datetime(&(start + additional).and_time(NaiveTime::MIN));
                // for the earliest time, subtract 14 hours to be safe, since it
                // could still be that date if it is the start of the day with a
                // +14:00 offset. for the latest time, add one day and 12 hours
                // to be safe, since it could still be that date if it is the
                // end of the day with a 12:00 offset.
                (start_point - Duration::hours(14), end_point + Duration::hours(24 + 12))
            }
        }
    }

    /// Shifts the start of the period to the new start time, returning the new
    /// period. If the period is a point in time, the new start time is the new
    /// period. If the period is an interval, the new period is the interval
    /// with the same duration as the original interval, but with the new start
    /// time. Returns `None` if the period and the new start time don't match up,
    /// i.e. shifting a date-time to a date-without-time or vice versa.
    fn shift_start(&self, new_start: Moment) -> Option<Self> {
        match (self, new_start) {
            (Period::DateTimeInterval { start, end }, Moment::DateTime(new_start)) => {
                Some(Period::DateTimeInterval { start: new_start, end: new_start + (*end - start) })
            }
            (Period::DateTime(_), Moment::DateTime(new_start)) => {
                Some(Period::DateTime(new_start))
            }
            (Period::DateInterval { start: _, additional }, Moment::Date(new_start)) => {
                Some(Period::DateInterval { start: new_start, additional: *additional })
            }
            _ => None,
        }
    }

    /// Same as `shift_start`, but does not require that this period and the
    /// new start are compatible; it will be coerced if required.
    fn shift_start_coerce(&self, new_start: DateTime<Utc>) -> Self {
        let new_start = match self {
            Period::DateTimeInterval { .. } | Period::DateTime(_) => Moment::DateTime(new_start),
            Period::DateInterval { .. } => Moment::Date(new_start.date_naive()),
        };
        self.shift_start(new_start).expect("made sure that the initial recurrence and the new start are compatible")
    }

    // Returns the `Moment` at which the `Period` starts.
    fn start(&self) -> Moment {
        match self {
            Period::DateTimeInterval { start, .. } => Moment::DateTime(*start),
            Period::DateInterval { start, .. } => Moment::Date(*start),
            Period::DateTime(dt) => Moment::DateTime(*dt),
        }
    }
}

impl Moment {
    // Forces the `Moment` to be a specific point in time. If it was just a date
    // in general, it will be converted to the specific date-time at the start
    // of that date.
    fn to_specific_time(&self) -> DateTime<Utc> {
        match self {
            Moment::DateTime(dt) => *dt,
            Moment::Date(date) => Utc.from_utc_datetime(&date.and_time(NaiveTime::MIN)),
        }
    }
}

/// Module for safely encapsulating a recurrence rule iterator, working around
/// the limitations of the `rrule` crate.
mod recurrence_iter {
    use std::rc::Rc;

    use rrule::{RRuleSet, RRuleSetIter};
    use chrono::TimeZone;

    use super::{IcalRecurrenceDesc, Moment, Period};

    pub struct IcalRecurrenceIter {
        initial_recurrence: Period,
        // in reality, this borrows from its sibling field `rrule_set`; the
        // static lifetime is fake to appease the borrow checker
        rrule_iter: rrule::RRuleSetIter<'static>,
        // although it says Rc, this is the only owner of the inner RRuleSet. it
        // is Rc instead of Box because Box asserts unique access to the
        // underlying data, which is not true here
        _rrule_set: Rc<RRuleSet>,
    }

    impl Iterator for IcalRecurrenceIter {
        type Item = Period;

        fn next(&mut self) -> Option<Self::Item> {
            self.rrule_iter.next().map(|dt| {
                self.initial_recurrence.shift_start_coerce(dt.to_utc())
            })
        }
    }

    impl<'a> IntoIterator for &'a IcalRecurrenceDesc {
        type Item = Period;
        type IntoIter = IcalRecurrenceIter;

        fn into_iter(self) -> Self::IntoIter {
            let IcalRecurrenceDesc { initial_recurrence, rrule } = self;

            // crate `rrule` only takes date-times, not date-without-times, so
            // convert the dt_start to a date-time
            let dt_start = initial_recurrence.start().to_specific_time();
            // convert from `chrono`'s `DateTime<Utc>` to `rrule`'s `DateTime<Tz>`,
            // while still keeping UTC
            let dt_start = rrule::Tz::Tz(chrono_tz::UTC).from_utc_datetime(&dt_start.naive_utc());

            // put the RRuleSet on the heap so that it can be borrowed by the
            // rrule iter
            let rrule_set = Rc::new(RRuleSet::new(dt_start).rrule(rrule.clone()));

            // SAFETY: the RRuleSet that the RRuleSetIter borrows from is on the
            // heap and never moved from there, so references to it will remain
            // valid as long as the Rc is valid. Since the Rc is moved into the
            // resulting struct at the same time as the RRuleSetIter, the two
            // will live together and have the same lifetime. Thus, the
            // internals of RRuleSetIter will always point to valid data, and
            // can be tricked into thinking the data is 'static.
            let rrule_iter: RRuleSetIter<'static> = unsafe {
                &*(rrule_set.as_ref() as *const RRuleSet)
            }.into_iter();

            IcalRecurrenceIter {
                initial_recurrence: *initial_recurrence,
                rrule_iter,
                _rrule_set: rrule_set,
            }
        }
    }

    #[cfg(test)]
    mod test {
        use chrono::{DateTime, Days, Duration, NaiveDate, NaiveTime, Utc};
        use rrule::{Frequency, RRule};

        use super::*;

        #[test]
        fn generates_dt_periods() {
            fn gen_period(start: DateTime<Utc>) -> Period {
                Period::DateTimeInterval {
                    start,
                    end: start + Duration::hours(1),
                }
            }

            let dt_start = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
            let rrule = IcalRecurrenceDesc {
                initial_recurrence: gen_period(dt_start),
                rrule: RRule::new(Frequency::Daily)
                    .count(3)
                    .interval(2)
                    .validate(dt_start.with_timezone(&rrule::Tz::UTC))
                    .unwrap(),
            };

            let dates = rrule.into_iter().collect::<Vec<_>>();
            assert_eq!(dates, vec![
                gen_period(Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap()),
                gen_period(Utc.with_ymd_and_hms(2024, 1, 3, 0, 0, 0).unwrap()),
                gen_period(Utc.with_ymd_and_hms(2024, 1, 5, 0, 0, 0).unwrap()),
            ]);
        }

        #[test]
        fn generates_date_periods() {
            fn gen_period(start: NaiveDate) -> Period {
                Period::DateInterval {
                    start,
                    additional: Days::new(1),
                }
            }

            let dt_start = NaiveDate::from_ymd_opt(2024, 1, 1).unwrap();
            let rrule = IcalRecurrenceDesc {
                initial_recurrence: gen_period(dt_start),
                rrule: RRule::new(Frequency::Daily)
                    .count(3)
                    .interval(2)
                    .validate(rrule::Tz::UTC.from_utc_datetime(&dt_start.and_time(NaiveTime::MIN)))
                    .unwrap(),
            };

            let dates = rrule.into_iter().collect::<Vec<_>>();
            assert_eq!(dates, vec![
                gen_period(NaiveDate::from_ymd_opt(2024, 1, 1).unwrap()),
                gen_period(NaiveDate::from_ymd_opt(2024, 1, 3).unwrap()),
                gen_period(NaiveDate::from_ymd_opt(2024, 1, 5).unwrap()),
            ]);
        }
    }
}

#[cfg(test)]
mod test {
    use rrule::Frequency;

    use super::*;

    #[test]
    fn period_pessimistic_boundaries() {
        let a = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();

        let dt_interval = Period::DateTimeInterval {
            start: a,
            end: a + Duration::hours(1),
        };
        assert_eq!(dt_interval.pessimistic_boundaries(), (a, a + Duration::hours(1)));

        let dt_point = Period::DateTime(a);
        assert_eq!(dt_point.pessimistic_boundaries(), (a, a));

        let date_interval = Period::DateInterval {
            start: NaiveDate::from_ymd_opt(2024, 1, 1).unwrap(),
            additional: Days::new(2),
        };
        let (bound_left, bound_right) = date_interval.pessimistic_boundaries();
        assert_eq!(bound_left, Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap() - Duration::hours(14));
        assert_eq!(bound_right, Utc.with_ymd_and_hms(2024, 1, 4, 0, 0, 0).unwrap() + Duration::hours(12));
    }

    #[test]
    fn enumerated_instances_pessimistic_boundaries() {
        fn gen_dt(offset_days: i64) -> DateTime<Utc> {
            let reference = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
            reference + Duration::days(offset_days)
        }

        let event_set = EventSetData { records: vec![
            EventRecord::EnumeratedInstances {
                periods: vec![
                    Period::DateTimeInterval {
                        start: gen_dt(0),
                        end: gen_dt(3),
                    },
                    Period::DateTimeInterval {
                        start: gen_dt(1),
                        end: gen_dt(2),
                    },
                ],
                event_data: EventDataTimeless::default(),
            },
        ] };
        let (earliest, latest) = event_set.pessimistic_boundaries();
        assert_eq!(earliest, gen_dt(0));
        assert_eq!(latest, Some(gen_dt(3)));

        let event_set = EventSetData { records: vec![
            EventRecord::EnumeratedInstances {
                periods: vec![
                    Period::DateTimeInterval {
                        start: gen_dt(0),
                        end: gen_dt(3),
                    },
                    Period::DateTime(gen_dt(4)),
                    Period::DateTimeInterval {
                        start: gen_dt(1),
                        end: gen_dt(2),
                    },
                ],
                event_data: EventDataTimeless::default(),
            },
        ]};
        let (earliest, latest) = event_set.pessimistic_boundaries();
        assert_eq!(earliest, gen_dt(0));
        assert_eq!(latest, Some(gen_dt(4)));
    }

    #[test]
    fn ical_recurrence_count_pessimistic_boundaries() {
        let dt_start = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
        let rrule = IcalRecurrenceDesc {
            initial_recurrence: Period::DateTimeInterval {
                start: dt_start,
                end: dt_start + Duration::hours(1),
            },
            rrule: RRule::new(Frequency::Daily)
                .interval(2)
                .count(3)
                .validate(dt_start.with_timezone(&rrule::Tz::UTC))
                .unwrap(),
        };

        let event_set = EventSetData { records: vec![
            EventRecord::IcalRecurringInstances {
                reccurence_desc: rrule,
                event_data: EventDataTimeless::default(),
            },
        ] };

        let (earliest, latest) = event_set.pessimistic_boundaries();
        assert_eq!(earliest, dt_start);
        assert_eq!(latest, Some(Utc.with_ymd_and_hms(2024, 1, 5, 1, 0, 0).unwrap()));
    }

    #[test]
    fn ical_recurrence_until_pessimistic_boundaries() {
        let dt_start = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
        let until = Utc.with_ymd_and_hms(2024, 1, 20, 0, 0, 0).unwrap();
        let rrule = IcalRecurrenceDesc {
            initial_recurrence: Period::DateTimeInterval {
                start: dt_start,
                end: dt_start + Duration::hours(1),
            },
            rrule: RRule::new(Frequency::Daily)
                .interval(2)
                .until(until.with_timezone(&rrule::Tz::UTC))
                .validate(dt_start.with_timezone(&rrule::Tz::UTC))
                .unwrap(),
        };

        let event_set = EventSetData { records: vec![
            EventRecord::IcalRecurringInstances {
                reccurence_desc: rrule,
                event_data: EventDataTimeless::default(),
            },
        ] };

        let (earliest, latest) = event_set.pessimistic_boundaries();
        assert_eq!(earliest, dt_start);
        assert_eq!(latest, Some(until + Duration::hours(1)));
    }

    #[test]
    fn ical_recurrence_forever_pessimistic_boundaries() {
        let dt_start = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
        let rrule = IcalRecurrenceDesc {
            initial_recurrence: Period::DateTimeInterval {
                start: dt_start,
                end: dt_start + Duration::hours(1),
            },
            rrule: RRule::new(Frequency::Daily)
                .interval(2)
                .validate(dt_start.with_timezone(&rrule::Tz::UTC))
                .unwrap(),
        };

        let event_set = EventSetData { records: vec![
            EventRecord::IcalRecurringInstances {
                reccurence_desc: rrule,
                event_data: EventDataTimeless::default(),
            },
        ] };

        let (earliest, latest) = event_set.pessimistic_boundaries();
        assert_eq!(earliest, dt_start);
        assert_eq!(latest, None);
    }

    #[test]
    fn all_records_pessimistic_boundaries() {
        fn gen_dt(offset_days: i64) -> DateTime<Utc> {
            let reference = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
            reference + Duration::days(offset_days)
        }

        let event_set = EventSetData { records: vec![
            EventRecord::EnumeratedInstances {
                periods: vec![
                    Period::DateTimeInterval {
                        start: gen_dt(0),
                        end: gen_dt(3),
                    },
                    Period::DateTimeInterval {
                        start: gen_dt(1),
                        end: gen_dt(2),
                    },
                ],
                event_data: EventDataTimeless::default(),
            },
            EventRecord::IcalRecurringInstances {
                reccurence_desc: IcalRecurrenceDesc {
                    initial_recurrence: Period::DateTimeInterval {
                        start: gen_dt(2),
                        end: gen_dt(2) + Duration::hours(25),
                    },
                    rrule: RRule::new(Frequency::Weekly)
                        .interval(2)
                        .until(gen_dt(50).with_timezone(&rrule::Tz::UTC))
                        .validate(gen_dt(2).with_timezone(&rrule::Tz::UTC))
                        .unwrap(),
                },
                event_data: EventDataTimeless::default(),
            },
            EventRecord::OverrideInstance { target: Moment::DateTime(gen_dt(0)), new_period: Some(Period::DateTimeInterval { start: gen_dt(-5), end: gen_dt(-4) }), event_data: Default::default() },
        ] };

        let (earliest, latest) = event_set.pessimistic_boundaries();
        assert_eq!(earliest, gen_dt(-5));
        assert_eq!(latest, Some(gen_dt(50) + Duration::hours(25)));
    }

    #[test]
    fn db_seed_segments() {
        let dt = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();

        let mut db = Database::new();
        assert!(db.prepend_segment(dt));
        assert_eq!(db.segments().collect::<Vec<_>>(), vec![
            &Segment { start: dt, events: Vec::new() },
        ]);
    }

    #[test]
    fn db_ensure_segments_back_to() {
        let mut db = Database::new();

        let dt = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
        assert!(db.ensure_segments_back_to(dt));
        assert_eq!(db.segments().collect::<Vec<_>>(), vec![
            &Segment { start: dt, events: Vec::new() },
        ]);

        let dt2 = Utc.with_ymd_and_hms(2023, 12, 31, 0, 0, 0).unwrap();
        assert!(db.ensure_segments_back_to(dt2));
        assert_eq!(db.segments().collect::<Vec<_>>(), vec![
            &Segment { start: dt - DEFAULT_SEGMENT_SIZE, events: Vec::new() },
            &Segment { start: dt, events: Vec::new() },
        ]);

        // dt3 is already included, so it should not add any other segments
        let dt3 = Utc.with_ymd_and_hms(2022, 12, 30, 0, 0, 0).unwrap();
        assert!(!db.ensure_segments_back_to(dt3));

        let dt4 = Utc.with_ymd_and_hms(2022, 1, 30, 0, 0, 0).unwrap();
        assert!(db.ensure_segments_back_to(dt4));
        assert_eq!(db.segments().collect::<Vec<_>>(), vec![
            &Segment { start: dt - DEFAULT_SEGMENT_SIZE * 2, events: Vec::new() },
            &Segment { start: dt - DEFAULT_SEGMENT_SIZE, events: Vec::new() },
            &Segment { start: dt, events: Vec::new() },
        ]);
    }

    #[test]
    fn db_add_event_set_to_empty() {
        let a = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
        let b = Utc.with_ymd_and_hms(2024, 1, 1, 1, 0, 0).unwrap();

        let mut db = Database::new();

        let event_set = EventSetData { records: vec![
            EventRecord::EnumeratedInstances {
                periods: vec![Period::DateTimeInterval { start: a, end: b }],
                event_data: EventDataTimeless::default(),
            },
        ] };

        let id = db.add_event_set(event_set.clone());
        assert_eq!(db.segments().collect::<Vec<_>>(), vec![
            &Segment { start: a, events: vec![id] },
        ]);
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
            EventSetData { records: vec![
                EventRecord::EnumeratedInstances {
                    periods: vec![Period::DateTimeInterval { start: a, end: b }],
                    event_data: EventDataTimeless::default(),
                },
            ] }
        }

        let mut db = Database::new();
        assert!(db.prepend_segment(gen_dt(500)));
        assert!(db.prepend_segment(gen_dt(400)));
        assert!(db.prepend_segment(gen_dt(300)));
        assert!(db.prepend_segment(gen_dt(200)));
        assert!(db.prepend_segment(gen_dt(100)));
        assert!(db.prepend_segment(gen_dt(0)));
        assert_eq!(db.segments().collect::<Vec<_>>(), vec![
            &Segment { start: gen_dt(0), events: Vec::new() },
            &Segment { start: gen_dt(100), events: Vec::new() },
            &Segment { start: gen_dt(200), events: Vec::new() },
            &Segment { start: gen_dt(300), events: Vec::new() },
            &Segment { start: gen_dt(400), events: Vec::new() },
            &Segment { start: gen_dt(500), events: Vec::new() },
        ]);

        let id_a = db.add_event_set(gen_event_set(150, 350));
        let id_b = db.add_event_set(gen_event_set(250, 251));
        let id_c = db.add_event_set(gen_event_set(300, 450));
        let id_d = db.add_event_set(gen_event_set(350, 500));
        let id_e = db.add_event_set(gen_event_set(450, 550));
        assert_eq!(db.segments().collect::<Vec<_>>(), vec![
            &Segment { start: gen_dt(0), events: vec![] },
            &Segment { start: gen_dt(100), events: vec![id_a] },
            &Segment { start: gen_dt(200), events: vec![id_a, id_b] },
            &Segment { start: gen_dt(300), events: vec![id_a, id_c, id_d] },
            &Segment { start: gen_dt(400), events: vec![id_c, id_d, id_e] },
            &Segment { start: gen_dt(500), events: vec![id_d, id_e] },
        ]);

        let id_f = db.add_event_set(gen_event_set(-1, 50));
        assert_eq!(db.segments().collect::<Vec<_>>(), vec![
            &Segment { start: gen_dt(0) - DEFAULT_SEGMENT_SIZE, events: vec![id_f] },
            &Segment { start: gen_dt(0), events: vec![id_f] },
            &Segment { start: gen_dt(100), events: vec![id_a] },
            &Segment { start: gen_dt(200), events: vec![id_a, id_b] },
            &Segment { start: gen_dt(300), events: vec![id_a, id_c, id_d] },
            &Segment { start: gen_dt(400), events: vec![id_c, id_d, id_e] },
            &Segment { start: gen_dt(500), events: vec![id_d, id_e] },
        ]);
    }
}
