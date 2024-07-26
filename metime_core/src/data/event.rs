use std::{collections::HashMap, convert::identity, rc::Rc};

use chrono::{DateTime, Utc};

use super::{
    category::CategoryId,
    time::{IcalRecurrenceDesc, Moment, Period},
};

/// A unique ID that can used to refer to an event set.
///
/// Event sets that are similar in time should have similar IDs, but there are
/// no guarantees.
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct EventSetId(pub u64);

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct EventSetData {
    /// Single event instances in this event set. This vector must be
    /// monotonically non-decreasing in the start time of the instances.
    pub single_instance_records: Vec<SingleInstanceRecord>,
    /// Recurring event instances in this event set. There is no restriction
    /// on the order of the `IcalRecurrenceRecord`s.
    pub ical_recurrence_records: Vec<IcalRecurrenceRecord>,
}

/// Enumerates a single instance in the event set.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SingleInstanceRecord {
    /// When this event instance took place.
    pub period: Period,
    /// The data for this event instance.
    pub event_data: EventDataTimeless,
}

/// Defines a possibly infinite set of instances in the event set based on
/// an iCalendar (RFC 5545) recurrence rule.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IcalRecurrenceRecord {
    pub recurrence_desc: IcalRecurrenceDesc,
    pub event_data: EventDataTimeless,
}

/// Stores event data, except the time at which the event took place.
#[derive(Debug, Default, PartialEq, Eq, Hash, Clone)]
pub struct EventDataTimeless {
    /// The categories to which this event belongs.
    pub categories: Vec<CategoryId>,
    /// A short description of the event, e.g. "weekly meeting with John".
    pub summary: String,
    /// A longer description of the event.
    pub description: String,
}

/// Representation of the data for a particular event instance.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct EventInstance<'a> {
    pub period: Period,
    pub event_data: &'a EventDataTimeless,
}

impl EventSetData {
    /// Returns a date-time before which it is guaranteed that there are no
    /// instances of the event set, and a date-time after which it is guaranteed
    /// that there are no instances of the event set. This includes the end
    /// times of event instances. The end bound is None if the event set goes
    /// on to infinity. The entire return value is None if the event set has
    /// no instances.
    pub fn pessimistic_boundaries(&self) -> Option<(DateTime<Utc>, Option<DateTime<Utc>>)> {
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

        for SingleInstanceRecord { period, .. } in self.single_instance_records.iter() {
            let (start, end) = period.pessimistic_boundaries();
            expand_limits(&mut earliest, &mut latest, start, Some(end));
        }
        for IcalRecurrenceRecord { recurrence_desc: reccurence_desc, .. } in
            self.ical_recurrence_records.iter()
        {
            if let Some((start, end)) = reccurence_desc.pessimistic_boundaries() {
                expand_limits(&mut earliest, &mut latest, start, end);
            }
        }

        if let (Some(earliest), Some(latest)) = (earliest, latest) {
            Some((earliest, latest))
        } else {
            None
        }
    }

    /// Returns an iterator over all instances of the event set that are in the
    /// specified closed interval. The instances are not necessarily returned in
    /// the order of their start time.
    pub fn get_instances_in_interval<'s>(
        &'s self,
        start: DateTime<Utc>,
        end: DateTime<Utc>,
    ) -> impl Iterator<Item = EventInstance<'s>> + 's {
        let EventSetData { single_instance_records, ical_recurrence_records } = self;

        let single_instances = single_instance_records
            .iter()
            // filter eligible periods
            .filter_map(move |SingleInstanceRecord { period, event_data }| {
                let (earliest, latest) = period.pessimistic_boundaries();
                if earliest > end {
                    // no other instance after this one can possibly
                    // be within the interval because they are
                    // sorted by start time
                    return None;
                }
                if latest > start {
                    let event_instance = EventInstance { period: *period, event_data };
                    return Some(Some(event_instance));
                } else {
                    // this instance is before the interval, but
                    // later instances might still be within the
                    // interval
                    return Some(None);
                }
            })
            // stop iteration on the first event that is after the interval;
            // this is a performance optimization to stop looking for eligible
            // instances after we are already past the interval
            .fuse()
            // eliminate the `Some(None)` cases from above
            .filter_map(identity);

        let recurring = ical_recurrence_records.iter().flat_map(
            move |IcalRecurrenceRecord { recurrence_desc: reccurence_desc, event_data }| {
                reccurence_desc
                    .get_all_instances_in_interval(start, end)
                    .map(|period| EventInstance { period, event_data })
            },
        );

        recurring.chain(single_instances)
    }
}

#[cfg(test)]
mod test {
    use std::{collections::HashSet, vec};

    use chrono::{Datelike, Duration, TimeZone as _};
    use rrule::{Frequency, RRule};

    use super::*;

    fn dt(offset_days: i64) -> DateTime<Utc> {
        let reference = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
        reference + Duration::days(offset_days)
    }

    fn period(offset_days_start: i64, offset_days_end: i64) -> Period {
        Period::DateTimeInterval { start: dt(offset_days_start), end: dt(offset_days_end) }
    }

    fn single_instance(offset_days_start: i64, offset_days_end: i64) -> SingleInstanceRecord {
        SingleInstanceRecord {
            period: period(offset_days_start, offset_days_end),
            event_data: EventDataTimeless::default(),
        }
    }

    #[test]
    fn enumerated_instances_pessimistic_boundaries() {
        let event_set = EventSetData {
            single_instance_records: vec![single_instance(0, 3), single_instance(1, 2)],
            ..Default::default()
        };

        let Some((earliest, latest)) = event_set.pessimistic_boundaries() else {
            unreachable!();
        };
        assert_eq!(earliest, dt(0));
        assert_eq!(latest, Some(dt(3)));

        let event_set = EventSetData {
            single_instance_records: vec![
                single_instance(0, 3),
                single_instance(3, 4),
                single_instance(1, 2),
            ],
            ..Default::default()
        };

        assert_eq!(event_set.pessimistic_boundaries(), Some((dt(0), Some(dt(4)))));
    }

    #[test]
    fn ical_recurrence_count_pessimistic_boundaries() {
        let dt_start = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
        let recurrence_desc = IcalRecurrenceDesc::new(
            Period::DateTimeInterval { start: dt_start, end: dt_start + Duration::hours(1) },
            RRule::new(Frequency::Daily).interval(2).count(3),
            vec![],
        )
        .unwrap();

        let event_set = EventSetData {
            ical_recurrence_records: vec![IcalRecurrenceRecord {
                recurrence_desc,
                event_data: EventDataTimeless::default(),
            }],
            ..Default::default()
        };

        assert_eq!(
            event_set.pessimistic_boundaries(),
            Some((dt_start, Some(Utc.with_ymd_and_hms(2024, 1, 5, 1, 0, 0).unwrap())))
        );
    }

    #[test]
    fn ical_recurrence_until_pessimistic_boundaries() {
        let dt_start = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
        let until = Utc.with_ymd_and_hms(2024, 1, 20, 0, 0, 0).unwrap();
        let recurrence_desc = IcalRecurrenceDesc::new(
            Period::DateTimeInterval { start: dt_start, end: dt_start + Duration::hours(1) },
            RRule::new(Frequency::Daily).interval(2).until(until.with_timezone(&rrule::Tz::UTC)),
            vec![],
        )
        .unwrap();

        let event_set = EventSetData {
            ical_recurrence_records: vec![IcalRecurrenceRecord {
                recurrence_desc,
                event_data: EventDataTimeless::default(),
            }],
            ..Default::default()
        };

        assert_eq!(
            event_set.pessimistic_boundaries(),
            Some((dt_start, Some(until + Duration::hours(1))))
        );
    }

    #[test]
    fn ical_recurrence_forever_pessimistic_boundaries() {
        let dt_start = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
        let recurrence_desc = IcalRecurrenceDesc::new(
            Period::DateTimeInterval { start: dt_start, end: dt_start + Duration::hours(1) },
            RRule::new(Frequency::Daily).interval(2),
            vec![],
        )
        .unwrap();

        let event_set = EventSetData {
            ical_recurrence_records: vec![IcalRecurrenceRecord {
                recurrence_desc,
                event_data: EventDataTimeless::default(),
            }],
            ..Default::default()
        };

        assert_eq!(event_set.pessimistic_boundaries(), Some((dt_start, None)));
    }

    #[test]
    fn all_records_pessimistic_boundaries() {
        let event_set = EventSetData {
            single_instance_records: vec![single_instance(0, 3), single_instance(1, 2)],
            ical_recurrence_records: vec![IcalRecurrenceRecord {
                recurrence_desc: IcalRecurrenceDesc::new(
                    Period::DateTimeInterval { start: dt(2), end: dt(2) + Duration::hours(25) },
                    RRule::new(Frequency::Weekly)
                        .interval(2)
                        .until(dt(50).with_timezone(&rrule::Tz::UTC)),
                    vec![],
                )
                .unwrap(),
                event_data: EventDataTimeless::default(),
            }],
        };

        assert_eq!(
            event_set.pessimistic_boundaries(),
            Some((dt(0), Some(dt(50) + Duration::hours(25))))
        );
    }

    #[test]
    fn event_set_get_instances_in_interval() {
        let event_set = EventSetData {
            single_instance_records: vec![
                single_instance(0, 13),
                single_instance(3, 7),
                single_instance(7, 13),
                single_instance(13, 17),
                single_instance(17, 23),
                single_instance(23, 27),
                single_instance(5, 10),
                single_instance(20, 25),
            ],
            ical_recurrence_records: vec![IcalRecurrenceRecord {
                recurrence_desc: IcalRecurrenceDesc::new(
                    period(1, 2),
                    RRule::new(Frequency::Daily).interval(2),
                    vec![Moment::DateTime(dt(13))],
                )
                .unwrap(),
                event_data: EventDataTimeless::default(),
            }],
        };

        let event_instances: HashSet<_> =
            event_set.get_instances_in_interval(dt(10), dt(20)).collect();

        let event_data = &EventDataTimeless::default();
        let expected_event_instances = HashSet::from([
            EventInstance { period: period(0, 13), event_data },
            EventInstance { period: period(7, 13), event_data },
            EventInstance { period: period(13, 17), event_data },
            EventInstance { period: period(17, 23), event_data },
            EventInstance { period: period(20, 25), event_data },
            EventInstance { period: period(11, 12), event_data },
            // 13-14 is skipped because it is an exception date.
            EventInstance { period: period(15, 16), event_data },
            EventInstance { period: period(17, 18), event_data },
            EventInstance { period: period(19, 20), event_data },
        ]);

        assert_eq!(event_instances, expected_event_instances);
    }
}
