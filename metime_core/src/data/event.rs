use std::{collections::HashMap, rc::Rc};

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
    pub overrides: Vec<OverrideInstance>,
    pub enumerated_instances: Vec<EnumeratedInstances>,
    pub ical_recurring_instances: Vec<IcalRecurringInstances>,
}

/// Enumerates a finite set of instances in the event set.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct EnumeratedInstances {
    /// The periods of the instances of the event. The start times of the
    /// periods must be monotonically increasing. Must be non-empty.
    pub periods: Vec<Period>,
    pub event_data: EventDataTimeless,
}

/// Defines a possibly infinite set of instances in the event set based on
/// an iCalendar (RFC 5545) recurrence rule.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IcalRecurringInstances {
    pub reccurence_desc: IcalRecurrenceDesc,
    pub event_data: EventDataTimeless,
}

/// Overrides an existing instancein the event set possibly rescheduling or
/// deleting them. May also edit the data of the overrided instance.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OverrideInstance {
    /// The target instance to override. Must refer to an existing instance
    /// of an event in the event set; cannot refer to the result of
    /// overriding an instance.
    pub target: Moment,
    /// The overriden instance's period and event data. If this is None, the
    /// instance is deleted. If only the event data is None, then the instance
    /// retains its original data.
    pub new_instance: Option<(Period, Option<EventDataTimeless>)>,
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct EventDataTimeless {
    /// The categories to which this event belongs.
    pub categories: Vec<CategoryId>,
    /// A short description of the event, e.g. "weekly meeting with John".
    pub summary: String,
    /// A longer description of the event.
    pub description: String,
}

/// Representation of the data for a particular event instance.
pub struct EventInstance {
    pub period: Period,
    pub data: EventDataTimeless,
}

impl EventSetData {
    /// Returns a date-time before which it is guaranteed that there are no
    /// instances of the event set, and a date-time after which it is guaranteed
    /// that there are no instances of the event set. This includes the end
    /// times of event instances.
    ///
    /// # Panics
    ///
    /// Panics if the event set has no instances.
    pub fn pessimistic_boundaries(&self) -> (DateTime<Utc>, Option<DateTime<Utc>>) {
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

        for EnumeratedInstances { periods, .. } in self.enumerated_instances.iter() {
            for period in periods {
                let (start, end) = period.pessimistic_boundaries();
                expand_limits(&mut earliest, &mut latest, start, Some(end));
            }
        }
        for IcalRecurringInstances { reccurence_desc, .. } in self.ical_recurring_instances.iter() {
            let Some((start, end)) = reccurence_desc.pessimistic_boundaries() else {
                continue;
            };

            expand_limits(&mut earliest, &mut latest, start, end);
        }
        for OverrideInstance { new_instance, .. } in self.overrides.iter() {
            if let Some((new_period, _)) = new_instance {
                let (start, end) = new_period.pessimistic_boundaries();
                expand_limits(&mut earliest, &mut latest, start, Some(end));
            }
        }

        (
            earliest.expect("should be at least one record in the event set"),
            latest.expect("shoudl be at least one record in the event set"),
        )
    }

    /// Returns an iterator over all instances of the event set that are in the
    /// specified interval. The instances are not necessarily returned in the
    /// order of their start time.
    pub fn get_instances_in_interval(
        &self,
        start: DateTime<Utc>,
        end: DateTime<Utc>,
    ) -> impl Iterator<Item = EventInstance> + '_ {
        let EventSetData { overrides, enumerated_instances, ical_recurring_instances } = self;

        let overrides: Rc<HashMap<_, _>> = Rc::new(HashMap::from_iter(overrides.iter().map(
            |OverrideInstance { target, new_instance: new_period }| {
                (target.clone(), new_period.clone())
            },
        )));
        // converts a period into an EventInstance, taking in to account
        // possible overrides
        fn maybe_override(
            period: &Period,
            original_event_data: &EventDataTimeless,
            overrides: &HashMap<Moment, Option<(Period, Option<EventDataTimeless>)>>,
        ) -> Option<EventInstance> {
            if let Some(new_instance) = overrides.get(&period.start()) {
                if let Some((new_period, new_data)) = new_instance {
                    Some(EventInstance {
                        period: *new_period,
                        data: new_data.as_ref().cloned().unwrap_or(original_event_data.clone()),
                    })
                } else {
                    // this instance was deleted
                    None
                }
            } else {
                Some(EventInstance { period: *period, data: original_event_data.clone() })
            }
        }

        let overrides_too = overrides.clone();
        let enumerated = enumerated_instances.iter().flat_map(
            move |EnumeratedInstances { periods, event_data }| {
                let overrides_too = overrides_too.clone();
                periods
                    .iter()
                    // filter out eligible periods
                    .filter_map(move |period| {
                        let (earliest, latest) = period.pessimistic_boundaries();
                        if earliest > end {
                            // no other instance after this one can possibly
                            // be within the interval because they are
                            // sorted by start time
                            return None;
                        }
                        if latest >= start {
                            return Some(Some(period));
                        } else {
                            // this instance is before the interval, but
                            // later instances might still be within the
                            // interval
                            return Some(None);
                        }
                    })
                    // stop iteration on the first event that is after the interval;
                    // this is a performance operation to stop looking for eligible
                    // instances after we are already past the interval
                    .fuse()
                    // eliminate the `Some(None)` cases from above, while also
                    // accounting for overridden events
                    .filter_map(move |maybe_period| {
                        maybe_period.and_then(|period| {
                            maybe_override(period, event_data, overrides_too.as_ref())
                        })
                    })
            },
        );

        let overrides_too = overrides.clone();
        let recurring = ical_recurring_instances.iter().flat_map(
            move |IcalRecurringInstances { reccurence_desc, event_data }| {
                let overrides_too = overrides_too.clone();
                reccurence_desc.get_all_instances_in_interval(start, end).filter_map(
                    move |period| maybe_override(&period, event_data, overrides_too.as_ref()),
                )
            },
        );

        recurring.chain(enumerated)
    }
}

#[cfg(test)]
mod test {
    use chrono::{Duration, TimeZone as _};
    use rrule::{Frequency, RRule};

    use super::*;

    #[test]
    fn enumerated_instances_pessimistic_boundaries() {
        fn gen_dt(offset_days: i64) -> DateTime<Utc> {
            let reference = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
            reference + Duration::days(offset_days)
        }

        let event_set = EventSetData {
            enumerated_instances: vec![EnumeratedInstances {
                periods: vec![
                    Period::DateTimeInterval { start: gen_dt(0), end: gen_dt(3) },
                    Period::DateTimeInterval { start: gen_dt(1), end: gen_dt(2) },
                ],
                event_data: EventDataTimeless::default(),
            }],
            ..Default::default()
        };
        let (earliest, latest) = event_set.pessimistic_boundaries();
        assert_eq!(earliest, gen_dt(0));
        assert_eq!(latest, Some(gen_dt(3)));

        let event_set = EventSetData {
            enumerated_instances: vec![EnumeratedInstances {
                periods: vec![
                    Period::DateTimeInterval { start: gen_dt(0), end: gen_dt(3) },
                    Period::DateTime(gen_dt(4)),
                    Period::DateTimeInterval { start: gen_dt(1), end: gen_dt(2) },
                ],
                event_data: EventDataTimeless::default(),
            }],
            ..Default::default()
        };
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

        let event_set = EventSetData {
            ical_recurring_instances: vec![IcalRecurringInstances {
                reccurence_desc: rrule,
                event_data: EventDataTimeless::default(),
            }],
            ..Default::default()
        };

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

        let event_set = EventSetData {
            ical_recurring_instances: vec![IcalRecurringInstances {
                reccurence_desc: rrule,
                event_data: EventDataTimeless::default(),
            }],
            ..Default::default()
        };

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

        let event_set = EventSetData {
            ical_recurring_instances: vec![IcalRecurringInstances {
                reccurence_desc: rrule,
                event_data: EventDataTimeless::default(),
            }],
            ..Default::default()
        };

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

        let event_set = EventSetData {
            enumerated_instances: vec![EnumeratedInstances {
                periods: vec![
                    Period::DateTimeInterval { start: gen_dt(0), end: gen_dt(3) },
                    Period::DateTimeInterval { start: gen_dt(1), end: gen_dt(2) },
                ],
                event_data: EventDataTimeless::default(),
            }],
            ical_recurring_instances: vec![IcalRecurringInstances {
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
            }],
            overrides: vec![OverrideInstance {
                target: Moment::DateTime(gen_dt(0)),
                new_instance: Some((
                    Period::DateTimeInterval { start: gen_dt(-5), end: gen_dt(-4) },
                    Some(Default::default()),
                )),
            }],
        };

        let (earliest, latest) = event_set.pessimistic_boundaries();
        assert_eq!(earliest, gen_dt(-5));
        assert_eq!(latest, Some(gen_dt(50) + Duration::hours(25)));
    }

    #[test]
    fn event_set_get_instances_in_interval() {
        fn gen_dt(offset_days: i64) -> DateTime<Utc> {
            let reference = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();
            reference + Duration::days(offset_days)
        }

        let event_set = EventSetData {
            enumerated_instances: vec![
                EnumeratedInstances {
                    periods: vec![
                        Period::DateTimeInterval { start: gen_dt(0), end: gen_dt(13) },
                        Period::DateTimeInterval { start: gen_dt(3), end: gen_dt(7) },
                        Period::DateTimeInterval { start: gen_dt(7), end: gen_dt(13) },
                        Period::DateTimeInterval { start: gen_dt(13), end: gen_dt(17) },
                        Period::DateTimeInterval { start: gen_dt(17), end: gen_dt(23) },
                        Period::DateTimeInterval { start: gen_dt(23), end: gen_dt(27) },
                    ],
                    event_data: EventDataTimeless::default(),
                },
                EnumeratedInstances {
                    periods: vec![
                        Period::DateTimeInterval { start: gen_dt(5), end: gen_dt(6) },
                        Period::DateTimeInterval { start: gen_dt(15), end: gen_dt(16) },
                        Period::DateTimeInterval { start: gen_dt(25), end: gen_dt(26) },
                    ],
                    event_data: EventDataTimeless::default(),
                },
            ],
            ical_recurring_instances: vec![IcalRecurringInstances {
                reccurence_desc: IcalRecurrenceDesc {
                    initial_recurrence: Period::DateTimeInterval {
                        start: gen_dt(0),
                        end: gen_dt(1),
                    },
                    rrule: RRule::new(Frequency::Daily)
                        .interval(2)
                        .validate(gen_dt(0).with_timezone(&rrule::Tz::UTC))
                        .unwrap(),
                },
                event_data: EventDataTimeless::default(),
            }],
            overrides: vec![
                // move an instance forward into the interval
                OverrideInstance {
                    target: Moment::DateTime(gen_dt(5)),
                    new_instance: Some((
                        Period::DateTimeInterval { start: gen_dt(15), end: gen_dt(16) },
                        Some(Default::default()),
                    )),
                },
                // move an instance backward into the interval
                OverrideInstance {
                    target: Moment::DateTime(gen_dt(25)),
                    new_instance: Some((
                        Period::DateTimeInterval { start: gen_dt(15), end: gen_dt(16) },
                        Some(Default::default()),
                    )),
                },
                // move an instance out of the interval
                OverrideInstance { target: Moment::DateTime(gen_dt(23)), new_instance: None },
            ],
        };

        let event_instances: Vec<_> =
            event_set.get_instances_in_interval(gen_dt(10), gen_dt(20)).collect();

        // it doesn't work because it doesn't check for overridden instances
        // that might land inside the interval. this calls for a restructuring
        // of the code
        panic!();
    }
}
