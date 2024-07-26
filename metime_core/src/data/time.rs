use chrono::{DateTime, Days, Duration, NaiveDate, NaiveTime, TimeZone as _, Utc};
use rrule::RRule;

/// Represents a single moment in time, which can be either a precise date-time
/// or a single date.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Moment {
    DateTime(DateTime<Utc>),
    Date(NaiveDate),
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

impl Period {
    /// Returns the earliest and latest date-times that are in the period. For
    /// periods without a specific time, this pessimistically returns the
    /// earliest and latest date-times for which it is that naive date in *some*
    /// time zone.
    pub fn pessimistic_boundaries(&self) -> (DateTime<Utc>, DateTime<Utc>) {
        match self {
            &Period::DateTimeInterval { start, end } => (start, end),
            &Period::DateTime(dt) => (dt, dt),
            &Period::DateInterval { start, additional } => {
                let start_point = Utc.from_utc_datetime(&start.and_time(NaiveTime::MIN));
                let end_point =
                    Utc.from_utc_datetime(&(start + additional).and_time(NaiveTime::MIN));
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
    pub fn shift_start(&self, new_start: Moment) -> Option<Self> {
        match (self, new_start) {
            (Period::DateTimeInterval { start, end }, Moment::DateTime(new_start)) => {
                Some(Period::DateTimeInterval { start: new_start, end: new_start + (*end - start) })
            }
            (Period::DateTime(_), Moment::DateTime(new_start)) => Some(Period::DateTime(new_start)),
            (Period::DateInterval { start: _, additional }, Moment::Date(new_start)) => {
                Some(Period::DateInterval { start: new_start, additional: *additional })
            }
            _ => None,
        }
    }

    /// Same as `shift_start`, but does not require that this period and the
    /// new start are compatible; it will be coerced if required.
    pub fn shift_start_coerce(&self, new_start: DateTime<Utc>) -> Self {
        let new_start = match self {
            Period::DateTimeInterval { .. } | Period::DateTime(_) => Moment::DateTime(new_start),
            Period::DateInterval { .. } => Moment::Date(new_start.date_naive()),
        };
        self.shift_start(new_start)
            .expect("made sure that the initial recurrence and the new start are compatible")
    }

    // Returns the `Moment` at which the `Period` starts.
    pub fn start(&self) -> Moment {
        match self {
            Period::DateTimeInterval { start, .. } => Moment::DateTime(*start),
            Period::DateInterval { start, .. } => Moment::Date(*start),
            Period::DateTime(dt) => Moment::DateTime(*dt),
        }
    }
}

/// A descriptor for all the periods in a recurring set of event instances.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IcalRecurrenceDesc {
    // TODO allow a time zone to be attached; this is to allow stuff like "3pm
    // in this time zone" even when daylight savings happens
    pub initial_recurrence: Period,
    pub rrule: RRule,
    // TODO these fields shouldn't be public
}

impl IcalRecurrenceDesc {
    /// Returns the earliest and latest date-times that might be in the
    /// recurrence set. Returns overall `None` if there are no elements in the
    /// recurrence. The end point is `None` if the recurrence goes on to
    /// infinity.
    pub fn pessimistic_boundaries(&self) -> Option<(DateTime<Utc>, Option<DateTime<Utc>>)> {
        let IcalRecurrenceDesc { initial_recurrence, rrule } = self;

        // find the start point of the recurrence
        let start = initial_recurrence.pessimistic_boundaries().0;

        // find the end point of the recurrence
        let end = if let Some(until) = rrule.get_until() {
            // the recurrence rule defines a set end point
            let last = initial_recurrence.shift_start_coerce(until.to_utc());
            Some(last.pessimistic_boundaries().1)
        } else if rrule.get_count().is_some() {
            // the recurrence rule defines a set number of instances
            let Some(end) = self.into_iter().last().map(|last| last.pessimistic_boundaries().1)
            else {
                // the recurrence rule defines no instances
                return None;
            };
            Some(end)
        } else {
            // the recurrence rule defines no end to instances
            None
        };

        Some((start, end))
    }

    pub fn get_all_instances_in_interval(
        &self,
        start: DateTime<Utc>,
        end: DateTime<Utc>,
    ) -> impl Iterator<Item = Period> + '_ {
        let start = rrule::Tz::Tz(chrono_tz::UTC).from_utc_datetime(&start.naive_utc());
        let end = rrule::Tz::Tz(chrono_tz::UTC).from_utc_datetime(&end.naive_utc());
        let rrule_set = self.to_rrule_set().after(start).before(end);
        let rrule::RRuleResult { dates, limited: false } = rrule_set.all(u16::MAX) else {
            panic!("there are way too many event instances to handle here");
        };
        dates.into_iter().map(|dt| self.initial_recurrence.shift_start_coerce(dt.to_utc()))
    }

    fn to_rrule_set(&self) -> rrule::RRuleSet {
        let IcalRecurrenceDesc { initial_recurrence, rrule } = self;
        // crate `rrule` only takes date-times, not date-without-times, so
        // convert the dt_start to a date-time
        let dt_start = initial_recurrence.start().to_specific_time();
        // convert from `chrono`'s `DateTime<Utc>` to `rrule`'s `DateTime<Tz>`,
        // while still keeping UTC
        let dt_start = rrule::Tz::Tz(chrono_tz::UTC).from_utc_datetime(&dt_start.naive_utc());

        rrule::RRuleSet::new(dt_start).rrule(rrule.clone())
    }
}

/// Module for safely encapsulating a recurrence rule iterator, working around
/// the limitations of the `rrule` crate.
mod recurrence_iter {
    use std::rc::Rc;

    use super::{IcalRecurrenceDesc, Period};

    pub struct IcalRecurrenceIter {
        initial_recurrence: Period,
        // in reality, this borrows from its sibling field `rrule_set`; the
        // static lifetime is fake to appease the borrow checker
        rrule_iter: rrule::RRuleSetIter<'static>,
        // although it says Rc, this is the only owner of the inner RRuleSet. it
        // is Rc instead of Box because Box asserts unique access to the
        // underlying data, which is not true here
        _rrule_set: Rc<rrule::RRuleSet>,
    }

    impl Iterator for IcalRecurrenceIter {
        type Item = Period;

        fn next(&mut self) -> Option<Self::Item> {
            self.rrule_iter.next().map(|dt| self.initial_recurrence.shift_start_coerce(dt.to_utc()))
        }
    }

    impl<'a> IntoIterator for &'a IcalRecurrenceDesc {
        type Item = Period;
        type IntoIter = IcalRecurrenceIter;

        fn into_iter(self) -> Self::IntoIter {
            // put the RRuleSet on the heap so that it can be borrowed by the
            // rrule iter
            let rrule_set = Rc::new(self.to_rrule_set());

            // SAFETY: the RRuleSet that the RRuleSetIter borrows from is on the
            // heap and never moved from there, so references to it will remain
            // valid as long as the Rc is valid. Since the Rc is moved into the
            // resulting struct at the same time as the RRuleSetIter, the two
            // will live together and have the same lifetime. Thus, the
            // internals of RRuleSetIter will always point to valid data, and
            // can be tricked into thinking the data is 'static.
            let rrule_iter: rrule::RRuleSetIter<'static> =
                unsafe { &*(rrule_set.as_ref() as *const rrule::RRuleSet) }.into_iter();

            IcalRecurrenceIter {
                initial_recurrence: self.initial_recurrence,
                rrule_iter,
                _rrule_set: rrule_set,
            }
        }
    }

    #[cfg(test)]
    mod test {
        use chrono::{DateTime, Days, Duration, NaiveDate, NaiveTime, TimeZone, Utc};
        use rrule::{Frequency, RRule};

        use super::*;

        #[test]
        fn generates_dt_periods() {
            fn gen_period(start: DateTime<Utc>) -> Period {
                Period::DateTimeInterval { start, end: start + Duration::hours(1) }
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
            assert_eq!(
                dates,
                vec![
                    gen_period(Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap()),
                    gen_period(Utc.with_ymd_and_hms(2024, 1, 3, 0, 0, 0).unwrap()),
                    gen_period(Utc.with_ymd_and_hms(2024, 1, 5, 0, 0, 0).unwrap()),
                ]
            );
        }

        #[test]
        fn generates_date_periods() {
            fn gen_period(start: NaiveDate) -> Period {
                Period::DateInterval { start, additional: Days::new(1) }
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
            assert_eq!(
                dates,
                vec![
                    gen_period(NaiveDate::from_ymd_opt(2024, 1, 1).unwrap()),
                    gen_period(NaiveDate::from_ymd_opt(2024, 1, 3).unwrap()),
                    gen_period(NaiveDate::from_ymd_opt(2024, 1, 5).unwrap()),
                ]
            );
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn period_pessimistic_boundaries() {
        let a = Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap();

        let dt_interval = Period::DateTimeInterval { start: a, end: a + Duration::hours(1) };
        assert_eq!(dt_interval.pessimistic_boundaries(), (a, a + Duration::hours(1)));

        let dt_point = Period::DateTime(a);
        assert_eq!(dt_point.pessimistic_boundaries(), (a, a));

        let date_interval = Period::DateInterval {
            start: NaiveDate::from_ymd_opt(2024, 1, 1).unwrap(),
            additional: Days::new(2),
        };
        let (bound_left, bound_right) = date_interval.pessimistic_boundaries();
        assert_eq!(
            bound_left,
            Utc.with_ymd_and_hms(2024, 1, 1, 0, 0, 0).unwrap() - Duration::hours(14)
        );
        assert_eq!(
            bound_right,
            Utc.with_ymd_and_hms(2024, 1, 4, 0, 0, 0).unwrap() + Duration::hours(12)
        );
    }
}
