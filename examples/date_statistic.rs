//! This examples shows how to use Augmentation to make date based statistics easy
use std::cmp::Ordering;

use sweep_bptree::{
    augment::Augmentation,
    tree::visit::{DescendVisit, DescendVisitResult},
    BPlusTreeMap,
};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Default)]
struct Date {
    year: u16,
    month: u8,
    day: u8,
}

impl Date {
    fn compare(&self, other: &Self) -> DateCompare {
        match (
            self.year == other.year,
            self.month == other.month,
            self.day == other.day,
        ) {
            (true, true, true) => DateCompare::SameDay,
            (true, true, _) => DateCompare::SameMonth,
            (true, _, _) => DateCompare::SameYear,
            _ => DateCompare::DifferentYear,
        }
    }
}

struct CountForYear {
    year: u16,
    count: usize,
}

impl CountForYear {
    pub fn new(year: u16) -> Self {
        Self { year, count: 0 }
    }
}

impl<V> DescendVisit<Date, V, DateStatistic> for CountForYear {
    type Result = usize;

    fn visit_inner(
        &mut self,
        _keys: &[Date],
        augmentations: &[DateStatistic],
    ) -> DescendVisitResult<Self::Result> {
        // Need to handle following cases:
        // 1. if the year is at min boundary, then we can return it
        // 2. if the year is larger than min, lower than max, then go down
        // 3. if the year is equal to max, then accumulate and move to next
        // 4. if the year is larger than max, then move to next

        for (idx, a) in augmentations.iter().enumerate() {
            match a.min.date.year.cmp(&self.year) {
                Ordering::Less => match a.max.date.year.cmp(&self.year) {
                    Ordering::Less => continue,
                    Ordering::Equal => {
                        self.count += a.max.counter.year;
                        continue;
                    }
                    Ordering::Greater => {
                        return DescendVisitResult::GoDown(idx);
                    }
                },
                Ordering::Equal => match a.max.date.year.cmp(&self.year) {
                    Ordering::Less => {
                        unreachable!()
                    }
                    Ordering::Equal => {
                        // min and max has same year, we can pick either min or max
                        self.count += a.max.counter.year;
                        continue;
                    }
                    Ordering::Greater => {
                        self.count += a.min.counter.year;
                        return DescendVisitResult::Complete(self.count);
                    }
                },
                Ordering::Greater => return DescendVisitResult::Complete(self.count),
            }
        }

        DescendVisitResult::Complete(self.count)
    }

    fn visit_leaf(&mut self, keys: &[Date], _values: &[V]) -> Option<Self::Result> {
        for k in keys {
            if k.year == self.year {
                self.count += 1
            }
        }

        Some(self.count)
    }
}

enum DateCompare {
    SameDay,
    SameMonth,
    SameYear,
    DifferentYear,
}

#[derive(Default, Clone, Debug)]
struct Counter {
    year: usize,
    month: usize,
    day: usize,
}

#[derive(Clone, Debug, Default)]
struct DateStatisticEntry {
    date: Date,
    /// counter to track how many items for each time granularity
    counter: Counter,
}

/// This Augmentation keeps track of item count for child node.
#[derive(Clone, Debug, Default)]
struct DateStatistic {
    min: DateStatisticEntry,
    max: DateStatisticEntry,
}

/// How the `DateStatistic` aggregated from children
impl Augmentation<Date> for DateStatistic {
    /// aggregate for inner
    fn from_inner(_keys: &[Date], augmentations: &[Self]) -> Self {
        let mut augmentation_iter = augmentations.iter();

        // unwrap: augmentation is not empty
        let first_a = augmentation_iter.next().unwrap();
        let mut min = first_a.min.clone();
        let mut max = first_a.max.clone();

        for augmentation in augmentation_iter {
            match min.date.compare(&augmentation.min.date) {
                DateCompare::SameDay => {
                    min.counter.day += augmentation.min.counter.day;
                    min.counter.month += augmentation.min.counter.month;
                    min.counter.year += augmentation.min.counter.year;
                }
                DateCompare::SameMonth => {
                    min.counter.month += augmentation.min.counter.month;
                    min.counter.year += augmentation.min.counter.year;
                }
                DateCompare::SameYear => {
                    min.counter.year += augmentation.min.counter.year;
                }
                DateCompare::DifferentYear => {}
            }

            match max.date.compare(&augmentation.max.date) {
                DateCompare::SameDay => {
                    max.counter.day += augmentation.max.counter.day;
                    max.counter.month += augmentation.max.counter.month;
                    max.counter.year += augmentation.max.counter.year;
                }
                DateCompare::SameMonth => {
                    max.date = augmentation.max.date;
                    max.counter.day = augmentation.max.counter.day;
                    max.counter.month += augmentation.max.counter.month;
                    max.counter.year += augmentation.max.counter.year;
                }
                DateCompare::SameYear => {
                    max.date = augmentation.max.date;
                    max.counter.day = augmentation.max.counter.day;
                    max.counter.month = augmentation.max.counter.month;
                    max.counter.year += augmentation.max.counter.year;
                }
                DateCompare::DifferentYear => {
                    max = augmentation.max.clone();
                }
            }
        }

        Self { min, max }
    }

    /// aggregate for leaf node
    fn from_leaf(keys: &[Date]) -> Self {
        let mut keys_iter = keys.iter();
        let first_key = keys_iter.next().unwrap();

        let mut min = DateStatisticEntry {
            date: first_key.clone(),
            counter: Counter {
                year: 1,
                month: 1,
                day: 1,
            },
        };
        let mut max = min.clone();

        for key in keys_iter {
            match min.date.compare(&key) {
                DateCompare::SameDay => {
                    min.counter.day += 1;
                    min.counter.month += 1;
                    min.counter.year += 1;
                }
                DateCompare::SameMonth => {
                    min.counter.month += 1;
                    min.counter.year += 1;
                }
                DateCompare::SameYear => {
                    min.counter.year += 1;
                }
                DateCompare::DifferentYear => {}
            }
            match max.date.compare(&key) {
                DateCompare::SameDay => {
                    max.counter.day += 1;
                    max.counter.month += 1;
                    max.counter.year += 1;
                }
                DateCompare::SameMonth => {
                    max.date = key.clone();
                    max.counter.day = 1;
                    max.counter.month += 1;
                    max.counter.year += 1;
                }
                DateCompare::SameYear => {
                    max.date = key.clone();
                    max.counter.day = 1;
                    max.counter.month = 1;
                    max.counter.year += 1;
                }
                DateCompare::DifferentYear => {
                    max.date = key.clone();
                    max.counter = Counter {
                        year: 1,
                        month: 1,
                        day: 1,
                    };
                }
            }
        }

        Self { min, max }
    }
}

fn main() {
    let mut tree = BPlusTreeMap::<Date, (), DateStatistic>::new();

    for year in 2011..2021 {
        for month in 1..13 {
            let day_count = day_count(year, month);
            for day in 0..day_count {
                let date = Date {
                    year: year as u16,
                    month: month as u8,
                    day: day as u8,
                };
                // insert two items each day
                tree.insert(date, ());
            }
        }
    }

    println!("size: {} root: {:?}", tree.len(), tree.root_augmentation());
    for year in 2011..2021 {
        println!(
            "date item at {year} is {}",
            tree.descend_visit(CountForYear::new(year))
                .unwrap_or_default()
        );
    }

    assert_eq!(
        tree.descend_visit(CountForYear::new(2011))
            .unwrap_or_default(),
        365
    );

    let year = 2011;
    // remove 3 days
    for (month, day) in [(1, 3), (3, 3), (5, 30)] {
        tree.remove(&Date { year, month, day });
    }
    assert_eq!(
        tree.descend_visit(CountForYear::new(2011))
            .unwrap_or_default(),
        362
    );
}

/// a function check whether a year is leap
/// https://en.wikipedia.org/wiki/Leap_year#Algorithm
fn is_leap_year(year: usize) -> bool {
    if year % 4 != 0 {
        return false;
    }

    if year % 100 != 0 {
        return true;
    }

    year % 400 == 0
}

/// a function returns day count for a month
fn day_count(year: usize, month: usize) -> usize {
    match (is_leap_year(year), month) {
        (true, 2) => 29,
        (false, 2) => 28,
        (_, 1 | 3 | 5 | 7 | 8 | 10 | 12) => 31,
        _ => 30,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_leap_year() {
        assert_eq!(is_leap_year(2020), true);
        assert_eq!(is_leap_year(2021), false);
        assert_eq!(is_leap_year(2024), true);
        assert_eq!(is_leap_year(2100), false);
        assert_eq!(is_leap_year(2000), true);
    }
}
