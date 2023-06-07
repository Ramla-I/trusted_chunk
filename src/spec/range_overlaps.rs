//! This function defines what it means for two RangeInclusives to overlap. 
//! It is used in both the implementation and specification (not sure how to work around that).
//! If this definition of overlapping doesn't match what the rest of the system expects, then the results of verification won't make sense.
//! 
//! To Do: Finalize relationship between overlapping and empty ranges.
//! Right now an empty range will never overlap with another even if the actual numbers do overlap

use prusti_contracts::*;
cfg_if::cfg_if! {
if #[cfg(prusti)] {
    use crate::external_spec::trusted_range_inclusive::*;
} else {
    use range_inclusive::*;
}
}

use core::cmp::{max,min};

// #[pure]
// fn max(a: usize, b: usize) -> usize {
//     if a >= b { a } else { b }
// }

// #[pure]
// fn min(a: usize, b: usize) -> usize {
//     if a <= b { a } else { b }
// }

#[pure]
#[trusted] // Only trusted functions can call themselves in their contracts
#[ensures(result ==> range_overlaps(range2, range1))]
pub fn range_overlaps(range1: &RangeInclusive<usize>, range2: &RangeInclusive<usize>) -> bool {
    if range1.is_empty() || range2.is_empty() {
        return false;
    }

    let starts = max(range1.start(), range2.start());
    let ends = min(range1.end(), range2.end());
    starts <= ends
}

#[cfg(test)]
mod test {
    use range_inclusive::RangeInclusive;

    use super::range_overlaps;

    #[test]
    fn overlapping() {
        let r1 = RangeInclusive::new(0,5);
        let r2 = RangeInclusive::new(4, 7);
        assert!(range_overlaps(&r1, &r2));

        let r1 = RangeInclusive::new(0,5);
        let r2 = RangeInclusive::new(5, 5);
        assert!(range_overlaps(&r1, &r2));
    }

    #[test]
    fn not_overlapping() {
        // empty ranges
        let r1 = RangeInclusive::new(5,0);
        let r2 = RangeInclusive::new(4, 7);
        assert!(!range_overlaps(&r1, &r2));

        // empty ranges
        let r1 = RangeInclusive::new(5,5);
        let r2 = RangeInclusive::new(6, 5);
        assert!(!range_overlaps(&r1, &r2));

        let r1 = RangeInclusive::new(3,5);
        let r2 = RangeInclusive::new(6, 7);
        assert!(!range_overlaps(&r1, &r2));
    }

}

// #[pure]
// #[trusted]
// #[ensures(result ==> range_overlaps(range2, range1))]
// pub fn range_overlaps<Idx: Clone + PartialOrd + Ord>(range1: &RangeInclusive<Idx>, range2: &RangeInclusive<Idx>) -> bool {
//     if range1.is_empty() || range2.is_empty() {
//         return false;
//     }

//     let starts = if range1.start() >= range2.start() {
//         range1.start()
//     } else {
//         range2.start()
//     };

//     let ends = if range1.end() <= range2.end() {
//         range1.end()
//     } else {
//         range2.end()
//     };

//     starts <= ends
// }