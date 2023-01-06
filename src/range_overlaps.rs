use crate::trusted_range_inclusive::*;
use core::cmp::{max,min};

#[pure]
#[trusted]
#[ensures(result ==> range_overlaps(range2, range1))]
// #[ensures(range1.is_empty || range2.is_empty() ==> result)]
// #[ensures(result ==> {

// })]
pub fn range_overlaps(range1: &RangeInclusive<usize>, range2: &RangeInclusive<usize>) -> bool {
    if range1.is_empty() || range2.is_empty() {
        return false;
    }

    let starts = max(range1.start(), range2.start());
    let ends = min(range1.end(), range2.end());
    starts <= ends
}