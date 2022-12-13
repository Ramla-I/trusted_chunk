// #[cfg(feature="prusti")]
use prusti_contracts::*;

use core::ops::RangeInclusive;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct TrustedRangeInclusive {
    pub(crate) start: usize,
    pub(crate) end: usize
}

impl TrustedRangeInclusive {
    // #[cfg_attr(feature="prusti", requires(start <= end))]
    // #[cfg_attr(feature="prusti", ensures(result.start == start))]
    // #[cfg_attr(feature="prusti", ensures(result.end == end))]
    #[requires(start <= end)]
    #[ensures(result.start == start)]
    #[ensures(result.end == end)]
    pub(crate) const fn new(start: usize, end: usize) -> Self {
        Self{start, end}
    }

    /// SPEC FUNCTION
    // #[cfg_attr(feature="prusti", pure)]
    #[pure]
    pub(crate) fn overlap(&self, range2: &Self) -> bool {
        ((self.end >= range2.start) && (self.start <= range2.end)) 
        || 
        ((range2.end >= self.start) && (range2.start <= self.end))
    }

    pub fn to_range_inclusive(&self) -> RangeInclusive<usize> {
        RangeInclusive::new(self.start, self.end)
    }
}

