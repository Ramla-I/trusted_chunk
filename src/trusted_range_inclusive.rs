// #[cfg(feature="prusti")]
use prusti_contracts::*;

use crate::unique_check::*;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct RangeInclusive<Idx: Clone + PartialOrd + PartialEq> {
    pub(crate) start: Idx,
    pub(crate) end: Idx
}

impl<Idx: Clone + PartialOrd + PartialEq> RangeInclusive<Idx> {
    // #[cfg_attr(feature="prusti", requires(start <= end))]
    // #[cfg_attr(feature="prusti", ensures(result.start == start))]
    // #[cfg_attr(feature="prusti", ensures(result.end == end))]
    #[ensures(result.start == start)]
    #[ensures(result.end == end)]
    pub(crate) const fn new(start: Idx, end: Idx) -> Self {
        Self{start, end}
    }

    pub const fn start(&self) -> &Idx {
        &self.start
    }

    pub const fn end(&self) -> &Idx {
        &self.end
    }

    #[pure]
    #[trusted]
    #[ensures(result ==> other.overlaps_with(&self))]
    pub fn overlaps_with(&self, other: &Self) -> bool {
        ((self.end >= other.start) && (self.start <= other.end)) 
        || 
        ((other.end >= self.start) && (other.start <= self.end))
    }
}


