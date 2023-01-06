// #[cfg(feature="prusti")]
use prusti_contracts::*;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct RangeInclusive<Idx: Clone + PartialOrd> {
    start: Idx,
    end: Idx
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

    #[pure]
    pub const fn start(&self) -> &Idx {
        &self.start
    }

    #[pure]
    pub const fn end(&self) -> &Idx {
        &self.end
    }

    pub fn is_empty(&self) -> bool {
        !(self.start <= self.end)
    }

}


#[pure]
#[trusted]
#[ensures(result ==> range_overlaps(range2, range1))]
pub fn range_overlaps<Idx: Clone + PartialOrd + Ord>(range1: &RangeInclusive<Idx>, range2: &RangeInclusive<Idx>) -> bool {
    if range1.is_empty() || range2.is_empty() {
        return false;
    }

    let starts = if range1.start() >= range2.start() {
        range1.start()
    } else {
        range2.start()
    };

    let ends = if range1.end() <= range2.end() {
        range1.end()
    } else {
        range2.end()
    };

    starts <= ends
}