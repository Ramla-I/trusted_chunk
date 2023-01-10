cfg_if::cfg_if! {
if #[cfg(prusti)] {
    use crate::spec::trusted_range_inclusive::*;
} else {
    use range_inclusive::*;
}
}

use core::{
    ops::{Add, AddAssign, Deref, DerefMut, Sub, SubAssign},
};
use crate::{MAX_VIRTUAL_ADDRESS, PAGE_SHIFT, PAGE_SIZE, MAX_PAGE_NUMBER};

/// A `" Frame "` is a chunk of **" physical "** memory aligned to a [`PAGE_SIZE`] boundary.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Frame {
    pub(crate) number: usize,
}

/// A range of [`Frame`]s that are contiguous in physical memory.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct FrameRange(RangeInclusive<Frame>);

impl FrameRange {
    /// Creates a new range of [`Frame`]s that spans from `start` to `end`, both inclusive bounds.
    pub const fn new(start: Frame, end: Frame) -> FrameRange {
        FrameRange(RangeInclusive::new(start, end))
    }

    pub const fn into_inner(&self) -> RangeInclusive<Frame> {
        self.0
    }
}

impl Deref for FrameRange {
    type Target = RangeInclusive<Frame>;
    #[pure]
    fn deref(&self) -> &RangeInclusive<Frame> {
        &self.0
    }
}
