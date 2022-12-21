use core::{
    ops::{Add, AddAssign, Deref, DerefMut, RangeInclusive, Sub, SubAssign},
};

pub const MAX_VIRTUAL_ADDRESS: usize = 0xFFFF_FFFF;//usize::MAX;

/// The lower 12 bits of a virtual address correspond to the P1 page frame offset. 
pub const PAGE_SHIFT: usize = 12;
/// Page size is 4096 bytes, 4KiB pages.
pub const PAGE_SIZE: usize = 1 << PAGE_SHIFT;

pub const MAX_PAGE_NUMBER: usize = MAX_VIRTUAL_ADDRESS / PAGE_SIZE;

/// A `" Frame "` is a chunk of **" physical "** memory aligned to a [`PAGE_SIZE`] boundary.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Frame {
    pub(crate) number: usize,
}

impl Add<usize> for Frame {
    type Output = Frame;
    fn add(self, rhs: usize) -> Frame {
        // cannot exceed max page number (which is also max frame number)
        Frame {
            number: core::cmp::min(MAX_PAGE_NUMBER, self.number.saturating_add(rhs)),
        }
    }
}
impl AddAssign<usize> for Frame {
    fn add_assign(&mut self, rhs: usize) {
        *self = Frame {
            number: core::cmp::min(MAX_PAGE_NUMBER, self.number.saturating_add(rhs)),
        };
    }
}
impl Sub<usize> for Frame {
    type Output = Frame;
    fn sub(self, rhs: usize) -> Frame {
        Frame {
            number: self.number.saturating_sub(rhs),
        }
    }
}
impl SubAssign<usize> for Frame {
    fn sub_assign(&mut self, rhs: usize) {
        *self = Frame {
            number: self.number.saturating_sub(rhs),
        };
    }
}


/// A range of [`Frame`]s that are contiguous in physical memory.
#[derive(Clone, PartialEq, Eq)]
pub struct FrameRange(RangeInclusive<Frame>);

impl FrameRange {
    /// Creates a new range of [`Frame`]s that spans from `start` to `end`, both inclusive bounds.
    pub const fn new(start: Frame, end: Frame) -> FrameRange {
        FrameRange(RangeInclusive::new(start, end))
    }
}

impl Deref for FrameRange {
    type Target = RangeInclusive<Frame>;
    fn deref(&self) -> &RangeInclusive<Frame> {
        &self.0
    }
}
impl DerefMut for FrameRange {
    fn deref_mut(&mut self) -> &mut RangeInclusive<Frame> {
        &mut self.0
    }
}