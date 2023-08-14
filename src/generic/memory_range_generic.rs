use prusti_contracts::*;

#[cfg(prusti)]
use crate::external_spec::trusted_range_inclusive::*;
#[cfg(not(prusti))]
use range_inclusive::*;

use core::char::MAX;
use core::ops::{Deref, DerefMut, Add, Sub};
use core::cmp::{PartialOrd, Ord, Ordering};
use crate::{
    *,
    external_spec::{trusted_option::*, trusted_result::*},
    generic::range_trait::*,
};

pub(crate) const MAX_VIRTUAL_ADDRESS: usize = usize::MAX;
pub(crate) const MAX_PAGE_NUMBER: usize = MAX_VIRTUAL_ADDRESS / PAGE_SIZE;
pub(crate) const PAGE_SIZE: usize = 4096;
pub(crate) const MIN_FRAME_NUMBER: usize = 0;
pub(crate) const MAX_FRAME_NUMBER: usize = 0xFF_FFFF_FFFF; // usize::MAX & 0x000F_FFFF_FFFF_FFFF / PAGE_SIZE


#[pure]
fn min(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

#[pure]
fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}

#[pure]
fn min_mem_unit<U: UnitTrait>(a: U, b: U) -> U {
    if a.less_than(&b) { a } else { b }
}

#[pure]
fn max_mem_unit<U: UnitTrait>(a: U, b: U) -> U {
    if a.greater_than(&b) { a } else { b }
}

#[extern_spec]
impl<U: UnitTrait> PartialEq for Range<U> {
    #[pure]
    fn eq(&self, other: &Self) -> bool;
}

/// A struct representing an unallocated region in memory.
/// Its functions are formally verified to prevent range overlaps between chunks.
// #[cfg_attr(not(prusti), derive(Debug))]
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Range<U: UnitTrait>(RangeInclusive<U>);

impl<U: UnitTrait> UniqueCheck for Range<U> {
    #[pure]
    #[trusted] // has to be trusted to call itself, which then requires us to define a spec for the fn as well :(
    fn range_overlaps(&self, other: &Self) -> bool {
        self.range_overlaps(other)
    }

    #[pure]
    #[trusted]
    fn equals(&self, other: &Self) -> bool {
        self == other
    }
}

impl<U: UnitTrait> Range<U> {
    #[ensures(result.start_frame() == start)]
    #[ensures(result.end_frame() == end)]
    pub const fn new(start: U, end: U) -> Range<U> {
        Range(RangeInclusive::new(start, end))
    }

    // #[trusted]
    #[ensures(result.is_empty())]
    pub fn empty() -> Range<U> {
        Range::new(U::new(1), U::new(0))
    }
}

// The newly added methods for FrameRange required for verification
impl <U: UnitTrait + PartialEq + Copy + PartialOrd> Range<U> {
    #[pure]
    #[trusted]
    #[ensures(result == *self.0.start())]
    pub fn start_frame(&self) -> U {
        *self.0.start()
    }

    #[pure]
    #[trusted]
    #[ensures(result == *self.0.end())]
    pub fn end_frame(&self) -> U {
        *self.0.end()
    }

    #[pure]
    #[ensures(result == (self.start_frame().greater_than(&self.end_frame())))]
    #[ensures(result == !(self.start_frame().less_than_equal(&self.end_frame())))]
    pub fn is_empty(&self) -> bool {
        !(self.start_frame().less_than_equal(&self.end_frame()))
    }

    #[pure]
    #[trusted] // has to be trusted to call itself, which then requires us to define a spec for the fn as well :(
    #[ensures(result == other.range_overlaps(&self))] // if we dont have this condition, then post-condition of push_unique_with_precond wont' verify
    #[ensures({
        let starts = max_mem_unit(self.start_frame(), other.start_frame());
        let ends   = min_mem_unit(self.end_frame(), other.end_frame());
        result == starts.less_than_equal(&ends) 
   })]
    /// Returning a FrameRange here requires use to set the RangeInclusive new function as pure which
    /// requires Idx to be Copy, so just return bool.
    pub fn range_overlaps(&self, other: &Range<U>) -> bool {
        let starts = max_mem_unit(self.start_frame(), other.start_frame());
        let ends   = min_mem_unit(self.end_frame(), other.end_frame());
        starts.less_than_equal(&ends)
    }

    #[pure]
    pub fn contains_range(&self, other: &Range<U>) -> bool {
        !other.is_empty()
        && (other.start_frame().greater_than_equal(&self.start_frame()))
        && (other.end_frame().less_than_equal(&self.end_frame()))
    }

    /// Splits a range into 1-3 ranges, depending on where the split is at.
    /// It is formally verified that the resulting chunks are disjoint, contiguous and their start/end is equal to that of the original chunk.
    /// 
    /// # Post-conditions:
    /// * If it succeeds, then the resulting chunks have no overlapping ranges
    /// * If it succeeds, then the resulting chunks are contiguous
    /// * If it succeeds, then the resulting chunks combined have the same range as `self`
    /// * If it fails, then the original chunk is returned
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        ((split_range.0).is_some() ==> !peek_option_ref(&split_range.0).range_overlaps(&split_range.1)) 
        && ((split_range.2).is_some() ==> !split_range.1.range_overlaps(peek_option_ref(&split_range.2)))
        && (((split_range.0).is_some() && (split_range.2).is_some()) ==> !peek_option_ref(&split_range.0).range_overlaps(peek_option_ref(&split_range.2)))
    })]
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        ((split_range.0).is_some() ==> peek_option_ref(&split_range.0).end_frame() == split_range.1.start_frame().minus(1))
        && ((split_range.2).is_some() ==> peek_option_ref(&split_range.2).start_frame() == split_range.1.end_frame().plus(1))
    })]
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        ((split_range.0).is_some() ==> peek_option_ref(&split_range.0).start_frame() == self.start_frame())
        && ((split_range.0).is_none() ==> (split_range.1.start_frame() == self.start_frame() || (split_range.1.start_frame().number() == MIN_FRAME_NUMBER)))
        && ((split_range.2).is_some() ==> peek_option_ref(&split_range.2).end_frame() == self.end_frame())
        && ((split_range.2).is_none() ==> ((split_range.1.end_frame() == self.end_frame()) || (split_range.1.end_frame().number() >= MAX_FRAME_NUMBER)))
    })]
    #[ensures(result.is_err() ==> {
        let orig_range = peek_err_ref(&result);
        (orig_range.start_frame() == self.start_frame()) && (orig_range.end_frame() == self.end_frame())
    })]
    pub fn split_range(self, frames_to_extract: Range<U>) -> Result<(Option<Range<U>>, Range<U>, Option<Range<U>>), Range<U>> {
        let min_mem_unit = U::new(MIN_FRAME_NUMBER);
        let max_mem_unit = U::new(MAX_FRAME_NUMBER);

        if !self.contains_range(&frames_to_extract) {
            return Err(self);
        }

        
        let start_frame = frames_to_extract.start_frame();
        let end_frame = frames_to_extract.end_frame();
        prusti_assert!(self.start_frame().less_than_equal(&start_frame));
        prusti_assert!(self.end_frame().greater_than_equal(&end_frame));

        let before_start = if start_frame == min_mem_unit || start_frame == self.start_frame() {
            None
        } else {
            prusti_assert!(self.start_frame().less_than(&start_frame));
            prusti_assert!(self.start_frame().less_than_equal(&start_frame.minus(1)));
            Some(Range::new(self.start_frame(), start_frame.minus(1)))
        };

        let start_to_end = frames_to_extract;

        // impossible for end_frame to be greater than max_mem_unit so should add a precond
        let after_end = if end_frame.greater_than_equal(&max_mem_unit) || end_frame == self.end_frame() {
            None
        } else {
            prusti_assert!(end_frame.less_than(&max_mem_unit));
            prusti_assert!(self.end_frame().greater_than(&end_frame));
            prusti_assert!(self.end_frame().greater_than_equal(&end_frame.plus(1)));
            prusti_assert!(self.end_frame().greater_than_equal(&start_to_end.end_frame().plus(1)));
            prusti_assert!(self.end_frame().greater_than(&start_to_end.end_frame()));
            prusti_assert!(end_frame.plus(1).greater_than(&end_frame));

            let range = Range::new(end_frame.plus(1), self.end_frame());
            prusti_assert!(range.start_frame().greater_than(&start_to_end.end_frame()));
            prusti_assert!(range.start_frame().greater_than(&start_to_end.end_frame()));

            Some(Range::new(end_frame.plus(1), self.end_frame())) 
        };

        Ok((before_start, start_to_end, after_end))
    }


    /// Splits a chunk into 2 chunks at the frame with number `at_frame`.
    /// It is formally verified that the resulting chunks are disjoint, contiguous and their start/end is equal to that of the original chunk.
    /// 
    /// # Post-conditions:
    /// * If it succeeds, then both chunks can't be empty
    /// * If it succeeds and the first chunk is empty, then the second chunk is equal to `self`
    /// * If it succeeds and the second chunk is empty, then the first chunk is equal to `self`
    /// * If it succeeds and both chunks aren't empty, then the chunks are contiguous and their combined range is equal to the range of `self`
    /// * If it fails, then the original chunk is returned
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        split_range.0.is_empty() && !split_range.1.is_empty() ||
        !split_range.0.is_empty() && split_range.1.is_empty() ||
        !split_range.0.is_empty() && !split_range.1.is_empty()
    })]
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        split_range.0.is_empty() ==> (split_range.1.start_frame() == self.start_frame() && split_range.1.end_frame() == self.end_frame())
    })]
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        split_range.1.is_empty() ==> (split_range.0.start_frame() == self.start_frame() && split_range.0.end_frame() == self.end_frame())
    })]
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        (!split_range.0.is_empty() && !split_range.1.is_empty()) ==> (
            split_range.0.start_frame() == self.start_frame() 
            && split_range.0.end_frame() == at_frame.minus(1) 
            && split_range.1.start_frame() == at_frame 
            && split_range.1.end_frame() == self.end_frame()
        )
    })]
    #[ensures(result.is_err() ==> {
        let orig_chunk = peek_err_ref(&result);
        (orig_chunk.start_frame() == self.start_frame()) && (orig_chunk.end_frame() == self.end_frame())
    })]
    pub fn split_at(mut self, at_frame: U) -> Result<(Self, Self), Self> {
        if self.is_empty() {
            return Err(self);
        }
        let end_of_first = at_frame.minus(1);

        let (first, second) = if at_frame == self.start_frame() && at_frame.less_than_equal(&self.end_frame()) {
            let first  = Range::empty();
            let second = Range::new(at_frame, self.end_frame());
            (first, second)
        } 
        else if at_frame == self.end_frame().plus(1) && end_of_first.greater_than_equal(&self.start_frame()) {
            let first  = Range::new(self.start_frame(), self.end_frame()); 
            let second = Range::empty();
            (first, second)
        }
        else if at_frame.greater_than(&self.start_frame()) && end_of_first.less_than_equal(&self.end_frame()) {
            let first  = Range::new(self.start_frame(), end_of_first);
            let second = Range::new(at_frame, self.end_frame());
            (first, second)
        }
        else {
            return Err(self);
        };
 
        Ok(( first, second ))
    }


    /// Merges `other` into `self`.
    /// Succeeds if `other` lies right before `self` or right after.
    /// 
    /// # Post-conditions:
    /// * If it succeeds, then `other` and `self` were contiguous, and either `self`'s start bound has been updated to `other`'s start 
    /// or `self`s end has been updated to `other`'s end
    /// * If it fails, then `self` remains unchanged and `other` is returned
    #[ensures(result.is_ok() ==> 
        (old(self.start_frame()) == other.end_frame().plus(1) && self.start_frame() == other.start_frame() && self.end_frame() == old(self.end_frame())) 
        || 
        (old(self.end_frame()).plus(1) == other.start_frame() && self.end_frame() == other.end_frame() && self.start_frame() == old(self.start_frame()))
    )]
    #[ensures(result.is_err() ==> {
        let chunk = peek_err_ref(&result);
        (chunk.start_frame() == other.start_frame()) && (chunk.end_frame() == other.end_frame()) 
    })]
    #[ensures(result.is_err() ==> {
        (self.start_frame() == old(self.start_frame())) && (self.end_frame() == old(self.end_frame())) 
    })]
    pub fn merge(&mut self, other: Self) -> Result<(), Self> {
        if self.is_empty() || other.is_empty() {
            return Err(other);
        }

        if self.start_frame() == other.end_frame().plus(1) {
            // `other` comes contiguously before `self`
            *self = Range::new(other.start_frame(), self.end_frame());
        } 
        else if self.end_frame().plus(1) == other.start_frame() {
            // `self` comes contiguously before `other`
            *self = Range::new(self.start_frame(), other.end_frame());
        }
        else {
            // non-contiguous
            return Err(other);
        } 
        Ok(())
    }
}


impl<U: UnitTrait + Copy + PartialEq + PartialOrd> Deref for Range<U> {
    type Target = RangeInclusive<U>;
    #[pure]
    fn deref(&self) -> &RangeInclusive<U> {
        &self.0
    }
}
