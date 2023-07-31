use prusti_contracts::*;

#[cfg(prusti)]
use crate::external_spec::trusted_range_inclusive::*;
#[cfg(not(prusti))]
use range_inclusive::*;

use core::ops::{Deref, DerefMut, Add, Sub};
use core::cmp::{PartialOrd, Ord, Ordering};
use crate::{
    *,
    external_spec::{trusted_option::*, trusted_result::*},
    // spec::{framerange_spec::*},
};

pub const MAX_VIRTUAL_ADDRESS: usize = usize::MAX;
pub const MAX_PAGE_NUMBER: usize = MAX_VIRTUAL_ADDRESS / PAGE_SIZE;
pub const PAGE_SIZE: usize = 4096;

//Prusti error: Unsupported constant type
const MIN_FRAME: Frame = Frame { number: 0 };
//usize::MAX & 0x000F_FFFF_FFFF_FFFF / PAGE_SIZE
const MAX_FRAME: Frame = Frame { number: 0xFF_FFFF_FFFF };

//Prusti error: Unsupported constant type
const MIN_FRAME_NUMBER: usize = 0;
//usize::MAX & 0x000F_FFFF_FFFF_FFFF / PAGE_SIZE
const MAX_FRAME_NUMBER: usize = 0xFF_FFFF_FFFF;


#[pure]
fn min(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

#[pure]
fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}

#[pure]
fn min_frame(a: Frame, b: Frame) -> Frame {
    if a.less_than(&b) { a } else { b }
}

#[pure]
fn max_frame(a: Frame, b: Frame) -> Frame {
    if a.greater_than(&b) { a } else { b }
}

#[pure]
#[trusted]
#[ensures(usize::MAX - a < b ==> result == usize::MAX)]
#[ensures(usize::MAX - a > b ==> result == a + b)]
#[ensures(usize::MAX - a == b ==> result == a + b)]
#[ensures(usize::MAX - a == b ==> result == usize::MAX)]
fn saturating_add(a: usize, b: usize) -> usize {
     a.saturating_add(b)
}

#[pure]
#[trusted]
#[ensures(a < b ==> result == 0)]
#[ensures(a >= b ==> result == a - b)]
#[ensures(a == b ==> result == 0)]
fn saturating_sub(a: usize, b: usize) -> usize {
     a.saturating_sub(b)
}


#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(prusti), derive(Debug))]
pub struct Frame{
    number: usize
}

impl Deref for Frame {
    type Target = usize;
    #[pure]
    fn deref(&self) -> &Self::Target {
        &self.number
    }
}

#[extern_spec]
impl PartialEq for Frame {
    #[pure]
    #[ensures(result == (self.number == other.number))]
    fn eq(&self, other: &Self) -> bool;
}

#[extern_spec]
impl PartialOrd for usize {
    #[pure]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering>;
}

#[extern_spec]
impl PartialOrd for Frame {
    #[pure]
    #[ensures(result == self.number.partial_cmp(&other.number))]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering>;

    // Uncommenting these leads to an unexpected panic in Prusti
    // but without these can't use comparison operators for frames in pure functions.
    
    // #[pure]
    // #[ensures(result == (self.number < other.number))]
    // fn lt(&self, other: &Self) -> bool;

    // #[pure]
    // #[ensures(result == (self.number <= other.number))]
    // fn le(&self, other: &Self) -> bool;
    
    // #[pure]
    // #[ensures(result == (self.number > other.number))]
    // fn gt(&self, other: &Self) -> bool;
    
    // #[pure]
    // #[ensures(result == (self.number >= other.number))]
    // fn ge(&self, other: &Self) -> bool;
}

impl Add<usize> for Frame {
    type Output = Frame;
    fn add(self, rhs: usize) -> Frame {
        Frame {
            number: min(0xFF_FFFF_FFFF, self.number.saturating_add(rhs)),
        }
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

impl Frame {
    #[pure]
    pub const fn number(&self) -> usize {
        self.number
    }

    #[pure]
    #[trusted]
    #[ensures(result.number == min(MAX_FRAME_NUMBER, saturating_add(self.number, rhs)))]
    #[ensures(result.greater_than_equal(&self))]
    #[ensures(rhs == 0 ==> result == self)]
    #[ensures(rhs > 0 ==> result.greater_than(&self))]
    pub fn plus(self, rhs: usize) -> Self {
        self + rhs
    }

    #[pure]
    #[trusted]
    #[ensures(result.number == saturating_sub(self.number, rhs))]
    #[ensures(result.less_than_equal(&self))]
    #[ensures(rhs == 0 ==> result == self)]
    #[ensures(rhs > 0 ==> result.less_than(&self))]
    pub fn minus(self, rhs: usize) -> Self {
        self - rhs
    }

    #[pure]
    #[trusted]
    #[ensures(result == (self.number < rhs.number))]
    #[ensures(!result ==> self.greater_than_equal(&rhs))]
    pub fn less_than(self, rhs: &Self) -> bool {
        self < *rhs
    }

    #[pure]
    #[trusted]
    #[ensures(result == (self.number <= rhs.number))]
    #[ensures(!result ==> self.greater_than(&rhs))]
    pub fn less_than_equal(self, rhs: &Self) -> bool {
        self <= *rhs
    }

    #[pure]
    #[trusted]
    #[ensures(result == (self.number > rhs.number))]
    #[ensures(!result ==> self.less_than_equal(&rhs))]
    pub fn greater_than(self, rhs: &Self) -> bool {
        self > *rhs
    }

    #[pure]
    #[trusted]
    #[ensures(result == (self.number >= rhs.number))]
    #[ensures(!result ==> self.less_than(&rhs))]
    pub fn greater_than_equal(self, rhs: &Self) -> bool {
        self >= *rhs
    }


}



/// A struct representing an unallocated region in memory.
/// Its functions are formally verified to prevent range overlaps between chunks.
#[cfg_attr(not(prusti), derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub struct FrameRange(RangeInclusive<Frame>);

impl FrameRange {
    #[ensures(result.start_frame() == start)]
    #[ensures(result.end_frame() == end)]
    pub const fn new(start: Frame, end: Frame) -> FrameRange {
        FrameRange(RangeInclusive::new(start, end))
    }

    #[pure]
    #[trusted]
    #[ensures(result == *self.0.start())]
    pub fn start_frame(&self) -> Frame {
        *self.0.start()
    }

    #[pure]
    #[trusted]
    #[ensures(result == *self.0.end())]
    pub fn end_frame(&self) -> Frame {
        *self.0.end()
    }

    pub fn frames(&self) -> RangeInclusive<Frame> {
        self.0
    }

    #[ensures(result.is_empty())]
    pub const fn empty() -> FrameRange {
        FrameRange( RangeInclusive::new(Frame{ number: 1 }, Frame{ number: 0 }) )
    }

    #[pure]
    #[ensures(result == (self.start_frame().greater_than(&self.end_frame())))]
    #[ensures(result == !(self.start_frame().less_than_equal(&self.end_frame())))]
    pub fn is_empty(&self) -> bool {
        !(self.start_frame().less_than_equal(&self.end_frame()))
    }

    #[pure]
    /// Returning a FrameRange here requires use to set the RangeInclusive new function as pure which
    /// requires Idx to be Copy.
    /// so just return bool.
    pub fn overlap(&self, other: &FrameRange) -> bool {
        let starts = max_frame(self.start_frame(), other.start_frame());
        let ends   = min_frame(self.end_frame(), other.end_frame());
        if starts.less_than_equal(&ends) {
            true
        } else {
            false
        }
    }

    #[pure]
    /// Returning a FrameRange here requires use to set the RangeInclusive new function as pure which
    /// requires Idx to be Copy.
    /// so just return bool.
    pub fn overlap_numbers(&self, other: &FrameRange) -> bool {
        let starts = max(self.start_frame().number, other.start_frame().number);
        let ends   = min(self.end_frame().number, other.end_frame().number);
        if starts <= ends {
            true
        } else {
            false
        }
    }



    /// Splits a chunk into 1-3 chunks, depending on where the split is at.
    /// It is formally verified that the resulting chunks are disjoint, contiguous and their start/end is equal to that of the original chunk.
    /// 
    /// # Post-conditions:
    /// * If it succeeds, then the resulting chunks have no overlapping ranges
    /// * If it succeeds, then the resulting chunks are contiguous
    /// * If it succeeds, then the resulting chunks combined have the same range as `self`
    /// * If it fails, then the original chunk is returned
    #[ensures(result.is_ok() ==> {
        let split_chunk = peek_result_ref(&result);
        ((split_chunk.0).is_some() ==> !peek_option_ref(&split_chunk.0).overlap(&split_chunk.1)) 
        &&
        ((split_chunk.2).is_some() ==> !split_chunk.1.overlap(peek_option_ref(&split_chunk.2)))
        &&
        ((split_chunk.2).is_some() ==> !split_chunk.1.overlap_numbers(peek_option_ref(&split_chunk.2)))

        && (((split_chunk.0).is_some() && (split_chunk.2).is_some()) ==> !peek_option_ref(&split_chunk.0).overlap(peek_option_ref(&split_chunk.2)))
        // split_chunk_has_no_overlapping_ranges(&split_chunk.0, &split_chunk.1, &split_chunk.2)
    })]
    // #[ensures(result.is_ok() ==> {
    //     let split_chunk = peek_result_ref(&result);
    //     split_chunk_is_contiguous(&split_chunk.0, &split_chunk.1, &split_chunk.2)
    // })]
    // #[ensures(result.is_ok() ==> split_chunk_has_same_range(&self, peek_result_ref(&result)))]
    // #[ensures(result.is_err() ==> {
    //     let orig_chunk = peek_err_ref(&result);
    //     (orig_chunk.start_frame() == self.start_frame()) && (orig_chunk.end_frame() == self.end_frame())
    // })]
    pub fn split(self, start_frame: Frame, num_frames: usize) -> Result<(Option<FrameRange>, FrameRange, Option<FrameRange>), FrameRange> {
        if (start_frame.less_than(&self.start_frame())) 
        || (num_frames > 0 && ((start_frame.plus(num_frames -1)).greater_than(&self.end_frame()))) 
        || (num_frames <= 0) {
            return Err(self);
        }

        let min_frame = Frame { number: 0 };
        let max_frame = Frame { number: 0xFF_FFFF_FFFF };
        let first_chunk = if start_frame == min_frame || start_frame == self.start_frame() {
            None
        } else {
            prusti_assert!(start_frame.greater_than(&self.start_frame()));
            prusti_assert!(start_frame.minus(1).greater_than_equal(&self.start_frame()));
            Some(FrameRange::new(self.start_frame(), start_frame.minus(1)))
        };

        // prusti_assert!(start_frame.number() + num_frames - 1 >= start_frame.number()); 
        // prusti_assert!((start_frame + num_frames - 1).number() >= start_frame.number()); // fails
        prusti_assert!(num_frames > 0);
        prusti_assert!(start_frame.plus(num_frames - 1).greater_than_equal(&start_frame));

        let second_chunk = FrameRange::new(start_frame, start_frame.plus(num_frames - 1));

        let third_chunk = if start_frame.plus(num_frames - 1) == max_frame || start_frame.plus(num_frames - 1) == self.end_frame() {
            None
        } else {
            prusti_assert!(num_frames > (num_frames - 1));
            prusti_assert!(start_frame.plus(num_frames).greater_than(&start_frame.plus(num_frames - 1)));
            // prusti_assert!(start_frame.plus(num_frames - 1).less_than(&start_frame.plus(num_frames)));
            // prusti_assert!(self.end_frame().greater_than_equal(&start_frame.plus(num_frames)));
            Some(FrameRange::new(start_frame.plus(num_frames), self.end_frame())) 
        };

        Ok((first_chunk, second_chunk, third_chunk))
    }


    // /// Splits a chunk into 2 chunks at the frame with number `at_frame`.
    // /// It is formally verified that the resulting chunks are disjoint, contiguous and their start/end is equal to that of the original chunk.
    // /// 
    // /// # Post-conditions:
    // /// * If it succeeds, then both chunks can't be empty
    // /// * If it succeeds and the first chunk is empty, then the second chunk is equal to `self`
    // /// * If it succeeds and the second chunk is empty, then the first chunk is equal to `self`
    // /// * If it succeeds and both chunks aren't empty, then the chunks are contiguous and their combined range is equal to the range of `self`
    // /// * If it fails, then the original chunk is returned
    // #[ensures(result.is_ok() ==> {
    //     let split_chunk = peek_result_ref(&result);
    //     split_chunk.0.is_empty() && !split_chunk.1.is_empty() ||
    //     !split_chunk.0.is_empty() && split_chunk.1.is_empty() ||
    //     !split_chunk.0.is_empty() && !split_chunk.1.is_empty()
    // })]
    // #[ensures(result.is_ok() ==> {
    //     let split_chunk = peek_result_ref(&result);
    //     split_chunk.0.is_empty() ==> (split_chunk.1.start_frame() == old(self.start_frame()) && split_chunk.1.end_frame() == old(self.end_frame()))
    // })]
    // #[ensures(result.is_ok() ==> {
    //     let split_chunk = peek_result_ref(&result);
    //     split_chunk.1.is_empty() ==> (split_chunk.0.start_frame() == old(self.start_frame()) && split_chunk.0.end_frame() == old(self.end_frame()))
    // })]
    // #[ensures(result.is_ok() ==> {
    //     let split_chunk = peek_result_ref(&result);
    //     (!split_chunk.0.is_empty() && !split_chunk.1.is_empty()) ==> {
    //         split_chunk.0.start_frame() == old(self.start_frame()) && split_chunk.0.end_frame() == at_frame - 1 &&
    //         split_chunk.1.start_frame() == at_frame && split_chunk.1.end_frame() == old(self.end_frame())
    //     }
    // })]
    // #[ensures(result.is_err() ==> {
    //     let orig_chunk = peek_err_ref(&result);
    //     (orig_chunk.start_frame() == self.start_frame()) && (orig_chunk.end_frame() == self.end_frame())
    // })]
    // pub fn split_at(mut self, at_frame: usize) -> Result<(TrustedChunk, TrustedChunk), TrustedChunk> {
    //    let end_of_first = at_frame - 1;

    //     let (first, second) = if at_frame == self.start_frame() && at_frame <= self.end_frame() {
    //         let first  = TrustedChunk::empty();
    //         let second = TrustedChunk::trusted_new(RangeInclusive::new(at_frame, self.end_frame()));
    //         (first, second)
    //     } 
    //     else if at_frame == (self.end_frame() + 1) && end_of_first >= self.start_frame() {
    //         let first  = TrustedChunk::trusted_new(RangeInclusive::new(self.start_frame(), self.end_frame())); 
    //         let second = TrustedChunk::empty();
    //         (first, second)
    //     }
    //     else if at_frame > self.start_frame() && end_of_first <= self.end_frame() {
    //         let first  = TrustedChunk::trusted_new(RangeInclusive::new(self.start_frame(), end_of_first));
    //         let second = TrustedChunk::trusted_new(RangeInclusive::new(at_frame, self.end_frame()));
    //         (first, second)
    //     }
    //     else {
    //         return Err(self);
    //     };

    //     core::mem::forget(self);   
    //     Ok(( first, second ))
    // }


    // /// Merges `other` into `self`.
    // /// Succeeds if `other` lies right before `self` or right after.
    // /// 
    // /// # Post-conditions:
    // /// * If it succeeds, then `other` and `self` were contiguous, and either `self`'s start bound has been updated to `other`'s start 
    // /// or `self`s end has been updated to `other`'s end
    // /// * If it fails, then `self` remains unchanged and `other` is returned
    // #[ensures(result.is_ok() ==> 
    //     (old(self.start_frame()) == other.end_frame() + 1 && self.start_frame() == other.start_frame() && self.end_frame() == old(self.end_frame())) 
    //     || 
    //     (old(self.end_frame()) + 1 == other.start_frame() && self.end_frame() == other.end_frame() && self.start_frame() == old(self.start_frame()))
    // )]
    // #[ensures(result.is_err() ==> {
    //     let chunk = peek_err_ref(&result);
    //     (chunk.start_frame() == other.start_frame()) && (chunk.end_frame() == other.end_frame()) 
    // })]
    // #[ensures(result.is_err() ==> {
    //     (self.start_frame() == old(self.start_frame())) && (self.end_frame() == old(self.end_frame())) 
    // })]
    // pub fn merge(&mut self, other: TrustedChunk) -> Result<(), TrustedChunk> {
    //     if self.is_empty() | other.is_empty() {
    //         return Err(other);
    //     }

    //     if self.start_frame() == other.end_frame() + 1 {
    //         // `other` comes contiguously before `self`
    //         self.frames = RangeInclusive::new(other.start_frame(), self.end_frame());
    //     } 
    //     else if self.end_frame() + 1 == other.start_frame() {
    //         // `self` comes contiguously before `other`
    //         self.frames = RangeInclusive::new(self.start_frame(), other.end_frame());
    //     }
    //     else {
    //         // non-contiguous
    //         return Err(other);
    //     }

    //     // ensure the now-merged TrustedChunk doesn't run its drop handler (currently not implemented, but to prevent any future issues.)
    //     core::mem::forget(other); 
    //     Ok(())
    // }
}


impl Deref for FrameRange {
    type Target = RangeInclusive<Frame>;
    #[pure]
    fn deref(&self) -> &RangeInclusive<Frame> {
        &self.0
    }
}
