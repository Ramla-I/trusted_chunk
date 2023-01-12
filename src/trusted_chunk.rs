use prusti_contracts::*;
use prusti_contracts::*;
cfg_if::cfg_if! {
if #[cfg(prusti)] {
    use crate::external_spec::{
        trusted_option::*,
        trusted_result::*,
        trusted_range_inclusive::*,
    };
} else {
    use range_inclusive::*;
}
}
use core::ops::{Deref};
use crate::{
    *,
    linked_list::*, spec::range_overlaps::range_overlaps,
};

#[ensures(result.is_some() ==> peek_option(&result) < 32)]
#[ensures(result.is_some() ==> list[peek_option(&result)].is_some())]
#[ensures(result.is_some() ==> {
    let idx = peek_option(&result);
    let elem = peek_option(&list[idx]);
    range_overlaps(&range, &elem)
}
)]
#[ensures(result.is_none() ==> 
    forall(|i: usize| ((0 <= i && i < 32) && list[i].is_some()) ==> {
        let elem = peek_option(&list[i]);
        !range_overlaps(&range, &elem)
    })
)]
pub fn range_overlaps_in_array(range: RangeInclusive<usize>, list: [Option<RangeInclusive<usize>>; 32]) -> Option<usize> {
    let mut i = 0;
    while i < 32 {
        body_invariant!(i < list.len());
        body_invariant!(i >= 0);

        if list[i].is_some(){
            if range_overlaps(&range, &list[i].unwrap()) {
                return Some(i);
            }
        }
    }
    None
}

#[ensures(result.is_some() ==> {
    let (i,j) = peek_option(&result);
    i < 32 && j < 32
})]
#[ensures(result.is_some() ==> {
    let (i,j) = peek_option(&result);
    list[i].is_some() && list[j].is_some()
})]

#[ensures(result.is_some() ==> {
    let (i,j) = peek_option(&result);
    range_overlaps(peek_option_ref(&list[i]), peek_option_ref(&list[j]))
}
)]
// #[ensures(result.is_none() ==> 
//     forall(|i: usize, j:usize| ((0 <= i && i < 32 && i < j && j < 32) && list[i].is_some() && list[j].is_some()) ==> {
//         let elem = peek_option(&list[i]);
//         let range = peek_option(&list[j]);
//         !range_overlaps(&range, &elem)
//     })
// )]
pub fn overlaps_in_array(list: [Option<RangeInclusive<usize>>; 32]) -> Option<(usize, usize)> {
    let mut i = 0;
    while i < 32 {
        body_invariant!(i < list.len());
        body_invariant!(i >= 0);

        if list[i].is_some(){
            let mut j = i+1;
            while j < 32 {
                body_invariant!(j < list.len());
                body_invariant!(j >= 0);
                if list[j].is_some(){
                    if range_overlaps(&list[j].unwrap(), &list[i].unwrap()) {
                        return Some((i,j));
                    }
                }
                j += 1;
            }
        }
        i += 1;
    }
    None
}


/// A struct representing a unique unallocated region in memory.
/// An instantiation of this struct is formally verified to not overlap with any other `TrustedChunk` in the system.
/// 
/// # Warning
/// A `RangeInclusive` is created with the precondition that start <= end.
/// Outside of verified code, it is the caller's responsibility to make sure that precondition is upheld.
pub struct TrustedChunk {
    frames: RangeInclusive<usize>
}

impl TrustedChunk {
    // #[cfg_attr(feature="prusti", pure)]
    #[pure]
    #[trusted]
    #[ensures(result == *self.frames.start())]
    pub fn start(&self) -> usize {
        *self.frames.start()
    }

    // #[cfg_attr(feature="prusti", pure)]
    #[pure]
    #[trusted]
    #[ensures(result == *self.frames.end())]
    pub fn end(&self) -> usize {
        *self.frames.end()
    }

    /// If no other range in `chunk_list` overlaps with `frames`:
    /// * creates a new `TrustedChunk` with `frames`  
    /// * adds the range of the newly created `TrustedChunk` to `chunk_list`.
    /// Returns an Err if there is an overlap, with the error value being the index in `chunk_list` of the element which overlaps with `frames`.
    #[requires(*frames.start() <= *frames.end())]
    #[ensures(result.is_ok() ==> peek_result_ref(&result).start() == *frames.start())]
    #[ensures(result.is_ok() ==> peek_result_ref(&result).end() == *frames.end())]
    #[ensures(result.is_err() ==> {
        let overlap_idx = peek_err(&result);
        overlap_idx < chunk_list.len()
    })]
    #[ensures(result.is_err() ==> {
        let overlap_idx = peek_err(&result);
        range_overlaps(&chunk_list.lookup(overlap_idx), &frames)
    })]
    #[ensures(result.is_ok() ==> chunk_list.len() >= 1)]
    #[ensures(result.is_ok() ==> {
        chunk_list.lookup(0) == frames
    })]
    #[ensures(result.is_ok() ==> {
        forall(|i: usize| (0 <= i && i < old(chunk_list.len())) ==> !range_overlaps(&old(chunk_list.lookup(i)), &frames))
    })]
    #[ensures(result.is_ok() ==> chunk_list.len() == old(chunk_list.len()) + 1)] 
    #[ensures(result.is_ok() ==> {
        forall(|i: usize| (1 <= i && i < chunk_list.len()) ==> old(chunk_list.lookup(i-1)) == chunk_list.lookup(i))
    })]
    fn new(frames: RangeInclusive<usize>, chunk_list: &mut List) -> Result<TrustedChunk, usize> {
        let overlap_idx = chunk_list.elem_overlaps_in_list(frames, 0);
        if overlap_idx.is_some(){
            Err(overlap_idx.unwrap())
        } else {
            chunk_list.push(frames);
            Ok(TrustedChunk { frames })
        }
    }

    /// Internal function that creates a chunk without any checks.
    /// Only to be used in the split() function.
    // #[cfg_attr(feature="prusti", requires(frames.start <= frames.end))]
    // #[cfg_attr(feature="prusti", ensures(result.frames.start == frames.start))]
    // #[cfg_attr(feature="prusti", ensures(result.frames.end == frames.end))]
    #[requires(*frames.start() <= *frames.end())]
    #[ensures(result.start() == *frames.start())]
    #[ensures(result.end() == *frames.end())]
    fn trusted_new(frames: RangeInclusive<usize>) -> TrustedChunk {
        TrustedChunk{frames}
    }

    /// Splits a chunk in to 1-3 chunks, depending on where the split is at.
    /// It is formally verified that the resulting chunks are disjoint, contiguous and their start/end is equal to that of the original chunk.
    // #[cfg_attr(feature="prusti", requires(start_page >= self.frames.start))]
    // #[cfg_attr(feature="prusti", requires(start_page + num_frames - 1 <= self.frames.end))]
    // #[cfg_attr(feature="prusti", requires(num_frames > 0))]
    // // #[cfg_attr(feature="prusti", requires(self.frames.end <= MAX_PAGE_NUMBER))]
    // #[cfg_attr(feature="prusti", ensures(split_chunk_has_no_overlapping_ranges(&result.0, &result.1, &result.2)))]
    // #[cfg_attr(feature="prusti", ensures(split_chunk_is_contiguous(&result.0, &result.1, &result.2)))]
    // #[cfg_attr(feature="prusti", ensures(start_end_are_equal(&self, &result)))]
    // #[requires(start_page >= self.frames.start)]
    // #[requires(start_page + num_frames - 1 <= self.frames.end)]
    // #[requires(num_frames > 0)]
    #[ensures(result.is_ok() ==> {
        let split_chunk = peek_result_ref(&result);
        split_chunk_has_no_overlapping_ranges(&split_chunk.0, &split_chunk.1, &split_chunk.2)
    })]
    #[ensures(result.is_ok() ==> {
        let split_chunk = peek_result_ref(&result);
        split_chunk_is_contiguous(&split_chunk.0, &split_chunk.1, &split_chunk.2)
    })]
    #[ensures(result.is_ok() ==> split_chunk_has_same_range(&self, peek_result_ref(&result)))]
    #[ensures(result.is_err() ==> {
        let orig_chunk = peek_err_ref(&result);
        (orig_chunk.start() == self.start()) && (orig_chunk.end() == self.end())
    })]
    pub fn split(self, start_page: usize, num_frames: usize) -> Result<(Option<TrustedChunk>, TrustedChunk, Option<TrustedChunk>), TrustedChunk> {
        if (start_page < self.start()) || (start_page + num_frames -1 > self.end()) || (num_frames <= 0) {
            return Err(self);
        }

        let first_chunk = if start_page == self.start()  {
            None
        } else {
            Some(TrustedChunk::trusted_new(RangeInclusive::new(self.start(), start_page - 1)))
        };
        let second_chunk = TrustedChunk::trusted_new(RangeInclusive::new(start_page, start_page + num_frames - 1));

        let third_chunk = if start_page + num_frames - 1 == self.end() {
            None
        } else {
            Some(TrustedChunk::trusted_new(RangeInclusive::new(start_page + num_frames, self.end())))
        };

        Ok((first_chunk, second_chunk, third_chunk))
    }

    #[ensures(result.is_ok() ==> 
        (old(self.start()) == other.end() + 1 && self.start() == other.start() && self.end() == old(self.end())) 
        || 
        (old(self.end()) + 1 == other.start() && self.end() == other.end() && self.start() == old(self.start()))
    )]
    #[ensures(result.is_err() ==> {
        let chunk = peek_err_ref(&result);
        (chunk.start() == other.start()) && (chunk.end() == other.end()) 
    })]
    #[ensures(result.is_err() ==> {
        (self.start() == old(self.start())) && (self.end() == old(self.end())) 
    })]
    pub fn merge(&mut self, other: TrustedChunk) -> Result<(), TrustedChunk> {
        if self.start() == other.end() + 1 {
            // `other` comes contiguously before `self`
            self.frames = RangeInclusive::new(other.start(), self.end());
        } 
        else if self.end() + 1 == other.start() {
            // `self` comes contiguously before `other`
            self.frames = RangeInclusive::new(self.start(), other.end());
        }
        else {
            // non-contiguous
            return Err(other);
        }

        // ensure the now-merged AllocatedFrames doesn't run its drop handler and free its frames.
        core::mem::forget(other); 
        Ok(())
    }
}


impl Deref for TrustedChunk {
    type Target = RangeInclusive<usize>;
    #[pure]
    fn deref(&self) -> &RangeInclusive<usize> {
        &self.frames
    }
}


/*** Following are a set of pure functions that are only used in the specification of a TrustedChunk ***/

/// Checks that either chunk1 ends before chunk2 starts, or that chunk2 ends before chunk1 starts.
// #[cfg_attr(feature="prusti", pure)]
#[pure]
fn chunks_do_not_overlap(chunk1: &TrustedChunk, chunk2: &TrustedChunk) -> bool {
    (chunk1.end() < chunk2.start()) | (chunk2.end() < chunk1.start())
}

/// Returns true if there is no overlap in the ranges of `chunk1`, `chunk2` and `chunk3`.
// #[cfg_attr(feature="prusti", pure)]
#[pure]
fn split_chunk_has_no_overlapping_ranges(chunk1: &Option<TrustedChunk>, chunk2: &TrustedChunk, chunk3: &Option<TrustedChunk>) -> bool {
    let mut no_overlap = true;

    if let Some(c1) = chunk1 {
        no_overlap &= chunks_do_not_overlap(c1, chunk2);
        if let Some(c3) = chunk3 {
            no_overlap &= chunks_do_not_overlap(c1, c3);
            no_overlap &= chunks_do_not_overlap(chunk2, c3);
        }
    } else {
        if let Some(c3) = chunk3 {
            no_overlap &= chunks_do_not_overlap(chunk2, c3);
        }
    }

    no_overlap
}

/// Returns true if the start and end of the original chunk is equal to the extreme bounds of the split chunk.
// #[cfg_attr(feature="prusti", pure)]
#[pure]
fn split_chunk_has_same_range(orig_chunk: &TrustedChunk, split_chunk: &(Option<TrustedChunk>, TrustedChunk, Option<TrustedChunk>)) -> bool {
    let (chunk1,chunk2,chunk3) = split_chunk;
    let min_page;
    let max_page;

    if let Some(c1) = chunk1 {
        min_page = c1.start();    
    } else {
        min_page = chunk2.start();
    }

    if let Some(c3) = chunk3 {
        max_page = c3.end();    
    } else {
        max_page = chunk2.end();
    }

    min_page == orig_chunk.start() && max_page == orig_chunk.end()
}


/// Returns true if `chunk1`, `chunk2` and `chunk3` are contiguous.
// #[cfg_attr(feature="prusti", pure)]
#[pure]
// The following are only required if CHECK_OVERFLOWS flag is enabled
// #[cfg_attr(feature="prusti", requires(end_frame_is_less_than_max_or_none(chunk1)))]
// #[cfg_attr(feature="prusti", requires(end_frame_is_less_than_max(chunk2)))]
// #[cfg_attr(feature="prusti", requires(end_frame_is_less_than_max_or_none(chunk3)))]
fn split_chunk_is_contiguous(chunk1: &Option<TrustedChunk>, chunk2: &TrustedChunk, chunk3: &Option<TrustedChunk>) -> bool {
    let mut contiguous = true;
    if let Some(c1) = chunk1 {
        contiguous &= c1.end() + 1 == chunk2.start()
    } 
    if let Some(c3) = chunk3 {
        contiguous &= chunk2.end() + 1 == c3.start()
    }
    contiguous
}

/// Returns true if the end frame of the chunk is less than `MAX_PAGE_NUMBER`, or if the chunk is None.
// #[cfg_attr(feature="prusti", pure)]
#[pure]
fn end_frame_is_less_than_max_or_none(chunk: &Option<TrustedChunk>) -> bool {
    if let Some(c) = chunk {
        if c.end() <= MAX_PAGE_NUMBER {
            return true;
        } else {
            return false;
        }
    } else {
        return true;
    }

}

/// Returns true if the end frame of the chunk is less than `MAX_PAGE_NUMBER`.
// #[cfg_attr(feature="prusti", pure)]
#[pure]
fn end_frame_is_less_than_max(chunk: &TrustedChunk) -> bool {
    if chunk.end() <= MAX_PAGE_NUMBER {
        return true;
    } else {
        return false;
    }
}
