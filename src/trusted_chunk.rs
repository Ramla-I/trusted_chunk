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
use core::ops::{Deref, DerefMut};
use crate::{
    *,
    linked_list::*, 
    spec::{
        range_overlaps::range_overlaps,
        chunk_spec::*
    },
    static_array::*,
};

#[ensures(result.is_some() ==> peek_option(&result) < list.len())]
#[ensures(result.is_some() ==> list[peek_option(&result)].is_some())]
#[ensures(result.is_some() ==> {
    let idx = peek_option(&result);
    let elem = peek_option(&list[idx]);
    range_overlaps(&range, &elem)
}
)]
#[ensures(result.is_none() ==> 
    forall(|i: usize| ((0 <= i && i < list.len()) && list[i].is_some()) ==> {
        let elem = peek_option(&list[i]);
        !range_overlaps(&range, &elem)
    })
)]
pub fn range_overlaps_in_array(range: RangeInclusive<usize>, list: [Option<RangeInclusive<usize>>; 64]) -> Option<usize> {
    let mut i = 0;
    while i < list.len() {
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


#[derive(Copy, Clone)]
pub enum ChunkCreationError {
    Overlap(usize),
    NoSpace
}

/// A struct representing a unique unallocated region in memory.
/// An instantiation of this struct is formally verified to not overlap with any other `TrustedChunk` in the system.
/// 
/// # Warning
/// A `RangeInclusive` is created with the precondition that start <= end.
/// Outside of verified code, it is the caller's responsibility to make sure that precondition is upheld.
#[cfg_attr(not(prusti), derive(Debug, PartialEq, Eq))]
pub struct TrustedChunk {
    frames: RangeInclusive<usize>
}

// assert_not_impl_any!(TrustedChunk: DerefMut, Clone);

impl TrustedChunk {
    #[pure]
    #[trusted]
    #[ensures(result == *self.frames.start())]
    pub fn start(&self) -> usize {
        *self.frames.start()
    }

    #[pure]
    #[trusted]
    #[ensures(result == *self.frames.end())]
    pub fn end(&self) -> usize {
        *self.frames.end()
    }

    pub fn frames(&self) -> RangeInclusive<usize> {
        self.frames
    }

    pub const fn empty() -> TrustedChunk {
        TrustedChunk { frames: RangeInclusive::new(1, 0) }
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
    pub fn new(frames: RangeInclusive<usize>, chunk_list: &mut List) -> Result<TrustedChunk, usize> {
        let overlap_idx = chunk_list.elem_overlaps_in_list(frames, 0);
        if overlap_idx.is_some(){
            Err(overlap_idx.unwrap())
        } else {
            chunk_list.push(frames);
            Ok(TrustedChunk { frames })
        }
    }

    #[requires(*frames.start() <= *frames.end())]
    #[ensures(result.is_err() ==> {
        match peek_err(&result) {
            ChunkCreationError::Overlap(idx) => (idx < chunk_list.len()) && (chunk_list.lookup(idx).is_some()) && range_overlaps(&peek_option(&chunk_list.lookup(idx)), &frames),
            ChunkCreationError::NoSpace => true
        }
    })]
    #[ensures(result.is_ok() ==> peek_result_ref(&result).0.start() == *frames.start())]
    #[ensures(result.is_ok() ==> peek_result_ref(&result).0.end() == *frames.end())]
    #[ensures(result.is_ok() ==> {
        peek_result_ref(&result).1 < chunk_list.len()
    })]
    #[ensures(result.is_ok() ==> {
        let idx = peek_result_ref(&result).1;
        chunk_list.lookup(idx).is_some()
    })]
    #[ensures(result.is_ok() ==> {
        let idx = peek_result_ref(&result).1;
        peek_option(&chunk_list.lookup(idx)) == frames
    })]
    #[ensures(result.is_ok() ==> 
        forall(|i: usize| ((0 <= i && i < chunk_list.len()) && (i != peek_result_ref(&result).1)) ==> old(chunk_list.lookup(i)) == chunk_list.lookup(i))
    )] 
    #[ensures(result.is_ok() ==> 
        forall(|i: usize| ((0 <= i && i < chunk_list.len()) && (i != peek_result_ref(&result).1)) && old(chunk_list.lookup(i)).is_some()
            ==> !range_overlaps(&peek_option(&old(chunk_list.lookup(i))), &frames))
    )] 
    pub fn new_pre_heap(frames: RangeInclusive<usize>, chunk_list: &mut StaticArray) -> Result<(TrustedChunk, usize), ChunkCreationError> {
        let overlap_idx = chunk_list.elem_overlaps_in_array(frames, 0);
        if overlap_idx.is_some(){
            Err(ChunkCreationError::Overlap(overlap_idx.unwrap()))
        } else {
            match chunk_list.push(frames){
                Some(idx) => Ok((TrustedChunk { frames }, idx)),
                None => Err(ChunkCreationError::NoSpace)
            }
        }
    }

    /// Internal function that creates a chunk without any checks.
    /// Only to be used in the split() function.
    #[requires(*frames.start() <= *frames.end())]
    #[ensures(result.start() == *frames.start())]
    #[ensures(result.end() == *frames.end())]
    pub(crate) fn trusted_new(frames: RangeInclusive<usize>) -> TrustedChunk {
        TrustedChunk{frames}
    }


    /// Splits a chunk in to 1-3 chunks, depending on where the split is at.
    /// It is formally verified that the resulting chunks are disjoint, contiguous and their start/end is equal to that of the original chunk.
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
    pub fn split(self, start_frame: usize, num_frames: usize) -> Result<(Option<TrustedChunk>, TrustedChunk, Option<TrustedChunk>), TrustedChunk> {
        if (start_frame < self.start()) || (start_frame + num_frames -1 > self.end()) || (num_frames <= 0) {
            return Err(self);
        }

        let first_chunk = if start_frame == self.start()  {
            None
        } else {
            Some(TrustedChunk::trusted_new(RangeInclusive::new(self.start(), start_frame - 1)))
        };
        let second_chunk = TrustedChunk::trusted_new(RangeInclusive::new(start_frame, start_frame + num_frames - 1));

        let third_chunk = if start_frame + num_frames - 1 == self.end() {
            None
        } else {
            Some(TrustedChunk::trusted_new(RangeInclusive::new(start_frame + num_frames, self.end())))
        };

        Ok((first_chunk, second_chunk, third_chunk))
    }


    /// Merges `other` into `self`.
    /// Succeeds if `other` lies right before `self` or right after.
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

        // ensure the now-merged TrustedChunk doesn't run its drop handler (currently not implemented, but to prevent any future issues.)
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
