use prusti_contracts::*;

#[cfg(prusti)]
use crate::external_spec::trusted_range_inclusive::*;
#[cfg(not(prusti))]
use range_inclusive::*;

use core::ops::{Deref, DerefMut};
use crate::{
    *,
    external_spec::{trusted_option::*, trusted_result::*},
    spec::{range_overlaps::range_overlaps, chunk_spec::*},
    linked_list::*, 
    static_array::*,
};


#[derive(Copy, Clone)]
pub enum ChunkCreationError {
    /// There was already a `TrustedChunk` created with an overlapping range
    Overlap(usize),
    /// In the pre-heap-intialization phase, if there is no more space in the array
    NoSpace,
    /// The requested range is empty (end > start)
    InvalidRange
}

/// An allocator that allocates `TrustedChunk` objects with the invariant that all 
/// chunks from this allocator are unique (there is no overlap in the ranges of the chunks).
/// 
/// Pre-heap initialization, the allocator keeps an array to store information about all the chunks created so far.
/// After the heap is initialized, the ranges stored in `array` are shifted to a linked list and the 
/// linked list is used to bookkeep all further allocations.
pub struct TrustedChunkAllocator {
    heap_init: bool,
    list: List,
    array: StaticArray
}

impl TrustedChunkAllocator {
    /// Creates an allocator with empty bookkeeping structures
    pub fn new() -> TrustedChunkAllocator {
        TrustedChunkAllocator { heap_init: false, list: List::new(), array: StaticArray::new() }
    }


    /// Shifts all elements in `array` to the heap-allocated `list`.
    /// Returns an error if the heap was already initialized and the transfer has already occured.
    /// 
    /// # Post-conditions:
    /// * If `heap_init` was set or the `list` was not empty, then an error is returned
    /// * If successful, `heap_init` is set
    /// * If successful, then all elements of `array` are set to None
    /// * If successful, then no element in `list` overlaps
    /// 
    /// # Verification Notes:
    /// Ideally, should relate each element in the old `array` with elements in the updated `list`
    /// but haven't figured out a loop invariant that does that.
    #[ensures((old(self.heap_init) || old(self.list.len() != 0)) ==> result.is_err())]
    #[ensures(result.is_ok() ==> self.heap_init)]
    #[ensures(result.is_ok() ==> forall(|i: usize| (0 <= i && i < self.array.arr.len()) ==> self.array.arr[i].is_none()))]
    #[ensures(result.is_ok() ==> forall(|i: usize, j: usize| (0 <= i && i < self.list.len() && 0 <= j && j < self.list.len()) ==> 
        (i != j ==> !range_overlaps(&self.list.lookup(i), &self.list.lookup(j))))
    )]
    pub fn switch_to_heap_allocated(&mut self) -> Result<(),()> {
        if self.heap_init || self.list.len() != 0 {
            return Err(());
        }

        let mut i = 0;
        while i < self.array.arr.len() {
            body_invariant!(forall(|i: usize, j: usize| (0 <= i && i < self.list.len() && 0 <= j && j < self.list.len()) ==> 
                (i != j ==> !range_overlaps(&self.list.lookup(i), &self.list.lookup(j))))
            );
            body_invariant!(forall(|j: usize| ((0 <= j && j < i) ==> self.array.arr[j].is_none())));
            body_invariant!(i < self.array.arr.len());
            body_invariant!(i >= 0);

            if let Some((start, end)) = self.array.lookup_range_bounds(i) {
                match self.list.push_unique_with_precond(RangeInclusive::new(start, end)) {
                    Ok(()) => self.array.set_element(i, None),
                    Err(_) => return Err(())
                }
            }
            i += 1;
        }
        self.heap_init = true;
        Ok(())
    }


    /// The only public interface to create a `TrustedChunk`.
    /// 
    /// # Post-conditions:
    /// * If ChunkCreationError::Overlap(idx) is returned, then `chunk_range` overlaps with the element at index idx
    /// * If successful, then result is equal to `chunk_range`
    /// * If successful, then `chunk_range` did not overlap with any element in the old array/ list
    /// * If successful, then `chunk_range` has been added to the array/ list
    /// 
    /// # Verification Notes:
    /// We could bring all post-conditions from the TrustedChunk::new functions as post-conditions here
    /// but it gets extremenly verbose
    #[ensures(result.is_err() ==> {
        match peek_err(&result) {
            ChunkCreationError::Overlap(idx) => {
                (self.heap_init && (idx < self.list.len()) & range_overlaps(&self.list.lookup(idx), &chunk_range)) ||
                (!self.heap_init && (idx < self.array.len()) && (self.array.lookup(idx).is_some()) && range_overlaps(&peek_option(&self.array.lookup(idx)), &chunk_range))
            },
            _ => true
        }
    })]
    #[ensures(result.is_ok() ==> {
        let (new_chunk, _) = peek_result_ref(&result);
        new_chunk.start() == *chunk_range.start() && new_chunk.end() == *chunk_range.end()
    })]
    #[ensures(result.is_ok() ==> {
        (self.heap_init && forall(|i: usize| (0 <= i && i < old(self.list.len())) ==> !range_overlaps(&old(self.list.lookup(i)), &chunk_range)))
        ||
        (!self.heap_init && forall(|i: usize| (0 <= i && i < old(self.array.len())) && old(self.array.lookup(i)).is_some()
            ==> !range_overlaps(&peek_option(&old(self.array.lookup(i))), &chunk_range)))
    })]
    #[ensures(result.is_ok() ==> {
        (self.heap_init && self.list.len() >= 1 && self.list.lookup(0) == chunk_range)
        ||
        (!self.heap_init && {
            let idx = peek_result_ref(&result).1;
            idx < self.array.len() && self.array.lookup(idx).is_some() && peek_option(&self.array.lookup(idx)) == chunk_range
        })
    })]
    pub fn create_chunk(&mut self, chunk_range: RangeInclusive<usize>) -> Result<(TrustedChunk, usize), ChunkCreationError> {
        if self.heap_init {
            match TrustedChunk::new(chunk_range, &mut self.list) { // can't use map because Prusti can't reason about the return value then
                Ok(chunk) => Ok((chunk, 0)),
                Err(e) => Err(e)
            }
        } else {
            TrustedChunk::new_pre_heap(chunk_range, &mut self.array)
        }
    }
}


/// A struct representing an unallocated region in memory.
/// Its public functions are formally verified to prevent range overlaps between chunks.
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

    #[ensures(result.is_empty())]
    pub const fn empty() -> TrustedChunk {
        TrustedChunk { frames: RangeInclusive::new(1, 0) }
    }

    #[pure]
    #[ensures(result ==> self.end() < self.start())]
    pub fn is_empty(&self) -> bool {
        !(self.start() <= self.end())

    }

    /// Creates a new `TrustedChunk` with `chunk_range` if no other range in `chunk_list` overlaps with `chunk_range`
    /// and adds the range of the newly created `TrustedChunk` to `chunk_list`.
    /// Returns an Err if there is an overlap, with the error value being the index in `chunk_list` of the element which overlaps with `frames`.
    /// 
    /// # Post-conditions:
    #[ensures(result.is_err() ==> {
        match peek_err(&result) {
            ChunkCreationError::Overlap(idx) => (idx < chunk_list.len()) & range_overlaps(&chunk_list.lookup(idx), &chunk_range),
            _ => true
        }
    })]
    #[ensures(result.is_ok() ==> {
        let new_chunk = peek_result_ref(&result);
        new_chunk.start() == *chunk_range.start() && new_chunk.end() == *chunk_range.end()
    })]
    #[ensures(result.is_ok() ==> {
        chunk_list.len() >= 1 && chunk_list.lookup(0) == chunk_range
    })]
    #[ensures(result.is_ok() ==> chunk_list.len() == old(chunk_list.len()) + 1)] 
    #[ensures(result.is_ok() ==> {
        forall(|i: usize| (1 <= i && i < chunk_list.len()) ==> old(chunk_list.lookup(i-1)) == chunk_list.lookup(i))
    })]
    #[ensures(result.is_ok() ==> {
        forall(|i: usize| (0 <= i && i < old(chunk_list.len())) ==> !range_overlaps(&old(chunk_list.lookup(i)), &chunk_range))
    })]
    fn new(chunk_range: RangeInclusive<usize>, chunk_list: &mut List) -> Result<TrustedChunk, ChunkCreationError> {
        if chunk_range.is_empty() {
            return Err(ChunkCreationError::InvalidRange);
        }

        let overlap_idx = chunk_list.elem_overlaps_in_list(chunk_range, 0);
        if overlap_idx.is_some(){
            Err(ChunkCreationError::Overlap(overlap_idx.unwrap()))
        } else {
            chunk_list.push(chunk_range);
            Ok(TrustedChunk { frames: chunk_range })
        }
    }


    /// Creates a new `TrustedChunk` with `chunk_range` if no other range in `chunk_list` overlaps with `chunk_range`
    /// and adds the range of the newly created `TrustedChunk` to `chunk_list`.
    /// Returns an Err if there is an overlap, with the error value being the index in `chunk_list` of the element which overlaps with `frames`.
    /// Also returns an error if the `chunk_list` is full and no new element can be added.
    /// 
    /// 
    /// # Post-conditions:
    #[ensures(result.is_err() ==> {
        match peek_err(&result) {
            ChunkCreationError::Overlap(idx) => (idx < chunk_list.len()) && (chunk_list.lookup(idx).is_some()) && range_overlaps(&peek_option(&chunk_list.lookup(idx)), &chunk_range),
            _ => true
        }
    })]
    #[ensures(result.is_ok() ==> {
        let (new_chunk, _) = peek_result_ref(&result);
        new_chunk.start() == *chunk_range.start() && new_chunk.end() == *chunk_range.end()
    })]
    #[ensures(result.is_ok() ==> {
        let idx = peek_result_ref(&result).1;
        idx < chunk_list.len() && chunk_list.lookup(idx).is_some() && peek_option(&chunk_list.lookup(idx)) == chunk_range
    })]
    #[ensures(result.is_ok() ==> 
        forall(|i: usize| ((0 <= i && i < chunk_list.len()) && (i != peek_result_ref(&result).1)) ==> old(chunk_list.lookup(i)) == chunk_list.lookup(i))
    )] 
    #[ensures(result.is_ok() ==> 
        forall(|i: usize| ((0 <= i && i < chunk_list.len()) ) && old(chunk_list.lookup(i)).is_some()
            ==> !range_overlaps(&peek_option(&old(chunk_list.lookup(i))), &chunk_range))
    )] 
    fn new_pre_heap(chunk_range: RangeInclusive<usize>, chunk_list: &mut StaticArray) -> Result<(TrustedChunk, usize), ChunkCreationError> {
        if chunk_range.is_empty() {
            return Err(ChunkCreationError::InvalidRange);
        }

        let overlap_idx = chunk_list.elem_overlaps_in_array(chunk_range, 0);
        if overlap_idx.is_some(){
            Err(ChunkCreationError::Overlap(overlap_idx.unwrap()))
        } else {
            match chunk_list.push(chunk_range){
                Ok(idx) => Ok((TrustedChunk { frames: chunk_range }, idx)),
                Err(()) => Err(ChunkCreationError::NoSpace)
            }
        }
    }

    /// Private function that creates a chunk without any checks.
    #[requires(*frames.start() <= *frames.end())]
    #[ensures(result.start() == *frames.start())]
    #[ensures(result.end() == *frames.end())]
    pub(crate) fn trusted_new(frames: RangeInclusive<usize>) -> TrustedChunk {
        TrustedChunk{frames}
    }


    /// Splits a chunk into 1-3 chunks, depending on where the split is at.
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


    /// Splits a chunk into 2 chunks at the frame with number `at_frame`.
    /// It is formally verified that the resulting chunks are disjoint, contiguous and their start/end is equal to that of the original chunk.
    #[ensures(result.is_ok() ==> {
        let split_chunk = peek_result_ref(&result);
        split_chunk.0.is_empty() && !split_chunk.1.is_empty() ||
        !split_chunk.0.is_empty() && split_chunk.1.is_empty() ||
        !split_chunk.0.is_empty() && !split_chunk.1.is_empty()
    })]
    #[ensures(result.is_ok() ==> {
        let split_chunk = peek_result_ref(&result);
        split_chunk.0.is_empty() ==> (split_chunk.1.start() == old(self.start()) && split_chunk.1.end() == old(self.end()))
    })]
    #[ensures(result.is_ok() ==> {
        let split_chunk = peek_result_ref(&result);
        split_chunk.1.is_empty() ==> (split_chunk.0.start() == old(self.start()) && split_chunk.0.end() == old(self.end()))
    })]
    #[ensures(result.is_ok() ==> {
        let split_chunk = peek_result_ref(&result);
        (!split_chunk.0.is_empty() && !split_chunk.1.is_empty()) ==> {
            split_chunk.0.start() == old(self.start()) && split_chunk.0.end() == at_frame - 1 &&
            split_chunk.1.start() == at_frame && split_chunk.1.end() == old(self.end())
        }
    })]
    #[ensures(result.is_err() ==> {
        let orig_chunk = peek_err_ref(&result);
        (orig_chunk.start() == self.start()) && (orig_chunk.end() == self.end())
    })]
    pub fn split_at(mut self, at_frame: usize) -> Result<(TrustedChunk, TrustedChunk), TrustedChunk> {
       let end_of_first = at_frame - 1;

        let (first, second) = if at_frame == self.start() && at_frame <= self.end() {
            let first  = TrustedChunk::empty();
            let second = TrustedChunk::trusted_new(RangeInclusive::new(at_frame, self.end()));
            (first, second)
        } 
        else if at_frame == (self.end() + 1) && end_of_first >= self.start() {
            let first  = TrustedChunk::trusted_new(RangeInclusive::new(self.start(), self.end())); 
            let second = TrustedChunk::empty();
            (first, second)
        }
        else if at_frame > self.start() && end_of_first <= self.end() {
            let first  = TrustedChunk::trusted_new(RangeInclusive::new(self.start(), end_of_first));
            let second = TrustedChunk::trusted_new(RangeInclusive::new(at_frame, self.end()));
            (first, second)
        }
        else {
            return Err(self);
        };

        core::mem::forget(self);   
        Ok(( first, second ))
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
        if self.is_empty() | other.is_empty() {
            return Err(other);
        }

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
