//! Following are a set of pure functions that are only used in the specification of a TrustedChunk.

use crate::trusted_chunk::*;

/// Checks that either chunk1 ends before chunk2 starts, or that chunk2 ends before chunk1 starts.
#[pure]
pub(crate) fn chunks_do_not_overlap(chunk1: &TrustedChunk, chunk2: &TrustedChunk) -> bool {
    (chunk1.end() < chunk2.start()) | (chunk2.end() < chunk1.start())
}

/// Returns true if there is no overlap in the ranges of `chunk1`, `chunk2` and `chunk3`.
#[pure]
pub(crate) fn split_chunk_has_no_overlapping_ranges(chunk1: &Option<TrustedChunk>, chunk2: &TrustedChunk, chunk3: &Option<TrustedChunk>) -> bool {
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
#[pure]
pub(crate) fn split_chunk_has_same_range(orig_chunk: &TrustedChunk, split_chunk: &(Option<TrustedChunk>, TrustedChunk, Option<TrustedChunk>)) -> bool {
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
#[pure]
// The following are only required if CHECK_OVERFLOWS flag is enabled
// #[cfg_attr(feature="prusti", requires(end_frame_is_less_than_max_or_none(chunk1)))]
// #[cfg_attr(feature="prusti", requires(end_frame_is_less_than_max(chunk2)))]
// #[cfg_attr(feature="prusti", requires(end_frame_is_less_than_max_or_none(chunk3)))]
pub(crate) fn split_chunk_is_contiguous(chunk1: &Option<TrustedChunk>, chunk2: &TrustedChunk, chunk3: &Option<TrustedChunk>) -> bool {
    let mut contiguous = true;
    if let Some(c1) = chunk1 {
        contiguous &= c1.end() + 1 == chunk2.start()
    } 
    if let Some(c3) = chunk3 {
        contiguous &= chunk2.end() + 1 == c3.start()
    }
    contiguous
}


/*** Constants taken from kernel_config crate. Only required if CHECK_OVERFLOWS flag is enabled. ***/ 
/// The lower 12 bits of a virtual address correspond to the P1 page frame offset. 
pub const PAGE_SHIFT: usize = 12;
/// Page size is 4096 bytes, 4KiB pages.
pub const PAGE_SIZE: usize = 1 << PAGE_SHIFT;
pub const MAX_VIRTUAL_ADDRESS: usize = usize::MAX;
pub const MAX_PAGE_NUMBER: usize = MAX_VIRTUAL_ADDRESS / PAGE_SIZE;

/// Returns true if the end frame of the chunk is less than `MAX_PAGE_NUMBER`, or if the chunk is None.
#[pure]
pub(crate) fn end_frame_is_less_than_max_or_none(chunk: &Option<TrustedChunk>) -> bool {
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
#[pure]
pub(crate) fn end_frame_is_less_than_max(chunk: &TrustedChunk) -> bool {
    if chunk.end() <= MAX_PAGE_NUMBER {
        return true;
    } else {
        return false;
    }
}
