#![feature(box_patterns)]
#![allow(unused)]
#![feature(step_trait)]
// #[cfg(feature="prusti")]
#[macro_use]
extern crate prusti_contracts;

// #[cfg(feature="prusti")]
use prusti_contracts::*;

use core::ops::{Deref};
use crate::{
    linked_list::*,
    trusted_range_inclusive::*,
    trusted_option::*,
	trusted_result::*,
    memory_structs::*,
    trusted_chunk::*
};

pub(crate) mod linked_list;
pub(crate) mod trusted_range_inclusive;
pub(crate) mod trusted_option;
pub(crate) mod trusted_result;
mod test;
mod memory_structs;
mod trusted_chunk;

// mod static_array;
// mod static_array_linked_list;

/*** Constants taken from kernel_config crate. Only required if CHECK_OVERFLOWS flag is enabled. ***/ 
/// The lower 12 bits of a virtual address correspond to the P1 page frame offset. 
const PAGE_SHIFT: usize = 12;
/// Page size is 4096 bytes, 4KiB pages.
const PAGE_SIZE: usize = 1 << PAGE_SHIFT;
const MAX_VIRTUAL_ADDRESS: usize = usize::MAX;
const MAX_PAGE_NUMBER: usize = MAX_VIRTUAL_ADDRESS / PAGE_SIZE;


// /// A trusted function that will create a new `TrustedChunk` and add it to the `chunk_list`.
// /// It will return an Err if:
// /// * range.start > range.end
// /// * there is an overlap with an existing chunk
// // #[cfg_attr(feature="prusti", trusted)]
// #[trusted]
// pub fn create_new_trusted_chunk(range: FrameRange, typ: MemoryRegionType, chunk_list: &mut List) -> Result<Chunk, &'static str> {
//     if range.start() > range.end() {
//         return Err("Invalid range, start > end");
//     }
//     TrustedChunk::new(RangeInclusive::new(range.start().number, range.end().number), chunk_list)
//         .ok_or("requested a chunk that overlapped with an exisiting chunk")
//         .and_then(|tchunk| Chunk::from_trusted(tchunk, *range.start(), *range.end(), typ))
// }


// // /// A trusted function that will create a `List` of the chunks (RangeInclusive) added to the frame allocator.
// // /// This should be called once the heap is initialized.
// // /// It will return an Err if for any of the chunks:
// // /// * chunk.start > chunk.end
// // /// * there is an overlap between chunks
// // /// This ensures that the List is initialized in a consistent state.
// // /// 
// // /// Ideally, creating and managing the initial array, and the conversion, should also be in this crate, 
// // /// but for some reason all verification efforts of StaticArray and StaticArrayLinkedList fail.
// // /// (See static_array.rs and static_array_linked_list.rs)
// // // #[cfg_attr(feature="prusti", trusted)]
// // #[trusted]
// // pub fn convert_unallocated_regions_to_chunks(unallocated_regions: [Option<RangeInclusive<usize>>; 32]) -> Result<List<RangeInclusive>, &'static str> {
// //     let mut list = List::new();
// //     for range in unallocated_regions {
// //         if let Some(r) = range {
// //             if r.start() <= r.end() {
// //                 let elem = RangeInclusive::new(*r.start(), *r.end());
// //                 if List::overlaps(&list.head, elem) {
// //                     return Err("overlapping ranges in the initial array of chunks");
// //                 }
// //                 list.push(elem);
// //             } else {
// //                 return Err("Invalid range, start > end");
// //             }
// //         }
// //     }
// //     Ok(list)
// // }

// pub struct Chunk {
//     /// The type of this memory chunk, e.g., whether it's in a free or reserved region.
//     typ: MemoryRegionType,
//     /// The Frames covered by this chunk, an inclusive range. 
//     frames: FrameRange,
// }

// impl Chunk {
//     #[trusted]
//     fn from_trusted(tchunk: TrustedChunk, start_frame: Frame, end_frame: Frame, typ: MemoryRegionType) -> Result<Self, &'static str> {
//         if tchunk.start() == start_frame.number && tchunk.end() == end_frame.number {
//             Ok(Chunk {
//                 typ,
//                 frames: FrameRange::new(start_frame, end_frame)
//             })
//         } else {
//             Err("The range of the TrustedChunk doesn't match that of the start_frame..end_frame")
//         }
//     }

//     // fn split(self, start_frame: Frame, num_frames: usize) -> Result<(Option<Chunk>, Chunk, Option<Chunk>), Chunk> {
//     //     let typ = self.typ;
//     //     let tchunk = TrustedChunk::from_chunk(self);
//     //     tchunk.split(start_frame.number, num_frames)
//     //         .and_then(||)

//     // }
// }

// /// Types of physical memory. See each variant's documentation.
// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
// pub enum MemoryRegionType {
//     /// Memory that is available for any general purpose.
//     Free,
//     /// Memory that is reserved for special use and is only ever allocated from if specifically requested. 
//     /// This includes custom memory regions added by third parties, e.g., 
//     /// device memory discovered and added by device drivers later during runtime.
//     Reserved,
//     /// Memory of an unknown type.
//     /// This is a default value that acts as a sanity check, because it is invalid
//     /// to do any real work (e.g., allocation, access) with an unknown memory region.
//     Unknown,
// }