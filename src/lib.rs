#![cfg_attr(not(std), no_std)]
#![feature(box_patterns)]
#![allow(unused)]
#![feature(step_trait)]
#![feature(rustc_private)]

#[macro_use]
extern crate prusti_contracts;
#[macro_use]
extern crate cfg_if;
extern crate core;

pub(crate) mod external_spec;
// mod test;
mod frames;
// mod pages;

// pub use frames::frame_chunk;
// pub use pages::page_chunk;

// use frames::frame_range::FrameRange;

cfg_if::cfg_if! {
if #[cfg(prusti)] {
    use crate::external_spec::trusted_range_inclusive::*;
} else {
    extern crate alloc;
    extern crate range_inclusive;
    extern crate spin;
    use range_inclusive::*;

    static INIT: spin::Once<bool> = spin::Once::new();
}
}


// #[cfg(not(prusti))] // prusti can't reason about fn pointers
// pub fn init_frame_chunk() -> Result<fn(FrameRange) -> frame_chunk::FrameChunk, &'static str> {

//     if INIT.is_completed() {
//         Err("Trusted Chunk has already been initialized and callback has been returned")
//     } else {
//         INIT.call_once(|| true);
//         Ok(create_from_unmapped)
//     }
// }

// #[requires(frames.start_frame().less_than_equal(&frames.end_frame()))]
// #[ensures(result.start_frame() == frames.start_frame())]
// #[ensures(result.end_frame() == frames.end_frame())]
// fn create_from_unmapped(frames: FrameRange) -> frame_chunk::FrameChunk {
//     frame_chunk::FrameChunk::trusted_new(frames)
// }

