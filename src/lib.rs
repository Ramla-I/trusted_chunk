// #![no_std]
#![feature(box_patterns)]
#![allow(unused)]
#![feature(step_trait)]
#![feature(rustc_private)]

use trusted_chunk::TrustedChunk;

#[macro_use]
extern crate prusti_contracts;
#[macro_use]
extern crate cfg_if;
extern crate core;
// #[macro_use]
// extern crate static_assertions;
// mod memory_structs;
pub(crate) mod spec;
pub mod linked_list;
pub mod static_array;
pub mod trusted_chunk;
// mod test;

cfg_if::cfg_if! {
if #[cfg(prusti)] {
    pub(crate) mod external_spec;
    use crate::external_spec::{
        trusted_range_inclusive::*,
        trusted_option::*,
        trusted_result::*,
    };
} else {
    extern crate alloc;
    extern crate range_inclusive;
    use range_inclusive::*;
}
}

#[cfg(not(prusti))] 
pub fn init() -> fn(RangeInclusive<usize>) -> trusted_chunk::TrustedChunk {
    |frames: RangeInclusive<usize>| -> trusted_chunk::TrustedChunk {
        trusted_chunk::TrustedChunk::trusted_new(frames)
    }
}
