use prusti_contracts::*;

pub(crate) const MIN_FRAME_NUMBER: usize = 0;
pub(crate) const MAX_FRAME_NUMBER: usize = 0xFF_FFFF_FFFF; // usize::MAX & 0x000F_FFFF_FFFF_FFFF / PAGE_SIZE

pub trait UniqueCheck: Copy + PartialEq {
    #[pure]
    #[trusted] // has to be trusted to call itself, which then requires us to define a spec for the fn as well :(
    #[ensures(result == other.overlaps(&self))] // if we dont have this condition, then post-condition of push_unique_with_precond wont' verify
    fn overlaps(&self, other: &Self) -> bool;
}
