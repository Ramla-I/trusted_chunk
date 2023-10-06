use prusti_contracts::*;

pub trait UniqueCheck: Copy + PartialEq {
    #[pure]
    #[trusted] // has to be trusted to call itself, which then requires us to define a spec for the fn as well :(
    #[ensures(result == other.overlaps(&self))] // if we dont have this condition, then post-condition of push_unique_with_precond wont' verify
    fn overlaps(&self, other: &Self) -> bool;
}
