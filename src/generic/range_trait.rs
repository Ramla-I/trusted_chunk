use prusti_contracts::*;

pub(crate) const MIN_FRAME_NUMBER: usize = 0;
pub(crate) const MAX_FRAME_NUMBER: usize = 0xFF_FFFF_FFFF; // usize::MAX & 0x000F_FFFF_FFFF_FFFF / PAGE_SIZE

pub trait UniqueCheck: Copy + PartialEq {
    #[pure]
    #[trusted] // has to be trusted to call itself, which then requires us to define a spec for the fn as well :(
    #[ensures(result == other.overlaps(&self))] // if we dont have this condition, then post-condition of push_unique_with_precond wont' verify
    fn overlaps(&self, other: &Self) -> bool;
}

pub trait UnitTrait: core::marker::Sized + Copy + PartialEq + PartialOrd {
    #[pure]
    fn number(&self) -> usize;

    #[ensures(result.number() == number)]
    fn new(number: usize) -> Self;

    #[pure]
    #[trusted]
    #[ensures(result.number() == min(MAX_FRAME_NUMBER, saturating_add(self.number(), rhs)))]
    #[ensures(result.greater_than_equal(&self))]
    #[ensures(rhs == 0 ==> result == self)]
    #[ensures(self.number() >= MAX_FRAME_NUMBER ==> result == self)]
    #[ensures(self.number() < MAX_FRAME_NUMBER ==> result.greater_than(&self))]
    fn plus(self, rhs: usize) -> Self;

    #[pure]
    #[trusted]
    #[ensures(result.number() == saturating_sub(self.number(), rhs))]
    #[ensures(result.less_than_equal(&self))]
    #[ensures(rhs == 0 ==> result == self)]
    fn minus(self, rhs: usize) -> Self;

    #[pure]
    #[trusted]
    #[ensures(result == (self.number() < rhs.number()))]
    #[ensures(!result ==> self.greater_than_equal(&rhs))]
    fn less_than(self, rhs: &Self) -> bool;

    #[pure]
    #[trusted]
    #[ensures(result == (self.number() <= rhs.number()))]
    #[ensures(!result ==> self.greater_than(&rhs))]
    #[ensures(result ==> self == *rhs || self.less_than(&rhs))]
    fn less_than_equal(self, rhs: &Self) -> bool;

    #[pure]
    #[trusted]
    #[ensures(result == (self.number() > rhs.number()))]
    #[ensures(!result ==> self.less_than_equal(&rhs))]
    fn greater_than(self, rhs: &Self) -> bool;

    #[pure]
    #[trusted]
    #[ensures(result == (self.number() >= rhs.number()))]
    #[ensures(!result ==> self.less_than(&rhs))]
    #[ensures(result ==> self == *rhs || self.greater_than(&rhs))]
    fn greater_than_equal(self, rhs: &Self) -> bool;
}

#[pure]
fn min(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

#[pure]
fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
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