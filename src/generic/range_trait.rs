pub trait RangeTrait<U: UnitTrait> {

    #[pure]
    #[trusted] // has to be trusted to call itself, which then requires us to define a spec for the fn as well :(
    #[ensures(result == other.range_overlaps(&self))] // if we dont have this condition, then post-condition of push_unique_with_precond wont' verify
    fn range_overlaps(&self, other: &Self) -> bool;

    #[pure]
    fn is_empty(&self) -> bool;
    
    #[pure]
    fn start(&self) -> &U;

    #[pure]
    fn end(&self) -> &U;

    fn empty() -> Self;
}

pub trait UnitTrait {
    #[pure]
    fn number(&self) -> usize;

    fn new(number: usize) -> Self;

    #[pure]
    #[trusted]
    #[ensures(result.number == min(MAX_FRAME_NUMBER, saturating_add(self.number, rhs)))]
    #[ensures(result.greater_than_equal(&self))]
    #[ensures(rhs == 0 ==> result == self)]
    fn plus(self, rhs: usize) -> Self;

    #[pure]
    #[trusted]
    #[ensures(result.number == saturating_sub(self.number, rhs))]
    #[ensures(result.less_than_equal(&self))]
    #[ensures(rhs == 0 ==> result == self)]
    fn minus(self, rhs: usize) -> Self;

    #[pure]
    #[trusted]
    #[ensures(result == (self.number < rhs.number))]
    #[ensures(!result ==> self.greater_than_equal(&rhs))]
    fn less_than(self, rhs: &Self) -> bool;

    #[pure]
    #[trusted]
    #[ensures(result == (self.number <= rhs.number))]
    #[ensures(!result ==> self.greater_than(&rhs))]
    fn less_than_equal(self, rhs: &Self) -> bool;

    #[pure]
    #[trusted]
    #[ensures(result == (self.number > rhs.number))]
    #[ensures(!result ==> self.less_than_equal(&rhs))]
    fn greater_than(self, rhs: &Self) -> bool;

    #[pure]
    #[trusted]
    #[ensures(result == (self.number >= rhs.number))]
    #[ensures(!result ==> self.less_than(&rhs))]
    fn greater_than_equal(self, rhs: &Self) -> bool;
}