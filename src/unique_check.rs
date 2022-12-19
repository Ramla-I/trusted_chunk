pub trait UniqueCheck {
    #[pure]
    #[trusted]
    #[ensures(result ==> other.overlaps_with(&self))]
    fn overlaps_with(&self, other: &Self) -> bool;
}