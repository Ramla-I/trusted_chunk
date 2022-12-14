pub trait UniqueCheck {
    #[pure]
    #[ensures(result ==> other.overlaps_with(&self))]
    fn overlaps_with(&self, other: &Self) -> bool;
}