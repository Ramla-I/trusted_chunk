pub trait UniqueCheck {
    #[pure]
    fn overlaps_with(&self, other: &Self) -> bool;
}