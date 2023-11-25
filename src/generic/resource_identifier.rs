use prusti_contracts::*;

pub trait ResourceIdentifier: Copy + PartialEq {
    type Resource;

    #[pure]
    fn overlaps(&self, other: &Self) -> bool;

    #[pure]
    fn equal_to_resource(&self, resource: &Self::Resource) -> bool;
}
