use core::ops::{Deref, DerefMut};

use prusti_contracts::*;

use super::{unique_trait::UniqueCheck, allocator_generic::ResourceAllocator};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct PciLocation {
    bus:  u8,
    slot: u8,
    func: u8,
}

pub struct PciDevice {
    location: PciLocation,
}

impl PciDevice {
    fn new(location: &PciLocation) -> Self {
        PciDevice { location: *location }
    }
}

impl UniqueCheck for PciLocation {
    type Resource = PciDevice;

    #[pure]
    // #[trusted] // has to be trusted to call itself, which then requires us to define a spec for the fn as well :(
    // #[ensures(result == other.overlaps(&self))] // if we dont have this condition, then post-condition of push_unique_with_precond wont' verify
    fn overlaps(&self, other: &Self) -> bool {
        self.bus == other.bus && self.slot == other.slot && self.func == other.func
    }

    #[pure]
    fn equal_to_resource(&self, resource: &Self::Resource) -> bool{
        self.bus == resource.location.bus && self.slot == resource.location.slot && self.func == resource.location.func
    }
}

struct PciDeviceAllocator(ResourceAllocator<PciLocation, PciDevice>);

impl PciDeviceAllocator {
    #[trusted] //Function pointers are currently unsupported by Prusti, so we have to trust this function.
    fn new() -> Self {
        PciDeviceAllocator(ResourceAllocator::new(PciDevice::new, false))
    }
}

impl Deref for PciDeviceAllocator {
    type Target = ResourceAllocator<PciLocation, PciDevice>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for PciDeviceAllocator {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
