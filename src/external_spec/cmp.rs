use core::cmp::{Eq, PartialEq};

#[extern_spec]
trait PartialEq <Rhs: ?Sized = Self>
{
    #[pure]
    fn eq(&self, other: &Rhs) -> bool;

    #[pure]
    fn ne(&self, other: &Rhs) -> bool;
}
