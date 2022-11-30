// #[cfg(feature="prusti")]
use prusti_contracts::*;

use crate::trusted_range_inclusive::*;
use crate::*;

// // #[cfg(feature="prusti")]
// #[extern_spec]
// impl<T,E> core::result::Result<T,E> {
//     #[pure]
//     #[ensures(matches!(*self, Ok(_)) == result)]
//     pub fn is_ok(&self) -> bool;

//     #[pure]
//     #[ensures(self.is_ok() == !result)]
//     pub fn is_err(&self) -> bool;

//     // #[requires(self.is_ok())]
//     // pub fn unwrap(self) -> T;
// }

// #[cfg_attr(feature="prusti", pure)]
// #[cfg_attr(feature="prusti", requires(val.is_ok()))]
#[pure]
#[requires(val.is_ok())]
pub(crate) fn peek_usize_range(val: &Result<usize, TrustedRangeInclusive>) -> usize {
    match val {
        Ok(val) => *val,
        Err(_) => unreachable!(),
    }
}
