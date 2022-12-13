/// Don't have to write an extern spec for Result because it's already in prusti_contracts

// #[cfg(feature="prusti")]
use prusti_contracts::*;

use crate::trusted_range_inclusive::*;
use crate::*;

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

#[pure]
#[requires(val.is_ok())]
pub(crate) fn peek_result<T: Copy, E>(val: &Result<T,E>) -> T {
    match val {
        Ok(val) => *val,
        Err(_) => unreachable!(),
    }
}
