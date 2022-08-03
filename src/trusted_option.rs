use prusti_contracts::*;
use crate::trusted_range_inclusive::*;

#[extern_spec]
impl<T> core::option::Option<T> {
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == !result)]
    pub fn is_none(&self) -> bool;

    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;
}

#[pure]
#[requires(val.is_some())]
pub(crate) fn peek_range(val: &Option<TrustedRangeInclusive>) -> TrustedRangeInclusive {
    match val {
        Some(val) => *val,
        None => unreachable!(),
    }
}

#[pure]
#[requires(val.is_some())]
pub(crate) fn peek_usize(val: &Option<usize>) -> usize {
    match val {
        Some(val) => *val,
        None => unreachable!(),
    }
}

// #[derive(Copy, Clone)]
// pub enum OptionRange {
//     Some(TrustedRangeInclusive),
//     None,
// }

// impl OptionRange {
//     #[pure]
//     pub fn is_none(&self) -> bool {
//         match self {
//             OptionRange::Some(_) => false,
//             OptionRange::None => true,
//         }
//     }

//     #[pure]
//     pub fn is_some(&self) -> bool {
//         !self.is_none()
//     }

//     #[pure]
//     #[requires(self.is_some())]
//     pub fn peek(&self) -> TrustedRangeInclusive {
//         match self {
//             OptionRange::Some(val) => *val,
//             OptionRange::None => unreachable!(),
//         }
//     }
// }
