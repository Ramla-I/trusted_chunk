// #[cfg(feature="prusti")]
use prusti_contracts::*;

use crate::trusted_range_inclusive::*;
use crate::TrustedChunk;

// #[cfg(feature="prusti")]
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

#[extern_spec]
impl<T: Copy + PartialEq> PartialEq for core::option::Option<T> {
    #[pure]
    #[ensures(self.is_none() && other.is_none() ==> result == true)]
    #[ensures(self.is_none() && other.is_some() ==> result == false)]
    #[ensures(self.is_some() && other.is_none() ==> result == false)]
    #[ensures(self.is_some() && other.is_some() ==> {
        let val1 = peek_option(&self);
        let val2 = peek_option(&other);
        result == (val1 == val2)
    })]
    fn eq(&self, other:&Self) -> bool;

    // #[pure]
    // #[ensures(result == !self.eq(other))]
    // fn ne(&self, other:&Self) -> bool;
}

// #[cfg_attr(feature="prusti", pure)]
// #[cfg_attr(feature="prusti", requires(val.is_some()))]
#[pure]
#[requires(val.is_some())]
pub(crate) fn peek_range(val: &Option<TrustedRangeInclusive>) -> TrustedRangeInclusive {
    match val {
        Some(val) => *val,
        None => unreachable!(),
    }
}

// #[cfg_attr(feature="prusti", pure)]
// #[cfg_attr(feature="prusti", requires(val.is_some()))]
#[pure]
#[requires(val.is_some())]
pub(crate) fn peek_usize(val: &Option<usize>) -> usize {
    match val {
        Some(val) => *val,
        None => unreachable!(),
    }
}

// #[cfg_attr(feature="prusti", pure)]
// #[cfg_attr(feature="prusti", requires(val.is_some()))]
#[pure]
#[requires(val.is_some())]
pub(crate) fn peek_chunk(val: &Option<TrustedChunk>) -> &TrustedChunk {
    match val {
        Some(val) => val,
        None => unreachable!(),
    }
}

#[pure]
#[requires(val.is_some())]
pub(crate) fn peek_option<T: Copy>(val: &Option<T>) -> T {
    match val {
        Some(val) => *val,
        None => unreachable!(),
    }
}

// #[pure]
// pub(crate) fn equal_option<T: Copy + PartialEq>(o1: Option<T>, o2: Option<T>) -> bool {
//     if o1.is_none() && o2.is_none() {
//         true
//     }
//     else if o1.is_none() && o2.is_some() {
//         false
//     }
//     else if o1.is_some() && o2.is_none() {
//         false
//     }


// }
