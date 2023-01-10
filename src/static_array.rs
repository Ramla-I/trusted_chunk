use prusti_contracts::*;

cfg_if::cfg_if! {
if #[cfg(prusti)] {
    use crate::external_spec::{
        trusted_option::*,
        trusted_result::*,
        trusted_range_inclusive::*,
    };
} else {
    use range_inclusive::*;
}
}

use crate::spec::range_overlaps::*;
use core::mem;

pub struct StaticArray  {
	pub(crate) arr: [Option<RangeInclusive<usize>>; 32]
}

impl StaticArray {
    pub const fn new() -> Self {
        StaticArray {
            arr: [None; 32]
        }
    }

    #[pure]
    #[ensures(result == self.arr.len())]
    pub const fn len(&self) -> usize {
        self.arr.len()
    }

    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> Option<RangeInclusive<usize>> {
        self.arr[index]
    }

    /// Push the given `value` onto the collection.
    /// For an array, it'll add the element to the first empty space.
    // #[cfg_attr(feature="prusti", ensures(result.is_err() ==> 
    //     forall(|i: usize| (0 <= i && i < 32) ==> old(self.arr[i]) == self.arr[i])
    // ))]
    // #[cfg_attr(feature="prusti", ensures(result.is_ok() ==> {
    //     let idx = peek_usize_range(&result);
    //     self.arr[idx] == Some(value)
    // }))]
    // #[cfg_attr(feature="prusti", ensures(result.is_ok() ==> 
    //     forall(|i: usize| ((0 <= i && i < 32) && (i != peek_usize_range(&result))) ==> old(self.arr[i]) == self.arr[i])
    // ))]
    #[ensures(result.is_err() ==> 
        forall(|i: usize| (0 <= i && i < 32) ==> old(self.arr[i]) == self.arr[i])
    )]
    #[ensures(result.is_ok() ==> {
        let idx = peek_result(&result);
        self.arr[idx].is_some()
    })]
    #[ensures(result.is_ok() ==> {
        let idx = peek_result(&result);
        let val = peek_option(&self.arr[idx]);
        val == value
    })]
    #[ensures(result.is_ok() ==> 
        forall(|i: usize| ((0 <= i && i < 32) && (i != peek_result(&result))) ==> old(self.arr[i]) == self.arr[i])
    )] 
	pub fn push(&mut self, value: RangeInclusive<usize>) -> Result<usize, RangeInclusive<usize>> {
        let mut i = 0;

        while i < 32 {
            body_invariant!(i < self.arr.len());
            body_invariant!(i >= 0);

            if self.arr[i].is_none() {
                self.arr[i] = Some(value);
                return Ok(i)
            }
            i += 1;
        }
        return Err(value);
	}


    // #[cfg_attr(feature="prusti", pure)]
    // #[cfg_attr(feature="prusti", requires(0 <= index && index < self.arr.len()))]
    // #[cfg_attr(feature="prusti", ensures(result.is_some() ==> peek_usize(&result) < 32))]
    // #[cfg_attr(feature="prusti", ensures(result.is_some() ==> self.arr[peek_usize(&result)].is_some()))]
    // #[cfg_attr(feature="prusti", ensures(result.is_some() ==> {
    //         let idx = peek_usize(&result);
    //         let range = peek_range(&self.arr[idx]);
    //         (range.end > elem.start) || (elem.end > range.start)
    //     }
    // ))]
    // #[cfg_attr(feature="prusti", ensures(result.is_none() ==> 
    //     forall(|i: usize| ((index <= i && i < 32) && self.arr[i].is_some()) ==> {
    //         let range = peek_range(&self.arr[i]);
    //         !(range.end > elem.start) && !(elem.end > range.start)
    //     })
    // ))]

    // #[pure]
    #[requires(0 <= index && index <= 32)]
    #[ensures(result.is_some() ==> peek_option(&result) < 32)]
    #[ensures(result.is_some() ==> self.arr[peek_option(&result)].is_some())]
    #[ensures(result.is_some() ==> {
            let idx = peek_option(&result);
            let range = peek_option(&self.arr[idx]);
            range_overlaps(&range, &elem)
        }
    )]
    #[ensures(result.is_none() ==> 
        forall(|i: usize| ((index <= i && i < 32) && self.arr[i].is_some()) ==> {
            let range = peek_option(&self.arr[i]);
            !range_overlaps(&range, &elem)
        })
    )]
    pub(crate) fn elem_overlaps_in_array(&self, elem: RangeInclusive<usize>, index: usize) -> Option<usize> {
        if index >= 32 {
            return None;
        }

        let ret = match self.arr[index] {
            Some(val) => {
                if range_overlaps(&val,&elem) {
                    Some(index)
                } else {
                    self.elem_overlaps_in_array(elem, index + 1)
                }
            },
            None => {
                self.elem_overlaps_in_array(elem, index + 1)
            }
        };
        ret
    }
}