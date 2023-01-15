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
	pub(crate) arr: [Option<RangeInclusive<usize>>; 64]
}

impl StaticArray {
    pub const fn new() -> Self {
        StaticArray {
            arr: [None; 64]
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


    #[ensures(result.is_none() ==> 
        forall(|i: usize| (0 <= i && i < self.arr.len()) ==> old(self.arr[i]) == self.arr[i])
    )]
    #[ensures(result.is_some() ==> {
        let idx = peek_option(&result);
        self.arr[idx].is_some()
    })]
    #[ensures(result.is_some() ==> {
        let idx = peek_option(&result);
        let val = peek_option(&self.arr[idx]);
        val == value
    })]
    #[ensures(result.is_some() ==> 
        forall(|i: usize| ((0 <= i && i < self.arr.len()) && (i != peek_option(&result))) ==> old(self.arr[i]) == self.arr[i])
    )] 
	pub fn push(&mut self, value: RangeInclusive<usize>) -> Option<usize> {
        let mut i = 0;

        while i < self.arr.len() {
            body_invariant!(i < self.arr.len());
            body_invariant!(i >= 0);

            if self.arr[i].is_none() {
                self.arr[i] = Some(value);
                return Some(i)
            }
            i += 1;
        }
        return None;
	}


    #[requires(0 <= index && index <= self.arr.len())]
    #[ensures(result.is_some() ==> peek_option(&result) < self.arr.len())]
    #[ensures(result.is_some() ==> self.arr[peek_option(&result)].is_some())]
    #[ensures(result.is_some() ==> {
            let idx = peek_option(&result);
            let range = peek_option(&self.arr[idx]);
            range_overlaps(&range, &elem)
        }
    )]
    #[ensures(result.is_none() ==> 
        forall(|i: usize| ((index <= i && i < self.arr.len()) && self.arr[i].is_some()) ==> {
            let range = peek_option(&self.arr[i]);
            !range_overlaps(&range, &elem)
        })
    )]
    pub(crate) fn elem_overlaps_in_array(&self, elem: RangeInclusive<usize>, index: usize) -> Option<usize> {
        if index >= self.arr.len() {
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