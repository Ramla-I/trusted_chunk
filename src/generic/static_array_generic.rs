use prusti_contracts::*;


// #[cfg(prusti)]
use crate::generic::unique_trait::*;
// #[cfg(not(prusti))]
// use unique_trait::*;

use crate::{
    external_spec::{trusted_option::*, trusted_result::*},
};

pub struct StaticArray<T: UniqueCheck> {
    pub(crate) arr: [Option<T>; 64], // only public so it can be used in spec
}

impl<T: UniqueCheck> StaticArray<T> {
    pub const fn new() -> Self {
        StaticArray {
            arr: [None; 64],
        }
    }

    #[pure]
    pub const fn len(&self) -> usize {
        self.arr.len()
    }

    /// Looks up an element in the array.
    /// 
    /// # Pre-conditions:
    /// * index is less than the length
    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> Option<T> {
        self.arr[index]
    }

 
    /// Adds an element to the array if there's space.
    /// 
    /// # Pre-conditions:
    /// * The array is ordered so that all Some(_) elements occur at the beginning of the array, followed by all None elements.
    ///
    /// # Post-conditions:
    /// * If the push fails, then all elements remain unchanged and were Some(_)
    /// * If the push succeeds, then the element at the returned index is now Some(_)
    /// * If the push succeeds, then the element at the returned index is equal to `value`
    /// * If the push succeeds, then all the elements are unchanged except at the returned index 
    /// * If successful, then the array remains ordered with all Some elements followed by all None elements
    // #[requires(forall(|i: usize| (i < self.arr.len() && self.arr[i].is_some()) ==> {
    //     forall(|j: usize| (j < i) ==> self.arr[j].is_some())
    // }))]
    // #[requires(forall(|i: usize| (i < self.arr.len() && self.arr[i].is_none()) ==> {
    //     forall(|j: usize| (i <= j && j < self.arr.len()) ==> self.arr[j].is_none())
    // }))]
    #[ensures(result.is_err() ==> 
        forall(|i: usize| (i < self.arr.len()) ==> self.arr[i].is_some() && old(self.arr[i]) == self.arr[i])
    )]
    #[ensures(result.is_ok() ==> self.arr[peek_result(&result)].is_some())]
    #[ensures(result.is_ok() ==> value == peek_option(&self.arr[peek_result(&result)]))]
    #[ensures(result.is_ok() ==> 
        forall(|i: usize| (i < self.arr.len() && i != peek_result(&result)) ==> old(self.arr[i]) == self.arr[i])
    )] 
    // #[ensures(forall(|i: usize| (i < self.arr.len() && self.arr[i].is_some()) ==> {
    //     forall(|j: usize| (j < i) ==> self.arr[j].is_some())
    // }))]
    // #[ensures(forall(|i: usize| (i < self.arr.len() && self.arr[i].is_none()) ==> {
    //     forall(|j: usize| (i <= j && j < self.arr.len()) ==> self.arr[j].is_none())
    // }))]
	pub(crate) fn push(&mut self, value: T) -> Result<usize,()> {
        let mut i = 0;

        while i < self.arr.len() {
            body_invariant!(forall(|j: usize| (j < i ==> self.arr[j].is_some())));
            body_invariant!(i < self.arr.len());

            if self.arr[i].is_none() {
                self.arr[i] = Some(value);
                return Ok(i)
            }
            i += 1;
        }
        return Err(());
	}


    /// Returns the index of the first element in the array, starting from `index`, which overlaps with `elem`.
    /// Returns None if there is no overlap.
    ///  
    /// # Pre-conditions:
    /// * index is less than or equal to the array length
    /// 
    /// # Post-conditions:
    /// * if the result is Some(idx), then idx is less than the list's length.
    /// * if the result is Some(idx), then the element at idx is Some(_)
    /// * if the result is Some(idx), then the element at idx overlaps with `elem`
    /// * if the result is None, then no element in the array overlaps with `elem`
    #[requires(index <= self.arr.len())]
    #[ensures(result.is_some() ==> peek_option(&result) < self.arr.len())]
    #[ensures(result.is_some() ==> self.arr[peek_option(&result)].is_some())]
    #[ensures(result.is_some() ==> self.lookup(peek_option(&result)).is_some())]
    #[ensures(result.is_some() ==> peek_option(&self.arr[peek_option(&result)]).overlaps(&elem))]
    #[ensures(result.is_none() ==> 
        forall(|i: usize| ((index <= i && i < self.arr.len()) && self.arr[i].is_some()) ==> {
            !peek_option(&self.arr[i]).overlaps(&elem)
        })
    )]
    pub(crate) fn elem_overlaps_in_array(&self, elem: T, index: usize) -> Option<usize> {
        if index == self.arr.len() {
            return None;
        }

        let ret = match self.arr[index] {
            Some(val) => {
                if val.overlaps(&elem) {
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