use prusti_contracts::*;
use crate::{
    generic::resource_identifier::*,
    external_spec::{trusted_option::*, trusted_result::*},
};

pub struct StaticArray<T: ResourceIdentifier> {
    pub(crate) arr: [Option<T>; 64], // only public so it can be used in the spec directly
}

impl<T: ResourceIdentifier> StaticArray<T> {
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

    // #[requires(index < self.len())]
    // #[ensures(self.lookup(index) == Some(value))]
    // #[ensures(self.lookup(index).is_some())]
    // #[ensures(forall(|i: usize| (i < self.len() && i != index) ==> old(self.lookup(i)) == self.lookup(i)))]
    // #[ensures(forall(|i: usize| (i < self.len() && i != index) ==> old(self.lookup(i).is_some()) ==> self.lookup(i).is_some()))]
    // fn set_element(&mut self, index: usize, value: T) {
    //     self.arr[index] = Some(value);
    // }

    // /// I tried to verify this using the public interface, but it eventually leads to Prusti errors.
    // /// So for now I'm sticking with the function that accesses the array directly.
    // ///
    // /// Adds an element to the array if there's space.
    // /// 
    // /// # Pre-conditions:
    // /// * The array is ordered so that all Some(_) elements occur at the beginning of the array, followed by all None elements.
    // ///
    // /// # Post-conditions:
    // /// * If the push fails, then all elements remain unchanged and were Some(_)
    // /// * If the push succeeds, then the element at the returned index is now Some(_)
    // /// * If the push succeeds, then the element at the returned index is equal to `value`
    // /// * If the push succeeds, then all the elements are unchanged except at the returned index 
    // /// * If successful, then the array remains ordered with all Some elements followed by all None elements
    // #[requires(forall(|i: usize| (i < self.len() && self.lookup(i).is_some()) ==> {
    //     forall(|j: usize| (j < i) ==> self.lookup(j).is_some())
    // }))]
    // #[requires(forall(|i: usize| (i < self.len() && self.lookup(i).is_none()) ==> {
    //     forall(|j: usize| (i <= j && j < self.len()) ==> self.lookup(j).is_none())
    // }))]
    // #[ensures(result.is_err() ==> 
    //     forall(|i: usize| (i < self.len()) ==> self.lookup(i).is_some() && old(self.lookup(i)) == self.lookup(i))
    // )]
    // #[ensures(result.is_ok() ==> peek_result(&result) < self.len())]
    // #[ensures(result.is_ok() ==> self.lookup(peek_result(&result)).is_some())]
    // #[ensures(result.is_ok() ==> value == peek_option(&self.lookup(peek_result(&result))))]
    // #[ensures(result.is_ok() ==> 
    //     forall(|i: usize| (i < self.len() && i != peek_result(&result)) ==> old(self.lookup(i)) == self.lookup(i))
    // )] 
    // // #[ensures(forall(|i: usize| (i < self.len() && self.lookup(i).is_some()) ==> {
    // //     forall(|j: usize| (j < i) ==> self.lookup(j).is_some())
    // // }))]
    // // #[ensures(forall(|i: usize| (i < self.arr.len() && self.arr[i].is_none()) ==> {
    // //     forall(|j: usize| (i <= j && j < self.arr.len()) ==> self.arr[j].is_none())
    // // }))]
	// pub(crate) fn push(&mut self, value: T) -> Result<usize,()> {
    //     let mut i = 0;

    //     while i < self.len() {
    //         body_invariant!(i < self.len());
    //         body_invariant!(forall(|j: usize| (j < i ==> self.lookup(j).is_some())));
    //         body_invariant!(forall(|j: usize| (j < i ==> self.arr[j].is_some())));

    //         if self.lookup(i).is_none() {
    //             prusti_assert!(forall(|j: usize| (j >= i && j < self.len() ==> self.lookup(j).is_none())));

    //             self.arr[i] = Some(value);
    //             prusti_assert!(self.lookup(i).is_some());
    //             prusti_assert!(!self.lookup(i).is_none());

    //             prusti_assert!(forall(|j: usize| (j <= i ==> self.arr[j].is_some())));
    //             prusti_assert!(forall(|j: usize| (j <= i ==> self.lookup(j).is_some())));
    //             prusti_assert!(forall(|j: usize| (j > i && j < self.len() ==> self.arr[j].is_none())));
    //             return Ok(i)
    //         }
    //         i += 1;
    //     }
    //     return Err(());
	// }

    predicate! {
        // predicate to check that the elements in the array are ordered
        fn ordered_static_array(&self) -> bool {
            forall(|i: usize| (i < self.arr.len() && self.arr[i].is_some()) ==> {
                forall(|j: usize| (j < i) ==> self.arr[j].is_some())
            })
            &&
            forall(|i: usize| (i < self.arr.len() && self.arr[i].is_none()) ==> {
                forall(|j: usize| (i <= j && j < self.arr.len()) ==> self.arr[j].is_none())
            })
        }
    }

    #[requires( // trying to use predicate in pre-condition leads to failing post-condition (why?)
        forall(|i: usize| (i < self.arr.len() && self.arr[i].is_some()) ==> {
            forall(|j: usize| (j < i) ==> self.arr[j].is_some())})
        &&
        forall(|i: usize| (i < self.arr.len() && self.arr[i].is_none()) ==> {
            forall(|j: usize| (i <= j && j < self.arr.len()) ==> self.arr[j].is_none())
    }))]
    #[ensures(result.is_err() ==> // moving these to a match statement leads to compiler error
        forall(|i: usize| (i < self.arr.len()) ==> self.arr[i].is_some() && old(self.arr[i]) == self.arr[i])
    )]
    #[ensures(result.is_ok() ==> {
        let idx = peek_result(&result);
        self.arr[idx].is_some() && peek_option(&self.arr[idx]) == value && self.ordered_static_array()
        && forall(|i: usize| ((i < self.arr.len()) && (i != idx)) ==> old(self.arr[i]) == self.arr[i])
    })]
	pub(crate) fn push(&mut self, value: T) -> Result<usize,()> {
        let mut i = 0;

        while i < self.arr.len() {
            body_invariant!(forall(|j: usize| ((j < i) ==> self.arr[j].is_some())));
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
    // #[requires(index <= self.arr.len())]
    #[requires(index <= self.len())]
    #[ensures(
        match result {
            Some(idx) => idx < self.len() && self.lookup(idx).is_some() && peek_option(&self.lookup(idx)).overlaps(&elem),
            None => forall(|i: usize| ((index <= i && i < self.len()) && self.lookup(i).is_some()) ==> {
                !peek_option(&self.lookup(i)).overlaps(&elem)
            })
        }
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