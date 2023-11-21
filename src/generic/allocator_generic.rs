use prusti_contracts::*;
use super::{unique_trait::UniqueCheck, static_array_generic::StaticArray};
use super::linked_list_generic::List;
use crate::external_spec::{
    trusted_option::*,
    trusted_result::*
};

#[derive(Clone, Copy)]
pub enum RepresentationCreationError {
    Overlap(usize),
    NoSpace
}

pub struct ResourceAllocator<T: UniqueCheck<Resource = R>, R> {
    array: Option<StaticArray<T>>,
    list: List<T>,
    constructor: fn(&T) -> R
}

impl<T: UniqueCheck<Resource = R>, R> ResourceAllocator<T, R> {
    #[trusted] // so we can takea  function pointer as an argument
    #[ensures(result.list.len() == 0)]
    #[ensures(!pre_heap ==> result.array.is_none())]
    #[ensures(pre_heap ==> result.array.is_some())]
    #[ensures(pre_heap ==> {
        let array = peek_option_ref(&result.array);
        forall(|i: usize| (i < array.len()) ==> array.lookup(i).is_none())
    })]
    pub fn new(constructor: fn(&T) -> R, pre_heap: bool) -> Self {
        let array = if pre_heap {
            Some(StaticArray::new())
        } else {
            None
        };

        ResourceAllocator {
            array,
            list: List::new(), 
            constructor
        }
    }


    // #[ensures(result.is_err() ==> 
    //     match peek_err(&result) {
    //         RepresentationCreationError::Overlap(idx) =>
    //             match self.array {
    //                 Some(ref array) => (idx < array.len()) && array.lookup(idx).is_some() 
    //                     && peek_option(&array.lookup(idx)).overlaps(&resource_id),
    //                 None => (idx < self.list.len()) && self.list.lookup(idx).overlaps(&resource_id)
    //             },
    //         RepresentationCreationError::NoSpace =>
    //             match snap(&self.array) {
    //                 Some(array) => forall(|i: usize| (i < array.len()) ==> array.lookup(i).is_some()),
    //                 None => unreachable!()
    //             }
    //     }
    // )]
    #[ensures(result.is_ok() ==> {
        let (new_resource, _) = peek_result_ref(&result);
        resource_id.equal_to_resource(&new_resource)
    })]  
    #[ensures(result.is_ok() ==> {
        let (_, idx) = peek_result_ref(&result);
        match self.array {
            Some(ref array) => forall(|i: usize| ((i < array.len()) && array.lookup(i).is_some() && i != *idx) ==> {
                (old(array.lookup(i)) == array.lookup(i)) && !peek_option(&array.lookup(i)).overlaps(&resource_id)}),
            None => forall(|i: usize| (i < old(self.list.len())) ==> !old(self.list.lookup(i)).overlaps(&resource_id))
        }
    })]    
    pub fn create_unique_representation(&mut self, resource_id: T) -> Result<(R, usize), RepresentationCreationError> 
    {
        let idx = match self.array { // ugly because Prusti doesn't understand the ? operator
            Some(ref mut array) => match Self::add_representation_info_pre_heap(array, resource_id) {
                Ok(idx) => idx,
                Err(err) => return Err(err)
            },
            None => match Self::add_representation_info_post_heap(&mut self.list, resource_id) {
                Ok(idx) => idx,
                Err(err) => return Err(err)
            }
        };

        Ok((self.create_new_representation(resource_id), idx))
    }

    
    #[ensures(result.is_err() ==> {
        match peek_err(&result) {
            RepresentationCreationError::Overlap(idx) => {
                (idx < array.len()) && array.lookup(idx).is_some() && peek_option(&array.lookup(idx)).overlaps(&resource_id)
            },
            RepresentationCreationError::NoSpace => {
                forall(|i: usize| (i < array.len()) ==> array.lookup(i).is_some())
            }
        }
    })]
    #[ensures(result.is_ok() ==> {
        let idx = peek_result(&result);
        idx < array.len()
        && array.lookup(idx).is_some()
        && resource_id == peek_option(&array.lookup(idx))
        && forall(|i: usize| ((i < array.len()) && array.lookup(i).is_some() && i != idx) ==> {
            (old(array.lookup(i)) == array.lookup(i)) && !peek_option(&array.lookup(i)).overlaps(&resource_id)
        })
    })]
    fn add_representation_info_pre_heap(array: &mut StaticArray<T>, resource_id: T) -> Result<usize, RepresentationCreationError> {
        let overlap_idx = array.elem_overlaps_in_array(resource_id, 0);
        match overlap_idx {
            Some(idx) => {
                Err(RepresentationCreationError::Overlap(idx))
            },
            None => {
                match array.push(resource_id) { // can't use closures because Prusti doesn't understand them :(
                    Ok(idx) => Ok(idx),
                    Err(()) => Err(RepresentationCreationError::NoSpace)
                }
            }
        }
    }


    #[ensures(result.is_err() ==> {
        match peek_err(&result) {
            RepresentationCreationError::Overlap(idx) => {
                (idx < list.len()) & list.lookup(idx).overlaps(&resource_id)
            },
            _ => unreachable!()
        }
    })]
    #[ensures(result.is_ok() ==> {
        forall(|i: usize| (i < old(list.len())) ==> !old(list.lookup(i)).overlaps(&resource_id))
        && list.len() >= 1 && snap(list.lookup(0)) === resource_id
    })]
    fn add_representation_info_post_heap(list: &mut List<T>, resource_id: T) -> Result<usize, RepresentationCreationError> {
        let overlap_idx = list.elem_overlaps_in_list(resource_id, 0);
        match overlap_idx {
            Some(idx) => Err(RepresentationCreationError::Overlap(idx)),
            None => {
                list.push(resource_id);
                Ok(0)
            }
        }
    }


    #[trusted]
    #[ensures(resource_id.equal_to_resource(&result))]
    /// Function pointers are currently unsupported by Prusti, so we have to trust this function.
    fn create_new_representation(&self, resource_id: T) -> R {
        (self.constructor)(&resource_id)
    }

    pub fn switch_to_heap_allocated(&mut self) -> Result<(),()> {
        if self.list.len() != 0 { return Err(()); }

        match self.array {
            Some(ref array) => {
                let mut i = 0;
                prusti_assert!(self.list.len() == 0);
                while i < array.len() {
                    body_invariant!(i < array.len());
                    body_invariant!(self.list.len() < array.len());
                    // body_invariant!(self.list.len() == i);
                    // body_invariant!(forall(|j: usize| ((0 <= j && j < self.list.len()) ==> self.array.arr[j].is_some())));
                    // body_invariant!(forall(|j: usize| ((0 <= j && j < self.list.len()) ==> peek_option(&self.array.arr[j]) == self.list.lookup_copy(self.list.len() - 1 - j))));
                    // body_invariant!(forall(|i: usize, j: usize| (0 <= i && i < self.list.len() && 0 <= j && j < self.list.len()) ==> 
                    //     (i != j ==> !self.list.lookup_copy(i).overlaps(&self.list.lookup_copy(j))))
                    // );
        
                    if let Some(resource_id) = array.lookup(i) {
                        self.list.push(resource_id);
                    }         
                    i += 1;
                }
            },
            None => return Err(())
        }

        self.array = None;
        Ok(())
    }

}