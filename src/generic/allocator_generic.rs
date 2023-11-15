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
    #[trusted]
    #[ensures(result.list.len() == 0)]
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

    // /// The only public interface to create a `PageChunk`.
    // /// 
    // /// # Pre-conditions:
    // /// * The `array` is ordered so that all Some(_) elements occur at the beginning of the array, followed by all None elements.
    // /// This pre-condtion is required so that we can relate each element in the old `array` with elements in the updated `list` when we start using the heap.
    // /// Since this is a public function, the  SMT solver cannot check that the pre-condition is valid, so we use the type system. 
    // /// The only exposed function to modify the array is the StaticArray::push() function which has this 
    // /// invariant as both a pre and post condition. So everytime we add an element to an array this condition is upheld.
    // /// 
    // /// # Post-conditions:
    // /// * If ChunkCreationError::Overlap(idx) is returned, then `chunk_range` overlaps with the element at index idx
    // /// * If successful, then result is equal to `chunk_range`
    // /// * If successful, then `chunk_range` did not overlap with any element in the old array/ list
    // /// * If successful, then `chunk_range` has been added to the array/ list
    // /// * If successful, then the `array` remains ordered with all Some elements followed by all None elements
    // #[ensures(result.is_err() ==> {
    //     let idx = peek_err(&result);
    //     (idx < self.list.len()) & self.list.lookup(idx).overlaps(&resource_id)
    // })]
    // #[ensures(result.is_ok() ==> {
    //     let (new_chunk, _) = peek_result_ref(&result);
    //     resource_id.equal_to_resource(new_chunk)
    // })]
    // #[ensures(result.is_ok() ==> {
    //     forall(|i: usize| (i < old(self.list.len())) ==> !old(self.list.lookup(i)).overlaps(&resource_id) || !resource_id.overlaps(old(self.list.lookup(i))))
    // })]
    // #[ensures(result.is_ok() ==> {
    //     self.list.len() >= 1 && snap(self.list.lookup(0)) === resource_id
    // })]
    pub fn create_unique_representation(&mut self, resource_id: T) -> Result<(R, usize), RepresentationCreationError> 
    {
        let idx = match self.array {
            Some(ref mut array) => Self::add_representation_info_pre_heap(array, resource_id)?,
            None => Self::add_representation_info_post_heap(&mut self.list, resource_id)?
        };

        Ok((self.create_new_representation(resource_id), idx))
    }

    
    #[ensures(result.is_err() ==> {
        match peek_err(&result) {
            RepresentationCreationError::Overlap(idx) => {
                true //(idx < array.len()) //& array.lookup(idx).is_some() //& peek_option(&array.lookup(idx)).overlaps(&resource_id)
            },
            RepresentationCreationError::NoSpace => { true
                // forall(|i: usize| (i < array.len()) ==> array.lookup(i).is_some())
            }
        }
    })]
    // #[ensures(result.is_ok() ==> {
    //     forall(|i: usize| (i < old(list.len())) ==> !old(list.lookup(i)).overlaps(&resource_id))
    // })]
    // #[ensures(result.is_ok() ==> {
    //     list.len() >= 1 && snap(list.lookup(0)) === resource_id
    // })]
    fn add_representation_info_pre_heap(array: &mut StaticArray<T>, resource_id: T) -> Result<usize, RepresentationCreationError> {
        let overlap_idx = array.elem_overlaps_in_array(resource_id, 0);
        match overlap_idx {
            Some(idx) => Err(RepresentationCreationError::Overlap(idx)),
            None => {
                array.push(resource_id).map_err(|()| RepresentationCreationError::NoSpace)
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
    })]
    #[ensures(result.is_ok() ==> {
        list.len() >= 1 && snap(list.lookup(0)) === resource_id
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

}