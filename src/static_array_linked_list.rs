// #[cfg(feature="prusti")]
use prusti_contracts::*;

use crate::{
    linked_list::*,
    trusted_range_inclusive::*,
    trusted_option::*,
	trusted_result::*,
	static_array::*
};


/// A convenience wrapper that abstracts either a `LinkedList<T>` or a primitive array `[T; N]`.
/// 
/// This allows the caller to create an array statically in a const context, 
/// and then abstract over both that and the inner `LinkedList` when using it. 
/// 
/// TODO: use const generics to allow this to be of any arbitrary size beyond 32 elements.
pub enum StaticArrayLinkedList {
	Array(StaticArray),
	LinkedList(List),
}

impl StaticArrayLinkedList {
	// #[cfg_attr(feature="prusti", pure)]
    #[pure]
	fn is_array(&self) -> bool {
		match self {
			StaticArrayLinkedList::Array(_) => true,
			StaticArrayLinkedList::LinkedList(_) => false,
		}
	}

	// #[cfg_attr(feature="prusti", pure)]
    #[pure]
	fn is_linked_list(&self) -> bool {
		!self.is_array()
	}

	// #[cfg_attr(feature="prusti", pure)]
	// #[cfg_attr(feature="prusti", requires(self.is_array()))]
	#[pure]
	#[requires(self.is_array())]
	fn peek_array(&self) -> &StaticArray {
		match self {
			StaticArrayLinkedList::Array(val) => val,
			StaticArrayLinkedList::LinkedList(_) => unreachable!(),
		}
	}

	// #[cfg_attr(feature="prusti", pure)]
	// #[cfg_attr(feature="prusti", requires(self.is_linked_list()))]
	#[pure]
	#[requires(self.is_linked_list())]
	fn peek_linked_list(&self) -> &List {
		match self {
			StaticArrayLinkedList::Array(_) => unreachable!(),
			StaticArrayLinkedList::LinkedList(val) => val,
		}
	}

	/// Push the given `value` onto the collection.
    /// For an array, it'll add the element to the first empty space.
    /// For a linked list, it'll add the element to the front.
	// #[cfg_attr(feature="prusti", trusted)]
    // #[cfg_attr(feature="prusti", ensures(self.is_array() && result.is_err() ==> forall(|i: usize| (0 <= i && i < 32) ==> {
	// 		let arr = self.peek_array().arr;
	// 		let old_arr = old(self).peek_array().arr;
	// 		arr[i] == old_arr[i]
	// 	})
	// ))]
    // #[cfg_attr(feature="prusti", ensures(self.is_array() && result.is_ok() ==> {
	// 		let idx = peek_usize_range(&result);
	// 		let arr = self.peek_array().arr;
	// 		arr[idx] == Some(value)
	// 	}
	// ))]
	// #[cfg_attr(feature="prusti", ensures(self.is_array() && result.is_ok() ==> 
	// 	forall(|i: usize| ((0 <= i && i < 32) && (i != peek_usize_range(&result))) ==> {
	// 		let arr = self.peek_array().arr;
	// 		let old_arr = old(self.peek_array().arr);
	// 		old_arr[i] == arr[i]
	// 	})
	// ))]
    // #[cfg_attr(feature="prusti", ensures(self.is_linked_list() ==> self.peek_linked_list().len() == old(self.peek_linked_list().len()) + 1))] 
    // #[cfg_attr(feature="prusti", ensures(self.is_linked_list() ==> self.peek_linked_list().lookup(0) == value))]
    // #[cfg_attr(feature="prusti", ensures(self.is_linked_list() ==> forall(|i: usize| (1 <= i && i < self.peek_linked_list().len()) ==>
    //     old(self.peek_linked_list().lookup(i-1)) == self.peek_linked_list().lookup(i))
	// ))]

    #[ensures(self.is_array() && result.is_err() ==> forall(|i: usize| (0 <= i && i < 32) ==> {
			let arr = self.peek_array().arr;
			let old_arr = old(self).peek_array().arr;
			arr[i] == old_arr[i]
		})
	)]
    #[ensures(self.is_array() && result.is_ok() ==> {
			let idx = peek_usize_range(&result);
			let arr = self.peek_array().arr;
			arr[idx] == Some(value)
		}
	)]
	#[ensures(self.is_array() && result.is_ok() ==> 
		forall(|i: usize| ((0 <= i && i < 32) && (i != peek_usize_range(&result))) ==> {
			let arr = self.peek_array().arr;
			let old_arr = old(self.peek_array().arr);
			old_arr[i] == arr[i]
		})
	)]
    #[ensures(self.is_linked_list() ==> self.peek_linked_list().len() == old(self.peek_linked_list().len()) + 1)] 
    #[ensures(self.is_linked_list() ==> self.peek_linked_list().lookup(0) == value)]
    #[ensures(self.is_linked_list() ==> forall(|i: usize| (1 <= i && i < self.peek_linked_list().len()) ==>
        old(self.peek_linked_list().lookup(i-1)) == self.peek_linked_list().lookup(i))
	)]
	pub(crate) fn push(&mut self, value: TrustedRangeInclusive) -> Result<usize, TrustedRangeInclusive> {
		match self {
			StaticArrayLinkedList::Array(arr) => {
				arr.push(value)
			}
			StaticArrayLinkedList::LinkedList(ll) => {
				ll.push(value);
				Ok(0)
			}
		}
	}


	// /// Converts the contained collection from a primitive array into a LinkedList.
	// /// If the contained collection is already using heap allocation, this is a no-op.
	// /// 
	// /// Call this function once heap allocation is available. 
	// #[ensures(old(self.is_array()) ==> self.is_linked_list())]
	// #[ensures(old(self.is_linked_list()) ==> self.is_linked_list())]
	// #[ensures(old(self.is_linked_list()) ==> self.peek_linked_list().len() == old(self.peek_linked_list().len()))]
	// #[ensures(old(self.is_linked_list()) ==> forall(|i: usize| (0 <= i && i < self.peek_linked_list().len()) 
	// 	==> self.peek_linked_list().lookup(i) == old(self.peek_linked_list().lookup(i)) 
	// ))]
	// #[ensures(old(self.is_array()) ==> self.peek_linked_list().len() <= old(self.peek_array().len()))]
	// // #[ensures(old(self.is_array()) ==> 
	// // 	forall(|i: usize| (0 <= i && i < self.peek_linked_list().len()) ==> 
	// // 		old(self.peek_array().lookup(i).is_some()) ==>
	// // 			self.peek_linked_list().lookup(i) == old(peek_range(&self.peek_array().lookup(i)))
	// // ))]
	// pub fn convert_to_heap_allocated(&mut self) {
	// 	let new_ll = match self {
	// 		StaticArrayLinkedList::Array(sa) => {
	// 			let mut ll = List::new();
	// 			let mut i = 0;
	// 			while i < sa.len() {
	// 				body_invariant!(i < sa.len());
	// 				body_invariant!(i >= 0);
	// 				if let Some(e) = sa.arr[i] {
	// 					ll.push(e);
	// 				}
	// 				i += 1;
	// 			}
	// 			assert!(ll.len() <= sa.len());
	// 			ll
	// 		}
	// 		StaticArrayLinkedList::LinkedList(_ll) => return,
	// 	};
	// 	*self = StaticArrayLinkedList::LinkedList(new_ll);
	// }

	// pub(crate) fn range_overlaps(&self, elem: TrustedRangeInclusive) -> bool {
	// 	let result = match self{
	// 		StaticArrayLinkedList::Array(sa) => {
	// 			sa.range_overlaps_in_array(elem, 0)
	// 		},
	// 		StaticArrayLinkedList::LinkedList(ll) => {
	// 			ll.range_overlaps_in_list(elem, 0)
	// 		}
	// 	};

	// 	result.is_some()
	// }
}
