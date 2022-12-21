//! Most of the List code is taken from the Prusti user guide 
//! https://viperproject.github.io/prusti-dev/user-guide/tour/summary.html

// #[cfg(feature="prusti")]
use prusti_contracts::*;

use crate::{
    trusted_option::*,
    unique_check::*,
    trusted_result::*,
    trusted_range_inclusive::*,
};
use core::{
    mem,
    marker::Copy,
    ops::Deref
};


pub struct List {
    pub(crate) head: Link,
}

pub(crate) enum Link {
    Empty,
    More(Box<Node>)
}

pub(crate) struct Node {
    elem: RangeInclusive<usize>,
    next: Link,
}


// #[cfg_attr(feature="prusti", trusted)]
// #[cfg_attr(feature="prusti", requires(src.is_empty()))]
// #[cfg_attr(feature="prusti", ensures(dest.is_empty()))]
// #[cfg_attr(feature="prusti", ensures(old(dest.len()) == result.len()))]
// #[cfg_attr(feature="prusti", ensures(forall(|i: usize| (0 <= i && i < result.len()) ==> 
//                 old(dest.lookup(i)) == result.lookup(i))))] 
#[trusted]
#[requires(src.is_empty())]
#[ensures(dest.is_empty())]
#[ensures(old(dest.len()) == result.len())]
#[ensures(forall(|i: usize| (0 <= i && i < result.len()) ==> 
                old(dest.lookup(i)) == result.lookup(i)))] 
fn replace(dest: &mut Link, src: Link) -> Link {
    mem::replace(dest, src)
}


impl List {

    // #[cfg_attr(feature="prusti", pure)]
    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    /// Looks up an element in the list.
    /// Requires that the index is within range. 
    // #[cfg_attr(feature="prusti", pure)]
    // #[cfg_attr(feature="prusti", requires(0 <= index && index < self.len()))]
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> RangeInclusive<usize> {
        self.head.lookup(index)
    }

    /// Creates an empty list.
    /// Ensures that the length is zero.
    // #[cfg_attr(feature="prusti", ensures(result.len() == 0))]
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: Link::Empty }
    }

    /// Adds an element to the list.
    /// Ensures that:
    /// * new_length = old_length + 1
    /// * `elem` is added at index 0
    /// * all previous elements remain in the list, just moved one index forward
    // #[cfg_attr(feature="prusti", ensures(self.len() == old(self.len()) + 1))] 
    // #[cfg_attr(feature="prusti", ensures(self.lookup(0) == elem))]
    // #[cfg_attr(feature="prusti", ensures(forall(|i: usize| (1 <= i && i < self.len()) ==>
    //     old(self.lookup(i-1)) == self.lookup(i))))]
    #[ensures(self.len() == old(self.len()) + 1)] 
    #[ensures(self.lookup(0) == elem)]
    #[ensures(forall(|i: usize| (1 <= i && i < self.len()) ==> old(self.lookup(i-1)) == self.lookup(i)))]
    pub fn push(&mut self, elem: RangeInclusive<usize>) {
        let new_node = Box::new(Node {
            elem: elem,
            next: replace(&mut self.head, Link::Empty)
        });

        self.head = Link::More(new_node);
    }

    #[ensures(result.is_err() ==> peek_err(&result) < self.len())]
    #[ensures(result.is_err() ==> {
            let idx = peek_err(&result);
            let range = self.lookup(idx);
            range.overlaps_with(&elem)
        }
    )]
    #[ensures(result.is_ok() ==> self.len() == old(self.len()) + 1)] 
    #[ensures(result.is_ok() ==> self.lookup(0) == elem)]
    #[ensures(result.is_ok() ==> forall(|i: usize| (1 <= i && i < self.len()) ==> old(self.lookup(i-1)) == self.lookup(i)))]
    #[ensures(result.is_ok() ==> 
        forall(|i: usize| (1 <= i && i < self.len()) ==> {
            let range = self.lookup(i);
            !range.overlaps_with(&elem)
        })
    )]
    pub fn push_unique(&mut self, elem: RangeInclusive<usize>) -> Result<(),usize> {
        match self.elem_overlaps_in_list(elem, 0) {
            Some(idx) => Err(idx),
            None => {
                let new_node = Box::new(Node {
                    elem: elem,
                    next: replace(&mut self.head, Link::Empty)
                });
                self.head = Link::More(new_node);
                Ok(())
            }
        }
    }

    #[requires(forall(|i: usize, j: usize| (0 <= i && i < self.len() && 0 <= j && j < self.len()) ==> 
        (i != j ==> !self.lookup(i).overlaps_with(&self.lookup(j))))
    )]
    #[ensures(result.is_ok() ==> self.len() == old(self.len()) + 1)] 
    #[ensures(result.is_ok() ==> self.lookup(0) == elem)]
    #[ensures(result.is_ok() ==> forall(|i: usize| (1 <= i && i < self.len()) ==> old(self.lookup(i-1)) == self.lookup(i)))]
    // #[ensures(result.is_ok() ==> 
    //     forall(|i: usize| (1 <= i && i < self.len()) ==> {
    //         let range = self.lookup(i);
    //         !range.overlaps_with(&elem)
    //     })
    // )]
    #[ensures(forall(|i: usize, j: usize| (0 <= i && i < self.len() && 0 <= j && j < self.len()) ==> 
        (i != j ==> !self.lookup(i).overlaps_with(&self.lookup(j))))
    )]
    pub fn push_unique2(&mut self, elem: RangeInclusive<usize>) -> Result<(),usize> {
        match self.elem_overlaps_in_list(elem, 0) {
            Some(idx) => Err(idx),
            None => {
                let new_node = Box::new(Node {
                    elem: elem,
                    next: replace(&mut self.head, Link::Empty)
                });
                self.head = Link::More(new_node);
                Ok(())
            }
        }
    }

    /// Removes element at index 0 from the list
    /// Ensures that:
    /// * if the list is empty, returns None.
    /// * if the list is not empty, returns Some().
    /// * if the list is empty, the length remains 0.
    /// * if the list is not empty, new_length = old_length - 1
    /// * if the list is not empty, the returned element was previously at index 0
    /// * if the list is not empty, all elements in the old list at index [1..] are still in the list, except at one index less.
    // #[cfg_attr(feature="prusti", ensures(old(self.len()) == 0 ==> result.is_none()))]
    // #[cfg_attr(feature="prusti", ensures(old(self.len()) > 0 ==> result.is_some()))]
    // #[cfg_attr(feature="prusti", ensures(old(self.len()) == 0 ==> self.len() == 0))]
    // #[cfg_attr(feature="prusti", ensures(old(self.len()) > 0 ==> self.len() == old(self.len()-1)))]
    // #[cfg_attr(feature="prusti", ensures(old(self.len()) > 0 ==> peek_range(&result) == old(self.lookup(0))))]
    // #[cfg_attr(feature="prusti", ensures(old(self.len()) > 0 ==>
    // forall(|i: usize| (0 <= i && i < self.len()) ==>
    //     old(self.lookup(i+1)) == self.lookup(i))))]
    #[ensures(old(self.len()) == 0 ==> result.is_none())]
    #[ensures(old(self.len()) > 0 ==> result.is_some())]
    #[ensures(old(self.len()) == 0 ==> self.len() == 0)]
    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()-1))]
    #[ensures(old(self.len()) > 0 ==> *peek_option_ref(&result) == old(self.lookup(0)))]
    #[ensures(old(self.len()) > 0 ==>
        forall(|i: usize| (0 <= i && i < self.len()) ==> old(self.lookup(i+1)) == self.lookup(i))
    )]
    pub fn pop(&mut self) -> Option<RangeInclusive<usize>> {
        match replace(&mut self.head, Link::Empty) {
            Link::Empty => {
                None
            }
            Link::More(node) => {
                self.head = node.next;
                Some(node.elem)
            }
        }
    }


    // /// Returns true if `elem` overlaps with any range in the list that starts at `link`
    // // #[cfg_attr(feature="prusti", pure)]
    // #[pure]
    // pub(crate) fn overlaps(link: &Link<T>, elem: T) -> bool {
    //     let ret = match link {
    //         Link::Empty => false,
    //         Link::More(box node) => {
    //             if node.elem.overlaps_with(&elem) {
    //                 true
    //             } else {
    //                 false || Self::overlaps(&node.next, elem)
    //             }
    //         }
    //     };
    //     ret
    // }



    /// Returns the index of the first element in the list which overlaps with `elem`.
    /// Returns None if there is no overlap.
    /// 
    /// Requires that the index lies with in range.
    /// 
    /// Ensures that:
    /// * if the result is Some(idx), then idx lies within the list's length.
    /// * if the result is Some(idx), then the element at idx overlaps with `elem`
    /// * if the result is None, then no element in the lists overlaps with `elem`
    /// 
    /// # Warning
    /// Only returns an accurate index if argument `index` is 0
    // #[cfg_attr(feature="prusti", pure)]
    // #[cfg_attr(feature="prusti", requires(0 <= index && index <= self.len()))]
    // #[cfg_attr(feature="prusti", ensures(result.is_some() ==> peek_usize(&result) < self.len()))]
    // #[cfg_attr(feature="prusti", ensures(result.is_some() ==> {
    //         let idx = peek_usize(&result);
    //         let range = self.lookup(idx);
    //         ((range.end >= elem.start) && (range.start <= elem.end)) 
    //         || 
    //         ((elem.end >= range.start) && (elem.start <= range.end))
    //     }
    // ))]
    // #[cfg_attr(feature="prusti", ensures(result.is_none() ==> 
    //     forall(|i: usize| (index <= i && i < self.len()) ==> {
    //         let range = self.lookup(i);
    //         !(((range.end >= elem.start) && (range.start <= elem.end)) 
    //         || 
    //         ((elem.end >= range.start) && (elem.start <= range.end)))
    //     })
    // ))]
    // #[pure]
    #[requires(0 <= index && index <= self.len())]
    #[ensures(result.is_some() ==> peek_option(&result) < self.len())]
    #[ensures(result.is_some() ==> {
            let idx = peek_option(&result);
            let range = self.lookup(idx);
            range.overlaps_with(&elem)
        }
    )]
    #[ensures(result.is_none() ==> 
        forall(|i: usize| (index <= i && i < self.len()) ==> {
            let range = self.lookup(i);
            !range.overlaps_with(&elem)
        })
    )]
    pub(crate) fn elem_overlaps_in_list(&self, elem: RangeInclusive<usize>, index: usize) -> Option<usize> {
        if index >= self.len() {
            return None;
        }
        let ret = if self.lookup(index).overlaps_with(&elem) {
            Some(index)
        } else {
            self.elem_overlaps_in_list(elem, index + 1)
        };
        ret
    }

}

impl Link {

    // #[cfg_attr(feature="prusti", pure)]
    // #[cfg_attr(feature="prusti", ensures(self.is_empty() ==> result == 0))]
    // #[cfg_attr(feature="prusti", ensures(!self.is_empty() ==> result > 0))]
    #[pure]
    #[ensures(self.is_empty() ==> result == 0)]
    #[ensures(!self.is_empty() ==> result > 0)]
    fn len(&self) -> usize {
        match self {
            Link::Empty => 0,
            Link::More(box node) => 1 + node.next.len(),
        }
    }

    // #[cfg_attr(feature="prusti", pure)]
    #[pure]
    fn is_empty(&self) -> bool {
        match self {
            Link::Empty => true,
            Link::More(box node) => false,
        }
    }

    // #[cfg_attr(feature="prusti", pure)]
    // #[cfg_attr(feature="prusti", requires(0 <= index && index < self.len()))]
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> RangeInclusive<usize> {
        match self {
            Link::Empty => unreachable!(),
            Link::More(box node) => {
                if index == 0 {
                    node.elem
                } else {
                    node.next.lookup(index - 1)
                }
            }
        }
    }

}