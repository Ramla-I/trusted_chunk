#[cfg(feature="prusti")]
use prusti_contracts::*;

use crate::{
    trusted_option::*,
    trusted_range_inclusive::*
};
use core::{
    mem,
};


pub struct List {
    pub(crate) head: Link,
}

pub(crate) enum Link {
    Empty,
    More(Box<Node>),
}

pub(crate) struct Node {
    elem: TrustedRangeInclusive,
    next: Link,
}

#[cfg_attr(feature="prusti", trusted)]
#[cfg_attr(feature="prusti", requires(src.is_empty()))]
#[cfg_attr(feature="prusti", ensures(dest.is_empty()))]
#[cfg_attr(feature="prusti", ensures(old(dest.len()) == result.len()))]
#[cfg_attr(feature="prusti", ensures(forall(|i: usize| (0 <= i && i < result.len()) ==> 
                old(dest.lookup(i)) == result.lookup(i))))] 
fn replace(dest: &mut Link, src: Link) -> Link {
    mem::replace(dest, src)
}


impl List {

    #[cfg_attr(feature="prusti", pure)]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[cfg_attr(feature="prusti", pure)]
    #[cfg_attr(feature="prusti", requires(0 <= index && index < self.len()))]
    pub fn lookup(&self, index: usize) -> TrustedRangeInclusive {
        self.head.lookup(index)
    }

    #[cfg_attr(feature="prusti", ensures(result.len() == 0))]
    pub fn new() -> Self {
        List {
            head: Link::Empty
        }
    }

    // #[requires(self.len() < usize::MAX)]
    #[cfg_attr(feature="prusti", ensures(self.len() == old(self.len()) + 1))] 
    #[cfg_attr(feature="prusti", ensures(self.lookup(0) == elem))]
    #[cfg_attr(feature="prusti", ensures(forall(|i: usize| (1 <= i && i < self.len()) ==>
        old(self.lookup(i-1)) == self.lookup(i))))]
    pub fn push(&mut self, elem: TrustedRangeInclusive) {
        let new_node = Box::new(Node {
            elem: elem,
            next: replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }

    #[cfg_attr(feature="prusti", ensures(old(self.len()) == 0 ==> result.is_none()))]
    #[cfg_attr(feature="prusti", ensures(old(self.len()) > 0 ==> result.is_some()))]
    #[cfg_attr(feature="prusti", ensures(old(self.len()) == 0 ==> self.len() == 0))]
    #[cfg_attr(feature="prusti", ensures(old(self.len()) > 0 ==> self.len() == old(self.len()-1)))]
    #[cfg_attr(feature="prusti", ensures(old(self.len()) > 0 ==> peek_range(&result) == old(self.lookup(0))))]
    #[cfg_attr(feature="prusti", ensures(old(self.len()) > 0 ==>
    forall(|i: usize| (0 <= i && i < self.len()) ==>
        old(self.lookup(i+1)) == self.lookup(i))))]
    pub fn pop(&mut self) -> Option<TrustedRangeInclusive> {
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

    #[cfg_attr(feature="prusti", pure)]
    pub(crate) fn overlaps(link: &Link, elem: TrustedRangeInclusive) -> bool {
        let ret = match link {
            Link::Empty => false,
            Link::More(box node) => {
                if node.elem.overlap(&elem) {
                    true
                } else {
                    false || Self::overlaps(&node.next, elem)
                }
            }
        };
        ret
    }

    #[cfg_attr(feature="prusti", pure)]
    fn overlap_idx(link: &Link, elem: TrustedRangeInclusive, start_idx: usize) -> Option<usize> {
        let ret = match link {
            Link::Empty => None,
            Link::More(box node) => {
                if node.elem.overlap(&elem) {
                    Some(start_idx)
                } else {
                    Self::overlap_idx(&node.next, elem, start_idx + 1)
                }
            }
        };
        ret
    }

    #[cfg_attr(feature="prusti", pure)]
    #[cfg_attr(feature="prusti", requires(0 <= index && index <= self.len()))]
    #[cfg_attr(feature="prusti", ensures(result.is_some() ==> peek_usize(&result) < self.len()))]
    #[cfg_attr(feature="prusti", ensures(result.is_some() ==> {
            let idx = peek_usize(&result);
            let range = self.lookup(idx);
            (range.end > elem.start) || (elem.end > range.start)
        }
    ))]
    #[cfg_attr(feature="prusti", ensures(result.is_none() ==> 
        forall(|i: usize| (index <= i && i < self.len()) ==> {
            let range = self.lookup(i);
            !(range.end > elem.start) && !(elem.end > range.start)
        })
    ))]
    pub(crate) fn range_overlaps_in_list(&self, elem: TrustedRangeInclusive, index: usize) -> Option<usize> {
        if index >= self.len() {
            return None;
        }
        let ret = if self.lookup(index).overlap(&elem) {
            Some(index)
        } else {
            self.range_overlaps_in_list(elem, index + 1)
        };
        ret
    }
}

impl Link {

    #[cfg_attr(feature="prusti", pure)]
    #[cfg_attr(feature="prusti", ensures(self.is_empty() ==> result == 0))]
    #[cfg_attr(feature="prusti", ensures(!self.is_empty() ==> result > 0))]
    fn len(&self) -> usize {
        match self {
            Link::Empty => 0,
            Link::More(box node) => 1 + node.next.len(),
        }
    }

    #[cfg_attr(feature="prusti", pure)]
    fn is_empty(&self) -> bool {
        match self {
            Link::Empty => true,
            Link::More(box node) => false,
        }
    }

    #[cfg_attr(feature="prusti", pure)]
    #[cfg_attr(feature="prusti", requires(0 <= index && index < self.len()))]
    pub fn lookup(&self, index: usize) -> TrustedRangeInclusive {
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