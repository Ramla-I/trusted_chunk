use prusti_contracts::*;
use crate::{
    trusted_option::*,
    trusted_range_inclusive::*
};
use core::{
    mem,
};


pub struct List {
    head: Link,
}

enum Link {
    Empty,
    More(Box<Node>),
}

struct Node {
    elem: TrustedRangeInclusive,
    next: Link,
}

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

    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> TrustedRangeInclusive {
        self.head.lookup(index)
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List {
            head: Link::Empty
        }
    }

    // #[requires(self.len() < usize::MAX)]
    #[ensures(self.len() == old(self.len()) + 1)] 
    #[ensures(self.lookup(0) == elem)]
    #[ensures(forall(|i: usize| (1 <= i && i < self.len()) ==>
        old(self.lookup(i-1)) == self.lookup(i)))]
    pub fn push(&mut self, elem: TrustedRangeInclusive) {
        let new_node = Box::new(Node {
            elem: elem,
            next: replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }

    #[ensures(old(self.len()) == 0 ==> result.is_none())]
    #[ensures(old(self.len()) > 0 ==> result.is_some())]
    #[ensures(old(self.len()) == 0 ==> self.len() == 0)]
    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()-1))]
    #[ensures(old(self.len()) > 0 ==> peek_range(&result) == old(self.lookup(0)))]
    #[ensures(old(self.len()) > 0 ==>
    forall(|i: usize| (0 <= i && i < self.len()) ==>
        old(self.lookup(i+1)) == self.lookup(i)))]
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

    #[pure]
    fn overlap(link: &Link, elem: TrustedRangeInclusive) -> bool {
        let ret = match link {
            Link::Empty => false,
            Link::More(box node) => {
                if node.elem.overlap(&elem) {
                    true
                } else {
                    false || Self::overlap(&node.next, elem)
                }
            }
        };
        ret
    }

    #[pure]
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

    #[pure]
    #[requires(0 <= index && index <= self.len())]
    #[ensures(result.is_some() ==> peek_usize(&result) < self.len())]
    #[ensures(result.is_some() ==> {
            let idx = peek_usize(&result);
            let range = self.lookup(idx);
            (range.end > elem.start) || (elem.end > range.start)
        }
    )]
    #[ensures(result.is_none() ==> 
        forall(|i: usize| (index <= i && i < self.len()) ==> {
            let range = self.lookup(i);
            !(range.end > elem.start) && !(elem.end > range.start)
        })
    )]
    fn range_overlaps_in_list(&self, elem: TrustedRangeInclusive, index: usize) -> Option<usize> {
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

    #[pure]
    #[ensures(self.is_empty() ==> result == 0)]
    #[ensures(!self.is_empty() ==> result > 0)]
    fn len(&self) -> usize {
        match self {
            Link::Empty => 0,
            Link::More(box node) => 1 + node.next.len(),
        }
    }

    #[pure]
    fn is_empty(&self) -> bool {
        match self {
            Link::Empty => true,
            Link::More(box node) => false,
        }
    }

    #[pure]
    #[requires(0 <= index && index < self.len())]
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