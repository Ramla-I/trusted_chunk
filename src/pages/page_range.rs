use prusti_contracts::*;

#[cfg(prusti)]
use crate::external_spec::trusted_range_inclusive::*;
#[cfg(not(prusti))]
use range_inclusive::*;


use core::char::MAX;
use core::ops::{Deref, DerefMut, Add, Sub};
use core::cmp::{PartialOrd, Ord, Ordering};
use crate::{
    *,
    external_spec::{trusted_option::*, trusted_result::*},
};

pub(crate) const MAX_VIRTUAL_ADDRESS: usize = usize::MAX;
pub(crate) const PAGE_SIZE: usize = 4096;

// //Prusti error: Unsupported constant type
// pub(crate) const MIN_PAGE: Page = Page { number: 0 };
// //Prusti error: Unsupported constant type
// pub(crate) const MAX_PAGE: Page = Page { number: 0xFF_FFFF_FFFF }; 

pub(crate) const MIN_PAGE_NUMBER: usize = 0;
pub(crate) const MAX_PAGE_NUMBER: usize = 0xF_FFFF_FFFF_FFFF; // usize::MAX | 0xFFFF_0000_0000_0000 / PAGE_SIZE

#[pure]
fn min(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

#[pure]
fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}

#[pure]
fn min_page(a: Page, b: Page) -> Page {
    if a.less_than(&b) { a } else { b }
}

#[pure]
fn max_page(a: Page, b: Page) -> Page {
    if a.greater_than(&b) { a } else { b }
}

#[pure]
#[trusted]
#[ensures(usize::MAX - a < b ==> result == usize::MAX)]
#[ensures(usize::MAX - a > b ==> result == a + b)]
#[ensures(usize::MAX - a == b ==> result == a + b)]
#[ensures(usize::MAX - a == b ==> result == usize::MAX)]
fn saturating_add(a: usize, b: usize) -> usize {
     a.saturating_add(b)
}

#[pure]
#[trusted]
#[ensures(a < b ==> result == 0)]
#[ensures(a >= b ==> result == a - b)]
#[ensures(a == b ==> result == 0)]
fn saturating_sub(a: usize, b: usize) -> usize {
     a.saturating_sub(b)
}


#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
// #[cfg_attr(not(prusti), derive(Debug))]
pub struct Page{
    number: usize
}

impl Deref for Page {
    type Target = usize;
    #[pure]
    fn deref(&self) -> &Self::Target {
        &self.number
    }
}

#[extern_spec]
impl PartialEq for Page {
    #[pure]
    #[ensures(result == (self.number == other.number))]
    fn eq(&self, other: &Self) -> bool;
}

// #[extern_spec]
// impl PartialOrd for usize {
//     #[pure]
//     fn partial_cmp(&self, other: &Self) -> Option<Ordering>;
// }

#[extern_spec]
impl PartialOrd for Page {
    #[pure]
    #[ensures(result == self.number.partial_cmp(&other.number))]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering>;

    // Uncommenting these leads to an unexpected panic in Prusti
    // but without these can't use comparison operators for pages in pure functions.
    
    // #[pure]
    // #[ensures(result == (self.number < other.number))]
    // fn lt(&self, other: &Self) -> bool;

    // #[pure]
    // #[ensures(result == (self.number <= other.number))]
    // fn le(&self, other: &Self) -> bool;
    
    // #[pure]
    // #[ensures(result == (self.number > other.number))]
    // fn gt(&self, other: &Self) -> bool;
    
    // #[pure]
    // #[ensures(result == (self.number >= other.number))]
    // fn ge(&self, other: &Self) -> bool;
}

impl Add<usize> for Page {
    type Output = Page;
    fn add(self, rhs: usize) -> Page {
        Page {
            number: min(MAX_PAGE_NUMBER, self.number.saturating_add(rhs)),
        }
    }
}

impl Sub<usize> for Page {
    type Output = Page;
    fn sub(self, rhs: usize) -> Page {
        Page {
            number: self.number.saturating_sub(rhs),
        }
    }
}

impl Page {
    #[pure]
    pub const fn number(&self) -> usize {
        self.number
    }
}

// The newly added methods for Page required for verification
impl Page {
    #[pure]
    #[trusted]
    #[ensures(result.number == min(MAX_PAGE_NUMBER, saturating_add(self.number, rhs)))]
    #[ensures(result.greater_than_equal(&self))]
    #[ensures(rhs == 0 ==> result == self)]
    pub fn plus(self, rhs: usize) -> Self {
        self + rhs
    }

    #[pure]
    #[trusted]
    #[ensures(result.number == saturating_sub(self.number, rhs))]
    #[ensures(result.less_than_equal(&self))]
    #[ensures(rhs == 0 ==> result == self)]
    pub fn minus(self, rhs: usize) -> Self {
        self - rhs
    }

    #[pure]
    #[trusted]
    #[ensures(result == (self.number < rhs.number))]
    #[ensures(!result ==> self.greater_than_equal(&rhs))]
    pub fn less_than(self, rhs: &Self) -> bool {
        self < *rhs
    }

    #[pure]
    #[trusted]
    #[ensures(result == (self.number <= rhs.number))]
    #[ensures(!result ==> self.greater_than(&rhs))]
    pub fn less_than_equal(self, rhs: &Self) -> bool {
        self <= *rhs
    }

    #[pure]
    #[trusted]
    #[ensures(result == (self.number > rhs.number))]
    #[ensures(!result ==> self.less_than_equal(&rhs))]
    pub fn greater_than(self, rhs: &Self) -> bool {
        self > *rhs
    }

    #[pure]
    #[trusted]
    #[ensures(result == (self.number >= rhs.number))]
    #[ensures(!result ==> self.less_than(&rhs))]
    pub fn greater_than_equal(self, rhs: &Self) -> bool {
        self >= *rhs
    }
}


/// A struct representing an unallocated region in memory.
/// Its functions are formally verified to prevent range overlaps between chunks.
// #[cfg_attr(not(prusti), derive(Debug))]
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct PageRange(RangeInclusive<Page>);

impl PageRange {
    #[ensures(result.start_page() == start)]
    #[ensures(result.end_page() == end)]
    pub const fn new(start: Page, end: Page) -> PageRange {
        PageRange(RangeInclusive::new(start, end))
    }

    #[ensures(result.is_empty())]
    pub const fn empty() -> PageRange {
        PageRange( RangeInclusive::new(Page{ number: 1 }, Page{ number: 0 }) )
    }
}

// The newly added methods for PageRange required for verification
impl PageRange {
    #[pure]
    #[trusted]
    #[ensures(result == *self.0.start())]
    pub fn start_page(&self) -> Page {
        *self.0.start()
    }

    #[pure]
    #[trusted]
    #[ensures(result == *self.0.end())]
    pub fn end_page(&self) -> Page {
        *self.0.end()
    }

    #[pure]
    #[ensures(result == (self.start_page().greater_than(&self.end_page())))]
    #[ensures(result == !(self.start_page().less_than_equal(&self.end_page())))]
    pub fn is_empty(&self) -> bool {
        !(self.start_page().less_than_equal(&self.end_page()))
    }

    #[pure]
    #[trusted] // has to be trusted to call itself, which then requires us to define a spec for the fn as well :(
    #[ensures(result == other.range_overlaps(&self))] // if we dont have this condition, then post-condition of push_unique_with_precond wont' verify
    #[ensures({
        let starts = max_page(self.start_page(), other.start_page());
        let ends   = min_page(self.end_page(), other.end_page());
        result == starts.less_than_equal(&ends) 
   })]
    /// Returning a PageRange here requires use to set the RangeInclusive new function as pure which
    /// requires Idx to be Copy, so just return bool.
    pub fn range_overlaps(&self, other: &PageRange) -> bool {
        let starts = max_page(self.start_page(), other.start_page());
        let ends   = min_page(self.end_page(), other.end_page());
        starts.less_than_equal(&ends)
    }

    #[pure]
    pub fn contains_range(&self, other: &PageRange) -> bool {
        !other.is_empty()
        && (other.start_page().greater_than_equal(&self.start_page()))
        && (other.end_page().less_than_equal(&self.end_page()))
    }

    /// Splits a range into 1-3 ranges, depending on where the split is at.
    /// It is formally verified that the resulting chunks are disjoint, contiguous and their start/end is equal to that of the original chunk.
    /// 
    /// # Post-conditions:
    /// * If it succeeds, then the resulting chunks have no overlapping ranges
    /// * If it succeeds, then the resulting chunks are contiguous
    /// * If it succeeds, then the resulting chunks combined have the same range as `self`
    /// * If it fails, then the original chunk is returned
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        ((split_range.0).is_some() ==> !peek_option_ref(&split_range.0).range_overlaps(&split_range.1)) 
        && ((split_range.2).is_some() ==> !split_range.1.range_overlaps(peek_option_ref(&split_range.2)))
        && (((split_range.0).is_some() && (split_range.2).is_some()) ==> !peek_option_ref(&split_range.0).range_overlaps(peek_option_ref(&split_range.2)))
    })]
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        ((split_range.0).is_some() ==> peek_option_ref(&split_range.0).end_page() == split_range.1.start_page().minus(1))
        && ((split_range.2).is_some() ==> peek_option_ref(&split_range.2).start_page() == split_range.1.end_page().plus(1))
    })]
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        ((split_range.0).is_some() ==> peek_option_ref(&split_range.0).start_page() == self.start_page())
        && ((split_range.0).is_none() ==> (split_range.1.start_page() == self.start_page() || (split_range.1.start_page().number == MIN_PAGE_NUMBER)))
        && ((split_range.2).is_some() ==> peek_option_ref(&split_range.2).end_page() == self.end_page())
        && ((split_range.2).is_none() ==> ((split_range.1.end_page() == self.end_page()) || (split_range.1.end_page().number == MAX_PAGE_NUMBER)))
    })]
    #[ensures(result.is_err() ==> {
        let orig_range = peek_err_ref(&result);
        (orig_range.start_page() == self.start_page()) && (orig_range.end_page() == self.end_page())
    })]
    pub fn split_range(self, pages_to_extract: PageRange) -> Result<(Option<PageRange>, PageRange, Option<PageRange>), PageRange> {
        let min_page = Page { number: MIN_PAGE_NUMBER };
        let max_page = Page { number: MAX_PAGE_NUMBER };

        if !self.contains_range(&pages_to_extract) {
            return Err(self);
        }

        let start_page = pages_to_extract.start_page();
        let end_page = pages_to_extract.end_page();

        let before_start = if start_page == min_page || start_page == self.start_page() {
            None
        } else {
            Some(PageRange::new(self.start_page(), start_page.minus(1)))
        };

        let start_to_end = pages_to_extract;

        let after_end = if end_page == max_page || end_page == self.end_page() {
            None
        } else {
            Some(PageRange::new(end_page.plus(1), self.end_page())) 
        };

        Ok((before_start, start_to_end, after_end))
    }


    /// Splits a chunk into 2 chunks at the page with number `at_page`.
    /// It is formally verified that the resulting chunks are disjoint, contiguous and their start/end is equal to that of the original chunk.
    /// 
    /// # Post-conditions:
    /// * If it succeeds, then both chunks can't be empty
    /// * If it succeeds and the first chunk is empty, then the second chunk is equal to `self`
    /// * If it succeeds and the second chunk is empty, then the first chunk is equal to `self`
    /// * If it succeeds and both chunks aren't empty, then the chunks are contiguous and their combined range is equal to the range of `self`
    /// * If it fails, then the original chunk is returned
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        split_range.0.is_empty() && !split_range.1.is_empty() ||
        !split_range.0.is_empty() && split_range.1.is_empty() ||
        !split_range.0.is_empty() && !split_range.1.is_empty()
    })]
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        split_range.0.is_empty() ==> (split_range.1.start_page() == self.start_page() && split_range.1.end_page() == self.end_page())
    })]
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        split_range.1.is_empty() ==> (split_range.0.start_page() == self.start_page() && split_range.0.end_page() == self.end_page())
    })]
    #[ensures(result.is_ok() ==> {
        let split_range = peek_result_ref(&result);
        (!split_range.0.is_empty() && !split_range.1.is_empty()) ==> (
            split_range.0.start_page() == self.start_page() 
            && split_range.0.end_page() == at_page.minus(1) 
            && split_range.1.start_page() == at_page 
            && split_range.1.end_page() == self.end_page()
        )
    })]
    #[ensures(result.is_err() ==> {
        let orig_chunk = peek_err_ref(&result);
        (orig_chunk.start_page() == self.start_page()) && (orig_chunk.end_page() == self.end_page())
    })]
    pub fn split_at(mut self, at_page: Page) -> Result<(Self, Self), Self> {
        if self.is_empty() {
            return Err(self);
        }
        let end_of_first = at_page.minus(1);

        let (first, second) = if at_page == self.start_page() && at_page.less_than_equal(&self.end_page()) {
            let first  = PageRange::empty();
            let second = PageRange::new(at_page, self.end_page());
            (first, second)
        } 
        else if at_page == self.end_page().plus(1) && end_of_first.greater_than_equal(&self.start_page()) {
            let first  = PageRange::new(self.start_page(), self.end_page()); 
            let second = PageRange::empty();
            (first, second)
        }
        else if at_page.greater_than(&self.start_page()) && end_of_first.less_than_equal(&self.end_page()) {
            let first  = PageRange::new(self.start_page(), end_of_first);
            let second = PageRange::new(at_page, self.end_page());
            (first, second)
        }
        else {
            return Err(self);
        };
 
        Ok(( first, second ))
    }


    /// Merges `other` into `self`.
    /// Succeeds if `other` lies right before `self` or right after.
    /// 
    /// # Post-conditions:
    /// * If it succeeds, then `other` and `self` were contiguous, and either `self`'s start bound has been updated to `other`'s start 
    /// or `self`s end has been updated to `other`'s end
    /// * If it fails, then `self` remains unchanged and `other` is returned
    #[ensures(result.is_ok() ==> 
        (old(self.start_page()) == other.end_page().plus(1) && self.start_page() == other.start_page() && self.end_page() == old(self.end_page())) 
        || 
        (old(self.end_page()).plus(1) == other.start_page() && self.end_page() == other.end_page() && self.start_page() == old(self.start_page()))
    )]
    #[ensures(result.is_err() ==> {
        let chunk = peek_err_ref(&result);
        (chunk.start_page() == other.start_page()) && (chunk.end_page() == other.end_page()) 
    })]
    #[ensures(result.is_err() ==> {
        (self.start_page() == old(self.start_page())) && (self.end_page() == old(self.end_page())) 
    })]
    pub fn merge(&mut self, other: Self) -> Result<(), Self> {
        if self.is_empty() || other.is_empty() {
            return Err(other);
        }

        if self.start_page() == other.end_page().plus(1) {
            // `other` comes contiguously before `self`
            *self = PageRange::new(other.start_page(), self.end_page());
        } 
        else if self.end_page().plus(1) == other.start_page() {
            // `self` comes contiguously before `other`
            *self = PageRange::new(self.start_page(), other.end_page());
        }
        else {
            // non-contiguous
            return Err(other);
        } 
        Ok(())
    }
}


impl Deref for PageRange {
    type Target = RangeInclusive<Page>;
    #[pure]
    fn deref(&self) -> &RangeInclusive<Page> {
        &self.0
    }
}
