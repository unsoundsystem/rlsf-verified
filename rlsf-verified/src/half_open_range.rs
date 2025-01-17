use vstd::prelude::*;
use vstd::{seq::*, seq_lib::*};
use vstd::set_lib::set_int_range;
use vstd::set::Set;
use crate::rational_numbers::Rational;

verus! {

/// Type for left half-open range
pub struct HalfOpenRange;

impl HalfOpenRange {
    /// Forbiding invalid construction of half-open range which start point is bigger than end. e.g. ]123, -42)
    pub closed spec fn new(start: int, size: nat) -> Self;

    pub spec fn start(self) -> int;

    pub spec fn end(self) -> int;

    pub open spec fn disjoint(self, rhs: Self) -> bool {
            self.end() <= rhs.start() || rhs.end() <= self.start() 
    }

    pub open spec fn contains(self, e: int) -> bool {
        self.start() <= e < self.end()
    }

    /// Compatibility with Set

    pub closed spec fn to_set(self) -> Set<int> {
        set_int_range(self.start(), self.end())
    }

    pub proof fn lemma_disjoint_hor_disjoint_set(r1: Self, r2: Self)
        ensures
            r1.disjoint(r2) <==> r1.to_set().disjoint(r2.to_set())
    {}

    pub proof fn lemma_hor_set_equiv(r: Self, e: int)
        ensures r.to_set().contains(e) <==> r.contains(e)
    {}
}

pub broadcast proof fn axiom_start_lte_end(r: HalfOpenRange)
    ensures r.start() <= r.end()
{ admit() }

pub broadcast proof fn axiom_new_range(start: int, size: nat)
    ensures
        HalfOpenRange::new(start, size).start() == start,
        HalfOpenRange::new(start, size).end() == start + size as int
{}


/// Type for left half-open range on Q
pub struct HalfOpenRangeOnRat;

impl HalfOpenRangeOnRat {

    pub spec fn new(start: Rational, size: Rational) -> Self;

    pub spec fn start(self) -> Rational;

    pub spec fn end(self) -> Rational;

    pub open spec fn contains(self, e: Rational) -> bool {
        self.start().lte(e) && e.lt(self.end())
    }

    pub open spec fn disjoint(self, rhs: Self) -> bool {
            self.end().lte(rhs.start()) || rhs.end().lte(self.start())
    }

    /// Compatibility with Set

    pub open spec fn to_set(self) -> Set<Rational> {
        Set::new(|p: Rational| self.start().lte(p) && p.lt(self.end()))
    }

    pub proof fn lemma_disjoint_hor_disjoint_set(r1: Self, r2: Self)
        ensures
            r1.disjoint(r2) <==> r1.to_set().disjoint(r2.to_set())
    {}

    pub proof fn lemma_hor_set_equiv(r: Self, e: Rational)
        ensures r.to_set().contains(e) <==> r.contains(e)
    {}
}

pub broadcast proof fn axiom_horor_start_lte_end(r: HalfOpenRangeOnRat)
    ensures r.start().lte(r.end())
{ admit() }

pub broadcast proof fn axiom_horor_new_range(start: Rational, size: Rational)
    requires Rational::from_int(0).lt(size)
    ensures
        HalfOpenRangeOnRat::new(start, size).start() == start,
        HalfOpenRangeOnRat::new(start, size).end() == start.add(size)
{}


}
