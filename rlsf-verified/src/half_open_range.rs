use vstd::prelude::*;
use vstd::{seq::*, seq_lib::*};
use vstd::set_lib::set_int_range;
use vstd::set::Set;

verus! {

/// Type for left half-open range
pub struct HalfOpenRange;

impl HalfOpenRange {
    /// Forbiding invalid construction of half-open range which start point is bigger than end. e.g. ]123, -42)
    pub closed spec fn new(start: int, size: nat) -> Self;

    pub spec fn start(self) -> int;

    pub spec fn end(self) -> int;

    pub closed spec fn to_set(self) -> Set<int> {
        set_int_range(self.start(), self.end())
    }

    pub open spec fn disjoint(self, rhs: Self) -> bool {
            self.end() <= rhs.start() || rhs.end() <= self.start() 
    }

    pub open spec fn contains(self, e: int) -> bool {
        self.start() <= e < self.end()
    }

    pub proof fn lemma_disjoint_hor_disjoint_set(r1: Self, r2: Self)
        ensures
            r1.disjoint(r2) <==> r1.to_set().disjoint(r2.to_set())
    {}

    // order on disjoint ranges
    pub open spec fn lt(r1: Self, r2: Self) -> bool
        recommends r1.disjoint(r2)
    {
        r1.end() <= r2.start()
    }

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
}
