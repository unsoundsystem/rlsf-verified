use vstd::prelude::*;
use vstd::{seq::*, seq_lib::*};
use vstd::set_lib::set_int_range;
use vstd::set::Set;
use vstd::calc;

verus! {

proof fn empty_set_not_contains<T>(s: Set<T>)
    requires forall|e: T| !s.contains(e)
    ensures s.is_empty()
{
    if !s.is_empty() {
        assert(s.len() != 0);
        assert(s.contains(s.choose()));
    }
    assert(!s.is_empty() ==> exists|e: T| s.contains(e));
}


pub struct HalfOpenRange(int, int);

impl HalfOpenRange {
    #[verifier::type_invariant]
    pub open spec fn wf(self) -> bool {
        self.start() < self.end()
    }


    pub closed spec fn new(start: int, size: int) -> Self
        recommends size >= 0
    {
        HalfOpenRange(start, start + size)
    }

    pub open spec fn contains(self, e: int) -> bool
        recommends self.wf()
    {
        self.start() <= e < self.end()
    }

    pub closed spec fn start(self) -> int {
        self.0
    }

    pub closed spec fn end(self) -> int {
        self.1
    }

    pub proof fn lemma_new_wf()
        ensures forall|x: int, y: int| y >= 0 ==> HalfOpenRange::new(x, y).wf()
    {}

    pub proof fn lemma_new_start()
        ensures forall|x: int, y: int| HalfOpenRange::new(x, y).start() == x
    {}

    pub proof fn lemma_new_end()
        ensures forall|x: int, y: int| HalfOpenRange::new(x, y).end() == x + y
    {}


    pub open spec fn is_empty(self) -> bool
        recommends self.wf()
    {
        self.start() == self.end()
    }


    pub open spec fn disjoint(self, rhs: Self) -> bool
        recommends self.wf(), rhs.wf()
    {
        if self.is_empty() || rhs.is_empty() {
            true
            // NOTE: following conditions for disjoint ranges not applies to empty ranges
            //        e.g. [a, a( ⊥  [b, c( where b ≤  a ∧  a < c
        } else {
            &&& self.wf()
            &&& rhs.wf()
            &&& self.end() <= rhs.start() || rhs.end() <= self.start()
        }
    }

    pub proof fn lemma_is_empty_wf()
        ensures forall|r: Self| r.is_empty() ==> r.wf()
    {}


    pub open spec fn to_set(self) -> Set<int>
        recommends self.wf()
    {
        Set::new(|p: int| self.start() <= p < self.end())
    }

    pub open spec fn lt(self, rhs: Self) -> bool {
        &&& self.wf()
        &&& self.end() <= self.start()
    }
}
}
