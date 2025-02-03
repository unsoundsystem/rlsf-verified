use vstd::prelude::*;
use vstd::{seq::*, seq_lib::*};
use vstd::set_lib::set_int_range;
use vstd::set::Set;
use crate::rational_numbers::{
    Rational, lemma_from_int_adequate,
    lemma_add_zero, lemma_lt_lte_trans, lemma_lte_trans, lemma_rat_range_split,
    rational_number_facts, lemma_lte_nonneg_add, lemma_hor_empty, lemma_lt_eq_equiv,
    lemma_add_eq_zero,
};

verus! {
/// Type for left half-open range on Q
pub struct HalfOpenRangeOnRat(Rational, Rational);

impl HalfOpenRangeOnRat {
    #[verifier::type_invariant]
    pub open spec fn wf(self) -> bool {
        self.start().lte(self.end())
    }
    pub closed spec fn new(start: Rational, size: Rational) -> Self
        recommends size.is_nonneg()
    {
        HalfOpenRangeOnRat(start, start.add(size))
    }

    pub closed spec fn start(self) -> Rational {
        self.0
    }

    pub closed spec fn end(self) -> Rational {
        self.1
    }

    pub open spec fn contains(self, e: Rational) -> bool
        recommends self.wf()
    {
        &&& self.start().lte(e)
        &&& e.lt(self.end())
    }


    ///  Interval is disjoint when one of then is empty or they are in the following situation
    ///
    ///  r1      r2
    ///  o-----o o-----o
    ///  "or vice versa"
    ///
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
            &&& self.end().lte(rhs.start()) || rhs.end().lte(self.start())
        }
    }

    pub open spec fn is_empty(self) -> bool
        recommends self.wf()
    {
        self.start().eq(self.end())
    }

    pub proof fn lemma_disjoint_not_contains(r1: Self, r2: Self)
        requires r1.wf(), r2.wf()
        ensures r1.disjoint(r2) <==> forall|e: Rational| r1.contains(e) ==> !r2.contains(e)
    {
        assert forall|e: Rational| r1.disjoint(r2) && r1.contains(e)
            implies !r2.contains(e) by {
            if r1.is_empty() {
                Self::lemma_empty_range_not_contains(r1);
                assert(!r1.contains(e));
                assert(false);
            }
            if r2.is_empty() {
                Self::lemma_empty_range_not_contains(r2);
                assert(!r2.contains(e));
            }
            if r1.end().lte(r2.start()) {
                lemma_lt_lte_trans(e, r1.end(), r2.start());
                assert(e.lt(r2.start()));
                Self::lemma_out_of_range_start(r2, e);
                assert(!r2.contains(e));
            } else if r2.end().lte(r1.start()) {
                assert(r2.end().lte(r1.start()) && r1.start().lte(e));
                lemma_lte_trans(r2.end(), r1.start(), e);
                assert(r2.end().lte(e));
                assert(!r2.contains(e));
            }
        };

        // When the intervals are not disjoint, possible situations are...
        //
        // case 1: "r1.start() <= r2.start()"    
        //     r1:   o-----o        o-----o 
        //     r2:       o-----o      o-o   
        //
        // case 2: "r1.start() >= r2.start()"    
        //     r1:      o-----o      o-o    
        //     r2:   o-----o       o-----o  
        //
        // * in case 1, r2.start() will be the witness.
        // * in case 2, r1.start() will be the witness.
        if !r1.disjoint(r2) {
            if r1.is_empty() || r2.is_empty() {
                assert(r1.disjoint(r2));
                assert(false);
            }

            // case 1:
            if r1.start().lte(r2.start()) {
                assert(r1.contains(r2.start()) && r2.contains(r2.start()))
            }

            // case 2:
            if r2.start().lte(r1.start()) {
                assert(r1.contains(r1.start()) && r2.contains(r1.start()))
            }
        }
        assert(!r1.disjoint(r2) ==>
            exists|x: Rational| (r1.contains(x) && r2.contains(x)));
    }

    pub proof fn lemma_out_of_range_start(r: Self, e: Rational)
        requires r.wf()
        ensures e.lt(r.start()) ==> !r.contains(e)
    {}

    pub proof fn lemma_out_of_range_end(r: Self, e: Rational)
        requires r.wf()
        ensures r.end().lte(e) ==> !r.contains(e)
    {}

    pub proof fn lemma_wf_if_size_is_pos(start: Rational, size: Rational)
        requires size.is_nonneg()
        ensures HalfOpenRangeOnRat::new(start, size).wf()
    {
        broadcast use rational_number_facts;
        lemma_lte_nonneg_add(start, size);
        assert(start.lte(start.add(size)));
    }

    /// Compatibility with Set

    pub open spec fn to_set(self) -> Set<Rational>
        recommends self.wf()
    {
        Set::new(|p: Rational| self.start().lte(p) && p.lt(self.end()))
    }

    pub proof fn lemma_disjoint_hor_disjoint_set(r1: Self, r2: Self)
        requires r1.wf(), r2.wf()
        ensures
            r1.disjoint(r2) <==> r1.to_set().disjoint(r2.to_set())
    {
        assert(r1.disjoint(r2) ==> r1.to_set().disjoint(r2.to_set())) by (nonlinear_arith);
    }

    pub proof fn lemma_hor_set_equiv(r: Self, e: Rational)
        requires r.wf()
        ensures r.to_set().contains(e) <==> r.contains(e)
    {}

    pub proof fn lemma_hor_disjoint(r1: Self, r2: Self)
        requires r1.wf(), r2.wf()
        ensures #[trigger] r1.disjoint(r2) <==>
            forall |e: Rational|
                #[trigger] r1.contains(e) <==> #[trigger] r2.contains(e) == false
    {
        assert(r1.disjoint(r2) <==> forall |e: Rational| #[trigger] r1.contains(e) <==> #[trigger] r2.contains(e) == false);
    }

    pub proof fn lemma_empty_range_disjoint(r1: Self, r2: Self)
        requires r1.is_empty() || r2.is_empty()
        ensures r1.disjoint(r2)
    {
    }

    pub proof fn lemma_empty_range(p: Rational, q: Rational)
        requires q.eq(Rational::zero())
        ensures ({
            let r = HalfOpenRangeOnRat::new(p, q); 
            r.wf() && r.to_set().is_empty()
        })
    {
        broadcast use rational_number_facts;
        let r = HalfOpenRangeOnRat::new(p, q); 
        assert(q.eq(Rational::zero()));
        Self::lemma_wf_if_size_is_pos(p, q);
        
        lemma_add_eq_zero(p, q);
        assert(q.eq(Rational::zero()));
        assert(p.add(q).eq(p));
        assert(r.is_empty());
        Self::lemma_empty_range_empty_set(r);
    }

    pub proof fn lemma_empty_range_empty_set(r: Self)
        requires r.wf(), r.is_empty()
        ensures r.to_set().is_empty()
    {
        assert forall|a: Rational| !(#[trigger] r.to_set().contains(a)) by {
            Self::lemma_empty_range_not_contains(r);
            assert(!r.contains(a));
            Self::lemma_hor_set_equiv(r, a);
        };
        empty_set_not_contains(r.to_set());
    }
    proof fn lemma_empty_range_not_contains(r: Self)
        requires r.wf(), r.is_empty()
        ensures forall|e: Rational| !r.contains(e)
    {
        assert forall|a: Rational| !r.contains(a) by {
            if r.start().lte(a) && a.lt(r.end()) {
                lemma_hor_empty(r.start(), a);
                lemma_lt_eq_equiv(a, r.start(), r.end());
                assert(r.start().eq(r.end()));
                assert(a.lt(r.start()));
                assert(false);
            }
            assert(!r.contains(a));
        }
    }
}

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
}
