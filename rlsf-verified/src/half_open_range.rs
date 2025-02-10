use vstd::prelude::*;
use vstd::{seq::*, seq_lib::*};
use vstd::set_lib::set_int_range;
use vstd::set::Set;
use crate::rational_numbers::{
    Rational, lemma_from_int_adequate,
    lemma_add_zero, lemma_lt_lte_trans, lemma_lte_trans, lemma_rat_range_split,
    rational_number_facts, lemma_lte_nonneg_add, lemma_hor_empty, lemma_lt_eq_equiv,
    lemma_add_eq_zero, lemma_add_lte_mono, rational_number_add_properties,
    rational_number_inequality, lemma_lte_sym, lemma_lte_eq_between, lemma_eq_trans, lemma_eq_sym,
    rational_number_equality, lemma_add_comm2
};
use vstd::calc;

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

    pub proof fn lemma_disjoint_start_end_eq(r1: Self, r2: Self, start: Rational, end: Rational)
        requires r1.wf(), r2.wf()
        ensures
            r1.end().eq(end) && r2.start().eq(start) && end.lte(start) ==> r1.disjoint(r2),
            r2.end().eq(end) && r1.start().eq(start) && end.lte(start) ==> r1.disjoint(r2)
    {
        if r1.is_empty() || r2.is_empty() {

        } else {
            if r1.end().eq(end) && r2.start().eq(start) && end.lte(start) {
                broadcast use rational_number_facts;
            }
            if r2.end().eq(end) && r1.start().eq(start) && end.lte(start) {
                broadcast use rational_number_facts;
            }
        }
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
        requires r1.wf(), r2.wf(), r1.disjoint(r2)
        ensures
            r1.to_set().disjoint(r2.to_set())
    {
        assert forall|r: Rational|
            r1.to_set().contains(r) implies !r2.to_set().contains(r) by {
                Self::lemma_hor_set_equiv(r1, r);
                Self::lemma_disjoint_not_contains(r1, r2);
        }
    }

    pub proof fn lemma_hor_set_equiv(r: Self, e: Rational)
        requires r.wf()
        ensures r.to_set().contains(e) <==> r.contains(e)
    {}

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

    pub closed spec fn slide(self, delta: Rational) -> Self {
        Self(self.start().add(delta), self.end().add(delta))
    }

    pub proof fn lemma_slide_start(self, delta: Rational)
        ensures self.slide(delta).start().eq(self.start().add(delta))
    {}

    pub proof fn lemma_slide_end(self, delta: Rational)
        ensures self.slide(delta).end().eq(self.end().add(delta))
    {}

    pub proof fn lemma_slide_new_size(start: Rational, size: Rational, delta: Rational) by (nonlinear_arith)
        ensures ({
            let r_slide = Self::new(start, size).slide(delta);
            r_slide.end().eq(r_slide.start().add(size))
        })
    {
        let r = Self::new(start, size);
        let r_slide = r.slide(delta);
        r.lemma_slide_start(delta);
        r.lemma_slide_end(delta);
        assert(r.end() == r.start().add(size));
        assert(r_slide.end().eq(r.end().add(delta)));
        lemma_add_comm2(r.start(), size, delta);
        assert(r_slide.end().eq(r.start().add(size).add(delta)));
        assert(r_slide.end().eq(r.start().add(delta).add(size)));

        assert(r_slide.end().eq(r_slide.start().add(size)));
    }

    pub proof fn lemma_slide_wf(r: Self, p: Rational) by (nonlinear_arith)
        requires r.wf()
        ensures r.slide(p).wf()
    {
        broadcast use rational_number_facts;
        lemma_add_lte_mono(r.start(), r.end(), p);
    }

    proof fn lemma_empty_slide_empty(r: Self, p: Rational) by (nonlinear_arith)
        requires r.is_empty()
        ensures r.slide(p).is_empty()
    {
        broadcast use rational_number_facts;
    }

    pub proof fn lemma_disjoint_add_equiv(r1: Self, r2: Self, delta: Rational) by (nonlinear_arith)
        requires r1.wf(), r2.wf()
        ensures r1.disjoint(r2) <==> r1.slide(delta).disjoint(r2.slide(delta))
    {
        Self::lemma_slide_wf(r1, delta);
        Self::lemma_slide_wf(r2, delta);
        if r1.is_empty() || r2.is_empty() {
            if r1.is_empty() {
                Self::lemma_empty_slide_empty(r1, delta);
                Self::lemma_empty_range_disjoint(r1, r2);
            } else {
                Self::lemma_empty_slide_empty(r2, delta);
                Self::lemma_empty_range_disjoint(r1, r2);
            }
        }
    }

    pub open spec fn subrange_of(self, rhs: Self) -> bool
        recommends self.wf(), rhs.wf()
    {
        rhs.start().lte(self.start()) && self.end().lte(rhs.end())
    }

    proof fn lemma_subrange_of_contains(r1: Self, r2: Self)
        requires r1.wf(), r2.wf(), /*NOTE*/ !r1.is_empty()
        ensures r1.subrange_of(r2) <==>
            forall|r: Rational| r1.contains(r) ==> r2.contains(r)
    {
        // ==>
        if r1.subrange_of(r2) {
            assert forall|r: Rational| r1.contains(r) implies r2.contains(r) by {
                assert(r1.start().lte(r) && r2.start().lte(r1.start()));
                assert(r.lt(r1.end()) && r1.end().lte(r2.end()));
                lemma_lte_trans(r2.start(), r1.start(), r);
                lemma_lt_lte_trans(r, r1.end(), r2.end());
                assert(r2.start().lte(r) && r.lt(r2.end()));
            }
        }

        // <==
        if !r1.subrange_of(r2) {
            // i.e. r1.start().lt(r2.start()) || r2.end().lt(r1.end())
            // we have witness `r` for each situations
            //
            // case 1: r1.start() <  r2.start()
            // r1: o-------------------o      o----------o          o--------o
            // r2:      o--------o               o------------o                o--------o
            // witness: e.g. r1.start()
            //
            // case 2: r2.end() < r1.end()
            // r1: o-------------------o         o------------o                o--------o
            // r2:      o--------o            o----------o          o--------o
            // witness: e.g. r2.end()
            //
            // case 3: empty ranges
            // NOTE: left is the reason of forbidding r1 to be empty range
            // r1: o             o             o-------o
            // r2:    o-------o            o               o
            // witness: (right) r1.start()
            //

            if r2.is_empty() {
                Self::lemma_empty_range_not_contains(r2);
                assert(r1.contains(r1.start()) && !r2.contains(r1.start()));
            }

            if r1.disjoint(r2) {
                Self::lemma_disjoint_not_contains(r1, r2);
                assert(r1.contains(r1.start()) && !r2.contains(r1.start()));
            } else if r1.start().lt(r2.start()) {
                lemma_lte_sym(r1.start(), r1.start());
                assert(r1.start().lte(r1.start()));
                assert(r1.contains(r1.start()));
                assert(r1.contains(r1.start()) && !r2.contains(r1.start()));
            } else if r2.end().lt(r1.end()) {
                assert(r1.start().lte(r2.end()) && r2.end().lt(r1.end()));
                assert(r1.contains(r2.end()) && !r2.contains(r2.end()));
            }

            assert(exists|r: Rational| r1.contains(r) && !r2.contains(r));
        }

        assert(!r1.subrange_of(r2) ==> exists|r: Rational| r1.contains(r) && !r2.contains(r));
    }

    proof fn lemma_superrange_disjoint_subrange_disjoint(r1: Self, r2: Self, r3: Self, r4: Self)
        requires
            r1.wf(), r2.wf(), r3.wf(), r4.wf(),
            r1.subrange_of(r2), r3.subrange_of(r4)
        ensures r2.disjoint(r4) ==> r1.disjoint(r3)
    {
        if r2.is_empty() || r4.is_empty() {
            if r2.is_empty() {
                Self::lemma_subrange_of_empty(r1, r2);
                assert(r1.disjoint(r3))
            } else {
                Self::lemma_subrange_of_empty(r3, r4);
                assert(r1.disjoint(r3))
            }
        }
        // r1:    o---o       r3:     o---o
        // r2: o----------o   r4: o------------o
        if r2.disjoint(r4) {
            if r2.end().lte(r4.start()) {
                assert(r1.end().lte(r2.end()));
                assert(r4.start().lte(r3.start()));
                lemma_lte_trans(r1.end(), r2.end(), r4.start());
                lemma_lte_trans(r1.end(), r4.start(), r3.start());
                assert(r1.end().lte(r3.start()));
            }

            if r4.end().lte(r2.start()) {
                assert(r3.end().lte(r4.end()));
                assert(r2.start().lte(r1.start()));
                lemma_lte_trans(r3.end(), r4.end(), r2.start());
                lemma_lte_trans(r3.end(), r2.start(), r1.start());
                assert(r3.end().lte(r1.start()));
            }
        }
    }

    proof fn lemma_subrange_of_empty(r1: Self, r2: Self)
        requires r1.wf(), r2.wf(), r2.is_empty(), r1.subrange_of(r2)
        ensures  r1.is_empty()
    {
        assert(r2.start().eq(r2.end()));
        assert(r2.start().lte(r1.start()));
        assert(r1.end().lte(r2.end()));
        lemma_lte_trans(r1.start(), r1.end(), r2.end());
        assert(r1.start().lte(r2.end()));
        lemma_lte_eq_between(r2.start(), r1.start(), r2.end());
        assert(r2.start().eq(r1.start()));

        lemma_lte_trans(r2.start(), r1.start(), r1.end());
        assert(r2.start().lte(r1.end()));
        lemma_lte_eq_between(r2.start(), r1.end(), r2.end());
        assert(r2.start().eq(r1.end()));

        lemma_eq_sym(r2.start(), r1.start());
        lemma_eq_trans(r1.start(), r2.start(), r1.end());
        assert(r1.start().eq(r1.end()));
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
