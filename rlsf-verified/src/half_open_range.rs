use vstd::prelude::*;
use vstd::{seq::*, seq_lib::*};
use vstd::set_lib::set_int_range;
use vstd::set::Set;
use crate::rational_numbers::{
    Rational, lemma_from_int_adequate, lemma_add_preserve_wf,
    lemma_add_zero, lemma_lt_lte_trans, lemma_lte_trans, lemma_rat_range_split,
    rational_number_facts, lemma_lte_nonneg_add
};

verus! {
/// Type for left half-open range on Q
pub struct HalfOpenRangeOnRat(Rational, Rational);

impl HalfOpenRangeOnRat {
    #[verifier::type_invariant]
    pub open spec fn wf(self) -> bool {
        self.start().wf() && self.end().wf() && self.start().lte(self.end())
    }
    pub closed spec fn new(start: Rational, size: Rational) -> Self
        recommends start.wf(), size.wf(), size.is_nonneg()
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
        recommends self.wf(), e.wf()
    {
        &&& e.wf()
        &&& self.start().lte(e)
        &&& e.lt(self.end())
    }

    pub open spec fn disjoint(self, rhs: Self) -> bool
        recommends self.wf(), rhs.wf()
    {
        &&& self.wf()
        &&& rhs.wf()
        &&& self.end().lte(rhs.start()) || rhs.end().lte(self.start())
    }

    pub proof fn lemma_disjoint_not_contains(r1: Self, r2: Self)
        requires r1.wf(), r2.wf()
        ensures r1.disjoint(r2) <==> forall|e: Rational| e.wf() && r1.contains(e) ==> !r2.contains(e)
    {
        assert forall|e: Rational| e.wf() && r1.disjoint(r2) && r1.contains(e) implies !r2.contains(e) by {
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

        if !r1.disjoint(r2) {
            //assert(r2.start().lt(r1.end()));
            //assert(r2.start().lte(r1.end()) && r1.end().lt(r2.end())
                //|| r1.start().lte(r2.end()) && r2.end().lt(r1.end()));
            //assert(r2.start().lte(r1.end()) && r1.end().lte(r2.end())
            // TODO
            if !(r1.contains(r1.start()) && r2.contains(r1.start())) {
                assert(r1.disjoint(r2));
                assert(false);
            }
            //assume(exists|x: Rational| x.wf() && (r1.contains(x) && r2.contains(x)));
        }
        assert(!r1.disjoint(r2) ==> exists|x: Rational| x.wf() && (r1.contains(x) && r2.contains(x)));
    }

    pub proof fn lemma_out_of_range_start(r: Self, e: Rational)
        requires r.wf(), e.wf()
        ensures e.lt(r.start()) ==> !r.contains(e)
    {}

    pub proof fn lemma_out_of_range_end(r: Self, e: Rational)
        requires r.wf(), e.wf()
        ensures r.end().lte(e) ==> !r.contains(e)
    {}

    pub proof fn lemma_wf_if_size_is_pos(start: Rational, size: Rational)
        requires start.wf(), size.wf(), size.is_nonneg()
        ensures HalfOpenRangeOnRat::new(start, size).wf()
    {
        broadcast use rational_number_facts;
        lemma_lte_nonneg_add(start, size);
        assert(start.add(size).wf());
        assert(start.lte(start.add(size)));
    }

    /// Compatibility with Set

    pub open spec fn to_set(self) -> Set<Rational>
        recommends self.wf()
    {
        Set::new(|p: Rational| p.wf() && self.start().lte(p) && p.lt(self.end()))
    }

    pub proof fn lemma_disjoint_hor_disjoint_set(r1: Self, r2: Self)
        requires r1.wf(), r2.wf()
        ensures
            r1.disjoint(r2) <==> r1.to_set().disjoint(r2.to_set())
    {
        assert(r1.disjoint(r2) ==> r1.to_set().disjoint(r2.to_set())) by (nonlinear_arith);
    }

    pub proof fn lemma_hor_set_equiv(r: Self, e: Rational)
        requires r.wf(), e.wf()
        ensures r.to_set().contains(e) <==> r.contains(e)
    {}

    pub proof fn lemma_hor_disjoint(r1: Self, r2: Self)
        requires r1.wf(), r2.wf()
        ensures #[trigger] r1.disjoint(r2) <==> forall |e: Rational| e.wf() ==> (#[trigger] r1.contains(e) <==> #[trigger] r2.contains(e) == false)
    {
        assert(r1.disjoint(r2) <==> forall |e: Rational| e.wf() ==> (#[trigger] r1.contains(e) <==> #[trigger] r2.contains(e) == false));
    }

    pub proof fn lemma_empty_range(p: Rational)
        requires p.wf()
        ensures ({
            let r = HalfOpenRangeOnRat::new(p, Rational::from_int(0)); 
            r.wf() && r.to_set().is_empty()
        })
    {
        let rat0 = Rational::from_int(0);
        lemma_from_int_adequate(0);
        assert(rat0.wf());
        let r = HalfOpenRangeOnRat::new(p, rat0);
        assert(p.wf());
        lemma_add_preserve_wf(p, rat0);
        lemma_add_zero(p);
        assert(p.lte(p.add(rat0)));
        assert(r.wf());
        assert(!p.lt(p));
        assert forall |e: Rational| e.wf() implies !r.contains(e) by {
            Self::lemma_hor_set_equiv(r, e);
            assert(!(p.lte(e) && p.lt(p)) ==> !r.contains(e));
            assert(!(p.lte(e) && e.lt(p)));
            //assert(!r.contains(e)) by (nonlinear_arith);
        };
    }
}

}
