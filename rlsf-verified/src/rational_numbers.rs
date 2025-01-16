use vstd::prelude::*;
use vstd::relations::{equivalence_relation, injective, transitive, connected};
use vstd::arithmetic::mul::{lemma_mul_equality_converse, lemma_mul_nonzero};
use vstd::calc;
use crate::relation_utils::{strict_total_ordering};

verus! {
/// Rational number `num/den`
struct Rational {
    num: int, // numerator
    den: int // denominator
}

impl Rational {
    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        self.den > 0
    }

    proof fn silly(self)
        ensures self.wf()
    {}

    /// self=self.num/self.den, rhs=rhs.num/rhs.den then self=rhs iff
    /// self.num*rhs.den/self.den*rhs.den = rhs.num*self.den/self.den*rhs.den
    /// i.e. self.num*rhs.den == rhs.num*self.den
    spec fn eq(self, rhs: Self) -> bool {
        self.num * rhs.den == rhs.num * self.den
    }

    spec fn lt(self, rhs: Self) -> bool {
        self.num * rhs.den < rhs.num * self.den
    }

    spec fn eq_int(self, rhs: int) -> bool {
        self.num == rhs * self.den
    }

    spec fn from_int(x: int) -> Self {
        Self {
            num: x,
            den: 1
        }
    }

    proof fn lemma_equivalence_transitive()
        
        ensures transitive(|p: Self, q: Self| p.eq(q))
    {
        assert forall |p: Self, q: Self, r: Self| p.eq(q) && p.eq(r) implies q.eq(r) by {
            //assume(p.wf() && q.wf() && r.wf());
            if p.num == 0 {
                calc! {
                    (==>)
                    p.num == 0 && p.eq(q) && p.eq(r); {}
                    0 == q.num * p.den && 0 == r.num * p.den;
                    {
                        assert(p.wf());
                        lemma_mul_zero_choose(q.num, p.den);
                        lemma_mul_zero_choose(r.num, p.den);
                        assert(p.den != 0);
                    }
                    q.num == 0 && r.num == 0;
                }
            } else {
                calc! {
                    (==>)
                    p.eq(q) && p.eq(r); {}
                    q.num * p.den == p.num * q.den && p.num * r.den == r.num * p.den; {
                        assert(q.num * p.den == p.num * q.den && p.num * r.den == r.num * p.den
                            ==> q.num * p.den * p.num * r.den == p.num * q.den * r.num * p.den) by (nonlinear_arith);
                    }
                    q.num * p.den * p.num * r.den == p.num * q.den * r.num * p.den; {
                        assert(q.num * p.den * p.num * r.den == p.num * q.den * r.num * p.den
                            ==> (p.den * p.num) * (q.num * r.den) == (p.den * p.num) * (r.num * q.den)) by (nonlinear_arith);
                    }
                    (p.den * p.num) * (q.num * r.den) == (p.den * p.num) * (r.num * q.den);
                    {
                        lemma_mul_nonzero(p.den, p.num);
                        assert(p.num * p.den != 0);
                        assert(forall |m: int, x: int, y: int|
                            m != 0 && #[trigger] (m * x) == #[trigger] (m * y) ==> x == y) by (nonlinear_arith);
                    }
                    q.num * r.den == r.num * q.den;
                }
            }
        }
    }

    proof fn lemma_equivalence()
        ensures equivalence_relation(|p: Self, q: Self| p.eq(q))
    {
        Self::lemma_equivalence_transitive();
    }

    proof fn lemma_int_embedding_injective(x: int)
        ensures
            injective(|x: int| Self::from_int(x))
    {}

    proof fn lemma_lt_is_connected()
        ensures connected(|p: Self, q: Self| p.lt(q))
    {

    }

    //proof fn lemma_lt_is_strict_total()
        //ensures strict_total_ordering(|p: Self, q: Self| p.lt(q))
    //{}
}

proof fn lemma_mul_equality(a: int, b: int, c: int, d: int)
    ensures
        a == b && c == d ==> a*c == b*d
{}

proof fn lemma_mul_zero_choose(x: int, y: int) by (nonlinear_arith)
    ensures x*y == 0 ==> x == 0 || y == 0
{}

} // verus!
