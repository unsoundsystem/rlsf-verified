use vstd::prelude::*;
use vstd::relations::{equivalence_relation, injective, transitive};
use vstd::arithmetic::mul::{lemma_mul_is_commutative, lemma_mul_strict_inequality, lemma_mul_equality_converse, lemma_mul_nonzero};
use vstd::calc;
use crate::relation_utils::{strict_total_ordering, connected};

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

    // NOTE: Axiomization
    proof fn axiom_denominator_is_nonzero(self)
        ensures self.wf()
    { admit() }

    /// self=self.num/self.den, rhs=rhs.num/rhs.den then self=rhs iff
    /// self.num*rhs.den/self.den*rhs.den = rhs.num*self.den/self.den*rhs.den
    /// i.e. self.num*rhs.den == rhs.num*self.den
    spec fn eq(self, rhs: Self) -> bool {
        self.num * rhs.den == rhs.num * self.den
    }

    spec fn lt(self, rhs: Self) -> bool {
        self.num * rhs.den < rhs.num * self.den
    }

    spec fn lte(self, rhs: Self) -> bool {
        self.lt(rhs) || self.eq(rhs)
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

    // TODO: find better way than asserting wf-ness in precondition of all lemmas about fracitonals
    proof fn lemma_equivalence_transitive()
        ensures transitive(|p: Self, q: Self| p.eq(q))
    {
        assert forall |p: Self, q: Self, r: Self| p.eq(q) && p.eq(r) implies q.eq(r) by {
            if p.num == 0 {
                calc! {
                    (==>)
                    p.num == 0 && p.eq(q) && p.eq(r); {}
                    0 == q.num * p.den && 0 == r.num * p.den;
                    {
                        lemma_mul_zero_choose(q.num, p.den);
                        lemma_mul_zero_choose(r.num, p.den);
                        p.axiom_denominator_is_nonzero();
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
                        p.axiom_denominator_is_nonzero();
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
        ensures connected(|p: Self, q: Self| p.lt(q), |p: Self, q: Self| p.eq(q))
    {}

    proof fn lemma_lt_is_transitive()
        ensures transitive(|p: Self, q: Self| p.lt(q))
    {
        assert forall |p: Self, q: Self, r: Self| p.lt(q) && q.lt(r) implies p.lt(r) by {
            calc! {
                (==>)
                p.lt(q); { lemma_mul_is_commutative(q.num, p.den); assert(p.lt(q) ==> p.num * q.den < p.den * q.num) by (compute) }
                p.num * q.den < p.den * q.num; {
                    r.axiom_denominator_is_nonzero();
                    lemma_mul_equality_converse_right(p.num * q.den, p.den * q.num, r.den);
                }
                p.num * q.den * r.den < p.den * q.num * r.den;
            };

            calc! {
                (==>)
                q.lt(r); { lemma_mul_is_commutative(r.num, q.den); assert(q.lt(r) ==> q.num * r.den < q.den * r.num) by (compute) }
                q.num * r.den < q.den * r.num; {
                    p.axiom_denominator_is_nonzero();
                    lemma_mul_strict_inequality_imp(q.num * r.den, q.den * r.num, p.den);
                    vstd::arithmetic::mul::lemma_mul_is_associative(p.den, q.num, r.den);
                    vstd::arithmetic::mul::lemma_mul_is_associative(p.den, q.den, r.num);
                }
                p.den * q.num * r.den < p.den * q.den * r.num;
            }

            // transitivity of inequality on int
            assert((p.num * q.den * r.den < p.den * q.num * r.den) &&
                (p.den * q.num * r.den < p.den * q.den * r.num)
                ==> p.num * q.den * r.den < p.den * q.den * r.num) by (nonlinear_arith);

            q.axiom_denominator_is_nonzero();
            assert(p.num * q.den * r.den < p.den * q.den * r.num ==> p.num * r.den * q.den < p.den * r.num * q.den) by (nonlinear_arith);
            lemma_mul_strict_inequality_converse_imp(p.num * r.den, p.den * r.num, q.den);
            assert(p.num * r.den * q.den < p.den * r.num * q.den ==> p.num * r.den < p.den * r.num);
            vstd::arithmetic::mul::lemma_mul_is_commutative(r.num, p.den);
            assert(p.num * r.den < r.num * p.den ==> p.lt(r));
        }
    }

    proof fn lemma_lt_is_strict_total()
        ensures strict_total_ordering(|p: Self, q: Self| p.lt(q), |p: Self, q: Self| p.eq(q))
    {
        Self::lemma_equivalence(); // to surpress recommendation warning
        Self::lemma_lt_is_transitive();
    }
}

proof fn lemma_mul_zero_choose(x: int, y: int) by (nonlinear_arith)
    ensures x*y == 0 ==> x == 0 || y == 0
{}

proof fn lemma_mul_equality_converse_right(x: int, y: int, z: int) by (nonlinear_arith)
    ensures
        z > 0 && x < y ==> x * z < y * z
{}

proof fn lemma_mul_strict_inequality_converse_imp(x: int, y: int, z: int) by (nonlinear_arith)
    ensures
        #[trigger] (x * z) < #[trigger] (y * z) && z >= 0 ==> x < y
{}

proof fn lemma_mul_strict_inequality_imp(x: int, y: int, z: int) by (nonlinear_arith)
    ensures
        x < y && z > 0 ==> #[trigger] (z * x) < #[trigger] (z * y)
{}

} // verus!
