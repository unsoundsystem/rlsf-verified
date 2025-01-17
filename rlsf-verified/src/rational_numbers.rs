use vstd::prelude::*;
use vstd::relations::{equivalence_relation, transitive};
use vstd::arithmetic::mul::{lemma_mul_is_commutative, lemma_mul_strict_inequality, lemma_mul_equality_converse, lemma_mul_nonzero};
use vstd::calc;
use crate::relation_utils::{strict_total_ordering, connected, injective};
use vstd::math::abs;

verus! {
/// Rational number `num/den`
pub struct Rational;

// TODO: theory of field
impl Rational {
    pub spec fn num(self) -> int; // numerator
    pub spec fn den(self) -> int; // denominator

    /// Although signiture is total, this function is undefined on d <= 0
    pub spec fn new(n: int, d: int) -> Rational recommends d > 0;

    /// self=a/b, rhs=c/d
    /// self=rhs <==> a*d = b*c
    pub open spec fn eq(self, rhs: Self) -> bool {
        self.num() * rhs.den() == rhs.num() * self.den()
    }

    pub open spec fn lt(self, rhs: Self) -> bool {
        self.num() * rhs.den() < rhs.num() * self.den()
    }

    pub open spec fn lte(self, rhs: Self) -> bool {
        self.lt(rhs) || self.eq(rhs)
    }

    spec fn eq_int(self, rhs: int) -> bool {
        self.num() == rhs * self.den()
    }

    pub spec fn from_int(x: int) -> Self;

    // TODO: find better way than asserting wf-ness in precondition of all lemmas about fracitonals
    proof fn lemma_equivalence_transitive()
        ensures transitive(|p: Self, q: Self| p.eq(q))
    {
        assert forall |p: Self, q: Self, r: Self| p.eq(q) && p.eq(r) implies q.eq(r) by {
            if p.num() == 0 {
                calc! {
                    (==>)
                    p.num() == 0 && p.eq(q) && p.eq(r); {}
                    0 == q.num() * p.den() && 0 == r.num() * p.den();
                    {
                        lemma_mul_zero_choose(q.num(), p.den());
                        lemma_mul_zero_choose(r.num(), p.den());
                        axiom_denominator_is_nonzero(p);
                        assert(p.den() != 0);
                    }
                    q.num() == 0 && r.num() == 0;
                }
            } else {
                calc! {
                    (==>)
                    p.eq(q) && p.eq(r); {}
                    q.num() * p.den() == p.num() * q.den() && p.num() * r.den() == r.num() * p.den(); {
                        assert(q.num() * p.den() == p.num() * q.den() && p.num() * r.den() == r.num() * p.den()
                            ==> q.num() * p.den() * p.num() * r.den() == p.num() * q.den() * r.num() * p.den()) by (nonlinear_arith);
                    }
                    q.num() * p.den() * p.num() * r.den() == p.num() * q.den() * r.num() * p.den(); {
                        assert(q.num() * p.den() * p.num() * r.den() == p.num() * q.den() * r.num() * p.den()
                            ==> (p.den() * p.num()) * (q.num() * r.den()) == (p.den() * p.num()) * (r.num() * q.den())) by (nonlinear_arith);
                    }
                    (p.den() * p.num()) * (q.num() * r.den()) == (p.den() * p.num()) * (r.num() * q.den());
                    {
                        lemma_mul_nonzero(p.den(), p.num());
                        axiom_denominator_is_nonzero(p);
                        assert(p.num() * p.den() != 0);
                        assert(forall |m: int, x: int, y: int|
                            m != 0 && #[trigger] (m * x) == #[trigger] (m * y) ==> x == y) by (nonlinear_arith);
                    }
                    q.num() * r.den() == r.num() * q.den();
                }
            }
        }
    }

    proof fn lemma_equivalence()
        ensures equivalence_relation(|p: Self, q: Self| p.eq(q))
    {
        Self::lemma_equivalence_transitive();
    }

    // TODO
    //proof fn lemma_int_embedding_injective(x: int)
        //ensures
            //injective(|x: int| Self::from_int(x), |p: Rational, q: Rational| p.eq(q), |x: int, y: int| x == y)
    //{ admit() }

    proof fn lemma_lt_is_connected()
        ensures connected(|p: Self, q: Self| p.lt(q), |p: Self, q: Self| p.eq(q))
    {}

    proof fn lemma_lt_is_transitive()
        ensures transitive(|p: Self, q: Self| p.lt(q))
    {
        assert forall |p: Self, q: Self, r: Self| p.lt(q) && q.lt(r) implies p.lt(r) by {
            calc! {
                (==>)
                p.lt(q); { lemma_mul_is_commutative(q.num(), p.den()); assert(p.lt(q) ==> p.num() * q.den() < p.den() * q.num()) by (compute) }
                p.num() * q.den() < p.den() * q.num(); {
                    axiom_denominator_is_nonzero(r);
                    lemma_mul_equality_converse_right(p.num() * q.den(), p.den() * q.num(), r.den());
                }
                p.num() * q.den() * r.den() < p.den() * q.num() * r.den();
            };

            calc! {
                (==>)
                q.lt(r); { lemma_mul_is_commutative(r.num(), q.den()); assert(q.lt(r) ==> q.num() * r.den() < q.den() * r.num()) by (compute) }
                q.num() * r.den() < q.den() * r.num(); {
                    axiom_denominator_is_nonzero(p);
                    lemma_mul_strict_inequality_imp(q.num() * r.den(), q.den() * r.num(), p.den());
                    vstd::arithmetic::mul::lemma_mul_is_associative(p.den(), q.num(), r.den());
                    vstd::arithmetic::mul::lemma_mul_is_associative(p.den(), q.den(), r.num());
                }
                p.den() * q.num() * r.den() < p.den() * q.den() * r.num();
            }

            // transitivity of inequality on int
            assert((p.num() * q.den() * r.den() < p.den() * q.num() * r.den()) &&
                (p.den() * q.num() * r.den() < p.den() * q.den() * r.num())
                ==> p.num() * q.den() * r.den() < p.den() * q.den() * r.num()) by (nonlinear_arith);

            axiom_denominator_is_nonzero(q);
            assert(p.num() * q.den() * r.den() < p.den() * q.den() * r.num() ==> p.num() * r.den() * q.den() < p.den() * r.num() * q.den()) by (nonlinear_arith);
            lemma_mul_strict_inequality_converse_imp(p.num() * r.den(), p.den() * r.num(), q.den());
            assert(p.num() * r.den() * q.den() < p.den() * r.num() * q.den() ==> p.num() * r.den() < p.den() * r.num());
            vstd::arithmetic::mul::lemma_mul_is_commutative(r.num(), p.den());
            assert(p.num() * r.den() < r.num() * p.den() ==> p.lt(r));
        }
    }

    proof fn lemma_lt_is_strict_total()
        ensures strict_total_ordering(|p: Self, q: Self| p.lt(q), |p: Self, q: Self| p.eq(q))
    {
        Self::lemma_equivalence(); // to surpress recommendation warning
        Self::lemma_lt_is_transitive();
    }

    pub open spec fn lt_int(self, i: int) -> bool {
        self.lt(Self::from_int(i))
    }

    // TODO
    proof fn lemma_eq_from_int_equiv(i: int, j: int)
        ensures
            i == j <==> Self::from_int(i).eq(Self::from_int(j))
    {}

    /// Addition, multiplication, opposite and inverse (division)

    pub open spec fn add(self, rhs: Rational) -> Rational {
        Rational::new(self.num() * rhs.den() + rhs.num() * self.den(), self.den() * rhs.den())
    }

    pub open spec fn mul(self, rhs: Rational) -> Rational {
        Rational::new(self.num() * rhs.num(), self.den() * rhs.den())
    }

    pub open spec fn neg(self) -> Rational {
        Rational::new(-(self.num()), self.den())
    }

    pub open spec fn sub(self, rhs: Rational) -> Rational {
        self.add(rhs.neg())
    }

    pub open spec fn inv(self) -> Rational {
        if self.num() == 0 {
            Rational::new(0, 1)
        } else if self.num() < 0 {
            Rational::new(self.den(), abs(self.num()) as int)
        } else { // p.num() > 0
            Rational::new(self.den(), self.num())
        }
    }

    pub open spec fn div(self, rhs: Rational) -> Rational {
        self.mul(rhs.inv())
    }
}

// NOTE: Axiomization
broadcast proof fn axiom_denominator_is_nonzero(r: Rational)
    ensures r.den() > 0
{ admit() }

// FIXME: this cause inconsistency!!! assert(false) proved
//      minimal example:
//      >    pub struct Rational;
//      >    impl Rational {
//      >        pub spec fn num(self) -> int; // numerator
//      >        pub spec fn den(self) -> int; // denominator
//      >        pub spec fn from_int(x: int) -> Self;
//      >    }
//      >    
//      >    broadcast proof fn axiom_denominator_is_nonzero(r: Rational)
//      >        ensures r.den() > 0
//      >    { admit() }
//      >    
//      >    broadcast proof fn axiom_from_int(i: int)
//      >        ensures
//      >            Rational::from_int(i).den() == 1,
//      >            Rational::from_int(i).num() == i
//      >    { admit() }
//      >    
//      >    proof fn test() {
//      >        axiom_from_int(0);
//      >        // axiom_from_int(1);
//      >        assert(false)
//      >    }
broadcast proof fn axiom_from_int(i: int)
    ensures
        Rational::from_int(i).den() == 1,
        Rational::from_int(i).num() == i
{ admit() }

broadcast proof fn axiom_new_rational(n: int, d: int)
    requires
        d > 0
    ensures
        Rational::new(n, d).num() == n,
        Rational::new(n, d).den() == d,
{ admit() }

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

proof fn examples() {
    axiom_from_int(0);
    axiom_from_int(1);
    assert(Rational::from_int(0).lt(Rational::from_int(1)));

    assert(Rational::new(2, 2).eq(Rational::from_int(1)));
    assert(Rational::new(1, 2).lt(Rational::from_int(1)));
    assert(Rational::new(1, 3).lt(Rational::new(2, 3)));
    assert(!Rational::new(1, 3).lt(Rational::new(1, 3)));

    assert(Rational::new(1, 3).div(Rational::new(1, 3)).eq(Rational::from_int(1)));
    assert(Rational::new(0, 3).div(Rational::new(0, 3)).eq(Rational::from_int(1234)));
    assert(false); // FIXME!!!!!
}

} // verus!
