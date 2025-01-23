use vstd::prelude::*;
use vstd::relations::{equivalence_relation, transitive};
use vstd::arithmetic::mul::{lemma_mul_is_commutative, lemma_mul_strict_inequality, lemma_mul_equality_converse, lemma_mul_nonzero};
use vstd::calc;
use crate::relation_utils::{injective, equivalence_relation_if, transitive_if, strict_total_ordering_if, partial_ordering_if};
use vstd::math::abs;

verus! {
/// Rational number `num/den`
pub struct Rational(int, int);

// TODO: theory of field
impl Rational {
    pub closed spec fn num(self) -> int // numerator
    {
        self.0
    }
    pub closed spec fn den(self) -> int // denominator
    {
        self.1
    }

    #[verifier::type_invariant]
    pub open spec fn wf(self) -> bool {
        self.den() > 0
    }

    // FIXME: denominator must d > 0, but there no way to enforce this in spec mode
    //      current workaround: just `recommends` on every spec function
    /// This function is only meaningful on d > 0
    pub closed spec fn new(n: int, d: int) -> Rational recommends d > 0 {
        Rational(n, d)
    }

    /// self=a/b, rhs=c/d
    /// self=rhs <==> a*d = b*c
    pub open spec fn eq(self, rhs: Self) -> bool
        recommends self.wf()
    {
        self.num() * rhs.den() == rhs.num() * self.den()
    }

    pub open spec fn lt(self, rhs: Self) -> bool
        recommends self.wf()
    {
        self.num() * rhs.den() < rhs.num() * self.den()
    }

    pub open spec fn lte(self, rhs: Self) -> bool
        recommends self.wf()
    {
        self.lt(rhs) || self.eq(rhs)
    }

    pub open spec fn eq_int(self, rhs: int) -> bool
        recommends self.wf()
    {

        self.num() == rhs * self.den()
    }

    pub open spec fn from_int(x: int) -> Self {
        Self::new(x, 1)
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

    pub open spec fn add(self, rhs: Rational) -> Rational
        recommends self.wf() && rhs.wf()
    {
        Rational::new(self.num() * rhs.den() + rhs.num() * self.den(), self.den() * rhs.den())
    }

    pub open spec fn mul(self, rhs: Rational) -> Rational
        recommends self.wf() && rhs.wf()
    {
        Rational::new(self.num() * rhs.num(), self.den() * rhs.den())
    }

    pub open spec fn neg(self) -> Rational
        recommends self.wf()
    {
        Rational::new(-(self.num()), self.den())
    }

    pub open spec fn sub(self, rhs: Rational) -> Rational
        recommends self.wf() && rhs.wf()
    {
        self.add(rhs.neg())
    }

    pub open spec fn inv(self) -> Rational
        recommends self.wf()
    {
        if self.num() == 0 {
            Rational::new(0, 1)
        } else if self.num() < 0 {
            Rational::new(self.den(), abs(self.num()) as int)
        } else { // p.num() > 0
            Rational::new(self.den(), self.num())
        }
    }

    pub open spec fn div(self, rhs: Rational) -> Rational
        recommends self.wf() && rhs.wf()
    {
        self.mul(rhs.inv())
    }

    pub open spec fn is_nonneg(self) -> bool {
        Self::zero().lte(self)
    }

    pub open spec fn zero() -> Self {
        Rational::new(0, 1)
    }
}

pub broadcast proof fn lemma_add_preserve_wf(lhs: Rational, rhs: Rational) by (nonlinear_arith)
    requires lhs.wf(), rhs.wf()
    ensures #[trigger] lhs.add(rhs).wf()
{}

pub broadcast proof fn lemma_sub_preserve_wf(lhs: Rational, rhs: Rational) by (nonlinear_arith)
    requires lhs.wf(), rhs.wf()
    ensures #[trigger] lhs.sub(rhs).wf()
{}

pub broadcast proof fn lemma_div_preserve_wf(lhs: Rational, rhs: Rational) by (nonlinear_arith)
    requires lhs.wf(), rhs.wf()
    ensures #[trigger] lhs.div(rhs).wf()
{}

pub broadcast proof fn lemma_mul_preserve_wf(lhs: Rational, rhs: Rational) by (nonlinear_arith)
    requires lhs.wf(), rhs.wf()
    ensures #[trigger] lhs.mul(rhs).wf()
{}

pub broadcast proof fn lemma_neg_preserve_wf(lhs: Rational) by (nonlinear_arith)
    requires lhs.wf()
    ensures #[trigger] lhs.neg().wf()
{}

pub broadcast proof fn lemma_inv_preserve_wf(lhs: Rational) by (nonlinear_arith)
    requires lhs.wf()
    ensures #[trigger] lhs.inv().wf()
{}

pub proof fn lemma_rat_range_split(rhs: Rational, lhs: Rational) by (nonlinear_arith)
    requires rhs.wf(), lhs.wf()
    ensures lhs.lt(rhs) <==> !rhs.lte(lhs)
{}

pub proof fn lemma_add_lt_mono(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    requires p.wf(), q.wf(), r.wf(), p.lt(q)
    ensures p.add(r).lt(q.add(r))
{}

pub proof fn lemma_sub_lt_mono(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    requires p.wf(), q.wf(), r.wf(), p.lt(q)
    ensures p.sub(r).lt(q.sub(r))
{}

pub proof fn lemma_neg_lt_inverse(p: Rational, q: Rational) by (nonlinear_arith)
    requires p.wf(), q.wf(), p.lt(q)
    ensures q.neg().lt(p.neg())
{}

pub proof fn lemma_add_eq_preserve(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    requires p.wf(), q.wf(), r.wf(), p.eq(q)
    ensures p.add(r).eq(q.add(r))
{}

pub broadcast proof fn lemma_from_int_adequate(i: int)
    ensures
        #[trigger] Rational::from_int(i).eq_int(i),
        #[trigger] Rational::from_int(i).wf()
{}

pub proof fn lemma_add_zero(p: Rational)
    requires p.wf()
    ensures p.add(Rational::zero()).eq(p)
{}

pub proof fn lemma_add_eq_zero(p: Rational, q: Rational) by (nonlinear_arith)
    requires p.wf(), q.wf(), q.eq(Rational::zero())
    ensures p.add(q).eq(p)
{}


proof fn lemma_equivalence_transitive() by (nonlinear_arith)
    ensures transitive_if(|p: Rational, q: Rational| p.eq(q), |p: Rational| p.wf())
{
}

proof fn lemma_equivalence()
    ensures equivalence_relation_if(|p: Rational, q: Rational| p.eq(q), |p: Rational| p.wf())
{
    lemma_equivalence_transitive();
}

// TODO
//proof fn lemma_int_embedding_injective(x: int)
    //ensures
        //injective(|x: int| Rational::from_int(x), |p: Rational, q: Rational| p.eq(q), |x: int, y: int| x == y)
//{ admit() }

proof fn lemma_lt_is_transitive() by (nonlinear_arith)
    ensures transitive_if(|p: Rational, q: Rational| p.lt(q), |p: Rational| p.wf())
{
}

proof fn lemma_lt_is_strict_total()
    ensures strict_total_ordering_if(|p: Rational, q: Rational| p.lt(q), |p: Rational, q: Rational| p.eq(q), |p: Rational| p.wf())
{
    lemma_equivalence(); // to surpress recommendation warning
    lemma_lt_is_transitive();
}

pub proof fn lemma_lte_is_transitive() by (nonlinear_arith)
    ensures transitive_if(|p: Rational, q: Rational| p.lte(q), |p: Rational| p.wf())
{
}

pub proof fn lemma_lte_is_partial_ordering()
    ensures partial_ordering_if(|p: Rational, q: Rational| p.lte(q), |p: Rational, q: Rational| p.eq(q), |p: Rational| p.wf())
{
    lemma_equivalence();
    lemma_lte_is_transitive();
}

pub proof fn lemma_lt_lte_trans(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    requires p.wf(), q.wf(), r.wf()
    ensures p.lt(q) && q.lte(r) ==> p.lt(r)
{}

// in another style
pub proof fn lemma_lte_trans(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    requires p.wf(), r.wf(), q.wf()
    ensures p.lte(q) && q.lte(r) ==> p.lte(r)
{}

pub proof fn lemma_lte_nonneg_add(p: Rational, q: Rational) by (nonlinear_arith)
    requires p.wf(), q.wf(), q.is_nonneg()
    ensures p.lte(p.add(q))
{}

pub proof fn lemma_nonneg_div(p: Rational, q: Rational)
    requires p.wf(), q.wf(), q.is_nonneg(), p.is_nonneg()
    ensures p.div(q).is_nonneg()
{}

pub proof fn lemma_rat_int_lte_equiv(p: int, q: int)
    ensures
        p <= q <==> Rational::from_int(p).lte(Rational::from_int(q))
{}

pub proof fn lemma_hor_empty(p: Rational, q: Rational)
    requires p.wf(), q.wf()
    ensures !(#[trigger] p.lte(q) && q.lt(p))
{}

pub proof fn lemma_lt_eq_equiv(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    requires p.wf(), q.wf(), r.wf(), q.eq(r)
    ensures p.lt(q) <==> p.lt(r)
{}

// silly lemma about integer arith

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
    lemma_from_int_adequate(0);
    lemma_from_int_adequate(1);
    assert(Rational::from_int(0).lt(Rational::from_int(1)));

    assert(Rational::new(2, 2).eq(Rational::from_int(1)));
    assert(Rational::new(1, 2).lt(Rational::from_int(1)));
    assert(Rational::new(1, 3).lt(Rational::new(2, 3)));
    assert(!Rational::new(1, 3).lt(Rational::new(1, 3)));

    assert(Rational::new(1, 3).div(Rational::new(1, 3)).eq(Rational::from_int(1)));
    //assert(Rational::new(0, 3).div(Rational::new(0, 3)).eq(Rational::from_int(1234)));
    //assert(false); // FIXME!!!!!
}

pub broadcast group rational_number_facts {
    lemma_add_preserve_wf,
    lemma_sub_preserve_wf,
    lemma_mul_preserve_wf,
    lemma_div_preserve_wf,
    lemma_neg_preserve_wf,
    lemma_inv_preserve_wf,
    lemma_from_int_adequate
}

} // verus!
