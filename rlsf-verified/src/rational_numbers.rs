use vstd::prelude::*;
use vstd::relations::{equivalence_relation, transitive};
use vstd::arithmetic::mul::{lemma_mul_is_commutative, lemma_mul_strict_inequality, lemma_mul_equality_converse, lemma_mul_nonzero, lemma_mul_is_distributive_add_other_way, group_mul_properties};
use vstd::calc;
use crate::relation_utils::{injective, strict_total_ordering, partial_ordering};
use vstd::math::abs;

verus! {


// Constructing structure isomorphic to positive numbers,
// *BUT NOT CONTAINING `int` IN ITS DEFINITION*
// by this indirection we can avoid following problems
// 
// * `.wf()` hell (when constructing Q *in* Verus)
//     * avoid validation on every function using `Rational`
// * inconsistency due to axiom on `int` (when using axiomatic style)
//     * axoim predicating over `int` can cause inconsistency easily


pub enum Pos {
    BaseOne,
    Suc(Box<Pos>),
}

impl Pos {
    pub open spec fn to_int(self) -> int
        decreases self,
    {
        match self {
            Pos::BaseOne => 1,
            Pos::Suc(q) => 1 + q.to_int()
        }
    }

    pub open spec fn from_int(i: int) -> Pos
        recommends i > 0,
        decreases i
    {
        if i > 1 {
            Pos::Suc(Box::new(Self::from_int(i - 1)))
        } else if i == 1 {
            Pos::BaseOne
        } else { Pos::BaseOne }
    }

}

pub broadcast proof fn lemma_from_int_inj(p: int, q: int)
    requires p == q
    ensures Pos::from_int(p) == Pos::from_int(q)
{
}

pub broadcast proof fn lemma_to_int_inj(p: Pos, q: Pos)
    requires p == q
    ensures #[trigger] p.to_int() == #[trigger] q.to_int()
{}

proof fn to_int_inj_silly(p: Pos)
    requires p is Suc
    ensures p.to_int() > 1
    decreases p
{
    match p {
        Pos::BaseOne => assert(false),
        Pos::Suc(q) => {
            if q == Pos::BaseOne {
                assert(Pos::Suc(Box::new(Pos::BaseOne)).to_int() > 1) by (compute);
            } else {
                to_int_inj_silly(*q)
            }
        }
    }
}

pub broadcast proof fn lemma_to_int_inj_inverse(p: Pos, q: Pos)
    requires p.to_int() == q.to_int()
    ensures p == q
    decreases p
{
    match p {
        Pos::BaseOne => {
            match q {
                Pos::BaseOne => assert(p == q),
                Pos::Suc(qpr) => {
                    assert(p == Pos::BaseOne);
                    assert(q == Pos::Suc(qpr));
                    to_int_inj_silly(q);
                    assert(q.to_int() > 1);
                    assert(p.to_int() == 1);
                    assert(false);
                },
            }
        }
        Pos::Suc(ppr) => {
            match q {
                Pos::BaseOne =>
                {
                    to_int_inj_silly(p);
                    assert(p.to_int() != q.to_int());
                    assert(false);
                },
                Pos::Suc(qpr) => lemma_to_int_inj_inverse(*ppr, *qpr),
            }
        }
    }
}

pub broadcast proof fn lemma_pos_is_positive(p: Pos)
    ensures #[trigger] p.to_int() > 0
    decreases p
{
    match p {
        Pos::BaseOne => assert(Pos::BaseOne.to_int() > 0) by (compute),
        Pos::Suc(q) => {
            lemma_pos_is_positive(*q);
            assert(q.to_int() > 0);
        }
    } 
}

pub broadcast proof fn lemma_pos_int_bij(p: Pos)
    ensures #[trigger] Pos::from_int(#[trigger] p.to_int()) == p
    decreases p
{
    match p {
        Pos::BaseOne => {
            assert(Pos::from_int(Pos::BaseOne.to_int()) == Pos::BaseOne);
        },
        Pos::Suc(q) => lemma_pos_int_bij(*q),
    }
}

pub broadcast proof fn lemma_int_pos_bij(i: int)
    requires i > 0
    ensures #[trigger] Pos::from_int(i).to_int() == i
    decreases i
{
    if i == 1 {
        assert(Pos::from_int(1).to_int() == 1);
    } else {
        lemma_int_pos_bij(i-1);
    }
}

pub broadcast proof fn lemma_from_int_mul_distr(p: Pos, q: Pos)
    ensures #[trigger] Pos::from_int(#[trigger] p.to_int() * q.to_int()).to_int() == p.to_int() * q.to_int()
{
    lemma_pos_is_positive(p);
    lemma_pos_is_positive(q);
    pos_int_mul_is_pos_int(p.to_int(), q.to_int());
    assert(p.to_int() * q.to_int() > 0);
    lemma_int_pos_bij(p.to_int() * q.to_int());
}

proof fn pos_int_mul_is_pos_int(i: int, j: int) by (nonlinear_arith)
    requires i > 0, j > 0
    ensures i * j > 0
{}

/// Rational number `num/den`
pub struct Rational(int, Pos);

// TODO: theory of field
impl Rational {
    pub closed spec fn num(self) -> int // numerator
    {
        self.0
    }
    pub closed spec fn den(self) -> int // denominator
    {
        self.1.to_int()
    }

    pub closed spec fn new(n: int, d: Pos) -> Rational {
        Rational(n, d)
    }

    /// self=a/b, rhs=c/d
    /// self=rhs <==> a*d = b*c
    pub open spec fn eq(self, rhs: Self) -> bool
    {
        self.num() * rhs.den() == rhs.num() * self.den()
    }

    pub open spec fn lt(self, rhs: Self) -> bool
    {
        self.num() * rhs.den() < rhs.num() * self.den()
    }

    pub open spec fn lte(self, rhs: Self) -> bool
    {
        self.lt(rhs) || self.eq(rhs)
    }

    pub open spec fn eq_int(self, rhs: int) -> bool
    {

        self.num() == rhs * self.den()
    }

    pub open spec fn from_int(x: int) -> Self {
        Self::new(x, Pos::from_int(1))
    }

    pub open spec fn lt_int(self, i: int) -> bool {
        self.lt(Self::from_int(i))
    }

    proof fn lemma_eq_from_int_equiv(i: int, j: int) by (nonlinear_arith)
        ensures
            i == j <==> Self::from_int(i).eq(Self::from_int(j))
    {
        broadcast use rational_number_facts;
    }

    /// Addition, multiplication, opposite and inverse (division)

    pub open spec fn add(self, rhs: Rational) -> Rational
    {
        Rational::new(self.num() * rhs.den() + rhs.num() * self.den(),
                    Pos::from_int(self.den() * rhs.den()))
    }

    pub open spec fn mul(self, rhs: Rational) -> Rational
    {
        Rational::new(self.num() * rhs.num(), Pos::from_int(self.den() * rhs.den()))
    }

    pub open spec fn neg(self) -> Rational
    {
        Rational::new(-(self.num()), Pos::from_int(self.den()))
    }

    pub open spec fn sub(self, rhs: Rational) -> Rational
    {
        self.add(rhs.neg())
    }

    pub open spec fn inv(self) -> Rational
    {
        if self.num() == 0 {
            Rational::zero()
        } else if self.num() < 0 {
            Rational::new(-(self.den()), Pos::from_int(-(self.num())))
        } else { // p.num() > 0
            Rational::new(self.den(), Pos::from_int(self.num()))
        }
    }

    pub open spec fn div(self, rhs: Rational) -> Rational
    {
        self.mul(rhs.inv())
    }

    pub open spec fn is_nonneg(self) -> bool {
        Self::zero().lte(self)
    }

    pub open spec fn zero() -> Self {
        Rational::new(0, Pos::from_int(1))
    }

    pub open spec fn one() -> Self {
        Rational::new(1, Pos::from_int(1))
    }
}

pub broadcast proof fn lemma_denominator_is_positive(p: Rational)
    ensures p.den() > 0
{
    lemma_pos_is_positive(p.1);
}

pub broadcast proof fn lemma_add_pos_to_int_structual_eq(p: Rational, q: Rational, r: Rational)
    ensures r == p.add(q) <==>
                r.den() == p.den() * q.den() &&
                r.num() == p.num() * q.den() + q.num() * p.den()
{
    assert(r == p.add(q) ==>
                r.den() == p.den() * q.den() &&
                r.num() == p.num() * q.den() + q.num() * p.den()) by
    {
        //lemma_pos_is_positive(p.add(q).1);
        //lemma_to_int_inj_inverse(p.add(q).1, r.1);
        if r == p.add(q) {
            lemma_from_int_mul_distr(p.1, q.1);
            assert(Pos::from_int(p.den() * q.den()).to_int() == p.den() * q.den());
            assert(p.add(q).den() == p.den() * q.den());
        }
        assert(r == p.add(q) ==> r.den() == p.den() * q.den());
    };

    assert(r.den() == p.den() * q.den() &&
                r.num() == p.num() * q.den() + q.num() * p.den()
                ==> r == p.add(q)) by
    {
        if r.den() == p.den() * q.den() &&
                r.num() == p.num() * q.den() + q.num() * p.den() {

            assert(p.add(q).1.to_int() == p.den() * q.den()) by {
                // i.e. == p.1.to_int() * q.1.to_int()
                lemma_from_int_mul_distr(p.1, q.1);
            };
            assert(r.1.to_int() == p.den() * q.den());
            lemma_to_int_inj_inverse(r.1, p.add(q).1);
            assert(p.add(q).1 == r.1);
        }
    };
}

pub broadcast proof fn lemma_add_pos_to_int(p: Rational, q: Rational)
    ensures
        p.add(q).den() == p.den() * q.den(),
        p.add(q).num() == p.num() * q.den() + q.num() * p.den()
{
    lemma_from_int_mul_distr(p.1, q.1);
}

pub broadcast proof fn lemma_neg_pos_to_int(p: Rational)
    ensures p.neg().den() == p.den(),
            p.neg().num() == -p.num()
{
    lemma_denominator_is_positive(p);
    lemma_int_pos_bij(p.den());
}

pub broadcast proof fn lemma_sub_pos_to_int(p: Rational, q: Rational) by (nonlinear_arith)
    ensures
        p.sub(q).den() == p.den() * q.den(),
        p.sub(q).num() == p.num() * q.den() - q.num() * p.den()
{
    lemma_neg_pos_to_int(q);
    lemma_add_pos_to_int(p, q.neg());
}


pub broadcast proof fn lemma_mul_pos_to_int(p: Rational, q: Rational)
    ensures p.mul(q).num() == p.num() * q.num(),
            p.mul(q).den() == p.den() * q.den()
{
    lemma_from_int_mul_distr(p.1, q.1);
}

pub broadcast proof fn lemma_inv_pos_to_int(p: Rational)
    ensures ({
        if p.num() == 0 {
            p.inv().num() == 0
        } else {
            &&& abs(p.inv().num()) == p.den()
            &&& p.inv().den() == abs(p.num())
            &&& p.num() > 0 <==> p.inv().num() > 0
        }
    })
{
    if p.num() == 0 {
        assert(p.inv().num() == 0);
    } else if p.num() < 0 {
        assert(p.inv().num() == -(p.den()));
        lemma_denominator_is_positive(p);
        assert(abs(p.inv().num()) == p.den());
        lemma_int_pos_bij(-p.num());
        assert(p.inv().den() == -p.num());
    } else { // p.num() > 0
        lemma_denominator_is_positive(p);
        assert(p.inv().num() == p.den());
        lemma_int_pos_bij(p.num());
        assert(p.inv().den() == p.num());
    }

}

pub broadcast proof fn lemma_div_pos_to_int(p: Rational, q: Rational) by (nonlinear_arith)
    requires p.num() != 0, q.num() != 0
    ensures abs(p.div(q).num()) == abs(p.num() * q.den()),
            abs(p.div(q).den()) == abs(p.den() * q.num()),
            p.num() * q.num() > 0 <==> p.div(q).num() > 0
{
    //if p.num() > 0 {
        
    //} else { // p.num() < 0
    //}
    lemma_denominator_is_positive(p);
    lemma_denominator_is_positive(q);
    lemma_inv_pos_to_int(q);
    lemma_mul_pos_to_int(p, q.inv());
}

pub broadcast proof fn lemma_add_comm(lhs: Rational, rhs: Rational)
    ensures lhs.add(rhs).eq(rhs.add(lhs))
{}

pub proof fn lemma_rat_range_split(rhs: Rational, lhs: Rational) by (nonlinear_arith)
    ensures lhs.lt(rhs) <==> !rhs.lte(lhs)
{}

proof fn lemma_mul_pos_is_pos(i: int, j: int) by (nonlinear_arith)
    requires i > 0, j > 0
    ensures i * j > 0
{}

pub broadcast proof fn lemma_add_lt_mono(p: Rational, q: Rational, r: Rational)
    ensures p.lt(q) <==> p.add(r).lt(q.add(r))
{
    broadcast use rational_number_facts;
    lemma_add_pos_to_int(p, r);
    lemma_add_pos_to_int(q, r);
    let (a, b) = (p.num(), p.den());
    let (c, d) = (q.num(), q.den());
    let (e, f) = (r.num(), r.den());
    assert(b > 0);
    assert(d > 0);
    assert(f > 0);

    calc! {
        (<==>)
        a * d < c * b; {
            assert(f > 0);
            broadcast use group_mul_properties;
        }
        d * a * f < b * c * f; {
            broadcast use group_mul_properties;
            assert(d * e * b == b * e * d);
        }
        d * a * f + d * e * b < b * c * f + b * e * d; {
            broadcast use group_mul_properties;
        }
        d * f * (a * f + e * b) < b * f * (c * f + e * d); (<==>) {}
        p.add(r).lt(q.add(r));
    }
}

pub broadcast proof fn lemma_lt_lte_implies(p: Rational, q: Rational)
    requires p.lt(q)
    ensures p.lte(q)
{}

pub broadcast proof fn lemma_add_lte_mono(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    ensures p.lte(q) <==> p.add(r).lte(q.add(r))
{
    broadcast use rational_number_facts;
    lemma_add_pos_to_int(p, r);
    lemma_add_pos_to_int(q, r);
    let (a, b) = (p.num(), p.den());
    let (c, d) = (q.num(), q.den());
    let (e, f) = (r.num(), r.den());
    assert(b > 0);
    assert(d > 0);
    assert(f > 0);

    calc! {
        (<==>)
        a * d <= c * b; {
            assert(f > 0);
            broadcast use group_mul_properties;
        }
        d * a * f <= b * c * f; {
            broadcast use group_mul_properties;
            assert(d * e * b == b * e * d);
        }
        d * a * f + d * e * b <= b * c * f + b * e * d; {
            broadcast use group_mul_properties;
        }
        d * f * (a * f + e * b) <= b * f * (c * f + e * d); (<==>) {}
        p.add(r).lte(q.add(r));
    }
}


proof fn lemma_strict_inequality_mono(x: int, y: int, a: int, b: int) by (nonlinear_arith)
    requires x + a < y + b, a == b
    ensures x < y
{}

proof fn lemma_mul_comm_3arity(x: int, y: int, z: int)
    ensures x * y * z == y * x * z
{}

pub broadcast proof fn lemma_sub_lt_mono(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    requires p.lt(q)
    ensures p.sub(r).lt(q.sub(r))
{
    lemma_add_lt_mono(p, q, r.neg());
}

pub proof fn lemma_neg_lt_inverse(p: Rational, q: Rational) by (nonlinear_arith)
    requires p.lt(q)
    ensures q.neg().lt(p.neg())
{
    broadcast use rational_number_facts;
}

// Lemmas for rewriting equations

pub broadcast proof fn lemma_add_eq_preserve(p: Rational, q: Rational, r: Rational, s: Rational)
    requires p.eq(q), r.eq(s)
    ensures p.add(r).eq(q.add(s))
 {
    broadcast use rational_number_facts;
    broadcast use positive_number_facts;
    assert(p.eq(q));
    let (a, b) = (p.num(), p.den());
    let (c, d) = (q.num(), q.den());
    let (e, f) = (r.num(), r.den());
    let (g, h) = (s.num(), s.den());
    assert(b > 0 && d > 0 && f > 0 && h > 0);
    assert(a * d == c * b);
    assert(e * h == g * f);

    calc! {
        (==)
        (a * f + e * b) * (d * h);
        {
            lemma_mul_is_distributive_add_other_way(d * h, a * f, e * b);
        }
        a * f * (d * h) + e * b * (d * h);
        {
            broadcast use group_mul_properties;
            assert(a * f * (d * h) == a * f * d * h);
            assert(e * b * (d * h) == e * b * d * h);
        }
        a * f * d * h + e * b * d * h;
        {
            broadcast use group_mul_properties;
            assert(a * f * d * h == (a * d) * f * h);
            assert(e * b * d * h == (e * h) * b * d);
        }
        (a * d) * f * h + (e * h) * b * d;
        {
            assert(a * d == c * b);
            assert(e * h == g * f);
        }
        c * b * f * h + g * f * b * d;
        {
            broadcast use group_mul_properties;
            assert(c * b * f * h == c * h * (b * f));
            assert(g * f * b * d == g * d * (b * f));
        }
        c * h * (b * f) + g * d * (b * f);
        {
            broadcast use group_mul_properties;
        }
        (c * h + g * d) * (b * f);
    }

    // (p.0 * r.1 + r.0 * p.1) * (q.1 * s.1) == (q.0 * s.1 + s.0 * q.1) * (p.1 * r.1)
    assert((a * f + e * b) * (d * h) == (c * h + g * d) * (b * f));

    assert(p.add(r).eq(q.add(s)));
}

pub broadcast proof fn lemma_mul_eq_preserve(p: Rational, q: Rational, r: Rational, s: Rational)
    requires p.eq(q), r.eq(s)
    ensures p.mul(r).eq(q.mul(s))
{
    lemma_mul_pos_to_int(p, r);
    lemma_mul_pos_to_int(q, s);
    let (a, b) = (p.num(), p.den());
    let (c, d) = (q.num(), q.den());
    let (e, f) = (r.num(), r.den());
    let (g, h) = (s.num(), s.den());
    assert(a * d == c * b);
    assert(e * h == g * f);

    calc! {
        (==>)
        a * d == c * b; {
            broadcast use group_mul_properties;
        }
        a * d * e * h == c * b * g * f; {
            broadcast use group_mul_properties;
        }
        p.mul(r).eq(q.mul(s));
    }


    assert(p.mul(r).eq(q.mul(s)));
}

pub proof fn lemma_zero_inv_eq_zero(p: Rational) by (nonlinear_arith)
    requires p.eq(Rational::zero())
    ensures p.inv().eq(Rational::zero())
{
    broadcast use rational_number_facts;
}

pub proof fn lemma_inv_eq_preserve(p: Rational, q: Rational)
    by (nonlinear_arith)
    requires p.eq(q)
    ensures p.inv().eq(q.inv())
{
    if p.eq(Rational::zero()) || q.eq(Rational::zero()) {
        if p.eq(Rational::zero()) {
            lemma_zero_inv_eq_zero(p);
            lemma_eq_sym(p, Rational::zero());
            lemma_eq_trans(Rational::zero(), p, q);
            assert(q.eq(Rational::zero()));
            lemma_zero_inv_eq_zero(q);
            assert(p.inv().eq(q.inv()));
        } else {
            lemma_zero_inv_eq_zero(q);
            lemma_eq_sym(p, q);
            lemma_eq_sym(q, Rational::zero());
            lemma_eq_trans(Rational::zero(), q, p);
            assert(p.eq(Rational::zero()));
            lemma_zero_inv_eq_zero(p);
            assert(p.inv().eq(q.inv()));
        }
    } else {
        lemma_inv_pos_to_int(p);
        lemma_inv_pos_to_int(q);
    }
}


pub broadcast proof fn lemma_div_eq_preserve(p: Rational, q: Rational, r: Rational, s: Rational) by (nonlinear_arith)
    requires p.eq(q), r.eq(s)
    ensures p.div(r).eq(q.div(s))
{
    lemma_inv_eq_preserve(r, s);
    lemma_mul_eq_preserve(p, q, r.inv(), s.inv());
}

pub proof fn lemma_neg_eq_preserve(p: Rational, q: Rational) by (nonlinear_arith)
    requires p.eq(q)
    ensures p.neg().eq(q.neg())
{
    broadcast use rational_number_facts;
}

pub broadcast proof fn lemma_sub_eq_preserve(p: Rational, q: Rational, r: Rational, s: Rational)
    requires p.eq(q), r.eq(s)
    ensures p.sub(r).eq(q.sub(s))
{
    lemma_neg_eq_preserve(r, s);
    lemma_add_eq_preserve(p, q, r.neg(), s.neg());
}


pub broadcast proof fn lemma_from_int_adequate(i: int)
    ensures
        #[trigger] Rational::from_int(i).eq_int(i),
{}

pub proof fn lemma_add_zero(p: Rational) by (nonlinear_arith)
    ensures p.add(Rational::zero()).eq(p)
{
    broadcast use rational_number_facts;
}

pub broadcast proof fn lemma_add_eq_zero(p: Rational, q: Rational) by (nonlinear_arith)
    requires #[trigger] q.eq(Rational::zero())
    ensures #[trigger] p.add(q).eq(p)
{
    broadcast use rational_number_facts;
}


proof fn lemma_equivalence_transitive() by (nonlinear_arith)
    ensures transitive(|p: Rational, q: Rational| p.eq(q))
{
    broadcast use rational_number_facts;
}

proof fn lemma_equivalence()
    ensures equivalence_relation(|p: Rational, q: Rational| p.eq(q))
{
    lemma_equivalence_transitive();
}

// TODO
//proof fn lemma_int_embedding_injective(x: int)
    //ensures
        //injective(|x: int| Rational::from_int(x), |p: Rational, q: Rational| p.eq(q), |x: int, y: int| x == y)
//{ admit() }

proof fn lemma_lt_is_transitive() by (nonlinear_arith)
    ensures transitive(|p: Rational, q: Rational| p.lt(q))
{
    broadcast use rational_number_facts;
}

proof fn lemma_lt_is_strict_total()
    ensures strict_total_ordering(|p: Rational, q: Rational| p.lt(q), |p: Rational, q: Rational| p.eq(q))
{
    lemma_equivalence(); // to surpress recommendation warning
    lemma_lt_is_transitive();
}

pub proof fn lemma_lte_is_transitive() by (nonlinear_arith)
    ensures transitive(|p: Rational, q: Rational| p.lte(q))
{
    broadcast use rational_number_facts;
}

pub proof fn lemma_lte_is_partial_ordering()
    ensures partial_ordering(|p: Rational, q: Rational| p.lte(q), |p: Rational, q: Rational| p.eq(q))
{
    lemma_equivalence();
    lemma_lte_is_transitive();
}

pub proof fn lemma_lt_lte_trans(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    ensures p.lt(q) && q.lte(r) ==> p.lt(r)
{
    broadcast use rational_number_facts;
}

// in another style
pub broadcast proof fn lemma_lte_trans(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    ensures #[trigger] p.lte(q) && #[trigger] q.lte(r) ==> #[trigger] p.lte(r)
{
    broadcast use rational_number_facts;
}

// FIXME: naming: it's reflexivity
pub broadcast proof fn lemma_lte_sym(p: Rational, q: Rational) by (nonlinear_arith)
    requires p.eq(q)
    ensures p.lte(q)
{}

pub broadcast proof fn lemma_lte_antisym(p: Rational, q: Rational) by (nonlinear_arith)
    requires p.lte(q), q.lte(p)
    ensures p.eq(q)
{}

pub broadcast proof fn lemma_lte_eq_between(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    requires p.eq(r), p.lte(q), q.lte(r)
    ensures p.eq(q)
{
    broadcast use rational_number_facts;
}

pub proof fn lemma_lte_nonneg_add(p: Rational, q: Rational) by (nonlinear_arith)
    requires q.is_nonneg()
    ensures p.lte(p.add(q))
{
    broadcast use rational_number_facts;
}

pub proof fn lemma_nonneg_div(p: Rational, q: Rational)
    requires q.is_nonneg(), p.is_nonneg()
    ensures p.div(q).is_nonneg()
{
    broadcast use rational_number_facts;
}

pub proof fn lemma_rat_int_lte_equiv(p: int, q: int) by (nonlinear_arith)
    ensures
        p <= q <==> Rational::from_int(p).lte(Rational::from_int(q))
{}

pub proof fn lemma_hor_empty(p: Rational, q: Rational)
    ensures !(#[trigger] p.lte(q) && q.lt(p))
{}

pub broadcast proof fn lemma_lt_eq_equiv(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    requires q.eq(r)
    ensures p.lt(q) <==> p.lt(r)
{
    broadcast use rational_number_facts;
}

// TODO
pub broadcast proof fn lemma_lte_eq_equiv(p: Rational, q: Rational, r: Rational, s: Rational)
    requires p.eq(q), r.eq(s)
    ensures p.lte(r) <==> q.lte(s)
{
    let (a, b) = (p.num(), p.den());
    let (c, d) = (q.num(), q.den());
    let (e, f) = (r.num(), r.den());
    let (g, h) = (s.num(), s.den());
    lemma_denominator_is_positive(p);
    lemma_denominator_is_positive(q);
    lemma_denominator_is_positive(r);
    lemma_denominator_is_positive(s);
    assert(b > 0 && d > 0 && f > 0 && h > 0);

    calc! {
        (<==>)
        a * f <= e * b; {
            broadcast use group_mul_properties;
        }
        a * f * d * h <= e * b * d * h; {
            broadcast use group_mul_properties;
        }
        a * d * f * h <= h * e * b * d; {
            broadcast use group_mul_properties;
        }
        b * c * f * h <= f * g * b * d; {
            broadcast use group_mul_properties;
        }
        c * h <= g * d;
    }
}

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

pub broadcast proof fn lemma_mul_associative(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    ensures #[trigger] p.mul(q).mul(r).eq(#[trigger] p.mul(q.mul(r)))
{
    broadcast use rational_number_facts;
    //assert(p.mul(q).mul(r).eq(p.mul(q.mul(r)))) by (nonlinear_arith);
}

pub broadcast proof fn lemma_mul_commutative(p: Rational, q: Rational)
    ensures #[trigger] p.mul(q).eq(q.mul(p))
{}

proof fn lemma_inv_mul_is_one(p: Rational)
    requires !p.eq(Rational::zero())
    ensures
        p.inv().mul(p).eq(Rational::one()),
        p.mul(p.inv()).eq(Rational::one())
{
        broadcast use rational_number_facts;
        if p.num() < 0 {
            let one = Rational::one();
            let (a, b) = (p.num(), p.den());
            let (c, d) = (p.inv().num(), p.inv().den());
            lemma_inv_pos_to_int(p);
            assert(c == -b);
            assert(d == -a);
            assert(one.den() == one.num() == 1);

            calc! {
                (==)
                a * c;
                { assert(c == -b) }
                a * -b; {  vstd::arithmetic::mul::lemma_mul_unary_negation(a, b); }
                -(a * b); { vstd::arithmetic::mul::lemma_mul_unary_negation(b, a); }
                b * -a; { assert(d == -a) }
                b * d;
            }
            assert(a * c == b * d);
            assert((a * c) * one.den() == one.num() * (b * d));

            assert(p.inv().mul(p).eq(Rational::one()));
            assert(p.mul(p.inv()).eq(Rational::one()));
        } else { // p.num() > 0
            let one = Rational::one();
            let (a, b) = (p.num(), p.den());
            let (c, d) = (p.inv().num(), p.inv().den());
            lemma_inv_pos_to_int(p);
            assert(c == b);
            assert(d == a);
            assert(one.den() == one.num() == 1);
            assert(a * c == b * d);
            assert((a * c) * one.den() == one.num() * (b * d));
        }
}

proof fn lemma_inv_zero_is_zero(p: Rational)
    requires p.eq(Rational::zero())
    ensures p.inv().eq(Rational::zero())
{}

pub broadcast proof fn lemma_mul_one_noop(p: Rational, q: Rational) by (nonlinear_arith)
    requires #[trigger] q.eq(Rational::one())
    ensures #[trigger] p.mul(q).eq(p)
{
    lemma_denominator_is_positive(p);
    lemma_denominator_is_positive(q);
    lemma_mul_pos_to_int(p, q);
}

pub broadcast proof fn lemma_div_mul_eq(p: Rational, q: Rational)
    requires !q.eq(Rational::zero())
    ensures #[trigger] p.div(q).mul(q).eq(p)
{
    broadcast use rational_number_facts;

    // div is mul inv
    assert(p.div(q).eq(p.mul(q.inv())));
    lemma_mul_eq_preserve(p.div(q), p.mul(q.inv()), q, q);
    assert(p.div(q).mul(q).eq(p.mul(q.inv()).mul(q)));

    // apply associativity
    lemma_mul_associative(p, q.inv(), q);
    assert(p.mul(q.inv()).mul(q).eq(p.mul(q.inv().mul(q))));

    // multiplying inverse become 1
    lemma_inv_mul_is_one(q);
    lemma_mul_one_noop(p, q.inv().mul(q));
    assert(q.inv().mul(q).eq(Rational::one()));

    // using transitivity of equality
    lemma_eq_trans(p.div(q).mul(q), p.mul(q.inv()).mul(q), p.mul(q.inv().mul(q)));
    lemma_eq_trans(p.div(q).mul(q), p.mul(q.inv().mul(q)), p);

    assert(p.div(q).mul(q).eq(p));
}

pub broadcast proof fn lemma_eq_trans(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    requires #[trigger] p.eq(q), #[trigger] q.eq(r)
    ensures #[trigger] p.eq(r)
{
    lemma_denominator_is_positive(p);
    lemma_denominator_is_positive(q);
    lemma_denominator_is_positive(r);
}

pub broadcast proof fn lemma_eq_sym(p: Rational, q: Rational) by (nonlinear_arith)
    requires p.eq(q)
    ensures #[trigger] q.eq(p)
{}

pub broadcast proof fn lemma_eq_refl(p: Rational) by (nonlinear_arith)
    ensures #[trigger] p.eq(p)
{}

//pub proof fn lemma_mul_silly(p: Rational, q: Rational, i: int, j: int)
    //requires i > j
    //ensures p.add(q.mul(i)).eq(p.add(q.mul(j-i))).add(q.mul(j))

//proof fn examples() {
    //lemma_from_int_adequate(0);
    //lemma_from_int_adequate(1);
    //assert(Rational::from_int(0).lt(Rational::from_int(1)));

    //assert(Rational::new(2, 2).eq(Rational::from_int(1)));
    //assert(Rational::new(1, 2).lt(Rational::from_int(1)));
    //assert(Rational::new(1, 3).lt(Rational::new(2, 3)));
    //assert(!Rational::new(1, 3).lt(Rational::new(1, 3)));

    //assert(Rational::new(1, 3).div(Rational::new(1, 3)).eq(Rational::from_int(1)));
//}

pub broadcast group positive_number_facts {
    lemma_from_int_inj,
    lemma_to_int_inj,
    lemma_to_int_inj_inverse,
    lemma_pos_is_positive,
    lemma_pos_int_bij,
    lemma_int_pos_bij,
}

pub broadcast group rational_number_facts {
    lemma_denominator_is_positive,
    lemma_from_int_adequate,
    lemma_neg_pos_to_int,
    lemma_add_pos_to_int,
    lemma_sub_pos_to_int,
    lemma_mul_pos_to_int,
    lemma_div_pos_to_int,
}

pub broadcast group rational_number_equality {
    lemma_mul_eq_preserve,
    lemma_div_eq_preserve,
    lemma_add_eq_preserve,
    lemma_sub_eq_preserve,
    lemma_eq_trans,
    lemma_eq_sym,
    lemma_eq_refl
}
pub broadcast group rational_number_inequality {
    rational_number_equality,
    lemma_add_lt_mono,
    lemma_add_lte_mono,
    lemma_lte_trans,
    lemma_lt_eq_equiv,
    lemma_lt_lte_implies,
    lemma_lte_sym,
    lemma_lte_antisym
}
pub broadcast group rational_number_div_mul_properties {
    lemma_div_mul_eq,
    rational_number_mul_properties,
    rational_number_div_properties
}
pub broadcast group rational_number_mul_properties {
    lemma_mul_pos_to_int,
    lemma_mul_eq_preserve,
    lemma_mul_associative,
    lemma_mul_is_commutative,
    lemma_mul_one_noop
}
pub broadcast group rational_number_div_properties {
    lemma_div_pos_to_int,
    lemma_div_eq_preserve,
}
pub broadcast group rational_number_add_properties {
    lemma_add_pos_to_int,
    lemma_add_eq_preserve,
    lemma_add_lt_mono,
    lemma_add_eq_zero,
    lemma_add_comm,
}

} // verus!
