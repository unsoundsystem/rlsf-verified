use vstd::prelude::*;

// Experiments around axiomatic style formalization for rational numbers

verus! {

// Constructing structure isomorphic to positive numbers,
// *BUT NOT CONTAINING `int` IN ITS DEFINITION*
// by this indirection we can avoid following problems
// 
// * `.wf()` hell (when constructing Q *in* Verus)
// * inconsistency (when using axiomatic style)
//


enum Pos {
    BaseOne,
    Suc(Box<Pos>),
}
spec fn to_int(p: Pos) -> int
decreases p,
{
    match p {
        Pos::BaseOne => 1,
        Pos::Suc(q) => 1 + to_int(*q)
    }
}

spec fn from_int(i: int) -> Pos
recommends i > 0,
decreases i
{
    if i > 1 {
        Pos::Suc(Box::new(from_int(i - 1)))
    } else if i == 1 {
        Pos::BaseOne
    } else { Pos::BaseOne }
}

proof fn from_int_inj(p: int, q: int)
    requires p == q
    ensures from_int(p) == from_int(q)
{
}

proof fn to_int_inj(p: Pos, q: Pos)
    requires p == q
    ensures to_int(p) == to_int(q)
{}

proof fn pos_is_positive(p: Pos)
ensures to_int(p) > 0
decreases p
{
    match p {
        Pos::BaseOne => assert(to_int(Pos::BaseOne) > 0) by (compute),
        Pos::Suc(q) => {
            pos_is_positive(*q);
            assert(to_int(*q) > 0);
        }
    } 
}

proof fn lemma_pos_int_bij(p: Pos)
ensures from_int(to_int(p)) == p
decreases p
{
    match p {
        Pos::BaseOne => {
            assert(from_int(to_int(Pos::BaseOne)) == Pos::BaseOne);
        },
        Pos::Suc(q) => lemma_pos_int_bij(*q),
    }
}

proof fn lemma_int_pos_bij(i: int)
requires i > 0
ensures to_int(from_int(i)) == i
decreases i
{
    if i == 1 {
        assert(to_int(from_int(1)) == 1);
    } else {
        lemma_int_pos_bij(i-1);
    }
}

struct Rational(int, Pos);
impl Rational {
    spec fn new(n: int, d: Pos) -> Self {
        Self(n, d) // no validation!
    }

    spec fn num(self) -> int {
        self.0
    }

    spec fn den(self) -> int {
        to_int(self.1)
    }

    // this is same as current formalization
    spec fn eq(self, rhs: Self) -> bool {
        self.num() * rhs.den() == self.den() * rhs.num()
    }
}

proof fn lemma_eq_sym(p: Rational, q: Rational)
    requires p.eq(q)
    ensures q.eq(p)
{}

proof fn lemma_eq_trans(p: Rational, q: Rational, r: Rational) by (nonlinear_arith)
    requires p.eq(q), q.eq(r),
    ensures p.eq(r)
{
    pos_is_positive(p.1);
    pos_is_positive(q.1);
    pos_is_positive(r.1);
    assert(p.den() > 0);
    assert(q.den() > 0);
    assert(r.den() > 0);
}



proof fn ex() {
    assert(to_int(Pos::BaseOne) == 1);
    assert(to_int(Pos::Suc(Box::new(Pos::Suc(Box::new(Pos::BaseOne))))) == 3) by (compute);
}
} // verus!
