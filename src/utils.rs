use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::set::Set;

verus! {
#[cfg(verus_keep_ghost)]
use vstd::relations::{transitive, equivalence_relation, irreflexive, reflexive};
use crate::Tlsf;

pub open spec fn antisymmetric<T>(r: spec_fn(T, T) -> bool, eq: spec_fn(T, T) -> bool) -> bool
    recommends equivalence_relation(eq)
{
    forall|x: T, y: T| #[trigger] r(x, y) && #[trigger] r(y, x) ==> eq(x, y)
}

pub open spec fn connected<T>(r: spec_fn(T, T) -> bool, eq: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T| !eq(x, y) ==> #[trigger] r(x, y) || #[trigger] r(y, x)
}

pub open spec fn strict_total_ordering<T>(r: spec_fn(T, T) -> bool, eq: spec_fn(T, T) -> bool) -> bool
    recommends equivalence_relation(eq)
{
    &&& irreflexive(r)
    &&& antisymmetric(r, eq)
    &&& transitive(r)
    &&& connected(r, eq)
}

pub open spec fn injective<X, Y>(r: spec_fn(X) -> Y, eq1: spec_fn(Y, Y) -> bool, eq2: spec_fn(X, X) -> bool) -> bool
    recommends equivalence_relation(eq1) && equivalence_relation(eq2)
{
    forall|x1: X, x2: X| #[trigger] eq1(r(x1), #[trigger] r(x2)) ==> eq2(x1, x2)
}

pub open spec fn irreflexive_if<T>(r: spec_fn(T, T) -> bool, p: spec_fn(T) -> bool) -> bool {
    forall|x: T| p(x) ==> #[trigger] r(x, x) == false
}

pub open spec fn antisymmetric_if<T>(r: spec_fn(T, T) -> bool, eq: spec_fn(T, T) -> bool, p: spec_fn(T) -> bool) -> bool
    recommends equivalence_relation_if(eq, p)
{
    forall|x: T, y: T| p(x) && p(y) && #[trigger] r(x, y) && #[trigger] r(y, x) ==> eq(x, y)
}

pub open spec fn connected_if<T>(r: spec_fn(T, T) -> bool, eq: spec_fn(T, T) -> bool, p: spec_fn(T) -> bool) -> bool {
    forall|x: T, y: T| p(x) && p(y) && !eq(x, y) ==> #[trigger] r(x, y) || #[trigger] r(y, x)
}

pub open spec fn transitive_if<T>(r: spec_fn(T, T) -> bool, p: spec_fn(T) -> bool) -> bool {
    forall|x: T, y: T, z: T| p(x) && p(y) && p(z) && #[trigger] r(x, y) && #[trigger] r(y, z) ==> r(x, z)
}

pub open spec fn reflexive_if<T>(r: spec_fn(T, T) -> bool, p: spec_fn(T) -> bool) -> bool {
    forall|x: T| p(x) ==> #[trigger] r(x, x)
}

pub open spec fn symmetric_if<T>(r: spec_fn(T, T) -> bool, p: spec_fn(T) -> bool) -> bool {
    forall|x: T, y: T| p(x) && p(y) ==> (#[trigger] r(x, y) <==> #[trigger] r(y, x))
}

pub open spec fn equivalence_relation_if<T>(r: spec_fn(T, T) -> bool, p: spec_fn(T) -> bool) -> bool {
    &&& reflexive_if(r, p)
    &&& symmetric_if(r, p)
    &&& transitive_if(r, p)
}

pub open spec fn strict_total_ordering_if<T>(r: spec_fn(T, T) -> bool, eq: spec_fn(T, T) -> bool, p: spec_fn(T) -> bool) -> bool
    recommends equivalence_relation_if(eq, p)
{
    &&& irreflexive_if(r, p)
    &&& antisymmetric_if(r, eq, p)
    &&& transitive_if(r, p)
    &&& connected_if(r, eq, p)
}

pub open spec fn partial_ordering_if<T>(r: spec_fn(T, T) -> bool, eq: spec_fn(T, T) -> bool, p: spec_fn(T) -> bool) -> bool
    recommends equivalence_relation_if(eq, p)
{
    &&& reflexive_if(r, p)
    &&& transitive_if(r, p)
    &&& antisymmetric_if(r, eq, p)
}

pub open spec fn partial_ordering<T>(r: spec_fn(T, T) -> bool, eq: spec_fn(T, T) -> bool) -> bool
    recommends equivalence_relation(eq)
{
    &&& reflexive(r)
    &&& transitive(r)
    &&& antisymmetric(r, eq)
}

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    pub(crate) proof fn lemma_usize_add_le_from_int(x: usize, y: usize)
        requires (x as int) <= (usize::MAX - y) as int
        ensures x + y <= usize::MAX
    {
        assert(x <= usize::MAX - y) by (nonlinear_arith);
        assert(x + y <= usize::MAX) by (bit_vector);
    }

    pub(crate) proof fn lemma_checked_add_eq(x: usize, y: usize, res: usize)
        requires x.checked_add(y) == Some(res)
        ensures res == x + y
    {
        assert(x + y <= usize::MAX) by (nonlinear_arith);
        assert(res == (x + y) as usize) by (bit_vector);
        assert(res == x + y) by (bit_vector);
    }

    pub(crate) proof fn lemma_usize_add_le_mono(a: usize, b: usize, c: usize)
        requires
            a <= b,
            b + c <= usize::MAX,
        ensures
            a + c <= b + c
    {
        assert(a as int <= b as int) by (nonlinear_arith);
        assert(a as int + c as int <= b as int + c as int) by (nonlinear_arith);
        assert((a + c) as int <= (b + c) as int) by (nonlinear_arith);
        assert(a + c <= b + c) by (bit_vector);
    }

    pub(crate) proof fn lemma_usize_le_from_int(x: usize, y: usize)
        requires (x as int) <= (y as int)
        ensures x <= y
    {
        assert(x <= y) by (nonlinear_arith);
    }

    pub(crate) proof fn lemma_int_le_implies_usize_le(x: int, y: usize)
        requires 0 <= x, x <= y as int
        ensures (x as usize) <= y
    {
        assert((x as usize) <= y) by (nonlinear_arith);
    }

    pub(crate) proof fn lemma_usize_nonneg(u: usize)
        ensures 0 <= u as int
    {
        assert(0 <= u as int) by (bit_vector);
    }
}

}
