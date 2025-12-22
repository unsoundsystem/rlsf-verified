use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::set::Set;

// NOTE: we have to rewrite some parts of vstd::relations because they are using == for equality
//       and Verus has no support for impl PartialEq

verus! {
#[cfg(verus_keep_ghost)]
use vstd::relations::{transitive, equivalence_relation, irreflexive, reflexive};

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

/// reimplementations made for adding precodition

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


} // verus!
