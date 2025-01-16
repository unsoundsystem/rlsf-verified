// TODO: we have to rewrite some parts of vstd::relations because they are using == for equality
//       and Verus has no support for impl PartialEq
use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::set::Set;

verus! {
use vstd::relations::{transitive, connected, equivalence_relation, irreflexive};

pub open spec fn antisymmetric<T>(r: spec_fn(T, T) -> bool, eq: spec_fn(T, T) -> bool) -> bool
    recommends equivalence_relation(eq)
{
    forall|x: T, y: T| #[trigger] r(x, y) && #[trigger] r(y, x) ==> eq(x, y)
}

pub open spec fn strict_total_ordering<T>(r: spec_fn(T, T) -> bool, eq: spec_fn(T, T) -> bool) -> bool
    recommends equivalence_relation(eq)
{
    &&& irreflexive(r)
    &&& antisymmetric(r, eq)
    &&& transitive(r)
    &&& connected(r)
}

}
