use vstd::prelude::*;
use vstd::raw_ptr::{expose_provenance, ptr_mut_write, ptr_ref, with_exposed_provenance, PointsTo};

verus! {

struct ListGroup {
    lss: Ghost<Seq<AList>>,
    gls: Ghost<Seq<*mut Val>>,
    // representation predicates for each list
    inv: Ghost<Seq<spec_fn(Map<*mut Val, PointsTo<Val>>, *mut Val) -> bool>>,
    m: Tracked<Map<*mut Val, PointsTo<Val>>>
}

struct AList {
    ls: Seq<*mut Val>,
    ii: Map<int, int>,
}

struct Val {
    x: *mut u8,
    y: *mut u8,
}



}
