use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {
struct Block {
    field: usize,
}
trait Link<T> {
    spec fn get_link() -> *mut T;
}

trait Index {
    spec fn wf(self) -> bool;
    //spec fn le(self, i: Self) -> bool;
}
trait Perm<V> {
    fn map_pred(p: spec_fn(V) -> bool) -> bool;
}

trait GhostList<L: Index, V: Sized, P: Perm<V>> {
    spec fn wf(self, s: GlobalStore<V, P>) -> bool;
    spec fn wf_weak(self, s: GlobalStore<V, P>, exc: Set<L>) -> bool;
    spec fn next_of(self, i: L) -> Option<*mut V>;
    spec fn prev_of(self, i: L) -> Option<*mut V>;
    //proof fn lemma_preserve_touch_top(&self, i: L);
}

trait LocalList<L: Index, V: Sized, P: Perm<V>>: GhostList<L, V, P> {
    spec fn is_ii(self) -> bool;
}

//trait Store<V, P: Perm<V>> {
    //spec fn wf(self, s: S) -> bool;
    //spec fn wf_weak(self, s: S, exc: Set<L>) -> bool;
    //spec fn wf_node(self, i: int) -> bool;
    //proof fn insert_ptr_and_perm(
        //&mut self,
        //ptr: *mut V,
        //perm: impl Perm<V>);
    //proof fn lemma_preserve_touch_cont3(&self, i: int);
//}

#[verifier::reject_recursive_types(V)]
struct GlobalStore<V: Sized, Pr: Perm<V>> {
    ptrs: Seq<*mut V>,
    perms: Map<*mut V, Pr>
}

struct ListA;
struct ListB;

//impl GhostList for ListA {}
//impl GhostList for ListB {}

#[repr(C)]
#[derive(Debug)]
pub struct BlockHdr {
    pub(crate) size: usize,
    pub(crate) prev_phys_block: *mut BlockHdr,
}

#[repr(C)]
pub(crate) struct FreeLink {
    pub(crate) next_free: *mut BlockHdr,
    pub(crate) prev_free: *mut BlockHdr,
}


}
