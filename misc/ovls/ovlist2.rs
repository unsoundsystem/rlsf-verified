// OVList2 - doubly-linked overlaid list.
//
// Nodes are BlockHdr instances; the link pointers live in a FreeLink struct
// overlaid at offset size_of::<BlockHdr>() inside each block.  The list
// owns its ghost sequence and head pointer; the perms map is supplied by
// the caller (typically borrowed from the corresponding OVList1).
//
// Operations: new, push_front, pop_front, remove.

use vstd::prelude::*;
use vstd::raw_ptr::*;
use core::marker::PhantomData;
use crate::block::*;

verus! {

pub struct OVList2<'pool> {
    pub head: *mut BlockHdr,
    pub ptrs: Ghost<Seq<*mut BlockHdr>>,
    pub _phantom: PhantomData<&'pool ()>,
}

impl<'pool> OVList2<'pool> {
    /// FreeLink at ptrs[i] points forward to ptrs[i+1] and backward to ptrs[i-1].
    pub open spec fn wf_node(self, perms: Map<*mut BlockHdr, BlockPerm>, i: int) -> bool {
        let p = self.ptrs@[i];
        &&& perms.contains_key(p)
        &&& perms[p].wf_freelink(p)
        &&& {
            let pt = perms[p].free_link_perm.unwrap();
            let nxt = pt.value().next_free;
            let prv = pt.value().prev_free;
            &&& (if i + 1 < self.ptrs@.len() {
                    nxt == self.ptrs@[i + 1]
                } else {
                    nxt@.addr == 0
                })
            &&& (if i > 0 {
                    prv == self.ptrs@[i - 1]
                } else {
                    prv@.addr == 0
                })
        }
    }

    pub open spec fn wf(self, perms: Map<*mut BlockHdr, BlockPerm>) -> bool {
        &&& self.ptrs@.no_duplicates()
        &&& (forall|p: *mut BlockHdr| #[trigger] self.ptrs@.contains(p)
                ==> perms.contains_key(p)
                    && p@.addr != 0
                    && (p as usize as int) + (size_of::<BlockHdr>() as int)
                        <= usize::MAX as int)
        &&& (if self.ptrs@.len() == 0 {
                self.head@.addr == 0
            } else {
                self.head == self.ptrs@[0]
            })
        &&& (forall|i: int| 0 <= i < self.ptrs@.len() ==> #[trigger] self.wf_node(perms, i))
    }

    pub fn new() -> (r: Self)
        ensures
            forall|p: Map<*mut BlockHdr, BlockPerm>| r.wf(p),
            r.ptrs@.len() == 0,
    {
        OVList2 {
            head: null_bhdr(),
            ptrs: Ghost(Seq::empty()),
            _phantom: PhantomData,
        }
    }

    /// Insert `node` at the head of the list.
    #[verifier::external_body]
    pub fn push_front(
        &mut self,
        node: *mut BlockHdr,
        Tracked(perms): Tracked<&mut Map<*mut BlockHdr, BlockPerm>>,
    )
        requires
            old(self).wf(*old(perms)),
            node@.addr != 0,
            !old(self).ptrs@.contains(node),
            old(perms).contains_key(node),
            old(perms)[node].wf_freelink(node),
            (node as usize as int) + (size_of::<BlockHdr>() as int) <= usize::MAX as int,
            old(self).ptrs@.len() > 0 ==>
                ((old(self).head as usize as int) + (size_of::<BlockHdr>() as int)
                    <= usize::MAX as int),
        ensures
            self.wf(*perms),
            self.ptrs@ == seq![node] + old(self).ptrs@,
            self.head == node,
            perms.dom() == old(perms).dom(),
            forall|p: *mut BlockHdr| #[trigger] old(perms).contains_key(p) ==>
                perms[p].points_to == old(perms)[p].points_to,
    {
        unimplemented!()
    }

    /// Remove the head node from the list.
    #[verifier::external_body]
    pub fn pop_front(
        &mut self,
        Tracked(perms): Tracked<&mut Map<*mut BlockHdr, BlockPerm>>,
    ) -> (r: *mut BlockHdr)
        requires
            old(self).wf(*old(perms)),
            old(self).ptrs@.len() > 0,
            (old(self).head as usize as int) + (size_of::<BlockHdr>() as int)
                <= usize::MAX as int,
        ensures
            self.wf(*perms),
            r == old(self).ptrs@.first(),
            self.ptrs@ == old(self).ptrs@.drop_first(),
            perms.dom() == old(perms).dom(),
            forall|p: *mut BlockHdr| #[trigger] old(perms).contains_key(p) ==>
                perms[p].points_to == old(perms)[p].points_to,
    {
        unimplemented!()
    }

    /// Remove an arbitrary node from the list.
    #[verifier::external_body]
    pub fn remove(
        &mut self,
        node: *mut BlockHdr,
        Tracked(perms): Tracked<&mut Map<*mut BlockHdr, BlockPerm>>,
    )
        requires
            old(self).wf(*old(perms)),
            old(self).ptrs@.contains(node),
            (node as usize as int) + (size_of::<BlockHdr>() as int)
                <= usize::MAX as int,
        ensures
            self.wf(*perms),
            self.ptrs@ == old(self).ptrs@.remove_value(node),
            perms.dom() == old(perms).dom(),
            forall|p: *mut BlockHdr| #[trigger] old(perms).contains_key(p) ==>
                perms[p].points_to == old(perms)[p].points_to,
    {
        unimplemented!()
    }
}

} // verus!
