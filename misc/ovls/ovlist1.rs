// OVList1 - singly-linked overlaid list.
//
// Nodes are BlockHdr instances; the chain runs through BlockHdr.next.
// The list owns a head pointer and a ghost ordered sequence of node
// addresses, but does NOT own the permissions map - perms are supplied by
// the caller (mirrors the OVList2 API).  This makes both list types share
// a single perms map when bundled together as fields of OVList.
//
// Operations: new, push_front, pop_front, remove.

use vstd::prelude::*;
use vstd::raw_ptr::*;
use core::marker::PhantomData;
use crate::block::*;

verus! {

pub struct OVList1<'pool> {
    pub head: *mut BlockHdr,
    pub ptrs: Ghost<Seq<*mut BlockHdr>>,
    pub _phantom: PhantomData<&'pool ()>,
}

impl<'pool> OVList1<'pool> {
    /// ptrs[i]'s permission is wf and its BlockHdr.next matches ptrs[i+1]
    /// (or null at the tail).
    pub open spec fn wf_node(
        self,
        perms: Map<*mut BlockHdr, BlockPerm>,
        i: int,
    ) -> bool {
        let p = self.ptrs@[i];
        let nxt = perms[p].points_to.value().next;
        &&& perms.contains_key(p)
        &&& perms[p].wf(p)
        &&& (if i + 1 < self.ptrs@.len() {
                nxt == self.ptrs@[i + 1]
            } else {
                nxt@.addr == 0
            })
    }

    pub open spec fn wf(self, perms: Map<*mut BlockHdr, BlockPerm>) -> bool {
        &&& self.ptrs@.no_duplicates()
        &&& (forall|p: *mut BlockHdr| #[trigger] self.ptrs@.contains(p)
                ==> perms.contains_key(p) && p@.addr != 0)
        &&& (if self.ptrs@.len() == 0 {
                self.head@.addr == 0
            } else {
                self.head == self.ptrs@[0]
            })
        &&& (forall|i: int| 0 <= i < self.ptrs@.len() ==> #[trigger] self.wf_node(perms, i))
    }

    pub fn new() -> (r: Self)
        ensures
            forall|perms: Map<*mut BlockHdr, BlockPerm>| r.wf(perms),
            r.ptrs@.len() == 0,
    {
        OVList1 {
            head: null_bhdr(),
            ptrs: Ghost(Seq::empty()),
            _phantom: PhantomData,
        }
    }

    /// Insert `node` at the head of the list.  Consumes the caller's fresh
    /// perm and inserts it into the shared perms map.
    #[verifier::external_body]
    pub fn push_front(
        &mut self,
        node: *mut BlockHdr,
        Tracked(perm_in): Tracked<BlockPerm>,
        Tracked(perms): Tracked<&mut Map<*mut BlockHdr, BlockPerm>>,
    )
        requires
            old(self).wf(*old(perms)),
            node@.addr != 0,
            !old(self).ptrs@.contains(node),
            !old(perms).contains_key(node),
            perm_in.wf(node),
        ensures
            self.wf(*perms),
            self.ptrs@ == seq![node] + old(self).ptrs@,
            self.head == node,
            perms.dom() == old(perms).dom().insert(node),
            forall|p: *mut BlockHdr| #[trigger] old(perms).contains_key(p) && p != node ==>
                perms[p] == old(perms)[p],
    {
        unimplemented!()
    }

    /// Remove the head node and return it along with its permission.
    #[verifier::external_body]
    pub fn pop_front(
        &mut self,
        Tracked(perms): Tracked<&mut Map<*mut BlockHdr, BlockPerm>>,
    ) -> (r: (*mut BlockHdr, Tracked<BlockPerm>))
        requires
            old(self).wf(*old(perms)),
            old(self).ptrs@.len() > 0,
        ensures
            self.wf(*perms),
            r.0 == old(self).ptrs@.first(),
            self.ptrs@ == old(self).ptrs@.drop_first(),
            r.1@.wf(r.0),
            perms.dom() == old(perms).dom().remove(r.0),
            forall|p: *mut BlockHdr| #[trigger] old(perms).contains_key(p) && p != r.0 ==>
                perms[p] == old(perms)[p],
    {
        unimplemented!()
    }

    /// Remove an arbitrary node from the list.
    #[verifier::external_body]
    pub fn remove(
        &mut self,
        node: *mut BlockHdr,
        Tracked(perms): Tracked<&mut Map<*mut BlockHdr, BlockPerm>>,
    ) -> (r: Tracked<BlockPerm>)
        requires
            old(self).wf(*old(perms)),
            old(self).ptrs@.contains(node),
        ensures
            self.wf(*perms),
            self.ptrs@ == old(self).ptrs@.remove_value(node),
            r@.wf(node),
            perms.dom() == old(perms).dom().remove(node),
            forall|p: *mut BlockHdr| #[trigger] old(perms).contains_key(p) && p != node ==>
                perms[p] == old(perms)[p],
    {
        unimplemented!()
    }
}

} // verus!
