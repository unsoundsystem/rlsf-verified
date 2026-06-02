// OVList - composition of OVList1 (singly-linked) and OVList2 (doubly-linked)
// sharing a single permissions map.
//
// Fields:
//   list1: OVList1<'pool>  - singly-linked view via BlockHdr.next
//   list2: OVList2<'pool>  - doubly-linked view via the FreeLink overlay
//   perms: Tracked<Map<...>> - shared permissions map for both views
//
// Operations are wrappers around list1/list2 methods that thread &mut perms.
// No cross-list invariant is imposed - list1.ptrs and list2.ptrs may overlap
// or be disjoint; callers manage that relationship.

use vstd::prelude::*;
use vstd::raw_ptr::*;
use core::marker::PhantomData;
use crate::block::*;
use crate::ovlist1::*;
use crate::ovlist2::*;

verus! {

pub struct OVList<'pool> {
    pub list1: OVList1<'pool>,
    pub list2: OVList2<'pool>,
    pub perms: Tracked<Map<*mut BlockHdr, BlockPerm>>,
    pub _phantom: PhantomData<&'pool ()>,
}

impl<'pool> OVList<'pool> {
    pub open spec fn wf(self) -> bool {
        &&& self.list1.wf(self.perms@)
        &&& self.list2.wf(self.perms@)
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.list1.ptrs@.len() == 0,
            r.list2.ptrs@.len() == 0,
    {
        OVList {
            list1: OVList1::new(),
            list2: OVList2::new(),
            perms: Tracked(Map::tracked_empty()),
            _phantom: PhantomData,
        }
    }

    /// Push `node` onto list1 (singly-linked).
    #[verifier::external_body]
    pub fn push_front_1(
        &mut self,
        node: *mut BlockHdr,
        Tracked(perm): Tracked<BlockPerm>,
    )
        requires
            old(self).wf(),
            node@.addr != 0,
            !old(self).list1.ptrs@.contains(node),
            !old(self).perms@.contains_key(node),
            perm.wf(node),
        ensures
            self.wf(),
            self.list1.ptrs@ == seq![node] + old(self).list1.ptrs@,
            self.list1.head == node,
            self.list2.ptrs@ == old(self).list2.ptrs@,
            self.list2.head == old(self).list2.head,
            self.perms@.dom() == old(self).perms@.dom().insert(node),
    {
        unimplemented!()
    }

    /// Pop the head of list1.
    #[verifier::external_body]
    pub fn pop_front_1(&mut self) -> (r: (*mut BlockHdr, Tracked<BlockPerm>))
        requires
            old(self).wf(),
            old(self).list1.ptrs@.len() > 0,
            !old(self).list2.ptrs@.contains(old(self).list1.ptrs@.first()),
        ensures
            self.wf(),
            r.0 == old(self).list1.ptrs@.first(),
            self.list1.ptrs@ == old(self).list1.ptrs@.drop_first(),
            r.1@.wf(r.0),
            self.list2.ptrs@ == old(self).list2.ptrs@,
            self.list2.head == old(self).list2.head,
            self.perms@.dom() == old(self).perms@.dom().remove(r.0),
    {
        unimplemented!()
    }

    /// Push `node` onto list2 (doubly-linked).
    #[verifier::external_body]
    pub fn push_front_2(&mut self, node: *mut BlockHdr)
        requires
            old(self).wf(),
            node@.addr != 0,
            !old(self).list2.ptrs@.contains(node),
            old(self).perms@.contains_key(node),
            old(self).perms@[node].wf_freelink(node),
            (node as usize as int) + (size_of::<BlockHdr>() as int) <= usize::MAX as int,
            old(self).list2.ptrs@.len() > 0 ==>
                ((old(self).list2.head as usize as int) + (size_of::<BlockHdr>() as int)
                    <= usize::MAX as int),
        ensures
            self.wf(),
            self.list2.ptrs@ == seq![node] + old(self).list2.ptrs@,
            self.list2.head == node,
            self.list1.ptrs@ == old(self).list1.ptrs@,
            self.list1.head == old(self).list1.head,
            self.perms@.dom() == old(self).perms@.dom(),
    {
        unimplemented!()
    }

    /// Pop the head of list2.
    #[verifier::external_body]
    pub fn pop_front_2(&mut self) -> (r: *mut BlockHdr)
        requires
            old(self).wf(),
            old(self).list2.ptrs@.len() > 0,
            (old(self).list2.head as usize as int) + (size_of::<BlockHdr>() as int)
                <= usize::MAX as int,
        ensures
            self.wf(),
            r == old(self).list2.ptrs@.first(),
            self.list2.ptrs@ == old(self).list2.ptrs@.drop_first(),
            self.list1.ptrs@ == old(self).list1.ptrs@,
            self.list1.head == old(self).list1.head,
            self.perms@.dom() == old(self).perms@.dom(),
    {
        unimplemented!()
    }

    /// Remove `node` from list1.
    #[verifier::external_body]
    pub fn remove_1(&mut self, node: *mut BlockHdr) -> (r: Tracked<BlockPerm>)
        requires
            old(self).wf(),
            old(self).list1.ptrs@.contains(node),
            !old(self).list2.ptrs@.contains(node),
        ensures
            self.wf(),
            self.list1.ptrs@ == old(self).list1.ptrs@.remove_value(node),
            r@.wf(node),
            self.list2.ptrs@ == old(self).list2.ptrs@,
            self.list2.head == old(self).list2.head,
            self.perms@.dom() == old(self).perms@.dom().remove(node),
    {
        unimplemented!()
    }

    /// Remove `node` from list2.
    #[verifier::external_body]
    pub fn remove_2(&mut self, node: *mut BlockHdr)
        requires
            old(self).wf(),
            old(self).list2.ptrs@.contains(node),
            (node as usize as int) + (size_of::<BlockHdr>() as int) <= usize::MAX as int,
        ensures
            self.wf(),
            self.list2.ptrs@ == old(self).list2.ptrs@.remove_value(node),
            self.list1.ptrs@ == old(self).list1.ptrs@,
            self.list1.head == old(self).list1.head,
            self.perms@.dom() == old(self).perms@.dom(),
    {
        unimplemented!()
    }
}

} // verus!
