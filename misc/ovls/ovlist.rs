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

    /// Push `node` onto list1 (singly-linked).  Inserts a fresh perm into
    /// the shared map.  `node` must not already be in either list nor in
    /// the perms map.
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
        self.list1.push_front(node, Tracked(perm), Tracked(self.perms.borrow_mut()));

        proof {
            // list2 invariants preserved: ptrs/head unchanged, and the new
            // perms entry is at `node`, which is not in list2.ptrs (since
            // node ∉ old perms.dom() ⊇ list2.ptrs.to_set()).
            assert(self.list2.ptrs@ =~= old(self).list2.ptrs@);
            assert forall|p: *mut BlockHdr| #[trigger] self.list2.ptrs@.contains(p)
                implies p != node
            by {
                assert(old(self).list2.ptrs@.contains(p));
                assert(old(self).perms@.contains_key(p));
            };
            assert forall|i: int| 0 <= i < self.list2.ptrs@.len()
                implies #[trigger] self.list2.wf_node(self.perms@, i)
            by {
                assert(old(self).list2.wf_node(old(self).perms@, i));
                assert(self.list2.ptrs@[i] == old(self).list2.ptrs@[i]);
                assert(self.list2.ptrs@.contains(self.list2.ptrs@[i]));
                assert(self.list2.ptrs@[i] != node);
                assert(self.perms@[self.list2.ptrs@[i]]
                    == old(self).perms@[self.list2.ptrs@[i]]);
            };
        }
    }

    /// Pop the head of list1.  Returns the popped pointer and its perm.
    /// Caller must ensure the popped node is not currently in list2.
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
        let r = self.list1.pop_front(Tracked(self.perms.borrow_mut()));

        proof {
            // list2 invariants preserved: ptrs/head unchanged, the removed
            // perms entry is at `r.0`, which is not in list2.ptrs by precondition.
            let popped = r.0;
            assert(self.list2.ptrs@ =~= old(self).list2.ptrs@);
            assert forall|i: int| 0 <= i < self.list2.ptrs@.len()
                implies #[trigger] self.list2.wf_node(self.perms@, i)
            by {
                assert(old(self).list2.wf_node(old(self).perms@, i));
                assert(self.list2.ptrs@[i] == old(self).list2.ptrs@[i]);
                assert(self.list2.ptrs@.contains(self.list2.ptrs@[i]));
                assert(self.list2.ptrs@[i] != popped);
                assert(self.perms@[self.list2.ptrs@[i]]
                    == old(self).perms@[self.list2.ptrs@[i]]);
            };
        }

        r
    }

    /// Push `node` onto list2 (doubly-linked).  Requires the perm for
    /// `node` already lives in `perms` with wf_freelink (typically because
    /// the caller pushed it onto list1 first, then promoted to list2).
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
        self.list2.push_front(node, Tracked(self.perms.borrow_mut()));

        proof {
            // list1 invariants preserved: ptrs/head unchanged.  list2's
            // push_front modifies perms[node] (BlockHdr.next is unchanged,
            // FreeLink is rewritten) and perms[old list2 head] (FreeLink only).
            // For list1.wf_node we only need BlockHdr.next, which is
            // untouched by list2.push_front.
            assert(self.list1.ptrs@ =~= old(self).list1.ptrs@);
            assert forall|i: int| 0 <= i < self.list1.ptrs@.len()
                implies #[trigger] self.list1.wf_node(self.perms@, i)
            by {
                assert(old(self).list1.wf_node(old(self).perms@, i));
                let p = self.list1.ptrs@[i];
                assert(self.list1.ptrs@.contains(p));
                assert(old(self).perms@.contains_key(p));
                // perms[p].points_to is preserved by list2.push_front
                // (which only modifies free_link_perm).  Need an extensional
                // check: BlockHdr.next at p didn't change.
                assert(self.perms@.contains_key(p));
                assert(self.perms@[p].points_to.value().next
                    == old(self).perms@[p].points_to.value().next);
                assert(self.perms@[p].wf(p));
            };
            assert forall|p: *mut BlockHdr| #[trigger] self.list1.ptrs@.contains(p)
                implies self.perms@.contains_key(p) && p@.addr != 0
            by {
                assert(old(self).list1.ptrs@.contains(p));
                assert(old(self).perms@.contains_key(p));
            };
        }
    }

    /// Pop the head of list2.  Returns the popped pointer; the corresponding
    /// perm stays in the shared map (it may still be owned by list1).
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
        let r = self.list2.pop_front(Tracked(self.perms.borrow_mut()));

        proof {
            // list1 preserved analogously: list2.pop_front does not touch
            // BlockHdr fields.
            assert(self.list1.ptrs@ =~= old(self).list1.ptrs@);
            assert forall|i: int| 0 <= i < self.list1.ptrs@.len()
                implies #[trigger] self.list1.wf_node(self.perms@, i)
            by {
                assert(old(self).list1.wf_node(old(self).perms@, i));
                let p = self.list1.ptrs@[i];
                assert(self.list1.ptrs@.contains(p));
                assert(old(self).perms@.contains_key(p));
                assert(self.perms@.contains_key(p));
                assert(self.perms@[p].points_to.value().next
                    == old(self).perms@[p].points_to.value().next);
                assert(self.perms@[p].wf(p));
            };
            assert forall|p: *mut BlockHdr| #[trigger] self.list1.ptrs@.contains(p)
                implies self.perms@.contains_key(p) && p@.addr != 0
            by {
                assert(old(self).list1.ptrs@.contains(p));
                assert(old(self).perms@.contains_key(p));
            };
        }

        r
    }

    /// Remove `node` from list1.  Delegates to OVList1::remove (currently
    /// external_body — TODO).
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
        let r = self.list1.remove(node, Tracked(self.perms.borrow_mut()));

        proof {
            assert(self.list2.ptrs@ =~= old(self).list2.ptrs@);
            assert forall|i: int| 0 <= i < self.list2.ptrs@.len()
                implies #[trigger] self.list2.wf_node(self.perms@, i)
            by {
                assert(old(self).list2.wf_node(old(self).perms@, i));
                assert(self.list2.ptrs@[i] == old(self).list2.ptrs@[i]);
                assert(self.list2.ptrs@.contains(self.list2.ptrs@[i]));
                assert(self.list2.ptrs@[i] != node);
                assert(self.perms@[self.list2.ptrs@[i]]
                    == old(self).perms@[self.list2.ptrs@[i]]);
            };
        }

        r
    }

    /// Remove `node` from list2.  Delegates to OVList2::remove (currently
    /// external_body — TODO).
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
        self.list2.remove(node, Tracked(self.perms.borrow_mut()));

        proof {
            assert(self.list1.ptrs@ =~= old(self).list1.ptrs@);
            assert forall|i: int| 0 <= i < self.list1.ptrs@.len()
                implies #[trigger] self.list1.wf_node(self.perms@, i)
            by {
                assert(old(self).list1.wf_node(old(self).perms@, i));
                let p = self.list1.ptrs@[i];
                assert(self.list1.ptrs@.contains(p));
                assert(old(self).perms@.contains_key(p));
                assert(self.perms@.contains_key(p));
                assert(self.perms@[p].points_to.value().next
                    == old(self).perms@[p].points_to.value().next);
                assert(self.perms@[p].wf(p));
            };
            assert forall|p: *mut BlockHdr| #[trigger] self.list1.ptrs@.contains(p)
                implies self.perms@.contains_key(p) && p@.addr != 0
            by {
                assert(old(self).list1.ptrs@.contains(p));
                assert(old(self).perms@.contains_key(p));
            };
        }
    }
}

} // verus!
