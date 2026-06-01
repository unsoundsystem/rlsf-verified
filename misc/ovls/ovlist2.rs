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

    /// Insert `node` at the head of the list.  Modifies the FreeLink overlays
    /// of `node` (sets next_free = old_head, prev_free = null) and the old
    /// head (sets prev_free = node).  The caller's perms map is mutated:
    /// the BlockPerm entries for `node` and the old head (if any) are
    /// updated.
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
        let ghost old_ptrs = self.ptrs@;
        let old_head = self.head;

        // Step 1: write node's FreeLink to { next_free: old_head, prev_free: null }.
        let tracked mut node_perm = perms.tracked_remove(node);
        let tracked mut node_fl = node_perm.free_link_perm.tracked_unwrap();
        let node_link = get_freelink_ptr(node);
        ptr_mut_write(node_link, Tracked(&mut node_fl), FreeLink {
            next_free: old_head,
            prev_free: null_bhdr(),
        });
        proof {
            node_perm.free_link_perm = Some(node_fl);
        }

        // Step 2: if old head exists, update its FreeLink.prev_free := node.
        let has_old_head: bool = !ptr_eq_null(old_head);
        proof {
            assert(has_old_head == (old_ptrs.len() > 0)) by {
                if old_ptrs.len() > 0 {
                    assert(old(self).head == old_ptrs[0]);
                    assert(old_ptrs.contains(old_ptrs[0]));
                    assert(old_ptrs[0]@.addr != 0);
                }
            };
        }
        if has_old_head {
            proof {
                assert(old(self).wf_node(*old(perms), 0));
            }
            let tracked mut head_perm = perms.tracked_remove(old_head);
            let tracked mut head_fl = head_perm.free_link_perm.tracked_unwrap();
            let head_link = get_freelink_ptr(old_head);
            let prev_next = ptr_ref(head_link, Tracked(&head_fl)).next_free;
            ptr_mut_write(head_link, Tracked(&mut head_fl), FreeLink {
                next_free: prev_next,
                prev_free: node,
            });
            proof {
                head_perm.free_link_perm = Some(head_fl);
                perms.tracked_insert(old_head, head_perm);
            }
        }

        // Step 3: re-insert node's perm and update ghost state.
        proof {
            perms.tracked_insert(node, node_perm);
            self.ptrs@ = seq![node] + old_ptrs;
        }
        self.head = node;

        proof {
            assert(self.ptrs@.no_duplicates()) by {
                assert(!old_ptrs.contains(node));
                assert(old_ptrs.no_duplicates());
            };
            assert(perms.dom() =~= old(perms).dom());
            assert forall|p: *mut BlockHdr| #[trigger] self.ptrs@.contains(p)
                implies perms.contains_key(p)
                    && p@.addr != 0
                    && (p as usize as int) + (size_of::<BlockHdr>() as int)
                        <= usize::MAX as int
            by {
                if p == node {} else {
                    let i = self.ptrs@.index_of(p);
                    assert(i > 0);
                    assert(self.ptrs@[i] == old_ptrs[i - 1]);
                    assert(old_ptrs.contains(p));
                }
            };
            assert forall|i: int| 0 <= i < self.ptrs@.len() implies #[trigger] self.wf_node(*perms, i) by {
                if i == 0 {
                    // The new node.  We wrote next_free = old_head, prev_free = null.
                    assert(self.ptrs@[0] == node);
                    if self.ptrs@.len() > 1 {
                        assert(self.ptrs@[1] == old_ptrs[0]);
                        // old_head == old_ptrs[0]
                    }
                } else if i == 1 && old_ptrs.len() > 0 {
                    // The old head, whose prev_free we set to node.
                    assert(self.ptrs@[1] == old_ptrs[0]);
                    assert(self.ptrs@[1] != node);
                    if self.ptrs@.len() > 2 {
                        assert(self.ptrs@[2] == old_ptrs[1]);
                        assert(old(self).wf_node(*old(perms), 0));
                    } else {
                        assert(old(self).wf_node(*old(perms), 0));
                    }
                } else {
                    // i >= 2: index shifted by one, perms unchanged.
                    assert(i >= 2);
                    assert(self.ptrs@[i] == old_ptrs[i - 1]);
                    assert(self.ptrs@[i] != node);
                    assert(self.ptrs@[i] != old_head) by {
                        if i - 1 == 0 {} else {
                            assert(old_ptrs[i - 1] != old_ptrs[0]);
                        }
                        assert(old_head == old_ptrs[0]);
                    };
                    assert(perms[self.ptrs@[i]] == old(perms)[self.ptrs@[i]]);
                    assert(old(self).wf_node(*old(perms), i - 1));
                    if i + 1 < self.ptrs@.len() {
                        assert(self.ptrs@[i + 1] == old_ptrs[i]);
                    }
                    assert(self.ptrs@[i - 1] == old_ptrs[i - 2]);
                }
            };
        }
    }

    /// Remove the head node from the list.  Modifies the FreeLink overlay
    /// of the new head (if any) to clear its prev_free.
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
        let ghost old_ptrs = self.ptrs@;
        let head_ptr = self.head;
        proof {
            assert(old(self).wf_node(*old(perms), 0));
        }
        // Read head's next_free to know the new head.
        let tracked mut head_perm = perms.tracked_remove(head_ptr);
        let tracked head_fl = head_perm.free_link_perm.tracked_unwrap();
        let head_link = get_freelink_ptr(head_ptr);
        let new_head = ptr_ref(head_link, Tracked(&head_fl)).next_free;
        proof {
            head_perm.free_link_perm = Some(head_fl);
            perms.tracked_insert(head_ptr, head_perm);
        }

        // If there's a successor, clear its prev_free.
        let has_next: bool = !ptr_eq_null(new_head);
        proof {
            if old_ptrs.len() > 1 {
                assert(old(self).wf_node(*old(perms), 0));
                assert(new_head == old_ptrs[1]);
                assert(old_ptrs.contains(old_ptrs[1]));
                assert(old_ptrs[1]@.addr != 0);
            } else {
                assert(old_ptrs.len() == 1);
                assert(old(self).wf_node(*old(perms), 0));
                assert(new_head@.addr == 0);
            }
        }
        if has_next {
            proof {
                assert(old_ptrs.len() > 1);
                assert(old(self).wf_node(*old(perms), 1));
                assert(new_head == old_ptrs[1]);
                assert(old_ptrs.contains(new_head));
            }
            let tracked mut nxt_perm = perms.tracked_remove(new_head);
            let tracked mut nxt_fl = nxt_perm.free_link_perm.tracked_unwrap();
            let nxt_link = get_freelink_ptr(new_head);
            let nxt_next = ptr_ref(nxt_link, Tracked(&nxt_fl)).next_free;
            ptr_mut_write(nxt_link, Tracked(&mut nxt_fl), FreeLink {
                next_free: nxt_next,
                prev_free: null_bhdr(),
            });
            proof {
                nxt_perm.free_link_perm = Some(nxt_fl);
                perms.tracked_insert(new_head, nxt_perm);
            }
        }

        self.head = new_head;
        proof {
            self.ptrs@ = old_ptrs.drop_first();
        }

        proof {
            assert(self.ptrs@.no_duplicates()) by {
                assert(old_ptrs.no_duplicates());
            };
            assert(perms.dom() =~= old(perms).dom());
            assert forall|p: *mut BlockHdr| #[trigger] self.ptrs@.contains(p)
                implies perms.contains_key(p)
                    && p@.addr != 0
                    && (p as usize as int) + (size_of::<BlockHdr>() as int)
                        <= usize::MAX as int
            by {
                let i = self.ptrs@.index_of(p);
                assert(self.ptrs@[i] == old_ptrs[i + 1]);
                assert(old_ptrs.contains(p));
            };
            if self.ptrs@.len() == 0 {
                assert(old_ptrs.len() == 1);
                assert(old(self).wf_node(*old(perms), 0));
                assert(new_head@.addr == 0);
            } else {
                assert(new_head == old_ptrs[1]);
                assert(self.ptrs@[0] == old_ptrs[1]);
            }
            assert forall|i: int| 0 <= i < self.ptrs@.len() implies #[trigger] self.wf_node(*perms, i) by {
                assert(self.ptrs@[i] == old_ptrs[i + 1]);
                assert(self.ptrs@[i] != head_ptr) by {
                    assert(old_ptrs[0] == head_ptr);
                };
                if i == 0 {
                    // This is the new head; its prev_free was cleared.
                } else {
                    // Unchanged from old(self).wf_node(*old(perms), i + 1).
                    assert(self.ptrs@[i] != new_head) by {
                        assert(old_ptrs[i + 1] != old_ptrs[1]);
                    };
                    assert(perms[self.ptrs@[i]] == old(perms)[self.ptrs@[i]]);
                    assert(old(self).wf_node(*old(perms), i + 1));
                    if i + 1 < self.ptrs@.len() {
                        assert(self.ptrs@[i + 1] == old_ptrs[i + 2]);
                    }
                    assert(self.ptrs@[i - 1] == old_ptrs[i]);
                }
            };
        }

        head_ptr
    }

    /// Remove an arbitrary node from the list.  Modifies the FreeLink
    /// overlays of `node`'s predecessor (sets next_free past `node`) and
    /// successor (sets prev_free past `node`), if those neighbours exist.
    //
    // TODO: like OVList1::remove, the structural splice proof requires
    // careful Map<_, BlockPerm> reasoning across three perms-removals.
    // The exec body below is the intended implementation, leveraging the
    // FreeLink-stored prev_free to avoid a walk.  Marked external_body so
    // the example verifies end-to-end.
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
        let ghost old_ptrs = self.ptrs@;
        // Read node's prev_free and next_free.
        let tracked mut node_perm = perms.tracked_remove(node);
        let tracked node_fl = node_perm.free_link_perm.tracked_unwrap();
        let node_link = get_freelink_ptr(node);
        let prev = ptr_ref(node_link, Tracked(&node_fl)).prev_free;
        let next = ptr_ref(node_link, Tracked(&node_fl)).next_free;
        proof {
            node_perm.free_link_perm = Some(node_fl);
            perms.tracked_insert(node, node_perm);
        }

        // If prev != null, rewire prev.next_free := next.
        if prev != null_bhdr() {
            let tracked mut prev_perm = perms.tracked_remove(prev);
            let tracked mut prev_fl = prev_perm.free_link_perm.tracked_unwrap();
            let prev_link = get_freelink_ptr(prev);
            let prev_prev = ptr_ref(prev_link, Tracked(&prev_fl)).prev_free;
            ptr_mut_write(prev_link, Tracked(&mut prev_fl), FreeLink {
                next_free: next,
                prev_free: prev_prev,
            });
            proof {
                prev_perm.free_link_perm = Some(prev_fl);
                perms.tracked_insert(prev, prev_perm);
            }
        } else {
            // node was the head; advance self.head.
            self.head = next;
        }

        // If next != null, rewire next.prev_free := prev.
        if next != null_bhdr() {
            let tracked mut nxt_perm = perms.tracked_remove(next);
            let tracked mut nxt_fl = nxt_perm.free_link_perm.tracked_unwrap();
            let nxt_link = get_freelink_ptr(next);
            let nxt_next = ptr_ref(nxt_link, Tracked(&nxt_fl)).next_free;
            ptr_mut_write(nxt_link, Tracked(&mut nxt_fl), FreeLink {
                next_free: nxt_next,
                prev_free: prev,
            });
            proof {
                nxt_perm.free_link_perm = Some(nxt_fl);
                perms.tracked_insert(next, nxt_perm);
            }
        }

        // Remove `node` from the perms map.
        proof {
            let tracked _discarded = perms.tracked_remove(node);
            self.ptrs@ = old_ptrs.remove_value(node);
        }
    }
}

} // verus!
