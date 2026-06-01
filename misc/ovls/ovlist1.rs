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
        let tracked mut perm = perm_in;
        let old_head = self.head;
        let ghost old_ptrs = self.ptrs@;
        // Write node.next = old_head.
        let tracked mut points_to = perm.points_to;
        let mut hdr = ptr_mut_read(node, Tracked(&mut points_to));
        hdr.next = old_head;
        ptr_mut_write(node, Tracked(&mut points_to), hdr);
        proof { perm.points_to = points_to; }

        self.head = node;
        proof {
            self.ptrs@ = seq![node] + old_ptrs;
            perms.tracked_insert(node, perm);
        }

        proof {
            assert(self.ptrs@.no_duplicates()) by {
                assert(!old_ptrs.contains(node));
                assert(old_ptrs.no_duplicates());
                assert forall|i: int, j: int|
                    0 <= i < self.ptrs@.len() && 0 <= j < self.ptrs@.len() && i != j
                    implies self.ptrs@[i] != self.ptrs@[j]
                by {
                    if i == 0 {
                        assert(self.ptrs@[j] == old_ptrs[j - 1]);
                        assert(old_ptrs.contains(old_ptrs[j - 1]));
                    } else if j == 0 {
                        assert(self.ptrs@[i] == old_ptrs[i - 1]);
                        assert(old_ptrs.contains(old_ptrs[i - 1]));
                    } else {
                        assert(self.ptrs@[i] == old_ptrs[i - 1]);
                        assert(self.ptrs@[j] == old_ptrs[j - 1]);
                    }
                };
            };

            assert forall|p: *mut BlockHdr| #[trigger] self.ptrs@.contains(p)
                implies perms.contains_key(p) && p@.addr != 0
            by {
                if p != node {
                    let i = self.ptrs@.index_of(p);
                    assert(i != 0);
                    assert(old_ptrs[i - 1] == p);
                    assert(old_ptrs.contains(p));
                }
            };

            assert forall|i: int| 0 <= i < self.ptrs@.len() implies #[trigger] self.wf_node(*perms, i) by {
                if i == 0 {
                    assert(self.ptrs@[0] == node);
                    assert(perms[node] == perm);
                    if self.ptrs@.len() > 1 {
                        assert(self.ptrs@[1] == old_ptrs[0]);
                    }
                } else {
                    assert(self.ptrs@[i] == old_ptrs[i - 1]);
                    assert(self.ptrs@[i] != node);
                    assert(perms[self.ptrs@[i]] == old(perms)[self.ptrs@[i]]);
                    assert(old(self).wf_node(*old(perms), i - 1));
                    if i + 1 < self.ptrs@.len() {
                        assert(self.ptrs@[i + 1] == old_ptrs[i]);
                    }
                }
            };

            assert(perms.dom() =~= old(perms).dom().insert(node));
        }
    }

    /// Remove the head node and return it along with its permission.
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
        let ghost old_ptrs = self.ptrs@;
        let head_ptr = self.head;
        proof { assert(old(self).wf_node(*old(perms), 0)); }
        let tracked mut perm = perms.tracked_remove(head_ptr);
        let tracked mut points_to = perm.points_to;
        let hdr = ptr_mut_read(head_ptr, Tracked(&mut points_to));
        let new_head = hdr.next;
        ptr_mut_write(head_ptr, Tracked(&mut points_to), hdr);
        proof { perm.points_to = points_to; }
        self.head = new_head;
        proof { self.ptrs@ = old_ptrs.drop_first(); }

        proof {
            assert(self.ptrs@.no_duplicates());

            assert forall|p: *mut BlockHdr| #[trigger] self.ptrs@.contains(p)
                implies perms.contains_key(p) && p@.addr != 0
            by {
                let i = self.ptrs@.index_of(p);
                assert(old_ptrs[i + 1] == p);
                assert(old_ptrs.contains(p));
                assert(p != head_ptr) by {
                    assert(old_ptrs[0] == head_ptr);
                    assert(old_ptrs.no_duplicates());
                };
            };

            assert forall|i: int| 0 <= i < self.ptrs@.len() implies #[trigger] self.wf_node(*perms, i) by {
                assert(self.ptrs@[i] == old_ptrs[i + 1]);
                assert(self.ptrs@[i] != head_ptr) by {
                    assert(old_ptrs[0] == head_ptr);
                    assert(old_ptrs.no_duplicates());
                };
                assert(perms[self.ptrs@[i]] == old(perms)[self.ptrs@[i]]);
                assert(old(self).wf_node(*old(perms), i + 1));
                if i + 1 < self.ptrs@.len() {
                    assert(self.ptrs@[i + 1] == old_ptrs[i + 2]);
                }
            };

            if self.ptrs@.len() == 0 {
                assert(old_ptrs.len() == 1);
                assert(new_head@.addr == 0);
            } else {
                assert(new_head == old_ptrs[1]);
                assert(self.ptrs@[0] == old_ptrs[1]);
            }

            assert(perms.dom() =~= old(perms).dom().remove(head_ptr));
        }
        (head_ptr, Tracked(perm))
    }

    /// Remove an arbitrary node from the list.
    //
    // TODO: structural splice proof still outstanding (carried over from
    // the original port).  Marked external_body so the surrounding example
    // verifies.  The intended implementation walks the chain to locate the
    // predecessor, then rewires it past `node`.
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
        let tracked mut perm = perms.tracked_remove(node);
        proof { self.ptrs@ = old(self).ptrs@.remove_value(node); }
        Tracked(perm)
    }
}

} // verus!
