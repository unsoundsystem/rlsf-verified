use vstd::prelude::*;
use crate::{FreeBlockHdr, BlockHdr};
use vstd::raw_ptr::{MemContents, PointsTo, PointsToRaw, ptr_mut_read, ptr_mut_write};

verus! {

pub(crate) struct DLL {
    pub(crate) first: Option<*mut FreeBlockHdr>,
    // TODO: add more information about managed region to perms
    pub(crate) perms: Tracked<Map<*mut FreeBlockHdr, PointsTo<FreeBlockHdr>>>,
    pub(crate) ptrs: Ghost<Seq<*mut FreeBlockHdr>> // node addrs ordered by list order
    // NOTE: first tried using int as ID for each pointer,
    //       but this wasn't work because equality issue when used it with Map
    //       i.e. different pointers not necessarily have distinct addresses.
    //
    //       current approach assuming, all managed region should have same provenance
    //       -- propagated from given pool
}

global layout FreeBlockHdr is size == 56, align == 8;

pub(crate) proof fn size_of_node()
    ensures size_of::<FreeBlockHdr>() == 56
        && align_of::<FreeBlockHdr>() == 8
{
}


impl DLL {
    pub closed spec fn wf(self) -> bool {
        &&& forall |i: int| 0 <= i && i < self.ptrs@.len()
            ==> #[trigger] self.wf_node(i)
        &&& self.ptrs@.no_duplicates()
        &&& if self.ptrs@.len() == 0 {
            self.first.is_none()
        } else {
            self.first matches Some(head)
                && self.ptrs@[0] == head
        }
    }

    pub closed spec fn view(self) -> Seq<BlockHdr> {
        Seq::new(self.ptrs@.len(), |i: int| self.perms@[self.ptrs@[i]].value().common)
    }

    proof fn nodup_index_inj<T>(l: Seq<T>, i: int, j: int)
        requires
            l.no_duplicates(),
            0 <= i < l.len(),
            0 <= j < l.len(),
        ensures l[i] == l[j] ==> i == j
    {}

    spec fn next_of(self, i: int) -> Option<*mut FreeBlockHdr>
        recommends 0 <= i < self.ptrs@.len() - 1
    {
        if i + 1 == self.ptrs@.len() {
            None
        } else {
            Some(self.ptrs@[i + 1])
        }
    }

    spec fn prev_of(self, i: int) -> Option<*mut FreeBlockHdr> {
        if i == 0 || self.ptrs@.len() <= i - 1 {
            None
        } else {
            Some(self.ptrs@[i-1])
        }
    }

    pub closed spec fn wf_node(self, i: int) -> bool {
        let node_addr = self.ptrs@[i];
        &&& 0 <= i < self.ptrs@.len()
        &&& self.perms@.contains_key(node_addr)
        // NOTE: following condition states two,
        // * if ptrs[i] exists then perms[ptrs[i]] is present
        // * moreover, PointsTo<FreeBlockHdr> in perms[ptrs[i]] is about
        //   the pointer contained in ptrs[i]
        &&& self.ptrs@[i] == self.perms@[self.ptrs@[i]].ptr()
        // header must be initialized
        &&& self.perms@[node_addr].opt_value() matches MemContents::Init(node)
            // just asserting that the addresses are same i.e. except provenance etc.
            && (node.next_free matches Some(ptr) ==> self.next_of(i) == Some(ptr))
            && (node.next_free == <Option<*mut FreeBlockHdr>>::None ==> self.next_of(i) == <Option<*mut FreeBlockHdr>>::None)
            && (node.prev_free matches Some(ptr) ==> self.prev_of(i) == Some(ptr))
            && (node.prev_free == <Option<*mut FreeBlockHdr>>::None ==> self.prev_of(i) == <Option<*mut FreeBlockHdr>>::None)
            // TODO: assert that free block has approprate region by e.g. PointsToRaw
    }

    pub(crate) closed spec fn wf_node_ptr(self, p: *mut FreeBlockHdr) -> bool {
        let node_addr = p as usize as int;
        exists|i: int| 0 <= i < self.ptrs@.len()
            && self.ptrs@[i] == p && #[trigger] self.wf_node(i)
    }

    pub(crate) closed spec fn has_no_duplicate(self, node: *mut FreeBlockHdr) -> bool {
        forall|i: int| 0 <= i < self.ptrs@.len() ==> self.ptrs@[i] != node
    }

    pub(crate) fn push_front(&mut self, new_node: *mut FreeBlockHdr, Tracked(perm_new_node): Tracked<&mut PointsTo<FreeBlockHdr>>)
        requires
            old(self).wf(),
            new_node == perm_new_node.ptr(),
            perm_new_node.is_init(),
            old(self).has_no_duplicate(new_node),
        ensures
           self.wf(),
           self.wf_node_ptr(new_node),
           self@ == seq![self.perms@[new_node].value().common].add(old(self)@)
    {
        let tracked mut perm_new_node = perm_new_node;
        let new_node_payload = {
            ptr_mut_read(new_node, Tracked(&mut perm_new_node)).common
        };

        if let Some(mut next_node) = core::mem::replace(&mut self.first, Some(new_node)) {
            assert(old(self).wf_node(0));
            let tracked mut perm_next = self.perms.borrow_mut().tracked_remove(next_node);

            ptr_mut_write(new_node, Tracked(&mut perm_new_node), FreeBlockHdr {
                prev_free: None,
                next_free: Some(next_node),
                common: new_node_payload,
            });
            let (next_node_next, next_node_payload) = {
                let n = ptr_mut_read(next_node, Tracked(&mut perm_next));
                (n.next_free, n.common)
            };
            ptr_mut_write(next_node, Tracked(&mut perm_next), FreeBlockHdr {
                prev_free: Some(new_node),
                next_free: next_node_next,
                common: next_node_payload
            });
            proof {
                self.perms.borrow_mut().tracked_insert(next_node, perm_next);
                self.perms.borrow_mut().tracked_insert(new_node, perm_new_node);
                //
                // update pointer set
                self.ptrs@ = seq![new_node].add(old(self).ptrs@);


                assert forall |i: int| 0 <= i && i < self.ptrs@.len()
                    implies #[trigger] self.wf_node(i)
                by {
                    if i > 0 {
                        assert(old(self).wf_node(i - 1));
                    } 
                };

                assert(self@ == seq![new_node_payload].add(old(self)@));
            }
        } else {
            assert(self@.len() == 0);
            self.first = Some(new_node);
            ptr_mut_write(new_node, Tracked(&mut perm_new_node), FreeBlockHdr {
                prev_free: None,
                next_free: None,
                common: new_node_payload,
            });
            proof {
                self.perms.borrow_mut().tracked_insert(new_node, perm_new_node);

                // update pointer set
                self.ptrs@ = seq![new_node].add(old(self).ptrs@);

                assert(self@ == seq![new_node_payload]);
            }
        }
    }


    pub(crate) fn pop_front(&mut self) -> (r: Option<(*mut FreeBlockHdr, Tracked<PointsTo<FreeBlockHdr>>)>)
        requires old(self).wf()
        ensures self.wf(),
            old(self)@.len() == 0 ==> r.is_none() && self@ == Seq::<BlockHdr>::empty(),
            old(self)@.len() > 0 ==>
                self@ == old(self)@.drop_first() &&
                (r matches Some((node, perm)) &&
                    // FreeBlockHdr is detached
                    // not in ptrs/perms
                     !self.ptrs@.contains(node) && !self.perms@.contains_key(node) &&
                    // unlinked
                    perm@.ptr() == node &&
                    perm@.is_init()
                ),
    {
        if let Some(head) = self.first {
            assert(old(self).wf_node(0));
            let tracked head_perm = self.perms.borrow_mut().tracked_remove(head);
            let (head_payload, head_next) = {
                let n = ptr_mut_read(head, Tracked(&mut head_perm));
                (n.common, n.next_free)
            };

            if let Some(new_head) = head_next {
                // doing *new_head.prev_free = None
                assert(old(self).wf_node(1));
                let tracked new_head_perm = self.perms.borrow_mut().tracked_remove(new_head);
                let (new_head_payload, new_head_next) = {
                    // NOTE: In ordinary Rust code this is unnecessary read
                    let n = ptr_mut_read(new_head, Tracked(&mut new_head_perm));
                    (n.common, n.next_free)
                };
                ptr_mut_write(new_head, Tracked(&mut new_head_perm), FreeBlockHdr {
                    next_free: new_head_next,
                    prev_free: None,
                    common: new_head_payload
                });

                self.first = Some(new_head);

                proof {
                    self.perms.borrow_mut().tracked_insert(new_head, new_head_perm);
                    self.ptrs@ = old(self).ptrs@.drop_first();

                    assert forall |i: int| 0 <= i && i < self.ptrs@.len()
                        implies #[trigger] self.wf_node(i)
                    by {
                        if i > 0 {
                            assert(old(self).wf_node(i + 1));
                        } 
                    };

                    assert(self@ == old(self)@.drop_first());
                }
            } else {
                proof {
                    self.ptrs@ = self.ptrs@.drop_first();
                }
                self.first = None;

                assert(self@ == old(self)@.drop_first());
            };

            ptr_mut_write(head, Tracked(&mut head_perm), FreeBlockHdr {
                next_free: None,
                prev_free: None,
                common: head_payload
            });
            Some((head, Tracked(head_perm)))
        } else {
            assert(self@ == Seq::<BlockHdr>::empty());
            None
        }
    }

    pub(crate) closed spec fn is_empty_spec(&self) -> bool {
        self@.len() == 0
    }

    #[verifier::when_used_as_spec(is_empty_spec)]
    pub(crate) fn is_empty(&self) -> (r: bool)
        ensures r == self.is_empty_spec()
    {
        self.first.is_none()
    }

    proof fn lemma_view_empty_iff_first_none(self)
        requires self.wf()
        ensures self.first.is_none() <==> self@.len() == 0
    {}

    pub(crate) const fn empty() -> Self {
        Self {
            first: None,
            perms: Tracked(Map::tracked_empty()),
            ptrs: Ghost(Seq::<*mut FreeBlockHdr>::empty())
        }
    }


    /// Dettach node through given pointer
    ///
    /// * Returns `PointsTo<FreeBlockHdr>`.
    ///   It ensures the node pointer won't modified by DLL anymore
    /// * the contents of given pointer is forgotten
    pub(crate) fn unlink(&mut self, node: *mut FreeBlockHdr) -> (r: Tracked<PointsTo<FreeBlockHdr>>)
        requires old(self).wf(),
            // NOTE: this ensures the list is not empty
            old(self).wf_node_ptr(node)
        ensures self.wf(),
            ({
                let i = choose|i: int| 0 <= i < old(self).ptrs@.len()
                    && old(self).ptrs@[i] == node && #[trigger] old(self).wf_node(i);
                &&& old(self)@.len() > 0 ==> self@ == old(self)@.remove(i)
                    && r@.ptr() == node
                &&& old(self)@.len() == 0 ==> self@.len() == 0
            })
    {
        let ghost node_index = choose|i: int| 0 <= i < old(self).ptrs@.len()
            && self.ptrs@[i] == node && #[trigger] self.wf_node(i);
        let tracked perm = self.perms.borrow_mut().tracked_remove(node);
        let FreeBlockHdr { next_free: node_next, prev_free: node_prev, common: node_payload } =
            ptr_mut_read(node, Tracked(&mut perm));

        if let Some(node_next) = node_next {
            //assert(node == old(self).ptrs[node_index]);
            assert(old(self).next_of(node_index) matches Some(node_next));
            assert(old(self).wf_node(node_index + 1));
            let tracked mut perm_node_next = self.perms.borrow_mut().tracked_remove(node_next);
            // TODO: unnecessary read in ordinary Rust
            let (node_next_next, node_next_payload) = {
                let n = ptr_mut_read(node_next, Tracked(&mut perm_node_next));
                (n.next_free, n.common)
            };
            ptr_mut_write(node_next, Tracked(&mut perm_node_next), FreeBlockHdr {
                next_free: node_next_next,
                prev_free: node_prev,
                common: node_next_payload
            });

            proof {
                self.perms.borrow_mut().tracked_insert(node_next, perm_node_next);
            }
        } // NOTE: else: node is tail!

        if let Some(node_prev) = node_prev {
            assert(old(self).prev_of(node_index) matches Some(node_prev));
            assert(old(self).wf_node(node_index-1));
            let tracked mut perm_node_prev = self.perms.borrow_mut().tracked_remove(node_prev);
            // TODO: unnecessary read in ordinary Rust
            let (node_prev_prev, node_prev_payload) = {
                let n = ptr_mut_read(node_prev, Tracked(&mut perm_node_prev));
                (n.prev_free, n.common)
            };
            ptr_mut_write(node_prev, Tracked(&mut perm_node_prev), FreeBlockHdr {
                next_free: node_next,
                prev_free: node_prev_prev,
                common: node_prev_payload
            });

            proof {
                self.perms.borrow_mut().tracked_insert(node_prev, perm_node_prev);
                self.ptrs@ = old(self).ptrs@.remove(node_index);
                assert(self@ == old(self)@.remove(node_index));
            }
        } else {
            // NOTE: node is head! i.e. ptrs[0] == node == self.first
            assert(self.first matches Some(node));

            self.first = node_next;
            assert(node_index == 0);
            proof {
                if old(self)@.len() > 0 {
                    self.ptrs@ = old(self).ptrs@.remove(node_index);
                    assert(self@ == old(self)@.remove(node_index));
                }
            }
        }

        proof {
            assert forall|i: int| 0 <= i < self.ptrs@.len()
                implies self.wf_node(i)
            by {
                if node_index > i {
                    assert(old(self).wf_node(i));
                } else if node_index <= i {
                    assert(old(self).wf_node(i+1));
                }
            }
        }

        Tracked(perm)
    }
}

/// External interface for `core::mem::replace`
/// NOTE: It's seems to easy to verify equivalent implementation of `replace` but Verus currently
///       doesn't support interoperation between mutable references and raw pointers.
///
///       if you going to do this, confirm that Verus really compile this into *two memcpy's* ref. https://github.com/rust-lang/rust/pull/83022
pub assume_specification<T> [core::mem::replace::<T>] (dest: &mut T, src: T) -> (res: T)
    ensures
        *dest == src,
        res == *old(dest)
    opens_invariants none
    no_unwind;

}
