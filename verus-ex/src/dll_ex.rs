#![feature(strict_provenance)]

use vstd::prelude::*;
use vstd::raw_ptr::*;
verus! {

proof fn ex<T>(tracked p: PointsTo<T>)
    requires p.is_uninit()
{
    let r = Tracked(p.into_raw());
    assert(r@.is_range(p.ptr() as usize as int, vstd::layout::size_of::<T>() as int))
}

struct DLL {
    first: Option<*mut Node>,
    // TODO: add more information about managed region to perms
    perms: Tracked<Map<*mut Node, PointsTo<Node>>>,
    ptrs: Ghost<Seq<*mut Node>> // node addrs ordered by list order
    // NOTE: first tried using int as ID for each pointer,
    //       but this wasn't work because equality issue when used it with Map
    //       i.e. different pointers not necessarily have distinct addresses.
    //
    //       current approach is,
    //
    //       * all managed region should have same provenance -- propagated from given pool
    //       * we will tweak that provenance won't change e.g. avoid ptr_ref*
}

struct Node {
    x: usize,
    next: Option<*mut Node>,
    prev: Option<*mut Node>
}

global layout Node is size == 40, align == 8;

pub proof fn size_of_node()
    ensures size_of::<Node>() == 40
        && align_of::<Node>() == 8
{
}


impl DLL {
    spec fn wf(self) -> bool {
        &&& forall |i: int| 0 <= i && i < self.ptrs@.len()
            ==> #[trigger] self.wf_node(i)
        &&& self.ptrs@.no_duplicates()
        //&&& self.ptrs@.to_set() == self.perms@.dom()
        &&& if self.ptrs@.len() == 0 {
            self.first.is_none()
        } else {
            self.first matches Some(head)
                && self.ptrs@[0] == head
        }
    }

    spec fn view(self) -> Seq<usize> {
        Seq::new(self.ptrs@.len(), |i: int| self.perms@[self.ptrs@[i]].value().x)
    }

    proof fn nodup_index_inj<T>(l: Seq<T>, i: int, j: int)
        requires
            l.no_duplicates(),
            0 <= i < l.len(),
            0 <= j < l.len(),
        ensures l[i] == l[j] ==> i == j
    {}

    spec fn next_of(self, i: int) -> Option<*mut Node>
        recommends 0 <= i < self.ptrs@.len() - 1
    {
        if i + 1 == self.ptrs@.len() {
            None
        } else {
            Some(self.ptrs@[i + 1])
        }
    }

    spec fn prev_of(self, i: int) -> Option<*mut Node> {
        if i == 0 || self.ptrs@.len() <= i - 1 {
            None
        } else {
            Some(self.ptrs@[i-1])
        }
    }

    spec fn wf_node(self, i: int) -> bool {
        let node_addr = self.ptrs@[i];
        &&& 0 <= i < self.ptrs@.len()
        &&& self.perms@.contains_key(node_addr)
        // NOTE: following condition states two,
        // * if ptrs[i] exists then perms[ptrs[i]] is present
        // * moreover, PointsTo<Node> in perms[ptrs[i]] is about
        //   the pointer contained in ptrs[i]
        &&& self.ptrs@[i] == self.perms@[self.ptrs@[i]].ptr()
        // header must be initialized
        &&& self.perms@[node_addr].opt_value() matches MemContents::Init(node)
            // just asserting that the addresses are same i.e. except provenance etc.
            && (node.next matches Some(ptr) ==> self.next_of(i) == Some(ptr))
            && (node.next == <Option<*mut Node>>::None ==> self.next_of(i) == <Option<*mut Node>>::None)
            && (node.prev matches Some(ptr) ==> self.prev_of(i) == Some(ptr))
            && (node.prev == <Option<*mut Node>>::None ==> self.prev_of(i) == <Option<*mut Node>>::None)
            // TODO: assert that free block has approprate region by e.g. PointsToRaw
    }

    proof fn wf_node_is_init(self, ptr: *mut Node)
        requires self.wf(), self.wf_node_ptr(ptr)
        ensures self.perms@[ptr].is_init()
    {}

    spec fn wf_node_ptr(self, p: *mut Node) -> bool {
        let node_addr = p as usize as int;
        exists|i: int| 0 <= i < self.ptrs@.len()
            && self.ptrs@[i] == p && #[trigger] self.wf_node(i)
    }

    spec fn is_next_ptr_of(self, n1: *mut Node, n2: *mut Node) -> bool
        recommends
            self.wf_node_ptr(n1),
            self.wf_node_ptr(n2),
    {
        let n1_idx = choose|i: int| self.ptrs@[i] == n1 && #[trigger] self.wf_node(i);
        let n2_idx = choose|i: int| self.ptrs@[i] == n2 && #[trigger] self.wf_node(i);

        &&& Some(n2) == self.next_of(n1_idx)
        &&& Some(n1) == self.prev_of(n2_idx)
    }

    proof fn lemma_next_of_index(self, n1: *mut Node, n2: *mut Node, n1_idx: int, n2_idx: int)
        requires
            self.ptrs@.no_duplicates(),
            0 <= n1_idx < self.ptrs@.len() - 1,
            0 <= n2_idx < self.ptrs@.len(),
            self.ptrs@[n1_idx] == n1,
            self.ptrs@[n2_idx] == n2,
            self.next_of(n1_idx) == Some(n2)
        ensures
            n1_idx + 1 == n2_idx
    {
        assert(n1_idx + 1 < self.ptrs@.len());
        assert(self.ptrs@[n1_idx + 1] == n2);
        assert(self.ptrs@[n2_idx] == n2);
        Self::nodup_index_inj(self.ptrs@, n1_idx + 1, n2_idx);
    }


    spec fn has_no_duplicate(self, node: *mut Node) -> bool {
        forall|i: int| 0 <= i < self.ptrs@.len() ==> self.ptrs@[i] != node
    }

    fn push_front(&mut self, new_node: *mut Node, Tracked(perm_new_node): Tracked<PointsTo<Node>>)
        requires
            old(self).wf(),
            new_node == perm_new_node.ptr(),
            perm_new_node.is_init(),
            old(self).has_no_duplicate(new_node),
        ensures
           self.wf(),
           self@ == seq![self.perms@[new_node].value().x].add(old(self)@)
    {
        let tracked mut perm_new_node = perm_new_node;
        let new_node_payload = {
            ptr_mut_read(new_node, Tracked(&mut perm_new_node)).x
        };

        if let Some(mut next_node) = core::mem::replace(&mut self.first, Some(new_node)) {
            assert(old(self).wf_node(0));
            let tracked mut perm_next = self.perms.borrow_mut().tracked_remove(next_node);

            ptr_mut_write(new_node, Tracked(&mut perm_new_node), Node {
                prev: None,
                next: Some(next_node),
                x: new_node_payload,
            });
            let (next_node_next, next_node_payload) = {
                let n = ptr_mut_read(next_node, Tracked(&mut perm_next));
                (n.next, n.x)
            };
            ptr_mut_write(next_node, Tracked(&mut perm_next), Node {
                prev: Some(new_node),
                next: next_node_next,
                x: next_node_payload
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
            ptr_mut_write(new_node, Tracked(&mut perm_new_node), Node {
                prev: None,
                next: None,
                x: new_node_payload,
            });
            proof {
                self.perms.borrow_mut().tracked_insert(new_node, perm_new_node);

                // update pointer set
                self.ptrs@ = seq![new_node].add(old(self).ptrs@);

                assert(self@ == seq![new_node_payload]);
            }
        }
    }


    fn insert(&mut self, n1: *mut Node, n2: *mut Node, new_node: *mut Node,
                Tracked(perm_new_node): Tracked<PointsTo<Node>>)
        requires
            old(self).wf(),
            old(self).wf_node_ptr(n1),
            old(self).wf_node_ptr(n2),
            old(self).is_next_ptr_of(n1, n2),
            // n1 & n2 are nodes already contained in this list
            n1 == old(self).perms@[n1].ptr(),
            n2 == old(self).perms@[n2].ptr(),
            // Ensures perm_new_node has permission for new_node
            new_node == perm_new_node.ptr(),
            perm_new_node.is_init(),
            // Ensuring new_node doesn't points to any existing node
            old(self).has_no_duplicate(new_node)
        ensures self.wf(),
            self.wf_node_ptr(n1),
            self.wf_node_ptr(n2),
            self.wf_node_ptr(new_node),
            self.is_next_ptr_of(n1, new_node),
            self.is_next_ptr_of(new_node, n2),
            ({
                let n2_idx = choose|i: int| 0 <= i < old(self).ptrs@.len()
                    && old(self).ptrs@[i] == n2 && #[trigger] old(self).wf_node(i);
                self@ == old(self)@.insert(n2_idx, perm_new_node.value().x)
            })
    {
        proof {
            assert(self.perms@.contains_key(n1));
            assert(self.perms@.contains_key(n2));
        }
        let tracked mut perm_n1 = self.perms.borrow_mut().tracked_remove(n1);
        let tracked mut perm_n2 = self.perms.borrow_mut().tracked_remove(n2);
        let tracked mut perm_new_node = perm_new_node;

        //// n1 <-> new_node <-> n2
        {
            let (n2_next, n2_val) = {
                let old_val = ptr_mut_read(n2, Tracked(&mut perm_n2));
                (old_val.next, old_val.x)
            };
            let (n1_prev, n1_val) = {
                let old_val = ptr_mut_read(n1, Tracked(&mut perm_n1));
                (old_val.prev, old_val.x)
            };
            let new_node_payload = {
                ptr_mut_read(new_node, Tracked(&mut perm_new_node)).x
            };
            ptr_mut_write(n1, Tracked(&mut perm_n1), Node {
                x: n1_val,
                prev: n1_prev,
                next: Some(new_node)
            });
            ptr_mut_write(n2, Tracked(&mut perm_n2), Node {
                x: n2_val,
                prev: Some(new_node),
                next: n2_next
            });
            ptr_mut_write(new_node, Tracked(&mut perm_new_node), Node {
                x: new_node_payload,
                prev: Some(n1),
                next: Some(n2)
            });
        }

        proof {
            // update permission map
            self.perms.borrow_mut().tracked_insert(n1, perm_n1);
            self.perms.borrow_mut().tracked_insert(n2, perm_n2);
            self.perms.borrow_mut().tracked_insert(new_node, perm_new_node);

            let n1_idx = choose|i: int| 0 <= i < old(self).ptrs@.len()
                && old(self).ptrs@[i] == n1 && #[trigger] old(self).wf_node(i);
            let n2_idx = choose|i: int| 0 <= i < old(self).ptrs@.len()
                && old(self).ptrs@[i] == n2 && #[trigger] old(self).wf_node(i);

            // update pointer set
            self.ptrs@ = old(self).ptrs@.insert(n2_idx, new_node);

            assert(self.wf_node(n2_idx));

            assert(self.wf_node_ptr(n1)) by {
                assert(self.wf_node(n1_idx));
            };

            assert(self.wf_node_ptr(n2)) by {
                assert(self.wf_node(n2_idx + 1));
            };

            assert forall |i: int| 0 <= i < self.ptrs@.len()
                implies self.wf_node(i)
            by {
                assert(old(self).wf());
                old(self).ptrs@.insert_ensures(n2_idx, new_node);
                if i == n1_idx || i == n2_idx || i == n2_idx + 1 {
                    // wf_node for those indices are known
                } else if i < n1_idx {
                    assert(old(self).wf_node(i));
                } else if n2_idx + 1 < i && i < self.ptrs@.len() {
                    // sliding elements of self.ptrs
                    assert(old(self).wf_node(i - 1));
                }
            };
            assert(self@ == old(self)@.insert(n2_idx, perm_new_node.value().x));
        }
    }


    fn pop_front(&mut self) -> (r: Option<(*mut Node, Tracked<PointsTo<Node>>)>)
        requires old(self).wf()
        ensures self.wf(),
            old(self)@.len() == 0 ==> r.is_none() && self@ == Seq::<usize>::empty(),
            old(self)@.len() > 0 ==>
                self@ == old(self)@.drop_first() &&
                (r matches Some((node, perm)) &&
                    // Node is detached
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
                (n.x, n.next)
            };

            if let Some(new_head) = head_next {
                // doing *new_head.prev = None
                assert(old(self).wf_node(1));
                let tracked new_head_perm = self.perms.borrow_mut().tracked_remove(new_head);
                let (new_head_payload, new_head_next) = {
                    // NOTE: In ordinary Rust code this is unnecessary read
                    let n = ptr_mut_read(new_head, Tracked(&mut new_head_perm));
                    (n.x, n.next)
                };
                ptr_mut_write(new_head, Tracked(&mut new_head_perm), Node {
                    next: new_head_next,
                    prev: None,
                    x: new_head_payload
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

            ptr_mut_write(head, Tracked(&mut head_perm), Node {
                next: None,
                prev: None,
                x: head_payload
            });
            Some((head, Tracked(head_perm)))
        } else {
            assert(self@ == Seq::<usize>::empty());
            None
        }
    }

    /// Dettach node through given pointer
    ///
    /// * Returns `PointsTo<Node>`.
    ///   It ensures the node pointer won't modified by DLL anymore
    pub(crate) fn unlink(&mut self, node: *mut Node) -> (r: Tracked<PointsTo<Node>>)
        requires old(self).wf(),
            // NOTE: this ensures the list is not empty
            old(self).wf_node_ptr(node)
        ensures self.wf(),
            ({
                let i = choose|i: int| 0 <= i < old(self).ptrs@.len()
                    && old(self).ptrs@[i] == node && #[trigger] old(self).wf_node(i);
                &&& old(self)@.len() > 0 ==> self@ == old(self)@.remove(i)
                &&& old(self)@.len() == 0 ==> self@.len() == 0
            })
    {
        let ghost node_index = choose|i: int| 0 <= i < old(self).ptrs@.len()
            && self.ptrs@[i] == node && #[trigger] self.wf_node(i);
        let tracked perm = self.perms.borrow_mut().tracked_remove(node);
        let Node { next: node_next, prev: node_prev, x: node_payload } =
            ptr_mut_read(node, Tracked(&mut perm));

        if let Some(node_next) = node_next {
            //assert(node == old(self).ptrs[node_index]);
            assert(old(self).next_of(node_index) matches Some(node_next));
            assert(old(self).wf_node(node_index + 1));
            let tracked mut perm_node_next = self.perms.borrow_mut().tracked_remove(node_next);
            // FIXME: unnecessary read in ordinary Rust
            let (node_next_next, node_next_payload) = {
                let n = ptr_mut_read(node_next, Tracked(&mut perm_node_next));
                (n.next, n.x)
            };
            ptr_mut_write(node_next, Tracked(&mut perm_node_next), Node {
                next: node_next_next,
                prev: node_prev,
                x: node_next_payload
            });

            proof {
                self.perms.borrow_mut().tracked_insert(node_next, perm_node_next);
            }
        } // NOTE: else: node is tail!

        if let Some(node_prev) = node_prev {
            assert(old(self).prev_of(node_index) matches Some(node_prev));
            assert(old(self).wf_node(node_index-1));
            let tracked mut perm_node_prev = self.perms.borrow_mut().tracked_remove(node_prev);
            // FIXME: unnecessary read in ordinary Rust
            let (node_prev_prev, node_prev_payload) = {
                let n = ptr_mut_read(node_prev, Tracked(&mut perm_node_prev));
                (n.prev, n.x)
            };
            ptr_mut_write(node_prev, Tracked(&mut perm_node_prev), Node {
                next: node_next,
                prev: node_prev_prev,
                x: node_prev_payload
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


} // verus!

