use crate::all_blocks::*;
use crate::block::*;
use crate::block_index::BlockIndex;
use crate::Tlsf;
use vstd::prelude::*;
use vstd::raw_ptr::{ptr_mut_read, ptr_mut_write, MemContents, PointsTo, PointsToRaw};
#[cfg(verus_keep_ghost)]
use vstd::relations::injective;

verus! {

    impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {

        pub(crate) closed spec fn all_freelist_wf(self) -> bool {
            &&& self.wf_shadow()
            &&& forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf() ==> self.freelist_wf(idx)
        }

        pub(crate) closed spec fn freelist_wf(self, idx: BlockIndex<FLLEN, SLLEN>) -> bool {
            self.free_list_pred(self.shadow_freelist@[idx], self.first_free[idx.0 as int][idx.1 as int])
        }

        pub(crate) closed spec fn wf_shadow(self) -> bool {
            // all wf index has corresponding freelist.
            &&& shadow_freelist_has_all_wf_index(self.shadow_freelist@)
            // pointers in freelist is not null
            &&& forall|idx: BlockIndex<FLLEN, SLLEN>, i: int|
                    idx.wf() && 0 <= i < self.shadow_freelist@.len()
                        ==> self.shadow_freelist@[idx][i]@.addr != 0
            // there is an identity injection to all_blocks
            &&& exists|pi: Pi<FLLEN, SLLEN>| self.is_ii(pi)
        }

        spec fn is_ii(self, pi: Pi<FLLEN, SLLEN>) -> bool {
            is_identity_injection(self.shadow_freelist@, self.all_blocks.ptrs@, pi)
        }


        pub(crate) closed spec fn shadow_freelist_nodup(self) -> bool {
            forall|i: BlockIndex<FLLEN, SLLEN>,
                   j: BlockIndex<FLLEN, SLLEN>,
                   k: int,
                   l: int|
                (i, k) != (j, l) &&
                i.wf() && j.wf() &&
                0 <= k < self.shadow_freelist@[i].len() &&
                0 <= l < self.shadow_freelist@[j].len()
                ==> self.shadow_freelist@[i][k] != self.shadow_freelist@[j][l]
        }

        pub(crate) proof fn wf_index_in_freelist(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires idx.wf(), self.all_freelist_wf()
            ensures
                self.freelist_wf(idx),
                self.free_list_pred(
                    self.shadow_freelist@[idx],
                    self.first_free[idx.0 as int][idx.1 as int]),
        {
        }

        /// Predicate means
        /// (1) doubly-linked list consists of all nodes in `freelist` with respect for order and
        /// (2) if the list has an element, first one is the `first`
        pub(crate) closed spec fn free_list_pred(self, freelist: Seq<*mut BlockHdr>, first: *mut BlockHdr) -> bool
            recommends self.all_blocks.wf()
        {
            &&& forall|i: int| 0 <= i < freelist.len() ==> self.wf_free_node(freelist, i)
            &&& if freelist.len() == 0 {
                first@.addr == 0
            } else {
                first@.addr != 0 && first == freelist.first()
            }
        }


        spec fn wf_free_node(self, freelist: Seq<*mut BlockHdr>, i: int) -> bool
            recommends
                self.all_blocks.wf(),
                0 <= i < freelist.len()
        {
            let node_link_ptr = get_freelink_ptr_spec(freelist[i]);
            let node_link = #[trigger] self.all_blocks.perms@[freelist[i]].free_link_perm.unwrap().value();
            &&& self.all_blocks.contains(freelist[i])
            &&& self.all_blocks.value_at(freelist[i]).is_free()
            &&& {
                ||| node_link.next_free@.addr != 0
                        ==> Some(node_link.next_free) == Self::free_next_of(freelist, i)
                ||| node_link.next_free@.addr == 0
                        ==> Self::free_next_of(freelist, i) is None
            }
            &&& {
                ||| node_link.prev_free@.addr != 0
                        ==> Self::free_prev_of(freelist, i) == Some(node_link.prev_free)
                ||| node_link.prev_free@.addr == 0
                        && Self::free_prev_of(freelist, i) is None
            }
        }

        spec fn free_next_of(ls: Seq<*mut BlockHdr>, i: int) -> Option<*mut BlockHdr> {
            if i == ls.len() - 1 {
                None
            } else {
                Some(ls[i + 1])
            }
        }

        spec fn free_prev_of(ls: Seq<*mut BlockHdr>, i: int) -> Option<*mut BlockHdr> {
            if i == 0 {
                None
            } else {
                Some(ls[i - 1])
            }
        }

        #[verifier::external_body] // debug
        pub(crate) fn unlink_free_block(&mut self,
            node: *mut BlockHdr,
            size: usize,
            Tracked(perm): Tracked<BlockPerm>)
        {
            unimplemented!()
        }

        pub(crate) fn link_free_block(&mut self,
            idx: BlockIndex<FLLEN, SLLEN>,
            node: *mut BlockHdr,
            Tracked(node_fl_pt): Tracked<&mut PointsTo<FreeLink>>)
        requires
            idx.wf(),
            old(self).all_blocks.wf(),
            old(self).all_freelist_wf(),
            !old(self).all_blocks.contains(node),
            get_freelink_ptr_spec(node) == old(node_fl_pt).ptr()
        ensures
            self.all_blocks.wf(),
            self.all_freelist_wf(),
            self.shadow_freelist@[idx] == seq![node].add(old(self).shadow_freelist@[idx])
        {
            if self.first_free[idx.0][idx.1] != null_bhdr() {
                let first_free = self.first_free[idx.0][idx.1];
                assert(self.shadow_freelist@[idx].len() != 0);
                assert(self.shadow_freelist@[idx].first() == first_free);
                assert(self.shadow_freelist@[idx].contains(first_free));
                assert(self.freelist_wf(idx));
                assert(self.all_freelist_wf());
                assert(self.wf_free_node(self.shadow_freelist@[idx], 0));
                assert(self.all_blocks.wf());
                assert(self.all_blocks.contains(first_free));
                proof {
                    self.all_blocks.lemma_contains(first_free);
                    self.all_blocks.lemma_node_is_wf(first_free);
                }
                assert(self.all_blocks.perms@.contains_key(first_free));
                assert(self.all_blocks.wf());
                let tracked first_free_perm = self.all_blocks.perms.borrow_mut().tracked_remove(first_free);
                assert(first_free_perm.wf()) by {
                    self.all_blocks.lemma_node_is_wf(first_free);
                };
                let tracked first_free_fl_pt = first_free_perm.free_link_perm.tracked_unwrap();

                // update first pointer
                Self::set_freelist(&mut self.first_free, idx, node);
                assert(old(self).shadow_freelist@[idx] == self.shadow_freelist@[idx]);

                // update link
                let link = get_freelink_ptr(first_free);
                assert(first_free == first_free_perm.points_to.ptr());
                assert(get_freelink_ptr_spec(first_free) == get_freelink_ptr_spec(first_free_perm.points_to.ptr()));
                assert(get_freelink_ptr_spec(first_free) == first_free_fl_pt.ptr());
                let link_payload = ptr_mut_read(link, Tracked(&mut first_free_fl_pt));
                ptr_mut_write(link, Tracked(&mut first_free_fl_pt), FreeLink {
                    next_free: link_payload.next_free,
                    prev_free: node
                });

                // update new node's link
                let link = get_freelink_ptr(node);
                ptr_mut_write(link, Tracked(node_fl_pt), FreeLink {
                    next_free: first_free,
                    prev_free: null_bhdr()
                });

                proof {

                    assert(old(self).shadow_freelist@.contains_key(idx));
                    assert(old(self).all_blocks.ptrs@ == self.all_blocks.ptrs@);
                    assert(ghost_pointer_ordered(old(self).all_blocks.ptrs@));
                    assert(ghost_pointer_ordered(self.all_blocks.ptrs@));

                    // New block has *new* address
                    assert forall|x: int|
                        0 <= x < self.all_blocks.ptrs@.len()
                        implies
                        node != self.all_blocks.ptrs@[x]
                        by {
                        };


                    //assume(forall|i: BlockIndex<FLLEN, SLLEN>| i.wf()
                    //==> !self.shadow_freelist@[i].contains(node));

                    // auxiliary data update
                    //self.all_blocks.perms.borrow_mut().tracked_insert(node,
                        //BlockPerm {
                            //points_to: node_pt,
                            //free_link_perm: Some(node_fl_pt),
                            //mem
                        //});
                    self.all_blocks.perms.borrow_mut().tracked_insert(first_free,
                        BlockPerm {
                            points_to: first_free_perm.points_to,
                            free_link_perm: Some(first_free_fl_pt),
                            mem: first_free_perm.mem,
                        });
                    self.all_blocks.ptrs@ = add_ghost_pointer(self.all_blocks.ptrs@, node);
                    lemma_add_ghost_pointer_ensures(old(self).all_blocks.ptrs@, node);
                    self.shadow_freelist@ = self.shadow_freelist@.insert(idx, seq![node].add(self.shadow_freelist@[idx]));

                    //lemma_sort_by_ensures
                    //assume(forall|m: int| 0 <= m < old_sls.len()
                    //==> old(self).all_blocks.perms@[old_sls[m]] == self.all_blocks.perms@[old_sls[m]]);

                    assert(self.all_blocks.ptrs@.contains(node));
                    assert(old(self).all_blocks.ptrs@.contains(first_free));
                    assert(self.all_blocks.contains(node) && self.all_blocks.contains(first_free));
                    assert(self.shadow_freelist@[idx].first() == node);
                    assert(self.shadow_freelist@[idx] == seq![node].add(old(self).shadow_freelist@[idx]));

                    self.shadow_freelist@.lemma_insert_invariant_contains(
                        old(self).shadow_freelist@[idx],
                        idx,
                        seq![node].add(old(self).shadow_freelist@[idx]));

                    assert(idx.wf() <==> self.shadow_freelist@.contains_key(idx));
                    assert(forall|i: BlockIndex<FLLEN, SLLEN>| i != idx ==> self.shadow_freelist@[i] == old(self).shadow_freelist@[i]);
                    assert(forall|i: BlockIndex<FLLEN, SLLEN>| i != idx ==>
                        self.shadow_freelist@[i] == old(self).shadow_freelist@[i]);

                    assert(forall|p: *mut BlockHdr| old(self).all_blocks.contains(p) ==> self.all_blocks.contains(p));

                    assume(self.all_blocks.wf());
                    assert(self.all_freelist_wf()) by {
                        assert forall|i: BlockIndex<FLLEN, SLLEN>| i.wf()
                            implies self.free_list_pred(
                                self.shadow_freelist@[i],
                                self.first_free[i.0 as int][i.1 as int]
                            )
                            by {
                                if i == idx {
                                    //&&& self.free_list_pred(self.shadow_freelist[i][j], self.first_free[i][j])
                                    //&&& forall|k: int| 0 <= k < self.shadow_freelist[i][j].len() ==>
                                    //self.all_blocks.contains(self.shadow_freelist[i][j][k])
                                    //assume(self.freelist_wf(idx));
                                    //assert(self.freelist_wf(i));
                                    admit();
                                } else {
                                    assert(i != idx);
                                    assert(old(self).shadow_freelist@[i] =~= self.shadow_freelist@[i]);
                                    if self.shadow_freelist@[i].len() > 0 {
                                        let sls = self.shadow_freelist@[i];
                                        let old_sls = old(self).shadow_freelist@[i];


                                        // Proof that all `p ∈ ∪_{i != idx} self.shadow_freelist[i]` agrees on `self.all_blocks.perms[p]` before and after update
                                        let stable_set = old(self).shadow_freelist@[i];


                                        let old_pi = choose|pi: Pi<FLLEN, SLLEN>| old(self).is_ii(pi);
                                        let new_pi = old(self).identity_injection_insert_new_node(old_pi, (idx, 0), node);

                                        assert(old(self).wf_shadow());
                                        old(self).lemma_link_free_block_update_identity_injection(old_pi, idx, node);
                                        assert(self.is_ii(new_pi));
                                        assert(self.wf_shadow());
                                        self.lemma_shadow_list_no_duplicates();
                                        old(self).lemma_shadow_list_contains_unique(idx, first_free);
                                        assert(!stable_set.contains(node));
                                        assert(old(self).shadow_freelist@[idx][0] == first_free);
                                        assert(!stable_set.contains(first_free));
                                        assert forall|x: int|
                                            0 <= x < stable_set.len()
                                            implies
                                            old(self).all_blocks.perms@.contains_key(stable_set[x])
                                            by {
                                                assert(old(self).wf_free_node(stable_set, x));
                                                let y = choose|y: int|
                                                    0 <= y < old(self).all_blocks.ptrs@.len() &&
                                                    old(self).all_blocks.ptrs@[y] == stable_set[x];
                                                assert(old(self).all_blocks.wf_node(y));
                                            };
                                        lemma_map_insert_agrees(
                                            stable_set,
                                            self.all_blocks.perms@,
                                            node,
                                        );

                                        lemma_map_insert_agrees(
                                            stable_set,
                                            self.all_blocks.perms@,
                                            first_free,
                                        );

                                        assert forall|n: int| 0 <= n < sls.len()
                                            implies self.wf_free_node(sls, n) by {

                                                //assert(self.wf_free_node(sls, 0));
                                                assert(old(self).wf_free_node(old_sls, n));
                                            };

                                    }
                                }
                            };

                        assume(self.wf_shadow());
                    };
                }
            } else {
                assert(self.shadow_freelist@[idx].len() == 0);
                Self::set_freelist(&mut self.first_free, idx, node);
                ptr_mut_write(get_freelink_ptr(node), Tracked(node_fl_pt), FreeLink {
                    next_free: null_bhdr(),
                    prev_free: null_bhdr()
                });
                proof {
                    admit()
                }
            }

            self.set_bit_for_index(idx);
        }

        #[verifier::external_body]
        pub(crate) fn set_freelist(
            freelist: &mut [[*mut BlockHdr; SLLEN]; FLLEN],
            idx: BlockIndex<FLLEN, SLLEN>, e: *mut BlockHdr)
            requires idx.wf()
            ensures
                freelist[idx.0 as int][idx.1 as int] == e,
                forall|i: BlockIndex<FLLEN, SLLEN>|
                    i != idx && i.wf() ==>
                        old(freelist)[i.0 as int][i.1 as int]
                            == freelist[i.0 as int][i.1 as int],
        {
            freelist[idx.0][idx.1] = e;
        }


        pub(crate) proof fn freelist_empty(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                //self.all_freelist_wf(),
                self.freelist_wf(idx),
                self.shadow_freelist@[idx].len() == 0
            ensures
                self.first_free[idx.0 as int][idx.1 as int]@.addr == 0
        {
        }

        pub(crate) proof fn freelist_nonempty(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.freelist_wf(idx),
                self.all_blocks.wf(),
                self.shadow_freelist@[idx].len() > 0
            ensures
                self.first_free[idx.0 as int][idx.1 as int]@.addr != 0,
                self.shadow_freelist@[idx].first() == self.first_free[idx.0 as int][idx.1 as int],
                self.all_blocks.contains(self.first_free[idx.0 as int][idx.1 as int])
        {
            let first = self.shadow_freelist@[idx].first();
            assert(self.free_list_pred(
                    self.shadow_freelist@[idx],
                    self.first_free[idx.0 as int][idx.1 as int]));
            assert(self.shadow_freelist@[idx].len() != 0);
            assert(forall|i: int| 0 <= i < self.shadow_freelist@[idx].len()
                ==> self.wf_free_node(self.shadow_freelist@[idx], i));
            //assert(self.first_free[idx.0 as int][idx.1 as int] matches Some(first)
                //&& self.shadow_freelist@[idx].first() == first);
            assert forall|i: int| 0 <= i < self.shadow_freelist@[idx].len() implies
                self.wf_free_node(self.shadow_freelist@[idx], i)
                    ==> self.all_blocks.contains(self.shadow_freelist@[idx][i])
            by {};
            assert forall|i: int| 0 <= i < self.shadow_freelist@[idx].len()
                implies self.all_blocks.contains(self.shadow_freelist@[idx][i]) by {
                assert(self.wf_free_node(self.shadow_freelist@[idx], i));
            };
            assert(self.shadow_freelist@[idx].all(|e| self.all_blocks.contains(e)));
            assert(self.shadow_freelist@[idx].contains(self.shadow_freelist@[idx].first()));
            assert(self.all_blocks.contains(self.shadow_freelist@[idx].first()));
        }

        pub(crate) proof fn lemma_free_block_allblock_contains(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.freelist_wf(idx),
                self.all_blocks.wf(), ensures
                forall|p: *mut BlockHdr|
                    self.shadow_freelist@[idx].contains(p)
                        ==> self.all_blocks.contains(p)
        {
            assert forall|i: int| 0 <= i < self.shadow_freelist@[idx].len()
                implies self.all_blocks.contains(self.shadow_freelist@[idx][i]) by {
                assert(self.wf_free_node(self.shadow_freelist@[idx], i));
            };
        }

        pub(crate) proof fn lemma_shadow_list_no_duplicates(self)
            requires
                self.wf_shadow(),
                self.all_blocks.wf(),
            ensures
                self.shadow_freelist_nodup()
        {
            self.all_blocks.lemma_wf_nodup();
        }

        pub(crate) proof fn lemma_shadow_list_contains_unique(self,
            idx: BlockIndex<FLLEN, SLLEN>,
            p: *mut BlockHdr)
            requires
                self.wf_shadow(),
                self.all_blocks.wf(),
                self.shadow_freelist@[idx].contains(p),
                idx.wf()
            ensures
                forall|i: BlockIndex<FLLEN, SLLEN>| i.wf() && i != idx
                    ==> !self.shadow_freelist@[i].contains(p)
        {
            self.lemma_shadow_list_no_duplicates();
        }



        // --------------------------------
        // Lemmas about identity injection
        // --------------------------------


        // updated II would look like like that
        spec fn identity_injection_insert_new_node(self,
            pi: Pi<FLLEN, SLLEN>,
            // shadow_freelist's index
            new_index: (BlockIndex<FLLEN, SLLEN>, int),
            node: *mut BlockHdr
        ) -> Pi<FLLEN, SLLEN>
            recommends
                self.is_ii(pi)
        {
            // choose all_blocks's index after inserting node
            let i = choose|i: int|
                node == add_ghost_pointer(self.all_blocks.ptrs@, node)[i];
            |index: (BlockIndex<FLLEN, SLLEN>, int)| {
                if new_index == index {
                    i
                } else {
                    if pi(index) > i {
                        pi(index) + 1
                    } else {
                        pi(index)
                    }
                }
            }
        }

        proof fn lemma_identity_injection_insert_new_node_ensures(self,
            pi: Pi<FLLEN, SLLEN>,
            // shadow_freelist's index
            new_index: (BlockIndex<FLLEN, SLLEN>, int),
            node: *mut BlockHdr)
            requires
                self.is_ii(pi),
                self.all_blocks.wf(),
            ensures ({
                let new_pi = self.identity_injection_insert_new_node(pi, new_index, node);
                let i = choose|i: int|
                    node == add_ghost_pointer(self.all_blocks.ptrs@, node)[i];

                &&& new_pi(new_index) == i
                &&& forall|index: (BlockIndex<FLLEN, SLLEN>, int)| {
                    &&& new_index != index && #[trigger] pi(index) > i ==> new_pi(index) == pi(index) + 1
                    &&& new_index != index && #[trigger] pi(index) <= i ==> new_pi(index) == pi(index)
                }
            })
        {
            lemma_add_ghost_pointer_ensures(self.all_blocks.ptrs@, node);
        }

        proof fn lemma_link_free_block_update_identity_injection(self,
            old_pi: Pi<FLLEN, SLLEN>,
            idx: BlockIndex<FLLEN, SLLEN>,
            node: *mut BlockHdr)
        requires
            self.wf_shadow(), self.all_blocks.wf(), self.is_ii(old_pi), !self.all_blocks.contains(node)
        ensures
            is_identity_injection(
                self.shadow_freelist@.insert(idx, seq![node].add(self.shadow_freelist@[idx])),
                add_ghost_pointer(self.all_blocks.ptrs@, node),
                self.identity_injection_insert_new_node(old_pi, (idx, 0), node))
        {
            let new_pi = self.identity_injection_insert_new_node(old_pi, (idx, 0), node);
            self.all_blocks.lemma_wf_nodup();
            //assert(self.
            //assert(self.all_blocks.ptrs@.no_duplicates());
            assume(add_ghost_pointer(self.all_blocks.ptrs@, node).no_duplicates());
            assert(injective(new_pi)) by {
                assert forall|x1: (BlockIndex<FLLEN, SLLEN>, int), x2: (BlockIndex<FLLEN, SLLEN>, int)|
                    #[trigger] new_pi(x1) == #[trigger] new_pi(x2)
                    implies x1 == x2
                by {
                    let x = choose|x: int| node == add_ghost_pointer(self.all_blocks.ptrs@, node)[x];
                    self.lemma_identity_injection_insert_new_node_ensures(old_pi, (idx, 0), node);
                    if x1 == (idx, 0int) {
                        assert(new_pi(x1) == x);
                        admit()
                    } else {
                        assert(injective(old_pi));
                        self.lemma_identity_injection_insert_new_node_ensures(old_pi, (idx, 0), node);
                        if old_pi(x1) > x {
                            //assert(old_pi((i, k)) + 1 == new_pi((i, k)));
                            //assert(old_pi((j, l)) + 1 == new_pi((j, l)));
                            //assert(old_pi((i, k)) == old_pi((j, l)));
                        } else {
                            //assert(old_pi((i, k)) + 1 == new_pi((i, k)));
                            assert(old_pi(x1) == new_pi(x1));
                            if old_pi(x2) > x {
                                //admit()
                            } else {
                                admit()
                            }
                            //assert(old_pi(x2) == new_pi(x2));
                            //assert(!(old_pi((j, l)) > x) ==> old_pi((j, l)) == new_pi((j, l)));
                            assume(old_pi(x2) == old_pi(x2));
                        }
                    }
                }
            };
            admit();
        }
    }

    proof fn lemma_map_insert_agrees<K, V>(
        s: Seq<K>,
        m: Map<K, V>,
        k: K,
    )
        requires
            !s.contains(k),
            forall|x: K| s.contains(x)
                ==> m.contains_key(x)
        ensures forall|x: K, v: V| s.contains(x)
            ==> m.insert(k, v).contains_key(x)
                && m[x] == m.insert(k, v)[x]
    {}
}
