use crate::all_blocks::*;
use crate::block::*;
use crate::block_index::BlockIndex;
use crate::Tlsf;
use core::hint::unreachable_unchecked;
use vstd::prelude::*;
use vstd::raw_ptr::{ptr_mut_read, ptr_mut_write, ptr_ref, MemContents, PointsTo, PointsToRaw};
#[cfg(verus_keep_ghost)]
use vstd::relations::injective;

verus! {

    impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {

        pub(crate) open spec fn all_freelist_wf(self) -> bool {
            &&& self.wf_shadow()
            &&& forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf() ==> self.freelist_wf(idx)
        }

        pub(crate) open spec fn freelist_wf(self, idx: BlockIndex<FLLEN, SLLEN>) -> bool {
            self.free_list_pred(self.shadow_freelist@.m[idx], self.first_free[idx.0 as int][idx.1 as int])
        }

        pub(crate) open spec fn wf_shadow(self) -> bool {
            // all wf index has corresponding freelist.
            &&& self.shadow_freelist@.shadow_freelist_has_all_wf_index()
            // pointers in freelist is not null
            &&& forall|idx: BlockIndex<FLLEN, SLLEN>, i: int|
                    idx.wf() && 0 <= i < self.shadow_freelist@.m.len()
                        ==> self.shadow_freelist@.m[idx][i]@.addr != 0
            // there is an identity injection to all_blocks
            &&& is_identity_injection(self.shadow_freelist@, self.all_blocks.ptrs@)
        }


        pub(crate) open spec fn shadow_freelist_nodup(self) -> bool {
            forall|i: BlockIndex<FLLEN, SLLEN>,
                   j: BlockIndex<FLLEN, SLLEN>,
                   k: int,
                   l: int|
                (i, k) != (j, l) &&
                i.wf() && j.wf() &&
                0 <= k < self.shadow_freelist@.m[i].len() &&
                0 <= l < self.shadow_freelist@.m[j].len()
                ==> self.shadow_freelist@.m[i][k] != self.shadow_freelist@.m[j][l]
        }

        pub(crate) proof fn wf_index_in_freelist(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires idx.wf(), self.all_freelist_wf()
            ensures
                self.freelist_wf(idx),
                self.free_list_pred(
                    self.shadow_freelist@.m[idx],
                    self.first_free[idx.0 as int][idx.1 as int]),
        {
        }

        /// Predicate means
        /// (1) doubly-linked list consists of all nodes in `freelist` with respect for order and
        /// (2) if the list has an element, first one is the `first`
        pub(crate) open spec fn free_list_pred(self, freelist: Seq<*mut BlockHdr>, first: *mut BlockHdr) -> bool
            recommends self.all_blocks.wf()
        {
            &&& forall|i: int| 0 <= i < freelist.len() ==> self.wf_free_node(freelist, i)
            &&& if freelist.len() == 0 {
                first@.addr == 0
            } else {
                first@.addr != 0 && first == freelist.first()
            }
        }


        pub(crate) open spec fn wf_free_node(self, freelist: Seq<*mut BlockHdr>, i: int) -> bool
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

        pub(crate) open spec fn free_next_of(ls: Seq<*mut BlockHdr>, i: int) -> Option<*mut BlockHdr> {
            if i == ls.len() - 1 {
                None
            } else {
                Some(ls[i + 1])
            }
        }

        pub(crate) open spec fn free_prev_of(ls: Seq<*mut BlockHdr>, i: int) -> Option<*mut BlockHdr> {
            if i == 0 {
                None
            } else {
                Some(ls[i - 1])
            }
        }

        //#[verifier::external_body] // debug
        pub(crate) fn unlink_free_block(&mut self,
            node: *mut BlockHdr,
            size: usize)
        {
            let link = get_freelink_ptr(node);
            let tracked node_blk = self.all_blocks.perms.borrow_mut().tracked_remove(node);
            let tracked link_perm = node_blk.free_link_perm.tracked_unwrap();

            let next_free = ptr_ref(link, Tracked(&link_perm)).next_free;
            let next_link = get_freelink_ptr(next_free);
            let tracked next_blk = self.all_blocks.perms.borrow_mut().tracked_remove(next_free);

            let prev_free = ptr_ref(link, Tracked(&link_perm)).prev_free;
            let prev_link = get_freelink_ptr(prev_free);
            let tracked prev_blk = self.all_blocks.perms.borrow_mut().tracked_remove(prev_free);

            if next_free != null_bhdr() {
                let tracked next_link_perm = next_blk.free_link_perm.tracked_unwrap();
                {
                    let n = ptr_ref(next_link, Tracked(&next_link_perm)).next_free;
                    ptr_mut_write(next_link, Tracked(&mut next_link_perm), FreeLink {
                        next_free: n,
                        prev_free: ptr_ref(link, Tracked(&link_perm)).prev_free,
                    });
                }
                proof {
                    self.all_blocks.perms.borrow_mut().tracked_insert(next_free, BlockPerm {
                        mem: next_blk.mem,
                        points_to: next_blk.points_to,
                        free_link_perm: Some(next_link_perm),
                    });
                }
            }

            if prev_free != null_bhdr() {
                let tracked prev_link_perm = prev_blk.free_link_perm.tracked_unwrap();
                {
                    let p = ptr_ref(prev_link, Tracked(&prev_link_perm)).prev_free;
                    ptr_mut_write(prev_link, Tracked(&mut prev_link_perm), FreeLink {
                        next_free: ptr_ref(link, Tracked(&link_perm)).next_free,
                        prev_free: p,
                    });
                }
                proof {
                    self.all_blocks.perms.borrow_mut().tracked_insert(prev_free, BlockPerm {
                        mem: prev_blk.mem,
                        points_to: prev_blk.points_to,
                        free_link_perm: Some(prev_link_perm),
                    });
                }
            } else {
                let idx = Self::map_floor(size).unwrap();
                let BlockIndex(fl, sl) = idx;

                Self::set_freelist(&mut self.first_free, idx, next_free);

                if next_free != null_bhdr() {
                    self.clear_bit_for_index(idx);
                }
            }
        }

        pub(crate) fn link_free_block(&mut self,
            idx: BlockIndex<FLLEN, SLLEN>,
            node: *mut BlockHdr)
        requires
            idx.wf(),
            Self::parameter_validity(),
            old(self).all_blocks.wf(),
            old(self).all_freelist_wf(),
            old(self).bitmap_sync(),
            old(self).bitmap_wf(),
            old(self).wf_shadow(),
            // this can be proved at caller side using pointer order and `phys_next_of` relation
            forall|i: BlockIndex<FLLEN, SLLEN>| i.wf()
                ==> !old(self).shadow_freelist@.m[i].contains(node),
            // we need node is wf in all_blocks
            old(self).all_blocks.contains(node),
            //get_freelink_ptr_spec(node) == old(node_fl_pt).ptr(),
            old(self).all_blocks.perms@[node].points_to.value().is_free(),
        ensures
            self.all_blocks.wf(),
            self.all_freelist_wf(),
            self.bitmap_sync(),
            self.bitmap_wf(),
            self.wf_shadow(),
            self.shadow_freelist@.m[idx] == seq![node].add(old(self).shadow_freelist@.m[idx])
        {
            proof {
                self.all_blocks.lemma_block_wf();
                self.all_blocks.lemma_node_is_wf(node);
            }
            let tracked node_blk = self.all_blocks.perms.borrow_mut().tracked_remove(node);
            assert forall|n: *mut BlockHdr| old(self).all_blocks.perms@.contains_key(n) && n != node
                implies old(self).all_blocks.perms@[n] == self.all_blocks.perms@[n]
                by {};
            assert(node_blk.free_link_perm is Some);
            let tracked node_fl_pt = node_blk.free_link_perm.tracked_unwrap();

            if self.first_free[idx.0][idx.1] != null_bhdr() {
                proof {admit()}
                let first_free = self.first_free[idx.0][idx.1];
                assert(self.freelist_wf(idx));
                assert(self.all_freelist_wf());
                assert(self.all_blocks.wf());
                assert(self.all_blocks.contains(first_free));
                proof {
                    self.all_blocks.lemma_contains(first_free);
                    //self.all_blocks.lemma_node_is_wf(first_free);
                }
                assert(self.all_blocks.perms@.contains_key(first_free));
                assert(self.all_blocks.wf());
                let tracked first_free_perm = self.all_blocks.perms.borrow_mut().tracked_remove(first_free);
                assert(first_free_perm.wf()) by {
                    //self.all_blocks.lemma_node_is_wf(first_free);
                };
                let tracked first_free_fl_pt = first_free_perm.free_link_perm.tracked_unwrap();

                // update first pointer
                Self::set_freelist(&mut self.first_free, idx, node);

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
                ptr_mut_write(link, Tracked(&mut node_fl_pt), FreeLink {
                    next_free: first_free,
                    prev_free: null_bhdr()
                });
            } else {
                assert(self.shadow_freelist@.m[idx].len() == 0);

                Self::set_freelist(&mut self.first_free, idx, node);

                assert(get_freelink_ptr_spec(node) == node_fl_pt.ptr());

                ptr_mut_write(get_freelink_ptr(node), Tracked(&mut node_fl_pt), FreeLink {
                    next_free: null_bhdr(),
                    prev_free: null_bhdr()
                });

                proof {
                    assert forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                            && old(self).all_blocks.ptrs@[i] != node
                        implies self.all_blocks.perms@[self.all_blocks.ptrs@[i]]
                            == old(self).all_blocks.perms@[self.all_blocks.ptrs@[i]]
                        by {
                            admit()
                        };
                    self.all_blocks.perms.borrow_mut().tracked_insert(node, BlockPerm {
                        points_to: node_blk.points_to,
                        free_link_perm: Some(node_fl_pt),
                        mem: node_blk.mem,
                    });
                    assert forall|n: *mut BlockHdr| old(self).all_blocks.perms@.contains_key(n) && n != node
                        implies old(self).all_blocks.perms@[n] == self.all_blocks.perms@[n]
                        by {};
                    assert(self.all_blocks.perms@.contains_key(node));
                    assert(exists|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                        && self.all_blocks.ptrs@[i] == node)
                    by {
                        assert(old(self).all_blocks.ptrs@.contains(node));
                        assert(self.all_blocks.ptrs@.contains(node));
                    };
                    let node_ind = choose|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                        && node == self.all_blocks.ptrs@[i];
                    assert(self.all_blocks.ptrs@[node_ind] == old(self).all_blocks.ptrs@[node_ind]);
                    assert(self.all_blocks.ptrs@ =~= old(self).all_blocks.ptrs@);
                    assert(node_blk.points_to == old(self).all_blocks.perms@[node].points_to);
                    assert(self.all_blocks.wf_node(node_ind)) by {
                        if 0 < node_ind < self.all_blocks.ptrs@.len() {
                            assert(self.all_blocks.phys_prev_of(node_ind) matches Some(p) &&
                                p == self.all_blocks.value_at(node).prev_phys_block) by {
                                assert(old(self).all_blocks.wf_node(node_ind));
                            };

                            assert(old(self).all_blocks.phys_next_of(node_ind) matches Some(p) &&
                                p@.addr == (node@.addr + old(self).all_blocks.value_at(node).size)) by {
                                assert(old(self).all_blocks.wf_node(node_ind));
                            };
                            assert(self.all_blocks.phys_next_of(node_ind) matches Some(p) &&
                                p@.addr == (node@.addr + self.all_blocks.value_at(node).size));
                        } else if node_ind == 0 {
                                assert(old(self).all_blocks.wf_node(0));
                        }
                    };
                    self.shadow_freelist@ =
                        self.shadow_freelist@.ii_push_for_index(
                            self.all_blocks,
                            idx,
                            node_ind);
                    assert forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                        implies self.all_blocks.wf_node(i) by {
                            if i == node_ind {
                                assert(self.all_blocks.wf_node(node_ind));
                            } else {
                                assert(old(self).all_blocks.wf_node(i));
                            }
                        };
                    assert(self.all_blocks.wf());

                    self.all_blocks.lemma_wf_nodup();

                    if old(self).shadow_freelist@.pi.values().contains(node_ind) {
                        let pi = old(self).shadow_freelist@.pi;
                        assert(exists|i: (BlockIndex<FLLEN, SLLEN>, int)| pi[i] == node_ind);
                        let i = choose|i: (BlockIndex<FLLEN, SLLEN>, int)|
                            i.0.wf() && 0 <= i.1 < old(self).shadow_freelist@.m[i.0].len() &&
                            pi[i] == node_ind;

                        assert(old(self).shadow_freelist@.m[i.0].contains(node)) by {
                            assert(old(self).shadow_freelist@.m[i.0][i.1]
                                == old(self).all_blocks.ptrs@[pi[i]]);
                        };

                        assert(false);
                    }

                    Self::lemma_ii_push_for_index_ensures(
                        old(self).shadow_freelist@,
                        old(self).all_blocks,
                        idx,
                        node_ind);
                    assert(self.wf_free_node(self.shadow_freelist@.m[idx], 0));

                    assert forall|i: BlockIndex<FLLEN, SLLEN>| idx.wf()
                        implies self.freelist_wf(i)
                    by {
                        if i == idx {
                            admit();

                        } else {
                            //assert forall|m: int| 0 <= m < old(self).shadow_freelist@.m[i].len()
                                //implies old(self).wf_free_node(old(self).shadow_freelist@.m[i], m) by {
                                    //assert((self).wf_free_node(old(self).shadow_freelist@.m[i], m));
                                    //admit();

                                //}
                            //if old(self).shadow_freelist@.m[i].len() == 0 {
                                //assert(
                            //} else if old(self).shadow_freelist@.m[i].len() > 0 {
                                //admit();
                            //}
                            assume(old(self).freelist_wf(i));
                        }
                    };
                    assert(self.all_freelist_wf());
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
                self.shadow_freelist@.m[idx].len() == 0
            ensures
                self.first_free[idx.0 as int][idx.1 as int]@.addr == 0
        {
        }

        pub(crate) proof fn freelist_nonempty(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.freelist_wf(idx),
                self.all_blocks.wf(),
                self.shadow_freelist@.m[idx].len() > 0
            ensures
                self.first_free[idx.0 as int][idx.1 as int]@.addr != 0,
                self.shadow_freelist@.m[idx].first() == self.first_free[idx.0 as int][idx.1 as int],
                self.all_blocks.contains(self.first_free[idx.0 as int][idx.1 as int])
        {
            let first = self.shadow_freelist@.m[idx].first();
            assert(self.free_list_pred(
                    self.shadow_freelist@.m[idx],
                    self.first_free[idx.0 as int][idx.1 as int]));
            assert(self.shadow_freelist@.m[idx].len() != 0);
            assert(forall|i: int| 0 <= i < self.shadow_freelist@.m[idx].len()
                ==> self.wf_free_node(self.shadow_freelist@.m[idx], i));
            //assert(self.first_free[idx.0 as int][idx.1 as int] matches Some(first)
                //&& self.shadow_freelist@.m[idx].first() == first);
            assert forall|i: int| 0 <= i < self.shadow_freelist@.m[idx].len() implies
                self.wf_free_node(self.shadow_freelist@.m[idx], i)
                    ==> self.all_blocks.contains(self.shadow_freelist@.m[idx][i])
            by {
            };
            assert forall|i: int| 0 <= i < self.shadow_freelist@.m[idx].len()
                implies self.all_blocks.contains(self.shadow_freelist@.m[idx][i]) by {
                assert(self.wf_free_node(self.shadow_freelist@.m[idx], i));
            };
            assert(self.shadow_freelist@.m[idx].all(|e| self.all_blocks.contains(e)));
            assert(self.shadow_freelist@.m[idx].contains(self.shadow_freelist@.m[idx].first()));
            assert(self.all_blocks.contains(self.shadow_freelist@.m[idx].first()));
        }

        pub(crate) proof fn lemma_free_block_allblock_contains(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.freelist_wf(idx),
                self.all_blocks.wf(), ensures
                forall|p: *mut BlockHdr|
                    self.shadow_freelist@.m[idx].contains(p)
                        ==> self.all_blocks.contains(p)
        {
            assert forall|i: int| 0 <= i < self.shadow_freelist@.m[idx].len()
                implies self.all_blocks.contains(self.shadow_freelist@.m[idx][i]) by {
                assert(self.wf_free_node(self.shadow_freelist@.m[idx], i));
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
                self.shadow_freelist@.m[idx].contains(p),
                idx.wf()
            ensures
                forall|i: BlockIndex<FLLEN, SLLEN>| i.wf() && i != idx
                    ==> !self.shadow_freelist@.m[i].contains(p)
        {
            self.lemma_shadow_list_no_duplicates();
        }

        proof fn lemma_ii_push_for_index_ensures(
            sfl: ShadowFreelist<FLLEN, SLLEN>,
            all_blocks: AllBlocks<FLLEN, SLLEN>,
            idx: BlockIndex<FLLEN, SLLEN>,
            i: int
        )
            requires
                all_blocks.ptrs@.no_duplicates(),
                !sfl.pi.values().contains(i),
                0 <= i < all_blocks.ptrs@.len(),
                sfl.shadow_freelist_has_all_wf_index(),
                is_identity_injection(sfl, all_blocks.ptrs@),
                all_blocks.wf_node(i)
            ensures ({
                let new_sfl = sfl.ii_push_for_index(all_blocks, idx, i);
                &&& is_identity_injection(new_sfl, all_blocks.ptrs@)
                &&& new_sfl.m[idx][0] == all_blocks.ptrs@[i]
            })
        {
            let old_ii = sfl.pi;
            let new_ii = sfl.ii_push_for_index(all_blocks, idx, i).pi;

            // injectivity

            // forall 0 <= i < sfl[idx].len(),  all_blocks.ptrs[sfl[idx, n]] == sfl[idx, n]

            //assert(shadow_freelist_has_all_wf_index(new_ii));
        }

    }


    // --------------------------------
    // Lemmas about identity injection
    // --------------------------------



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
    {
    }
}
