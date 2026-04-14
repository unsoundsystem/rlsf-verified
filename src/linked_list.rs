// vim: foldmethod=marker
use crate::all_blocks::*;
use crate::block::*;
use crate::block_index::BlockIndex;
use crate::ordered_pointer_list::*;
use crate::Tlsf;
use core::hint::unreachable_unchecked;
use vstd::prelude::*;
use vstd::raw_ptr::{ptr_mut_read, ptr_mut_write, ptr_ref, MemContents, PointsTo, PointsToRaw};
#[cfg(verus_keep_ghost)]
use vstd::relations::injective;

verus! {

use crate::*;

    impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {

        /// Primary predicate: wf_shadow + freelist_wf for all indices + free_blocks_in_freelist_except(exceptions).
        pub(crate) open spec fn all_freelist_wf_weak(self, exceptions: Set<*mut BlockHdr>) -> bool {
            &&& self.wf_shadow()
            &&& forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf() ==> self.freelist_wf(idx)
            &&& self.free_blocks_in_freelist_except(exceptions)
        }

        /// all_freelist_wf() = all_freelist_wf_weak(Set::empty()), embedding free_blocks_in_freelist.
        pub(crate) open spec fn all_freelist_wf(self) -> bool {
            self.all_freelist_wf_weak(Set::empty())
        }

        pub(crate) closed spec fn freelist_wf(self, idx: BlockIndex<FLLEN, SLLEN>) -> bool {
            let sfle = self.shadow_freelist@.m[idx];
            let first = self.first_free[idx.0 as int][idx.1 as int];
            &&& forall|i: int| 0 <= i < sfle.len() ==> self.wf_free_node(idx, i)
            &&& if sfle.len() == 0 {
                AllBlocks::<FLLEN, SLLEN>::ptr_is_null(first)
            } else {
                !AllBlocks::<FLLEN, SLLEN>::ptr_is_null(first) && first == sfle.first()
            }
        }

//        /// Predicate means
//        /// (1) doubly-linked list consists of all nodes in `freelist` with respect for order and
//        /// (2) if the list has an element, first one is the `first`
//        pub(crate) open spec fn free_list_pred(self, freelist: Seq<*mut BlockHdr>, first: *mut BlockHdr) -> bool
//            recommends self.all_blocks.wf()
//        {
//            &&& forall|i: int| 0 <= i < freelist.len() ==> self.wf_free_node(freelist, i)
//            &&& if freelist.len() == 0 {
//                first@.addr == 0
//            } else {
//                first@.addr != 0 && first == freelist.first()
//            }
//        }



        pub(crate) open spec fn wf_shadow(self) -> bool {
            // all wf index has corresponding freelist.
            &&& self.shadow_freelist@.shadow_freelist_has_all_wf_index()
            // pointers in freelist is not null (opaque to avoid trigger explosion)
            &&& self.shadow_ptrs_nonnull()
            // there is an identity injection to all_blocks
            &&& is_identity_injection(self.shadow_freelist@, self.all_blocks.ptrs@)
        }

        #[verifier::opaque]
        pub(crate) open spec fn shadow_ptrs_nonnull(self) -> bool {
            forall|idx: BlockIndex<FLLEN, SLLEN>, i: int|
                idx.wf() && 0 <= i < self.shadow_freelist@.m[idx].len()
                    ==> self.shadow_freelist@.m[idx][i]@.addr != 0
        }

        pub(crate) proof fn lemma_shadow_ptr_nonnull_at(
            self,
            idx: BlockIndex<FLLEN, SLLEN>,
            i: int,
        )
            requires
                self.wf_shadow(),
                idx.wf(),
                0 <= i < self.shadow_freelist@.m[idx].len(),
            ensures
                self.shadow_freelist@.m[idx][i]@.addr != 0
        {
            reveal(Tlsf::shadow_ptrs_nonnull);
        }

        /// shadow_freelist unchanged → shadow_ptrs_nonnull preserved
        pub(crate) proof fn lemma_shadow_ptrs_nonnull_frame(
            old_self: Self,
            new_self: Self,
        )
            requires
                old_self.shadow_ptrs_nonnull(),
                new_self.shadow_freelist == old_self.shadow_freelist,
            ensures
                new_self.shadow_ptrs_nonnull()
        {
            reveal(Tlsf::shadow_ptrs_nonnull);
        }

        /// node prepended at idx → shadow_ptrs_nonnull preserved
        pub(crate) proof fn lemma_shadow_ptrs_nonnull_after_push(
            old_self: Self,
            new_self: Self,
            idx: BlockIndex<FLLEN, SLLEN>,
            node: *mut BlockHdr,
        )
            requires
                old_self.shadow_ptrs_nonnull(),
                idx.wf(),
                node@.addr != 0,
                new_self.shadow_freelist@.m[idx] == seq![node].add(old_self.shadow_freelist@.m[idx]),
                forall|bi: BlockIndex<FLLEN, SLLEN>| #[trigger] bi.wf() && bi != idx
                    ==> new_self.shadow_freelist@.m[bi] == old_self.shadow_freelist@.m[bi],
            ensures
                new_self.shadow_ptrs_nonnull()
        {
            reveal(Tlsf::shadow_ptrs_nonnull);
            assert forall|bi: BlockIndex<FLLEN, SLLEN>, i: int|
                bi.wf() && 0 <= i < new_self.shadow_freelist@.m[bi].len()
                    implies new_self.shadow_freelist@.m[bi][i]@.addr != 0
            by {
                if bi == idx {
                    if i == 0 {
                        assert(new_self.shadow_freelist@.m[idx][0] == node);
                    } else {
                        assert(new_self.shadow_freelist@.m[idx][i]
                            == old_self.shadow_freelist@.m[idx][i - 1]);
                        reveal(Tlsf::shadow_ptrs_nonnull);
                    }
                } else {
                    assert(new_self.shadow_freelist@.m[bi][i]
                        == old_self.shadow_freelist@.m[bi][i]);
                    reveal(Tlsf::shadow_ptrs_nonnull);
                }
            };
        }

        /// head of idx removed → shadow_ptrs_nonnull preserved
        pub(crate) proof fn lemma_shadow_ptrs_nonnull_after_pop(
            old_self: Self,
            new_self: Self,
            idx: BlockIndex<FLLEN, SLLEN>,
        )
            requires
                old_self.shadow_ptrs_nonnull(),
                idx.wf(),
                old_self.shadow_freelist@.m[idx].len() > 0,
                new_self.shadow_freelist@.m[idx] == old_self.shadow_freelist@.m[idx].remove(0),
                forall|bi: BlockIndex<FLLEN, SLLEN>| #[trigger] bi.wf() && bi != idx
                    ==> new_self.shadow_freelist@.m[bi] == old_self.shadow_freelist@.m[bi],
            ensures
                new_self.shadow_ptrs_nonnull()
        {
            reveal(Tlsf::shadow_ptrs_nonnull);
            assert forall|bi: BlockIndex<FLLEN, SLLEN>, i: int|
                bi.wf() && 0 <= i < new_self.shadow_freelist@.m[bi].len()
                    implies new_self.shadow_freelist@.m[bi][i]@.addr != 0
            by {
                if bi == idx {
                    assert(new_self.shadow_freelist@.m[idx][i]
                        == old_self.shadow_freelist@.m[idx][i + 1]);
                    reveal(Tlsf::shadow_ptrs_nonnull);
                } else {
                    assert(new_self.shadow_freelist@.m[bi][i]
                        == old_self.shadow_freelist@.m[bi][i]);
                    reveal(Tlsf::shadow_ptrs_nonnull);
                }
            };
        }

        #[verifier::opaque]
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

        #[verifier::opaque]
        pub(crate) open spec fn size_class_condition(self) -> bool {
            forall|idx: BlockIndex<FLLEN, SLLEN>, i: int|
                self.shadow_freelist@.m.contains_key(idx)
                    && 0 <= i < self.shadow_freelist@.m[idx].len() ==>
                    idx == Self::map_floor_spec(
                        self.all_blocks.perms@[
                            self.shadow_freelist@.m[idx][i]
                        ].points_to.value().size as usize)
                    && idx.block_size_range().contains(
                        self.all_blocks.perms@[
                            self.shadow_freelist@.m[idx][i]
                        ].points_to.value().size as int)
        }

        /// shadow_freelist had its first element at idx removed; other indices unchanged
        #[verifier::opaque]
        pub(crate) open spec fn shadow_freelist_popped_at(
            old_sfl: ShadowFreelist<FLLEN, SLLEN>,
            new_sfl: ShadowFreelist<FLLEN, SLLEN>,
            idx: BlockIndex<FLLEN, SLLEN>,
        ) -> bool {
            new_sfl.m[idx] == old_sfl.m[idx].remove(0)
            && forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != idx
                ==> new_sfl.m[bi] == old_sfl.m[bi]
        }

        /// For all freelist entries (except allocated_block), size is unchanged between old_blocks and new_blocks
        #[verifier::opaque]
        pub(crate) open spec fn perms_size_unchanged_for_freelist(
            old_sfl: ShadowFreelist<FLLEN, SLLEN>,
            old_blocks: AllBlocks<FLLEN, SLLEN>,
            new_blocks: AllBlocks<FLLEN, SLLEN>,
            allocated_block: *mut BlockHdr,
        ) -> bool {
            forall|bi: BlockIndex<FLLEN, SLLEN>, i: int|
                bi.wf() && 0 <= i < old_sfl.m[bi].len() && old_sfl.m[bi][i] != allocated_block
                    ==> new_blocks.perms@[old_sfl.m[bi][i]].points_to.value().size
                        == old_blocks.perms@[old_sfl.m[bi][i]].points_to.value().size
        }

        pub(crate) proof fn lemma_size_class_after_pop(
            old_self: Self,
            new_self: Self,
            idx: BlockIndex<FLLEN, SLLEN>,
            allocated_block: *mut BlockHdr,
        )
            requires
                old_self.wf_shadow(),
                new_self.wf_shadow(),
                old_self.size_class_condition(),
                old_self.shadow_freelist_nodup(),
                idx.wf(),
                old_self.shadow_freelist@.m[idx].len() > 0,
                old_self.shadow_freelist@.m[idx][0] == allocated_block,
                Self::shadow_freelist_popped_at(old_self.shadow_freelist@, new_self.shadow_freelist@, idx),
                Self::perms_size_unchanged_for_freelist(old_self.shadow_freelist@, old_self.all_blocks, new_self.all_blocks, allocated_block),
            ensures
                new_self.size_class_condition()
        {
            reveal(Tlsf::size_class_condition);
            reveal(Tlsf::shadow_freelist_popped_at);
            reveal(Tlsf::perms_size_unchanged_for_freelist);
            assert forall|bi: BlockIndex<FLLEN, SLLEN>, i: int|
                new_self.shadow_freelist@.m.contains_key(bi)
                    && 0 <= i < new_self.shadow_freelist@.m[bi].len()
                implies
                    bi == Self::map_floor_spec(
                        new_self.all_blocks.perms@[new_self.shadow_freelist@.m[bi][i]].points_to.value().size as usize)
                    && bi.block_size_range().contains(
                        new_self.all_blocks.perms@[new_self.shadow_freelist@.m[bi][i]].points_to.value().size as int)
            by {
                let node = new_self.shadow_freelist@.m[bi][i];
                assert(bi.wf()) by {
                    assert(new_self.wf_shadow());
                    assert(new_self.shadow_freelist@.shadow_freelist_has_all_wf_index());
                    assert(new_self.shadow_freelist@.m.contains_key(bi) <==> bi.wf());
                };
                if bi == idx {
                    assert(new_self.shadow_freelist@.m[bi] == old_self.shadow_freelist@.m[bi].remove(0));
                    assert(node == old_self.shadow_freelist@.m[bi][i + 1]);
                    assert(node != allocated_block) by {
                        old_self.lemma_nodup_get(idx, 0, idx, i + 1);
                    };
                    assert(old_self.shadow_freelist@.m.contains_key(bi));
                    // fire trigger for perms_size_unchanged_for_freelist at (idx, i+1)
                    assert(0 <= i + 1 < old_self.shadow_freelist@.m[idx].len());
                } else {
                    assert(new_self.shadow_freelist@.m[bi] == old_self.shadow_freelist@.m[bi]);
                    assert(node == old_self.shadow_freelist@.m[bi][i]);
                    assert(node != allocated_block) by {
                        if node == allocated_block {
                            old_self.lemma_nodup_get(bi, i, idx, 0);
                            assert(false);
                        }
                    };
                    assert(old_self.shadow_freelist@.m.contains_key(bi));
                }
                assert(new_self.all_blocks.perms@[node].points_to.value().size
                    == old_self.all_blocks.perms@[node].points_to.value().size);
            };
        }

        pub(crate) proof fn lemma_size_class_perm_change_preserved(
            old_self: Self,
            new_self: Self,
            changed_block: *mut BlockHdr,
        )
            requires
                old_self.wf_shadow(),
                old_self.size_class_condition(),
                new_self.shadow_freelist@ == old_self.shadow_freelist@,
                !old_self.shadow_freelist@.contains(changed_block),
                Self::perms_size_unchanged_for_freelist(old_self.shadow_freelist@, old_self.all_blocks, new_self.all_blocks, changed_block),
            ensures
                new_self.size_class_condition()
        {
            reveal(Tlsf::size_class_condition);
            reveal(Tlsf::perms_size_unchanged_for_freelist);
            assert forall|bi: BlockIndex<FLLEN, SLLEN>, i: int|
                new_self.shadow_freelist@.m.contains_key(bi)
                    && 0 <= i < new_self.shadow_freelist@.m[bi].len()
                implies
                    bi == Self::map_floor_spec(
                        new_self.all_blocks.perms@[new_self.shadow_freelist@.m[bi][i]].points_to.value().size as usize)
                    && bi.block_size_range().contains(
                        new_self.all_blocks.perms@[new_self.shadow_freelist@.m[bi][i]].points_to.value().size as int)
            by {
                let node = new_self.shadow_freelist@.m[bi][i];
                assert(new_self.shadow_freelist@ == old_self.shadow_freelist@);
                assert(node == old_self.shadow_freelist@.m[bi][i]);
                assert(bi.wf()) by {
                    assert(old_self.wf_shadow());
                    assert(old_self.shadow_freelist@.shadow_freelist_has_all_wf_index());
                    assert(old_self.shadow_freelist@.m.contains_key(bi) <==> bi.wf());
                };
                assert(node != changed_block) by {
                    if node == changed_block {
                        assert(old_self.shadow_freelist@.m[bi].contains(changed_block));
                        assert(old_self.shadow_freelist@.contains(changed_block));
                        assert(!old_self.shadow_freelist@.contains(changed_block));
                        assert(false);
                    }
                };
                assert(old_self.shadow_freelist@.m.contains_key(bi));
                assert(new_self.all_blocks.perms@[node].points_to.value().size
                    == old_self.all_blocks.perms@[node].points_to.value().size);
            };
        }

        /// Instantiate size_class_condition for a specific (idx, i) pair.
        pub(crate) proof fn lemma_size_class_at(
            self,
            idx: BlockIndex<FLLEN, SLLEN>,
            i: int,
        )
            requires
                self.size_class_condition(),
                self.shadow_freelist@.m.contains_key(idx),
                0 <= i < self.shadow_freelist@.m[idx].len(),
            ensures
                idx == Self::map_floor_spec(
                    self.all_blocks.perms@[self.shadow_freelist@.m[idx][i]].points_to.value().size as usize),
                idx.block_size_range().contains(
                    self.all_blocks.perms@[self.shadow_freelist@.m[idx][i]].points_to.value().size as int)
        {
            reveal(Tlsf::size_class_condition);
        }

        pub(crate) proof fn wf_index_in_freelist(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires idx.wf(), self.all_freelist_wf()
            ensures
                self.freelist_wf(idx),
                //self.free_list_pred(
                    //self.shadow_freelist@.m[idx],
                    //self.first_free[idx.0 as int][idx.1 as int]),
        {
        }

        /// Bridge: extract wf_free_node(idx, n) from freelist_wf(idx).
        pub(crate) proof fn lemma_freelist_wf_extract_wf_free_node(
            self,
            idx: BlockIndex<FLLEN, SLLEN>,
            n: int,
        )
            requires
                self.freelist_wf(idx),
                idx.wf(),
                0 <= n < self.shadow_freelist@.m[idx].len(),
            ensures
                self.wf_free_node(idx, n)
        {
            reveal(Tlsf::freelist_wf);
        }

        /// Bridge: extract wf_free_node(idx, n) from all_freelist_wf().
        pub(crate) proof fn lemma_all_freelist_wf_extract_wf_free_node(
            self,
            idx: BlockIndex<FLLEN, SLLEN>,
            n: int,
        )
            requires
                self.all_freelist_wf(),
                idx.wf(),
                0 <= n < self.shadow_freelist@.m[idx].len(),
            ensures
                self.wf_free_node(idx, n)
        {
            reveal(Tlsf::freelist_wf);
        }

        /// Bridge: extract freelist_wf(idx) from all_freelist_wf_weak(exceptions).
        pub(crate) proof fn wf_weak_index_in_freelist(
            self, idx: BlockIndex<FLLEN, SLLEN>, exceptions: Set<*mut BlockHdr>)
            requires idx.wf(), self.all_freelist_wf_weak(exceptions)
            ensures self.freelist_wf(idx)
        {
        }

        /// Bridge: extract wf_free_node(idx, n) from all_freelist_wf_weak(exceptions).
        pub(crate) proof fn lemma_all_freelist_wf_weak_extract_wf_free_node(
            self,
            idx: BlockIndex<FLLEN, SLLEN>,
            n: int,
            exceptions: Set<*mut BlockHdr>,
        )
            requires
                self.all_freelist_wf_weak(exceptions),
                idx.wf(),
                0 <= n < self.shadow_freelist@.m[idx].len(),
            ensures
                self.wf_free_node(idx, n)
        {
            reveal(Tlsf::freelist_wf);
        }

        /// Bridge: extract wf_shadow() from all_freelist_wf_weak(exceptions).
        pub(crate) proof fn wf_weak_extract_wf_shadow(
            self, exceptions: Set<*mut BlockHdr>)
            requires self.all_freelist_wf_weak(exceptions)
            ensures self.wf_shadow()
        {
        }

        pub(crate) open spec fn wf_free_node(self, idx: BlockIndex<FLLEN, SLLEN>, i: int) -> bool
            recommends
                self.all_blocks.wf(),
                0 <= i < self.shadow_freelist@.m[idx].len()
        {
            let freelist = self.shadow_freelist@.m[idx];
            let node_link_ptr = get_freelink_ptr_spec(freelist[i]);
            let node_link = #[trigger] self.all_blocks.perms@[freelist[i]].free_link_perm.unwrap().value();
            &&& self.all_blocks.contains(freelist[i])
            &&& self.all_blocks.value_at(freelist[i]).is_free()
            // Glue invariants for abstract freelist
            &&& !AllBlocks::<FLLEN, SLLEN>::ptr_is_null(node_link.next_free)
                    ==> Some(node_link.next_free) == Self::free_next_of(freelist, i)
            &&& AllBlocks::<FLLEN, SLLEN>::ptr_is_null(node_link.next_free)
                    ==> Self::free_next_of(freelist, i) is None
            &&& !AllBlocks::<FLLEN, SLLEN>::ptr_is_null(node_link.prev_free)
                    ==> Self::free_prev_of(freelist, i) == Some(node_link.prev_free)
            &&& AllBlocks::<FLLEN, SLLEN>::ptr_is_null(node_link.prev_free)
                    ==> Self::free_prev_of(freelist, i) is None
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

        /// Reverse of wf_free_node with exception set:
        /// every free block in all_blocks (except those in `exceptions`) is in some shadow_freelist bucket.
        #[verifier::opaque]
        pub(crate) open spec fn free_blocks_in_freelist_except(self, exceptions: Set<*mut BlockHdr>) -> bool {
            forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                && self.all_blocks.value_at(self.all_blocks.ptrs@[i]).is_free()
                && !exceptions.contains(self.all_blocks.ptrs@[i])
                ==> self.shadow_freelist@.contains(self.all_blocks.ptrs@[i])
        }

        /// Full-strength version (no exceptions).
        pub(crate) open spec fn free_blocks_in_freelist(self) -> bool {
            self.free_blocks_in_freelist_except(Set::empty())
        }

        /// Bridge: extract that a specific free block is in the shadow_freelist.
        pub(crate) proof fn lemma_free_block_in_freelist(self, ptr: *mut BlockHdr)
            requires
                self.free_blocks_in_freelist(),
                self.all_blocks.wf(),
                self.all_blocks.contains(ptr),
                self.all_blocks.value_at(ptr).is_free(),
            ensures
                self.shadow_freelist@.contains(ptr)
        {
            reveal(Tlsf::free_blocks_in_freelist_except);
            let i = self.all_blocks.get_ptr_internal_index(ptr);
            assert(0 <= i < self.all_blocks.ptrs@.len());
            assert(self.all_blocks.ptrs@[i] == ptr);
            assert(!Set::<*mut BlockHdr>::empty().contains(ptr));
        }

        /// Weakening: free_blocks_in_freelist_except(Set::empty()) implies free_blocks_in_freelist_except(exceptions).
        pub(crate) proof fn lemma_free_blocks_weaken(self, exceptions: Set<*mut BlockHdr>)
            requires self.free_blocks_in_freelist()
            ensures self.free_blocks_in_freelist_except(exceptions)
        {
            reveal(Tlsf::free_blocks_in_freelist_except);
        }

        /// Extract: freelist_wf(idx) with empty sfl implies first_free is null.
        pub(crate) proof fn lemma_extract_first_free_null(
            &self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.freelist_wf(idx),
                self.shadow_freelist@.m[idx].len() == 0,
            ensures
                AllBlocks::<FLLEN, SLLEN>::ptr_is_null(
                    self.first_free[idx.0 as int][idx.1 as int])
        {
            reveal(Tlsf::freelist_wf);
        }

        /// Construct freelist_wf from the raw facts (empty sfl case).
        pub(crate) proof fn lemma_freelist_wf_from_empty(
            &self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.shadow_freelist@.m[idx].len() == 0,
                AllBlocks::<FLLEN, SLLEN>::ptr_is_null(
                    self.first_free[idx.0 as int][idx.1 as int]),
            ensures self.freelist_wf(idx)
        {
            reveal(Tlsf::freelist_wf);
        }

        /// Construct free_blocks_in_freelist_except when the underlying forall is already proved.
        pub(crate) proof fn lemma_free_blocks_in_freelist_except_intro(
            self, exceptions: Set<*mut BlockHdr>)
            requires
                forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                    && self.all_blocks.value_at(self.all_blocks.ptrs@[i]).is_free()
                    && !exceptions.contains(self.all_blocks.ptrs@[i])
                    ==> self.shadow_freelist@.contains(self.all_blocks.ptrs@[i]),
            ensures self.free_blocks_in_freelist_except(exceptions)
        {
            reveal(Tlsf::free_blocks_in_freelist_except);
        }

        /// Weakening from any subset: if free_blocks_in_freelist_except(s1) and s1 ⊆ s2, then free_blocks_in_freelist_except(s2).
        pub(crate) proof fn lemma_free_blocks_weaken_exceptions(self, s1: Set<*mut BlockHdr>, s2: Set<*mut BlockHdr>)
            requires
                self.free_blocks_in_freelist_except(s1),
                forall|x: *mut BlockHdr| s1.contains(x) ==> s2.contains(x),
            ensures self.free_blocks_in_freelist_except(s2)
        {
            reveal(Tlsf::free_blocks_in_freelist_except);
        }

        /// After marking a node as used (is_free→false), remove it from exception set.
        /// If old_self has free_blocks_in_freelist_except(exceptions), and new_self is the same
        /// except node is no longer free, then new_self has free_blocks_in_freelist_except(exceptions.remove(node)).
        pub(crate) proof fn lemma_free_blocks_exception_resolved(
            old_self: Self, new_self: Self,
            node: *mut BlockHdr, exceptions: Set<*mut BlockHdr>)
            requires
                old_self.free_blocks_in_freelist_except(exceptions),
                old_self.all_blocks.ptrs@ == new_self.all_blocks.ptrs@,
                !new_self.all_blocks.value_at(node).is_free(),
                new_self.shadow_freelist@ == old_self.shadow_freelist@,
                forall|i: int| 0 <= i < old_self.all_blocks.ptrs@.len()
                    && old_self.all_blocks.ptrs@[i] != node
                    ==> new_self.all_blocks.value_at(old_self.all_blocks.ptrs@[i])
                        == old_self.all_blocks.value_at(old_self.all_blocks.ptrs@[i]),
            ensures
                new_self.free_blocks_in_freelist_except(exceptions.remove(node))
        {
            reveal(Tlsf::free_blocks_in_freelist_except);
            assert forall|i: int| 0 <= i < new_self.all_blocks.ptrs@.len()
                && new_self.all_blocks.value_at(new_self.all_blocks.ptrs@[i]).is_free()
                && !exceptions.remove(node).contains(new_self.all_blocks.ptrs@[i])
                implies new_self.shadow_freelist@.contains(new_self.all_blocks.ptrs@[i])
            by {
                let ptr = new_self.all_blocks.ptrs@[i];
                if ptr == node {
                    // contradiction: node is not free in new_self
                    assert(false);
                } else {
                    assert(old_self.all_blocks.ptrs@[i] == ptr);
                    assert(new_self.all_blocks.value_at(ptr) == old_self.all_blocks.value_at(ptr));
                    assert(old_self.all_blocks.value_at(ptr).is_free());
                    assert(!exceptions.contains(ptr));
                }
            };
        }

        /// Frame: if shadow_freelist and all_blocks agree, free_blocks_in_freelist_except is preserved.
        pub(crate) proof fn lemma_free_blocks_in_freelist_except_frame(
            old_self: Self, new_self: Self, exceptions: Set<*mut BlockHdr>)
            requires
                old_self.free_blocks_in_freelist_except(exceptions),
                old_self.all_blocks.ptrs@ == new_self.all_blocks.ptrs@,
                new_self.shadow_freelist@ == old_self.shadow_freelist@,
                forall|i: int| 0 <= i < old_self.all_blocks.ptrs@.len()
                    ==> new_self.all_blocks.value_at(old_self.all_blocks.ptrs@[i])
                        == old_self.all_blocks.value_at(old_self.all_blocks.ptrs@[i]),
            ensures
                new_self.free_blocks_in_freelist_except(exceptions)
        {
            reveal(Tlsf::free_blocks_in_freelist_except);
        }

        /// Frame: if only perms changed (not values), free_blocks_in_freelist_except is preserved.
        pub(crate) proof fn lemma_free_blocks_in_freelist_except_perms_frame(
            old_self: Self, new_self: Self, exceptions: Set<*mut BlockHdr>)
            requires
                old_self.free_blocks_in_freelist_except(exceptions),
                old_self.all_blocks.ptrs@ == new_self.all_blocks.ptrs@,
                new_self.shadow_freelist@ == old_self.shadow_freelist@,
                forall|i: int| 0 <= i < old_self.all_blocks.ptrs@.len()
                    ==> new_self.all_blocks.perms@[old_self.all_blocks.ptrs@[i]].points_to
                        == old_self.all_blocks.perms@[old_self.all_blocks.ptrs@[i]].points_to,
            ensures
                new_self.free_blocks_in_freelist_except(exceptions)
        {
            reveal(Tlsf::free_blocks_in_freelist_except);
        }

        pub(crate) proof fn lemma_wf_free_node_preserve_if_not_touched(
            self,
            other: Self,
            idx: BlockIndex<FLLEN, SLLEN>,
            n: int,
        )
            requires
                idx.wf(),
                0 <= n < self.shadow_freelist@.m[idx].len(),
                self.wf_free_node(idx, n),
                self.shadow_freelist@.m[idx] == other.shadow_freelist@.m[idx],
                self.all_blocks.perms@[self.shadow_freelist@.m[idx][n]]
                    == other.all_blocks.perms@[other.shadow_freelist@.m[idx][n]],
                other.is_ii(),
            ensures
                other.wf_free_node(idx, n)
        {
            let ghost freelist = self.shadow_freelist@.m[idx];
            let ghost node = freelist[n];
            assert(other.shadow_freelist@.m[idx] == freelist);
            assert(other.shadow_freelist@.m[idx][n] == node);
            assert(other.all_blocks.perms@[node] == self.all_blocks.perms@[node]);

            assert(other.all_blocks.contains(node)) by {
                assert(0 <= n < other.shadow_freelist@.m[idx].len());
                assert(0 <= other.shadow_freelist@.pi[(idx, n)] < other.all_blocks.ptrs@.len());
                assert(other.shadow_freelist@.m[idx][n]
                    == other.all_blocks.ptrs@[other.shadow_freelist@.pi[(idx, n)]]);
                assert(other.all_blocks.ptrs@.contains(node));
            };

            assert(other.all_blocks.value_at(node).is_free());

            assert(self.all_blocks.perms@[node].free_link_perm.unwrap().value()
                == other.all_blocks.perms@[node].free_link_perm.unwrap().value());

            assert(other.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free@.addr != 0
                    ==> Some(other.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free)
                        == Self::free_next_of(other.shadow_freelist@.m[idx], n)) by {
                reveal(AllBlocks::ptr_is_null);
                assert(self.wf_free_node(idx, n));
                assert(self.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free@.addr != 0
                    ==> Some(self.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free)
                        == Self::free_next_of(self.shadow_freelist@.m[idx], n));
                assert(Self::free_next_of(other.shadow_freelist@.m[idx], n)
                    == Self::free_next_of(self.shadow_freelist@.m[idx], n));
            };
            assert(other.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free@.addr == 0
                    ==> Self::free_next_of(other.shadow_freelist@.m[idx], n) is None) by {
                reveal(AllBlocks::ptr_is_null);
                assert(self.wf_free_node(idx, n));
                assert(self.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free@.addr == 0
                    ==> Self::free_next_of(self.shadow_freelist@.m[idx], n) is None);
                assert(Self::free_next_of(other.shadow_freelist@.m[idx], n)
                    == Self::free_next_of(self.shadow_freelist@.m[idx], n));
            };
            assert(other.all_blocks.perms@[node].free_link_perm.unwrap().value().prev_free@.addr != 0
                    ==> Self::free_prev_of(other.shadow_freelist@.m[idx], n)
                        == Some(other.all_blocks.perms@[node].free_link_perm.unwrap().value().prev_free)) by {
                reveal(AllBlocks::ptr_is_null);
                assert(self.wf_free_node(idx, n));
                assert(self.all_blocks.perms@[node].free_link_perm.unwrap().value().prev_free@.addr != 0
                    ==> Self::free_prev_of(self.shadow_freelist@.m[idx], n)
                        == Some(self.all_blocks.perms@[node].free_link_perm.unwrap().value().prev_free));
                assert(Self::free_prev_of(other.shadow_freelist@.m[idx], n)
                    == Self::free_prev_of(self.shadow_freelist@.m[idx], n));
            };
            assert(other.all_blocks.perms@[node].free_link_perm.unwrap().value().prev_free@.addr == 0
                    ==> Self::free_prev_of(other.shadow_freelist@.m[idx], n) is None) by {
                reveal(AllBlocks::ptr_is_null);
                assert(self.wf_free_node(idx, n));
                assert(self.all_blocks.perms@[node].free_link_perm.unwrap().value().prev_free@.addr == 0
                    ==> Self::free_prev_of(self.shadow_freelist@.m[idx], n) is None);
                assert(Self::free_prev_of(other.shadow_freelist@.m[idx], n)
                    == Self::free_prev_of(self.shadow_freelist@.m[idx], n));
            };
        }

        pub(crate) proof fn lemma_wf_free_node_preserve_remove_head(
            self,
            other: Self,
            idx: BlockIndex<FLLEN, SLLEN>,
            n: int,
        )
            requires
                idx.wf(),
                self.shadow_freelist@.m[idx].len() > 0,
                0 < n < self.shadow_freelist@.m[idx].len() - 1,
                self.wf_free_node(idx, n + 1),
                other.shadow_freelist@.m[idx] == self.shadow_freelist@.m[idx].remove(0),
                self.all_blocks.perms@[self.shadow_freelist@.m[idx][n + 1]]
                    == other.all_blocks.perms@[other.shadow_freelist@.m[idx][n]],
                other.is_ii(),
            ensures
                other.wf_free_node(idx, n)
        {
            let ghost old_ls = self.shadow_freelist@.m[idx];
            let ghost new_ls = other.shadow_freelist@.m[idx];
            let ghost node = new_ls[n];
            assert(new_ls == old_ls.remove(0));
            assert(new_ls[n] == old_ls[n + 1]);
            assert(other.all_blocks.perms@[node] == self.all_blocks.perms@[old_ls[n + 1]]);

            assert(other.all_blocks.contains(node)) by {
                assert(0 <= n < new_ls.len());
                assert(0 <= other.shadow_freelist@.pi[(idx, n)] < other.all_blocks.ptrs@.len());
                assert(new_ls[n] == other.all_blocks.ptrs@[other.shadow_freelist@.pi[(idx, n)]]);
                assert(other.all_blocks.ptrs@.contains(node));
            };

            assert(other.all_blocks.value_at(node).is_free());

            assert(old_ls[n + 1] == node);
            assert(self.all_blocks.perms@[old_ls[n + 1]].free_link_perm.unwrap().value()
                == other.all_blocks.perms@[node].free_link_perm.unwrap().value());

            assert(other.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free@.addr != 0
                    ==> Some(other.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free)
                        == Self::free_next_of(new_ls, n)) by {
                reveal(AllBlocks::ptr_is_null);
                assert(self.wf_free_node(idx, n + 1));
                assert(self.all_blocks.perms@[old_ls[n + 1]].free_link_perm.unwrap().value().next_free@.addr != 0
                    ==> Some(self.all_blocks.perms@[old_ls[n + 1]].free_link_perm.unwrap().value().next_free)
                        == Self::free_next_of(old_ls, n + 1));
                assert(Self::free_next_of(new_ls, n) == Self::free_next_of(old_ls, n + 1));
            };

            assert(other.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free@.addr == 0
                    ==> Self::free_next_of(new_ls, n) is None) by {
                reveal(AllBlocks::ptr_is_null);
                assert(self.wf_free_node(idx, n + 1));
                assert(self.all_blocks.perms@[old_ls[n + 1]].free_link_perm.unwrap().value().next_free@.addr == 0
                    ==> Self::free_next_of(old_ls, n + 1) is None);
                assert(Self::free_next_of(new_ls, n) == Self::free_next_of(old_ls, n + 1));
            };

            assert(other.all_blocks.perms@[node].free_link_perm.unwrap().value().prev_free@.addr != 0
                    ==> Self::free_prev_of(new_ls, n)
                        == Some(other.all_blocks.perms@[node].free_link_perm.unwrap().value().prev_free)) by {
                reveal(AllBlocks::ptr_is_null);
                assert(self.wf_free_node(idx, n + 1));
                assert(self.all_blocks.perms@[old_ls[n + 1]].free_link_perm.unwrap().value().prev_free@.addr != 0
                    ==> Self::free_prev_of(old_ls, n + 1)
                        == Some(self.all_blocks.perms@[old_ls[n + 1]].free_link_perm.unwrap().value().prev_free));
                assert(Self::free_prev_of(new_ls, n) == Self::free_prev_of(old_ls, n + 1));
            };

            assert(other.all_blocks.perms@[node].free_link_perm.unwrap().value().prev_free@.addr == 0
                    ==> Self::free_prev_of(new_ls, n) is None) by {
                reveal(AllBlocks::ptr_is_null);
                assert(self.wf_free_node(idx, n + 1));
                assert(self.all_blocks.perms@[old_ls[n + 1]].free_link_perm.unwrap().value().prev_free@.addr == 0
                    ==> Self::free_prev_of(old_ls, n + 1) is None);
                assert(Self::free_prev_of(new_ls, n) == Self::free_prev_of(old_ls, n + 1));
            };
        }

        /// Bridge: given addr-form conditions for position 0, prove wf_free_node(idx, 0).
        /// Used when the new head after a pop has prev_free set to null explicitly.
        pub(crate) proof fn lemma_wf_free_node_head_from_addr_form(
            self,
            idx: BlockIndex<FLLEN, SLLEN>,
        )
            requires
                idx.wf(),
                0 < self.shadow_freelist@.m[idx].len(),
                self.all_blocks.contains(self.shadow_freelist@.m[idx][0]),
                self.all_blocks.value_at(self.shadow_freelist@.m[idx][0]).is_free(),
                self.all_blocks.perms@[self.shadow_freelist@.m[idx][0]]
                    .free_link_perm.unwrap().value().next_free@.addr != 0
                    ==> Some(self.all_blocks.perms@[self.shadow_freelist@.m[idx][0]]
                            .free_link_perm.unwrap().value().next_free)
                        == Self::free_next_of(self.shadow_freelist@.m[idx], 0),
                self.all_blocks.perms@[self.shadow_freelist@.m[idx][0]]
                    .free_link_perm.unwrap().value().next_free@.addr == 0
                    ==> Self::free_next_of(self.shadow_freelist@.m[idx], 0) is None,
                self.all_blocks.perms@[self.shadow_freelist@.m[idx][0]]
                    .free_link_perm.unwrap().value().prev_free@.addr == 0,
            ensures
                self.wf_free_node(idx, 0)
        {
            reveal(AllBlocks::ptr_is_null);
            // free_prev_of(ls, 0) is None by definition (index 0 has no predecessor)
        }

        //#[verifier::external_body] // debug
        #[inline(always)]
        pub(crate) fn unlink_free_block(&mut self,
            node: *mut BlockHdr,
            size: usize,
            Ghost(exceptions): Ghost<Set<*mut BlockHdr>>)
        requires
            Self::parameter_validity(),
            size >= GRANULARITY,
            size % GRANULARITY == 0,
            BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int),
            old(self).all_blocks.perms@[node].points_to.value().size == size,
            old(self).all_blocks.wf(),
            old(self).all_freelist_wf_weak(exceptions),
            old(self).bitmap_sync(),
            old(self).bitmap_wf(),
            old(self).size_class_condition(),
            old(self).all_blocks.contains(node),
            old(self).all_blocks.perms@[node].points_to.value().is_free(),
            !exceptions.contains(node),
        ensures
            self.all_blocks.wf(),
            self.all_freelist_wf_weak(exceptions.insert(node)),
            self.bitmap_sync(),
            self.bitmap_wf(),
            self.wf_shadow(),
            ({
                let idx = Self::map_floor_spec(size);
                let i = choose|i: int|
                    0 <= i < old(self).shadow_freelist@.m[idx].len()
                    && old(self).shadow_freelist@.m[idx][i] == node;
                self.shadow_freelist@.m[idx] == old(self).shadow_freelist@.m[idx].remove(i)
            }),
            self.all_blocks.ptrs@ == old(self).all_blocks.ptrs@,
            forall|p: *mut BlockHdr|
                old(self).all_blocks.perms@.contains_key(p) ==> (
                    self.all_blocks.perms@.contains_key(p)
                    && self.all_blocks.perms@[p].points_to == old(self).all_blocks.perms@[p].points_to
                    && self.all_blocks.perms@[p].mem == old(self).all_blocks.perms@[p].mem
                    && self.all_blocks.perms@[p].overhead_mem == old(self).all_blocks.perms@[p].overhead_mem
                    && self.all_blocks.perms@[p].pad_perm == old(self).all_blocks.perms@[p].pad_perm
                ),
            // After unlinking, node is not in any freelist bucket
            !self.shadow_freelist@.contains(node),
            self.size_class_condition(),
            // Other freelist buckets are unchanged
            forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != Self::map_floor_spec(size)
                ==> self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi],
        {
            vstd::layout::layout_for_type_is_valid::<BlockHdr>();
            proof {
                broadcast use VERUS_layout_of_BlockHdr;
                assert(size_of::<BlockHdr>() as int <= GRANULARITY as int);
            }
            let idx = match Self::map_floor(size) {
                Some(v) => v,
                None => unsafe { core::hint::unreachable_unchecked() },
            };
            // Prove membership: node is in shadow_freelist@.m[idx]
            proof {
                // Step 1: free block → in shadow_freelist (some bucket)
                // We have free_blocks_in_freelist_except(exceptions) and node is free.
                // node is not in exceptions (it was not yet unlinked, exceptions tracks already-unlinked blocks)
                // But node.is_free() and all_blocks.contains(node), so if node ∉ exceptions,
                // then shadow_freelist contains node.
                reveal(Tlsf::free_blocks_in_freelist_except);
                let node_i = self.all_blocks.get_ptr_internal_index(node);
                assert(0 <= node_i < self.all_blocks.ptrs@.len());
                assert(self.all_blocks.ptrs@[node_i] == node);
                // node ∉ exceptions from precondition
                assert(self.shadow_freelist@.contains(node));

                // Step 2: choose the actual bucket
                let actual_bi: BlockIndex<FLLEN, SLLEN> = choose|bi: BlockIndex<FLLEN, SLLEN>|
                    bi.wf() && self.shadow_freelist@.m[bi].contains(node);
                let j: int = choose|j: int|
                    0 <= j < self.shadow_freelist@.m[actual_bi].len()
                    && self.shadow_freelist@.m[actual_bi][j] == node;

                // Step 3: size_class_condition → actual_bi == map_floor_spec(node.size)
                self.lemma_size_class_at(actual_bi, j);
                // Now: actual_bi == map_floor_spec(node.size as usize)
                // And: idx == map_floor_spec(size) from map_floor postcondition
                // And: node.size == size from precondition
                // Therefore: actual_bi == idx
                assert(self.shadow_freelist@.m[idx].contains(node));
                // Overflow bound for get_freelink_ptr(node)
                self.all_blocks.lemma_wf_free_ptr_hdr_bound(node_i);
            }
            let link = get_freelink_ptr(node);
            proof {
                old(self).wf_weak_index_in_freelist(idx, exceptions);
                old(self).lemma_free_block_allblock_contains(idx);
                assert(old(self).all_blocks.contains(node));
                old(self).all_blocks.lemma_contains(node);
                assert(self.all_blocks.perms@.contains_key(node));
            }
            let tracked node_blk = self.all_blocks.perms.borrow_mut().tracked_remove(node);
            proof {
                // node is free → free_link_perm is Some (from BlockPerm::wf)
                let ghost node_ai = old(self).all_blocks.get_ptr_internal_index(node);
                old(self).all_blocks.lemma_wf_perm_wf(node_ai);
                assert(old(self).all_blocks.perms@[node].wf());
                assert(old(self).all_blocks.perms@[node].points_to.value().is_free());
                assert(node_blk.free_link_perm is Some);
            }
            let tracked link_perm = node_blk.free_link_perm.tracked_unwrap();
            let ghost i = choose|i: int|
                0 <= i < old(self).shadow_freelist@.m[idx].len()
                && old(self).shadow_freelist@.m[idx][i] == node;
            proof {
                assert(old(self).wf_free_node(idx, i));
                assert(link_perm.ptr() == link) by {
                    assert(link == get_freelink_ptr_spec(node));
                };
                // link_perm.is_init() from BlockPerm::wf()
                assert(link_perm.is_init());
            }

            let next_free = ptr_ref(link, Tracked(&link_perm)).next_free;
            let prev_free = ptr_ref(link, Tracked(&link_perm)).prev_free;

            if next_free != null_bhdr() {
                proof {
                    // Overflow bound for get_freelink_ptr(next_free)
                    reveal(AllBlocks::ptr_is_null);
                    assert(old(self).wf_free_node(idx, i));
                    assert(Some(next_free) == Self::free_next_of(old(self).shadow_freelist@.m[idx], i));
                    assert(i < old(self).shadow_freelist@.m[idx].len() - 1);
                    assert(old(self).shadow_freelist@.m[idx][i + 1] == next_free);
                    assert(old(self).all_blocks.contains(next_free));
                    let ghost nf_ai = old(self).all_blocks.get_ptr_internal_index(next_free);
                    assert(old(self).wf_free_node(idx, i + 1));
                    old(self).all_blocks.lemma_wf_free_ptr_hdr_bound(nf_ai);
                }
                let next_link = get_freelink_ptr(next_free);
                proof {
                    reveal(AllBlocks::ptr_is_null);
                    assert(old(self).wf_free_node(idx, i));
                    assert(Some(next_free) == Self::free_next_of(old(self).shadow_freelist@.m[idx], i));
                    assert(i < old(self).shadow_freelist@.m[idx].len() - 1);
                    assert(old(self).shadow_freelist@.m[idx][i + 1] == next_free);
                    // next_free != node (positions i+1 vs i in no-dup list)
                    old(self).lemma_shadow_list_no_duplicates();
                    old(self).lemma_nodup_get(idx, i + 1, idx, i);
                    assert(next_free != node);
                    assert(old(self).all_blocks.contains(next_free));
                    old(self).all_blocks.lemma_contains(next_free);
                    assert(self.all_blocks.perms@.contains_key(next_free));
                }
                let tracked next_blk = self.all_blocks.perms.borrow_mut().tracked_remove(next_free);
                proof {
                    // next_free is free → free_link_perm is Some
                    let ghost nf_ai = old(self).all_blocks.get_ptr_internal_index(next_free);
                    old(self).all_blocks.lemma_wf_perm_wf(nf_ai);
                    assert(old(self).all_blocks.perms@[next_free].wf());
                    assert(old(self).wf_free_node(idx, i + 1));
                    assert(old(self).all_blocks.value_at(next_free).is_free());
                    assert(next_blk.free_link_perm is Some);
                }
                let tracked next_link_perm = next_blk.free_link_perm.tracked_unwrap();
                proof {
                    assert(next_link_perm.ptr() == next_link) by {
                        assert(next_link == get_freelink_ptr_spec(next_free));
                    };
                    assert(next_link_perm.is_init());
                }
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
                        overhead_mem: next_blk.overhead_mem,
                        pad_perm: next_blk.pad_perm,
                    });
                }
            }

            if prev_free != null_bhdr() {
                proof {
                    // Overflow bound for get_freelink_ptr(prev_free)
                    reveal(AllBlocks::ptr_is_null);
                    assert(old(self).wf_free_node(idx, i));
                    assert(Self::free_prev_of(old(self).shadow_freelist@.m[idx], i) == Some(prev_free));
                    assert(0 < i);
                    assert(old(self).shadow_freelist@.m[idx][i - 1] == prev_free);
                    assert(old(self).all_blocks.contains(prev_free));
                    let ghost pf_ai = old(self).all_blocks.get_ptr_internal_index(prev_free);
                    assert(old(self).wf_free_node(idx, i - 1));
                    old(self).all_blocks.lemma_wf_free_ptr_hdr_bound(pf_ai);
                }
                let prev_link = get_freelink_ptr(prev_free);
                proof {
                    reveal(AllBlocks::ptr_is_null);
                    assert(old(self).wf_free_node(idx, i));
                    assert(Self::free_prev_of(old(self).shadow_freelist@.m[idx], i) == Some(prev_free));
                    assert(0 < i);
                    assert(old(self).shadow_freelist@.m[idx][i - 1] == prev_free);
                    assert(old(self).all_blocks.contains(prev_free));
                    old(self).all_blocks.lemma_contains(prev_free);
                    // prev_free != node (positions i-1 vs i in no-dup list)
                    old(self).lemma_shadow_list_no_duplicates();
                    old(self).lemma_nodup_get(idx, i - 1, idx, i);
                    assert(prev_free != node);
                    assert(self.all_blocks.perms@.contains_key(prev_free));
                }
                let tracked prev_blk = self.all_blocks.perms.borrow_mut().tracked_remove(prev_free);
                proof {
                    // prev_free is free → free_link_perm is Some
                    let ghost pf_ai = old(self).all_blocks.get_ptr_internal_index(prev_free);
                    old(self).all_blocks.lemma_wf_perm_wf(pf_ai);
                    assert(old(self).all_blocks.perms@[prev_free].wf());
                    assert(old(self).wf_free_node(idx, i - 1));
                    assert(old(self).all_blocks.value_at(prev_free).is_free());
                    assert(prev_blk.free_link_perm is Some);
                }
                let tracked prev_link_perm = prev_blk.free_link_perm.tracked_unwrap();
                proof {
                    assert(prev_link_perm.ptr() == prev_link) by {
                        assert(prev_link == get_freelink_ptr_spec(prev_free));
                    };
                    assert(prev_link_perm.is_init());
                }
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
                        overhead_mem: prev_blk.overhead_mem,
                        pad_perm: prev_blk.pad_perm,
                    });
                }
            } else {
                self.set_freelist(idx, next_free);

                if next_free == null_bhdr() {
                    self.clear_bit_for_sl(idx);
                }
            }

            // Re-insert node's perm (points_to and mem preserved, free_link_perm same as before)
            proof {
                self.all_blocks.perms.borrow_mut().tracked_insert(node, BlockPerm {
                    points_to: node_blk.points_to,
                    free_link_perm: Some(link_perm),
                    mem: node_blk.mem,
                    overhead_mem: node_blk.overhead_mem,
                    pad_perm: node_blk.pad_perm,
                });
            }

            // Shadow freelist ghost assignment
            proof {
                old(self).all_blocks.lemma_wf_nodup();
                Self::lemma_ii_remove_for_index_ensures(
                    old(self).shadow_freelist@,
                    old(self).all_blocks,
                    idx,
                    i);
                self.shadow_freelist@ =
                    old(self).shadow_freelist@.ii_remove_for_index(
                        old(self).all_blocks, idx, i);
            }

            // Prove all_blocks.wf()
            proof {
                reveal(AllBlocks::ptr_is_null);

                // Establish perms@ frame: for all ptrs, points_to and mem preserved
                assert forall|p: *mut BlockHdr|
                    old(self).all_blocks.perms@.contains_key(p)
                    implies self.all_blocks.perms@.contains_key(p)
                        && self.all_blocks.perms@[p].points_to
                            == old(self).all_blocks.perms@[p].points_to
                        && self.all_blocks.perms@[p].mem
                            == old(self).all_blocks.perms@[p].mem
                by {};

                assert(self.all_blocks.wf()) by {
                    assert forall|j: int| 0 <= j < self.all_blocks.ptrs@.len()
                        implies self.all_blocks.wf_node(j)
                    by {
                        let ptr = self.all_blocks.ptrs@[j];
                        assert(old(self).all_blocks.perms@.contains_key(ptr)) by {
                            old(self).all_blocks.lemma_wf_extract_node(j);
                        };
                        assert(self.all_blocks.perms@.contains_key(ptr));
                        if (next_free@.addr != 0 && ptr == next_free)
                            || (prev_free@.addr != 0 && ptr == prev_free) {
                            // These nodes had free_link_perm modified
                            old(self).all_blocks.lemma_wf_extract_node(j);
                            old(self).all_blocks.lemma_wf_glue_facts(j);
                            old(self).all_blocks.lemma_wf_structural_facts(j);
                            old(self).all_blocks.lemma_wf_perm_wf(j);
                            self.all_blocks.lemma_construct_wf_node_glue(j);
                            self.all_blocks.lemma_construct_wf_node_structural(j);
                        } else {
                            // node and all other nodes: perm unchanged
                            old(self).all_blocks.lemma_wf_extract_node(j);
                            assert(self.all_blocks.perms@[ptr]
                                == old(self).all_blocks.perms@[ptr]);
                            if old(self).all_blocks.value_at(ptr).is_free()
                                && old(self).all_blocks.phys_next_of(j) is Some {
                                let next_ptr = old(self).all_blocks.phys_next_of(j).unwrap();
                                assert(self.all_blocks.perms@[next_ptr].points_to
                                    == old(self).all_blocks.perms@[next_ptr].points_to);
                            }
                            AllBlocks::<FLLEN, SLLEN>::lemma_transfer_wf_node(
                                &old(self).all_blocks, &self.all_blocks, j, j);
                        }
                    }
                    AllBlocks::<FLLEN, SLLEN>::lemma_pool_size_bounded_transfer(
                        &old(self).all_blocks, &self.all_blocks);
                    self.all_blocks.lemma_wf_from_nodes();
                };
            }

            // Prove free_blocks_in_freelist_except(exceptions.insert(node))
            proof {
                // node is not in any other bucket
                old(self).lemma_shadow_list_contains_unique(idx, node);

                assert(self.free_blocks_in_freelist_except(exceptions.insert(node))) by {
                    reveal(Tlsf::free_blocks_in_freelist_except);
                    assert forall|j: int| 0 <= j < self.all_blocks.ptrs@.len()
                        && self.all_blocks.value_at(self.all_blocks.ptrs@[j]).is_free()
                        && !exceptions.insert(node).contains(self.all_blocks.ptrs@[j])
                        implies self.shadow_freelist@.contains(self.all_blocks.ptrs@[j])
                    by {
                        let ptr = self.all_blocks.ptrs@[j];
                        assert(ptr != node);
                        assert(!exceptions.contains(ptr));
                        // perms unchanged for all ptrs
                        assert(self.all_blocks.perms@[ptr].points_to
                            == old(self).all_blocks.perms@[ptr].points_to);
                        assert(old(self).all_blocks.value_at(old(self).all_blocks.ptrs@[j]).is_free());
                        assert(old(self).free_blocks_in_freelist_except(exceptions));
                        reveal(Tlsf::free_blocks_in_freelist_except);
                        assert(old(self).shadow_freelist@.contains(ptr));
                        // ptr was in old shadow_freelist at some (bi, k).
                        // If bi != idx: m[bi] unchanged, so still contains ptr.
                        // If bi == idx: ptr != node, so ptr is still in m[idx].remove(i).
                        let bi = choose|bi: BlockIndex<FLLEN, SLLEN>|
                            bi.wf() && old(self).shadow_freelist@.m[bi].contains(ptr);
                        if bi != idx {
                            assert(self.shadow_freelist@.m[bi].contains(ptr));
                        } else {
                            // ptr is in old m[idx] at some position k != i
                            let k = choose|k: int|
                                0 <= k < old(self).shadow_freelist@.m[idx].len()
                                && old(self).shadow_freelist@.m[idx][k] == ptr;
                            old(self).lemma_shadow_list_no_duplicates();
                            old(self).lemma_nodup_get(idx, k, idx, i);
                            assert(k != i);
                            // After remove(i), ptr is still in the list
                            if k < i {
                                assert(self.shadow_freelist@.m[idx][k] == ptr);
                            } else {
                                assert(self.shadow_freelist@.m[idx][k - 1] == ptr);
                            }
                            assert(self.shadow_freelist@.m[idx].contains(ptr));
                        }
                        assert(self.shadow_freelist@.contains(ptr));
                    };
                };
            }

            // Prove freelist_wf for all indices
            proof {
                assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf()
                    implies self.freelist_wf(bi)
                by {
                    reveal(Tlsf::freelist_wf);
                    if bi != idx {
                        // m[bi] unchanged, first_free[bi] unchanged, perms preserved
                        assert forall|k: int| 0 <= k < self.shadow_freelist@.m[bi].len()
                            implies self.wf_free_node(bi, k)
                        by {
                            assert(old(self).wf_free_node(bi, k));
                        };
                    } else {
                        // m[idx] = old_m.remove(i)
                        let old_m = old(self).shadow_freelist@.m[idx];
                        let new_m = self.shadow_freelist@.m[idx];
                        assert(new_m == old_m.remove(i));
                        reveal(AllBlocks::ptr_is_null);

                        assert forall|k: int| 0 <= k < new_m.len()
                            implies self.wf_free_node(idx, k)
                        by {
                            let old_k = if k < i { k } else { k + 1 };
                            assert(new_m[k] == old_m[old_k]);
                            assert(old(self).wf_free_node(idx, old_k));

                            // Node at new position k: prove link pointers match new list
                            let ptr = new_m[k];
                            assert(self.all_blocks.contains(ptr));
                            assert(self.all_blocks.value_at(ptr).is_free());

                            // Case split on whether this node's links were modified
                            if k == i - 1 && !AllBlocks::<FLLEN, SLLEN>::ptr_is_null(prev_free) {
                                // This is prev_free — its next_free link was updated
                                assert(ptr == prev_free);
                                // prev_free != node already proved
                                // prev_free != next_free when both non-null
                                if !AllBlocks::<FLLEN, SLLEN>::ptr_is_null(next_free) {
                                    assert(i + 1 < old_m.len() as int);
                                    old(self).lemma_nodup_get(idx, i - 1, idx, i + 1);
                                    assert(prev_free != next_free);
                                }
                                // Map entry for prev_free is the one we tracked_insert-ed
                                // (not clobbered by node re-insertion since prev_free != node)

                                // next in new list
                                if k < new_m.len() - 1 {
                                    assert(Self::free_next_of(new_m, k) == Some(new_m[k + 1]));
                                    assert(new_m[k + 1] == old_m[k + 2]);
                                    assert(old_m[k + 2] == old_m[i + 1]);
                                    assert(old_m[i + 1] == next_free);
                                }
                                // prev in new list: unchanged from old
                            } else if k == i && !AllBlocks::<FLLEN, SLLEN>::ptr_is_null(next_free) {
                                // This is next_free — its prev_free link was updated
                                assert(ptr == next_free);
                                assert(old_k == i + 1);
                                // next_free != node already proved
                                // next_free != prev_free when both non-null
                                if !AllBlocks::<FLLEN, SLLEN>::ptr_is_null(prev_free) {
                                    assert(0 <= i - 1);
                                    old(self).lemma_nodup_get(idx, i + 1, idx, i - 1);
                                    assert(next_free != prev_free);
                                }
                                // Map entry for next_free is the one we tracked_insert-ed
                                // (not clobbered by prev_free or node operations)

                                // prev in new list
                                if k > 0 {
                                    assert(Self::free_prev_of(new_m, k) == Some(new_m[k - 1]));
                                    assert(new_m[k - 1] == old_m[k - 1]);
                                    assert(old_m[k - 1] == old_m[i - 1]);
                                    assert(old_m[i - 1] == prev_free);
                                }
                                // next in new list: unchanged from old
                            } else {
                                // Unmodified node: perms unchanged
                                // Help solver: ptr is distinct from all modified nodes
                                assert(ptr != node) by {
                                    old(self).lemma_nodup_get(idx, old_k, idx, i);
                                };
                                // ptr is also distinct from next_free and prev_free
                                // (the only other keys whose Map entries were modified)
                                if !AllBlocks::<FLLEN, SLLEN>::ptr_is_null(next_free) {
                                    // old_k != i+1 because in else case,
                                    // k < i => old_k = k <= i-2, or k > i => old_k = k+1 >= i+2
                                    assert(i + 1 < old_m.len() as int) by {
                                        assert(!AllBlocks::<FLLEN, SLLEN>::ptr_is_null(next_free));
                                        assert(old(self).wf_free_node(idx, i));
                                    };
                                    old(self).lemma_nodup_get(idx, old_k, idx, i + 1);
                                    assert(ptr != next_free);
                                }
                                if !AllBlocks::<FLLEN, SLLEN>::ptr_is_null(prev_free) {
                                    // old_k != i-1 because in else case,
                                    // k < i => k != i-1 => old_k = k <= i-2, or k > i => old_k >= i+2
                                    assert(0 <= i - 1) by {
                                        assert(!AllBlocks::<FLLEN, SLLEN>::ptr_is_null(prev_free));
                                        assert(old(self).wf_free_node(idx, i));
                                    };
                                    old(self).lemma_nodup_get(idx, old_k, idx, i - 1);
                                    assert(ptr != prev_free);
                                }
                                // Map entry is unchanged since ptr != node, next_free, prev_free
                                assert(self.all_blocks.perms@[ptr]
                                    == old(self).all_blocks.perms@[ptr]);

                                // free_next_of: same physical neighbor
                                if k < new_m.len() - 1 {
                                    assert(Self::free_next_of(new_m, k)
                                        == Self::free_next_of(old_m, old_k));
                                }
                                if k == new_m.len() - 1 {
                                    if old_k == old_m.len() - 1 {
                                        assert(Self::free_next_of(new_m, k) is None);
                                        assert(Self::free_next_of(old_m, old_k) is None);
                                    } else {
                                        assert(old_k + 1 == i);
                                    }
                                }
                                // free_prev_of: same physical neighbor
                                if k > 0 {
                                    assert(Self::free_prev_of(new_m, k)
                                        == Self::free_prev_of(old_m, old_k));
                                }
                                if k == 0 {
                                    assert(Self::free_prev_of(new_m, k) is None);
                                    assert(Self::free_prev_of(old_m, old_k) is None);
                                }
                            }
                        };

                        // first_free matches
                        if AllBlocks::<FLLEN, SLLEN>::ptr_is_null(prev_free) {
                            // i == 0: set_freelist(idx, next_free)
                            if new_m.len() == 0 {
                            } else {
                                assert(new_m.first() == next_free);
                            }
                        }
                    }
                };
            }

            // Prove wf_shadow
            proof {
                // is_identity_injection: from lemma_ii_remove_for_index_ensures
                assert(is_identity_injection(self.shadow_freelist@, self.all_blocks.ptrs@));

                // shadow_freelist_has_all_wf_index: preserved by ii_remove
                assert(self.shadow_freelist@.shadow_freelist_has_all_wf_index()) by {
                    assert forall|bi: BlockIndex<FLLEN, SLLEN>|
                        self.shadow_freelist@.m.contains_key(bi) <==> bi.wf()
                    by {
                        assert(self.shadow_freelist@.m.contains_key(bi)
                            == old(self).shadow_freelist@.m.contains_key(bi));
                    };
                };

                // shadow_ptrs_nonnull: all remaining elements were already nonnull
                assert(self.shadow_ptrs_nonnull()) by {
                    reveal(Tlsf::shadow_ptrs_nonnull);
                    assert(old(self).shadow_ptrs_nonnull()) by {
                        assert(old(self).wf_shadow());
                    };
                    assert forall|bi: BlockIndex<FLLEN, SLLEN>, k: int|
                        bi.wf() && 0 <= k < self.shadow_freelist@.m[bi].len()
                        implies self.shadow_freelist@.m[bi][k]@.addr != 0
                    by {
                        if bi != idx {
                            assert(self.shadow_freelist@.m[bi][k]
                                == old(self).shadow_freelist@.m[bi][k]);
                        } else {
                            let old_k = if k < i { k } else { k + 1 };
                            assert(self.shadow_freelist@.m[idx][k]
                                == old(self).shadow_freelist@.m[idx][old_k]);
                        }
                    };
                };
            }

            // Prove !self.shadow_freelist@.contains(node)
            proof {
                old(self).lemma_shadow_list_contains_unique(idx, node);
                assert(!self.shadow_freelist@.contains(node)) by {
                    assert forall|bi: BlockIndex<FLLEN, SLLEN>|
                        bi.wf() implies !self.shadow_freelist@.m[bi].contains(node)
                    by {
                        if bi != idx {
                            // node was not in m[bi] originally
                            assert(!old(self).shadow_freelist@.m[bi].contains(node));
                            assert(self.shadow_freelist@.m[bi]
                                == old(self).shadow_freelist@.m[bi]);
                        } else {
                            // node was removed from m[idx]
                            old(self).lemma_shadow_list_no_duplicates();
                            assert forall|k: int|
                                0 <= k < self.shadow_freelist@.m[idx].len()
                                implies self.shadow_freelist@.m[idx][k] != node
                            by {
                                let old_k = if k < i { k } else { k + 1 };
                                assert(self.shadow_freelist@.m[idx][k]
                                    == old(self).shadow_freelist@.m[idx][old_k]);
                                old(self).lemma_nodup_get(idx, old_k, idx, i);
                            };
                        }
                    };
                };
            }

            // Prove size_class_condition
            proof {
                assert(self.size_class_condition()) by {
                    reveal(Tlsf::size_class_condition);
                    assert forall|bi: BlockIndex<FLLEN, SLLEN>, k: int|
                        self.shadow_freelist@.m.contains_key(bi)
                            && 0 <= k < self.shadow_freelist@.m[bi].len()
                        implies
                            bi == Self::map_floor_spec(
                                self.all_blocks.perms@[self.shadow_freelist@.m[bi][k]].points_to.value().size as usize)
                            && bi.block_size_range().contains(
                                self.all_blocks.perms@[self.shadow_freelist@.m[bi][k]].points_to.value().size as int)
                    by {
                        let entry = self.shadow_freelist@.m[bi][k];
                        if bi != idx {
                            assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]);
                            assert(entry == old(self).shadow_freelist@.m[bi][k]);
                        } else {
                            let old_k = if k < i { k } else { k + 1 };
                            assert(entry == old(self).shadow_freelist@.m[idx][old_k]);
                        }
                    };
                };
            }
        }

        #[inline(always)]
        pub(crate) fn link_free_block(&mut self,
            size: usize,
            node: *mut BlockHdr)
        requires
            Self::parameter_validity(),
            size >= GRANULARITY,
            size % GRANULARITY == 0,
            BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int),
            old(self).all_blocks.perms@[node].points_to.value().size == size,
            old(self).all_blocks.wf(),
            old(self).all_freelist_wf_weak(set![node]),
            old(self).bitmap_sync(),
            old(self).bitmap_wf(),
            old(self).size_class_condition(),
            // this can be proved at caller side using pointer order and `phys_next_of` relation
            !old(self).shadow_freelist@.contains(node),
            // we need node is wf in all_blocks
            old(self).all_blocks.contains(node),
            // NOTE: not linked to freelist but the flag is marked free & free_link_perm is Some
            old(self).all_blocks.perms@[node].points_to.value().is_free(),
        ensures
            self.all_blocks.wf(),
            // preserving pointer set
            self.all_blocks.ptrs@ == old(self).all_blocks.ptrs@,
            self.all_blocks.perms@.contains_key(node),
            self.all_blocks.perms@[node].points_to == old(self).all_blocks.perms@[node].points_to,
            self.all_blocks.perms@[node].mem == old(self).all_blocks.perms@[node].mem,
            forall|p: *mut BlockHdr|
                old(self).all_blocks.perms@.contains_key(p) ==> (
                    self.all_blocks.perms@.contains_key(p)
                    && self.all_blocks.perms@[p].points_to == old(self).all_blocks.perms@[p].points_to
                    && self.all_blocks.perms@[p].mem == old(self).all_blocks.perms@[p].mem
                    && self.all_blocks.perms@[p].overhead_mem == old(self).all_blocks.perms@[p].overhead_mem
                    && self.all_blocks.perms@[p].pad_perm == old(self).all_blocks.perms@[p].pad_perm
                ),
            self.all_freelist_wf(),
            self.bitmap_sync(),
            self.bitmap_wf(),
            self.size_class_condition(),
            ({
                let idx = Self::map_floor_spec(size);
                self.shadow_freelist@.m[idx] == seq![node].add(old(self).shadow_freelist@.m[idx])
            }),
            forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != Self::map_floor_spec(size)
                ==> self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]
        {
            let _ = core::mem::size_of::<BlockHdr>();
            let idx = match Self::map_floor(size) {
                Some(v) => v,
                None => unsafe { core::hint::unreachable_unchecked() },
            };
            proof {
                self.all_blocks.lemma_block_wf();
                self.all_blocks.lemma_node_is_wf(node);
                self.shadow_freelist@
                    .lemma_sfl_not_contains_iff_pi_undefined(self.all_blocks, node);
            }
            proof {
                // Overflow bound for get_freelink_ptr(node) — needed in both branches
                let ghost node_i = self.all_blocks.get_ptr_internal_index(node);
                self.all_blocks.lemma_wf_free_ptr_hdr_bound(node_i);
            }
            let tracked node_blk = self.all_blocks.perms.borrow_mut().tracked_remove(node);
            let tracked node_fl_pt = node_blk.free_link_perm.tracked_unwrap();

            if self.first_free[idx.0][idx.1] != null_bhdr() {
                let first_free = self.first_free[idx.0][idx.1];

                assert(old(self).shadow_freelist@.m[idx].len() > 0) by {
                    reveal(AllBlocks::ptr_is_null);
                    assert(first_free@.addr != 0);
                };
                proof {
                    // Overflow bound for get_freelink_ptr(first_free)
                    old(self).freelist_nonempty(idx);
                    let ghost ff_i = old(self).all_blocks.get_ptr_internal_index(first_free);
                    assert(old(self).wf_free_node(idx, 0));
                    old(self).all_blocks.lemma_wf_free_ptr_hdr_bound(ff_i);
                }
                assert(self.all_blocks.perms@.contains_key(first_free)) by {
                    old(self).freelist_nonempty(idx);
                    old(self).all_blocks.lemma_contains(first_free);
                };
                let tracked first_free_perm = self.all_blocks.perms.borrow_mut().tracked_remove(first_free);
                assert(old(self).wf_free_node(idx, 0));
                let tracked first_free_fl_pt = first_free_perm.free_link_perm.tracked_unwrap();

                // update first pointer
                self.set_freelist(idx, node);

                // update link
                let first_free_link = get_freelink_ptr(first_free);
                assert(old(self).all_blocks.wf_node(old(self).all_blocks.get_ptr_internal_index(first_free))) by {
                    old(self).all_blocks.lemma_wf_extract_node(
                        old(self).all_blocks.get_ptr_internal_index(first_free));
                };
                assert(get_freelink_ptr_spec(first_free) == first_free_fl_pt.ptr());
                {
                    let n = ptr_ref(first_free_link, Tracked(&first_free_fl_pt)).next_free;
                    ptr_mut_write(first_free_link, Tracked(&mut first_free_fl_pt), FreeLink {
                        next_free: n,
                        prev_free: node
                    });
                }

                // update new node's link
                let new_node_link = get_freelink_ptr(node);
                ptr_mut_write(new_node_link, Tracked(&mut node_fl_pt), FreeLink {
                    next_free: first_free,
                    prev_free: null_bhdr()
                });

                // {{{ proof block
                proof {
                    self.all_blocks.perms.borrow_mut().tracked_insert(first_free, BlockPerm {
                        points_to: first_free_perm.points_to,
                        free_link_perm: Some(first_free_fl_pt),
                        mem: first_free_perm.mem,
                        overhead_mem: first_free_perm.overhead_mem,
                        pad_perm: first_free_perm.pad_perm,
                    });

                    self.all_blocks.perms.borrow_mut().tracked_insert(node, BlockPerm {
                        points_to: node_blk.points_to,
                        free_link_perm: Some(node_fl_pt),
                        mem: node_blk.mem,
                        overhead_mem: node_blk.overhead_mem,
                        pad_perm: node_blk.pad_perm,
                    });


                    assert(self.all_blocks.wf()) by {
                        assert forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                            implies self.all_blocks.wf_node(i)
                        by {
                            let ptr = self.all_blocks.ptrs@[i];
                            if ptr == node || ptr == first_free {
                                old(self).all_blocks.lemma_wf_extract_node(i);
                                old(self).all_blocks.lemma_wf_glue_facts(i);
                                old(self).all_blocks.lemma_wf_structural_facts(i);
                                old(self).all_blocks.lemma_wf_perm_wf(i);
                                assert(self.all_blocks.perms@[ptr].points_to
                                    == old(self).all_blocks.perms@[ptr].points_to);
                                assert(self.all_blocks.perms@[ptr].mem
                                    == old(self).all_blocks.perms@[ptr].mem);
                                self.all_blocks.lemma_construct_wf_node_glue(i);
                                self.all_blocks.lemma_construct_wf_node_structural(i);
                            } else {
                                old(self).all_blocks.lemma_wf_extract_node(i);
                                assert(self.all_blocks.perms@[ptr]
                                    == old(self).all_blocks.perms@[ptr]);
                                if old(self).all_blocks.value_at(ptr).is_free()
                                    && old(self).all_blocks.phys_next_of(i) is Some {
                                    let next_ptr = old(self).all_blocks.phys_next_of(i).unwrap();
                                    assert(self.all_blocks.perms@[next_ptr].points_to
                                        == old(self).all_blocks.perms@[next_ptr].points_to);
                                }
                                AllBlocks::<FLLEN, SLLEN>::lemma_transfer_wf_node(
                                    &old(self).all_blocks, &self.all_blocks, i, i);
                            }
                        }
                        AllBlocks::<FLLEN, SLLEN>::lemma_pool_size_bounded_transfer(
                            &old(self).all_blocks, &self.all_blocks);
                        self.all_blocks.lemma_wf_from_nodes();
                    };

                    let node_ind = self.all_blocks.get_ptr_internal_index(node);
                    self.all_blocks.lemma_wf_node_ptr(node_ind);
                    self.shadow_freelist@ =
                        self.shadow_freelist@.ii_push_for_index(
                            self.all_blocks,
                            idx,
                            node_ind);

                    self.all_blocks.lemma_wf_nodup();
                    Self::lemma_ii_push_for_index_ensures(
                            old(self).shadow_freelist@,
                            old(self).all_blocks,
                            idx,
                            node_ind);


                    assert forall|i: BlockIndex<FLLEN, SLLEN>| i.wf()
                        implies self.freelist_wf(i)
                    by {
                        reveal(Tlsf::freelist_wf);
                        if i == idx {
                            assert(!AllBlocks::<FLLEN, SLLEN>::ptr_is_null(node)) by {
                                reveal(AllBlocks::ptr_is_null);
                            };
                            assert forall|n: int|
                                    0 <= n < self.shadow_freelist@.m[i].len()
                                implies self.wf_free_node(i, n)
                            by {
                                reveal(AllBlocks::ptr_is_null);
                                if n != 0 {
                                    assert(old(self).wf_free_node(idx, n - 1));
                                }
                            };
                        } else {
                            assert forall|n: int|
                                    0 <= n < self.shadow_freelist@.m[i].len()
                                implies self.wf_free_node(i, n)
                            by {
                                assert(self.shadow_freelist@.m[i] == old(self).shadow_freelist@.m[i]);
                                assert(self.shadow_freelist@.pi[(i, n)] == old(self).shadow_freelist@.pi[(i, n)]);
                                assert(self.shadow_freelist@.m[i][n] == old(self).shadow_freelist@.m[i][n]);
                                let ghost x = old(self).shadow_freelist@.m[i][n];
                                assert(x != node) by {
                                    assert(!old(self).shadow_freelist@.contains(node));
                                    assert(old(self).shadow_freelist@.m[i].contains(x));
                                    assert(old(self).shadow_freelist@.m.contains_pair(i, old(self).shadow_freelist@.m[i]));
                                    assert(old(self).shadow_freelist@.contains(x));
                                };
                                assert(x != first_free) by {
                                    old(self).lemma_shadow_list_contains_unique(idx, first_free);
                                    assert(i.wf() && i != idx);
                                    assert(!old(self).shadow_freelist@.m[i].contains(first_free));
                                    assert(old(self).shadow_freelist@.m[i].contains(x));
                                };
                                assert(self.all_blocks.perms@[x] == old(self).all_blocks.perms@[x]);
                                old(self).lemma_wf_free_node_preserve_if_not_touched(*self, i, n);
                            };
                        }
                    };

                    Self::lemma_shadow_ptrs_nonnull_after_push(*old(self), *self, idx, node);
                    assert(self.wf_shadow());
                    // Prove free_blocks_in_freelist_except(Set::empty())
                    assert(self.free_blocks_in_freelist_except(Set::empty())) by {
                        reveal(Tlsf::free_blocks_in_freelist_except);
                        assert forall|j: int| 0 <= j < self.all_blocks.ptrs@.len()
                            && self.all_blocks.value_at(self.all_blocks.ptrs@[j]).is_free()
                            && !Set::<*mut BlockHdr>::empty().contains(self.all_blocks.ptrs@[j])
                            implies self.shadow_freelist@.contains(self.all_blocks.ptrs@[j])
                        by {
                            let ptr = self.all_blocks.ptrs@[j];
                            if ptr == node {
                                // node was just pushed to shadow_freelist@.m[idx]
                                assert(self.shadow_freelist@.m[idx][0] == node);
                                assert(self.shadow_freelist@.m[idx].contains(node));
                                assert(idx.wf());
                            } else {
                                // ptr != node, so perms unchanged
                                assert(self.all_blocks.perms@[ptr].points_to
                                    == old(self).all_blocks.perms@[ptr].points_to);
                                assert(old(self).all_blocks.value_at(old(self).all_blocks.ptrs@[j]).is_free());
                                // from old(self).free_blocks_in_freelist_except(set![node])
                                assert(old(self).free_blocks_in_freelist_except(set![node]));
                                reveal(Tlsf::free_blocks_in_freelist_except);
                                assert(!set![node].contains(ptr));
                                assert(old(self).shadow_freelist@.contains(ptr));
                                // old(self).shadow_freelist and self.shadow_freelist differ only at idx
                                // where we prepended node. For other indices, they match.
                                // So if ptr was in old shadow_freelist, it's still in new shadow_freelist.
                            }
                        };
                    };
                    assert(self.all_freelist_wf());
                    assert(self.shadow_freelist@.m[idx] == seq![node].add(old(self).shadow_freelist@.m[idx]));
                    assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != idx
                        implies self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]
                    by {
                        assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]);
                    };
                }
                // }}}
            } else {
                self.set_freelist(idx, node);
                ptr_mut_write(get_freelink_ptr(node), Tracked(&mut node_fl_pt), FreeLink {
                    next_free: null_bhdr(),
                    prev_free: null_bhdr()
                });
                // {{{ proof block
                proof {
                    self.all_blocks.perms.borrow_mut().tracked_insert(node, BlockPerm {
                        points_to: node_blk.points_to,
                        free_link_perm: Some(node_fl_pt),
                        mem: node_blk.mem,
                        overhead_mem: node_blk.overhead_mem,
                        pad_perm: node_blk.pad_perm,
                    });

                    assert(exists|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                        && self.all_blocks.ptrs@[i] == node)
                    by {
                        assert(old(self).all_blocks.ptrs@.contains(node));
                        assert(self.all_blocks.ptrs@.contains(node));
                    };
                    let node_ind = self.all_blocks.get_ptr_internal_index(node);

                    assert(self.all_blocks.wf()) by {
                        assert forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                            implies self.all_blocks.wf_node(i)
                        by {
                            let ptr = self.all_blocks.ptrs@[i];
                            if ptr == node {
                                old(self).all_blocks.lemma_wf_extract_node(i);
                                old(self).all_blocks.lemma_wf_glue_facts(i);
                                old(self).all_blocks.lemma_wf_structural_facts(i);
                                old(self).all_blocks.lemma_wf_perm_wf(i);
                                assert(self.all_blocks.perms@[ptr].points_to
                                    == old(self).all_blocks.perms@[ptr].points_to);
                                assert(self.all_blocks.perms@[ptr].mem
                                    == old(self).all_blocks.perms@[ptr].mem);
                                self.all_blocks.lemma_construct_wf_node_glue(i);
                                self.all_blocks.lemma_construct_wf_node_structural(i);
                            } else {
                                old(self).all_blocks.lemma_wf_extract_node(i);
                                assert(self.all_blocks.perms@[ptr]
                                    == old(self).all_blocks.perms@[ptr]);
                                if old(self).all_blocks.value_at(ptr).is_free()
                                    && old(self).all_blocks.phys_next_of(i) is Some {
                                    let next_ptr = old(self).all_blocks.phys_next_of(i).unwrap();
                                    assert(self.all_blocks.perms@[next_ptr].points_to
                                        == old(self).all_blocks.perms@[next_ptr].points_to);
                                }
                                AllBlocks::<FLLEN, SLLEN>::lemma_transfer_wf_node(
                                    &old(self).all_blocks, &self.all_blocks, i, i);
                            }
                        }
                        AllBlocks::<FLLEN, SLLEN>::lemma_pool_size_bounded_transfer(
                            &old(self).all_blocks, &self.all_blocks);
                        self.all_blocks.lemma_wf_from_nodes();
                    };
                    self.all_blocks.lemma_wf_node_ptr(node_ind);

                    // Update identity injection
                    self.shadow_freelist@ =
                        self.shadow_freelist@.ii_push_for_index(
                            self.all_blocks,
                            idx,
                            node_ind);

                    self.all_blocks.lemma_wf_nodup();
                    Self::lemma_ii_push_for_index_ensures(
                            old(self).shadow_freelist@,
                            old(self).all_blocks,
                            idx,
                            node_ind);

                    assert forall|i: BlockIndex<FLLEN, SLLEN>| i.wf()
                        implies self.freelist_wf(i)
                    by {
                        reveal(Tlsf::freelist_wf);
                        if i == idx {
                            assert(!AllBlocks::<FLLEN, SLLEN>::ptr_is_null(node)) by {
                                reveal(AllBlocks::ptr_is_null);
                            };
                            old(self).wf_weak_index_in_freelist(idx, set![node]);
                            assert(old(self).shadow_freelist@.m[idx].len() == 0) by {
                                if old(self).shadow_freelist@.m[idx].len() != 0 {
                                    old(self).freelist_nonempty(idx);
                                }
                            };
                            assert(self.shadow_freelist@.m[idx] == seq![node]) by {
                                assert(self.all_blocks.ptrs@[node_ind] == node);
                                assert(old(self).shadow_freelist@.m[idx] == Seq::<*mut BlockHdr>::empty());
                            };
                            assert forall|n: int|
                                    0 <= n < self.shadow_freelist@.m[i].len()
                                implies self.wf_free_node(i, n)
                            by {
                                assert(n == 0);
                                assert(self.shadow_freelist@.m[i][n] == node);
                                assert(self.all_blocks.contains(node));
                                assert(self.all_blocks.value_at(node).is_free());
                                reveal(AllBlocks::ptr_is_null);
                                assert(self.all_blocks.perms@[self.shadow_freelist@.m[i][n]].free_link_perm.unwrap().value().next_free@.addr == 0);
                                assert(self.all_blocks.perms@[self.shadow_freelist@.m[i][n]].free_link_perm.unwrap().value().prev_free@.addr == 0);
                                assert(Self::free_next_of(self.shadow_freelist@.m[i], n) is None);
                                assert(Self::free_prev_of(self.shadow_freelist@.m[i], n) is None);
                            };
                        } else {
                            assert forall|n: int|
                                    0 <= n < self.shadow_freelist@.m[i].len()
                                implies self.wf_free_node(i, n)
                            by {
                                assert(self.shadow_freelist@.m[i] == old(self).shadow_freelist@.m[i]);
                                assert(self.shadow_freelist@.pi[(i, n)] == old(self).shadow_freelist@.pi[(i, n)]);
                                assert(self.shadow_freelist@.m[i][n] == old(self).shadow_freelist@.m[i][n]);
                                assert(old(self).shadow_freelist@.m[i].contains(old(self).shadow_freelist@.m[i][n]));
                                assert(old(self).shadow_freelist@.m.contains_pair(i, old(self).shadow_freelist@.m[i]));
                                assert(old(self).shadow_freelist@.contains(old(self).shadow_freelist@.m[i][n]));
                                assert(old(self).shadow_freelist@.m[i][n] != node);
                                assert(old(self).all_blocks.perms@[old(self).shadow_freelist@.m[i][n]]
                                    == self.all_blocks.perms@[old(self).shadow_freelist@.m[i][n]]);
                                assert(self.all_blocks.perms@[self.shadow_freelist@.m[i][n]]
                                    == old(self).all_blocks.perms@[old(self).shadow_freelist@.m[i][n]]);
                                old(self).lemma_wf_free_node_preserve_if_not_touched(*self, i, n);
                            }
                        }
                    };
                    assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != idx
                        implies self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]
                    by {
                        assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]);
                    };
                    Self::lemma_shadow_ptrs_nonnull_after_push(*old(self), *self, idx, node);
                    assert(self.wf_shadow());
                    // Prove free_blocks_in_freelist_except(Set::empty())
                    assert(self.free_blocks_in_freelist_except(Set::empty())) by {
                        reveal(Tlsf::free_blocks_in_freelist_except);
                        assert forall|j: int| 0 <= j < self.all_blocks.ptrs@.len()
                            && self.all_blocks.value_at(self.all_blocks.ptrs@[j]).is_free()
                            && !Set::<*mut BlockHdr>::empty().contains(self.all_blocks.ptrs@[j])
                            implies self.shadow_freelist@.contains(self.all_blocks.ptrs@[j])
                        by {
                            let ptr = self.all_blocks.ptrs@[j];
                            if ptr == node {
                                assert(self.shadow_freelist@.m[idx][0] == node);
                                assert(self.shadow_freelist@.m[idx].contains(node));
                                assert(idx.wf());
                            } else {
                                assert(self.all_blocks.perms@[ptr].points_to
                                    == old(self).all_blocks.perms@[ptr].points_to);
                                assert(old(self).all_blocks.value_at(old(self).all_blocks.ptrs@[j]).is_free());
                                assert(old(self).free_blocks_in_freelist_except(set![node]));
                                reveal(Tlsf::free_blocks_in_freelist_except);
                                assert(!set![node].contains(ptr));
                                assert(old(self).shadow_freelist@.contains(ptr));
                            }
                        };
                    };
                    assert(self.all_freelist_wf());
                } // }}}
            }

            let ghost pre = *self;
            self.set_bit_for_index(idx);
            // NOTE: this is workaround for discontineuous proof context
            proof { Self::lemma_shadow_ptrs_nonnull_frame(pre, *self); }
            // free_blocks_in_freelist_except preserved: shadow_freelist and perms unchanged
            // (must be proved before all_freelist_wf since the new definition includes it)
            proof {
                Self::lemma_free_blocks_in_freelist_except_perms_frame(pre, *self, Set::empty());
            }
            assert(self.all_freelist_wf()) by {
                assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf()
                    implies self.freelist_wf(bi)
                by {
                    reveal(Tlsf::freelist_wf);
                    pre.wf_index_in_freelist(bi);
                    assert(self.shadow_freelist@.m[bi] == pre.shadow_freelist@.m[bi]);
                    assert forall|n: int| 0 <= n < self.shadow_freelist@.m[bi].len()
                        implies self.wf_free_node(bi, n)
                    by {
                        pre.lemma_freelist_wf_extract_wf_free_node(bi, n);
                        pre.lemma_wf_free_node_preserve_if_not_touched(*self, bi, n);
                    };
                };
            };
            assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != idx
                implies self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]
            by {
                assert(self.shadow_freelist == pre.shadow_freelist);
                assert(pre.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]);
            };
            assert(self.size_class_condition()) by {
                reveal(Tlsf::size_class_condition);
                assert(old(self).size_class_condition());
                assert forall|bi: BlockIndex<FLLEN, SLLEN>, i: int|
                    self.shadow_freelist@.m.contains_key(bi)
                        && 0 <= i < self.shadow_freelist@.m[bi].len()
                    implies
                        bi == Self::map_floor_spec(
                            self.all_blocks.perms@[self.shadow_freelist@.m[bi][i]].points_to.value().size as usize)
                        && bi.block_size_range().contains(
                            self.all_blocks.perms@[self.shadow_freelist@.m[bi][i]].points_to.value().size as int)
                by {
                    if bi == idx {
                        assert(self.shadow_freelist@.m[idx] == seq![node].add(old(self).shadow_freelist@.m[idx]));
                        if i == 0 {
                            assert(self.shadow_freelist@.m[idx][0] == node);
                            assert(self.all_blocks.perms@[node].points_to == old(self).all_blocks.perms@[node].points_to);
                            // idx == map_floor_spec(size) from map_floor postcondition
                            // node.size == size from precondition
                            assert(idx == Self::map_floor_spec(size));
                            // range containment from bridge lemma
                            Self::lemma_map_floor_spec_range_contains(size);
                        } else {
                            let prev = i - 1;
                            let old_node = old(self).shadow_freelist@.m[idx][prev];
                            assert(self.shadow_freelist@.m[idx][i] == old_node);
                            assert(0 <= prev < old(self).shadow_freelist@.m[idx].len());
                            assert(self.all_blocks.perms@[old_node].points_to
                                == old(self).all_blocks.perms@[old_node].points_to);
                            assert(old(self).shadow_freelist@.m.contains_key(idx));
                        }
                    } else {
                        assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]);
                        let old_node = old(self).shadow_freelist@.m[bi][i];
                        assert(self.shadow_freelist@.m[bi][i] == old_node);
                        assert(self.all_blocks.perms@[old_node].points_to
                            == old(self).all_blocks.perms@[old_node].points_to);
                        assert(old(self).shadow_freelist@.m.contains_key(bi));
                    }
                };
            };
        }

        #[verifier::external_body]
        pub(crate) fn set_freelist(
            &mut self,
            idx: BlockIndex<FLLEN, SLLEN>,
            e: *mut BlockHdr)
            requires idx.wf()
            ensures
                self.first_free[idx.0 as int][idx.1 as int] == e,
                forall|i: BlockIndex<FLLEN, SLLEN>|
                    i != idx && i.wf() ==>
                        old(self).first_free[i.0 as int][i.1 as int]
                            == self.first_free[i.0 as int][i.1 as int],
                self.shadow_freelist == old(self).shadow_freelist,
                self.all_blocks == old(self).all_blocks,
                self.sl_bitmap == old(self).sl_bitmap,
                self.fl_bitmap == old(self).fl_bitmap,
        {
            self.first_free[idx.0][idx.1] = e;
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
            reveal(Tlsf::freelist_wf);
            reveal(AllBlocks::ptr_is_null);
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
            reveal(Tlsf::freelist_wf);
            reveal(AllBlocks::ptr_is_null);
            let first = self.shadow_freelist@.m[idx].first();
            assert(self.shadow_freelist@.m[idx].len() != 0);
            assert forall|i: int| 0 <= i < self.shadow_freelist@.m[idx].len()
                implies self.wf_free_node(idx, i) by {
            };
            //assert(self.first_free[idx.0 as int][idx.1 as int] matches Some(first)
                //&& self.shadow_freelist@.m[idx].first() == first);
            assert forall|i: int| 0 <= i < self.shadow_freelist@.m[idx].len()
                implies self.all_blocks.contains(self.shadow_freelist@.m[idx][i]) by {
                assert(self.wf_free_node(idx, i));
            };
            assert(self.shadow_freelist@.m[idx].all(|e| self.all_blocks.contains(e)));
            assert(self.shadow_freelist@.m[idx].contains(self.shadow_freelist@.m[idx].first()));
            assert(self.all_blocks.contains(self.shadow_freelist@.m[idx].first()));
        }

        /// Bridge: freelist_wf(idx) from addr-based conditions (no ptr_is_null needed at call site).
        pub(crate) proof fn lemma_freelist_wf_from_addr_conditions(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                forall|n: int| 0 <= n < self.shadow_freelist@.m[idx].len() ==> self.wf_free_node(idx, n),
                self.shadow_freelist@.m[idx].len() == 0
                    ==> self.first_free[idx.0 as int][idx.1 as int]@.addr == 0,
                self.shadow_freelist@.m[idx].len() > 0
                    ==> self.first_free[idx.0 as int][idx.1 as int]@.addr != 0
                        && self.first_free[idx.0 as int][idx.1 as int]
                            == self.shadow_freelist@.m[idx].first(),
            ensures
                self.freelist_wf(idx)
        {
            reveal(Tlsf::freelist_wf);
            reveal(AllBlocks::ptr_is_null);
        }

        /// Bridge: freelist_wf(idx) + null head → len == 0.
        pub(crate) proof fn lemma_freelist_len_zero_of_null_head(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.freelist_wf(idx),
                self.first_free[idx.0 as int][idx.1 as int]@.addr == 0,
            ensures
                self.shadow_freelist@.m[idx].len() == 0
        {
            reveal(Tlsf::freelist_wf);
            reveal(AllBlocks::ptr_is_null);
        }

        /// Bridge: freelist_wf(idx) + nonnull head → len > 0.
        pub(crate) proof fn lemma_freelist_len_nonzero_of_nonnull_head(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.freelist_wf(idx),
                self.first_free[idx.0 as int][idx.1 as int]@.addr != 0,
            ensures
                self.shadow_freelist@.m[idx].len() > 0
        {
            reveal(Tlsf::freelist_wf);
            reveal(AllBlocks::ptr_is_null);
        }

        /// Bridge: wf_free_node(idx, 0) + nonnull next_free → len >= 2.
        pub(crate) proof fn lemma_freelist_len_gt1_from_nonnull_next(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.shadow_freelist@.m[idx].len() >= 1,
                self.wf_free_node(idx, 0),
                self.all_blocks.perms@[self.shadow_freelist@.m[idx][0]]
                    .free_link_perm.unwrap().value().next_free@.addr != 0,
            ensures
                self.shadow_freelist@.m[idx].len() >= 2
        {
            reveal(AllBlocks::ptr_is_null);
        }

        /// Bridge: wf_free_node(idx, n) → addr form of next_free/prev_free conditions.
        pub(crate) proof fn lemma_wf_free_node_next_addr(self, idx: BlockIndex<FLLEN, SLLEN>, n: int)
            requires
                idx.wf(),
                0 <= n < self.shadow_freelist@.m[idx].len(),
                self.wf_free_node(idx, n),
            ensures
                self.all_blocks.perms@[self.shadow_freelist@.m[idx][n]]
                    .free_link_perm.unwrap().value().next_free@.addr != 0
                    ==> Some(self.all_blocks.perms@[self.shadow_freelist@.m[idx][n]]
                            .free_link_perm.unwrap().value().next_free)
                        == Self::free_next_of(self.shadow_freelist@.m[idx], n),
                self.all_blocks.perms@[self.shadow_freelist@.m[idx][n]]
                    .free_link_perm.unwrap().value().next_free@.addr == 0
                    ==> Self::free_next_of(self.shadow_freelist@.m[idx], n) is None,
        {
            reveal(AllBlocks::ptr_is_null);
        }

        /// Bridge: freelist_wf(idx) + len == 0 → first_free addr == 0.
        pub(crate) proof fn lemma_freelist_addr_zero_if_len_zero(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.freelist_wf(idx),
                self.shadow_freelist@.m[idx].len() == 0,
            ensures
                self.first_free[idx.0 as int][idx.1 as int]@.addr == 0
        {
            reveal(Tlsf::freelist_wf);
            reveal(AllBlocks::ptr_is_null);
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
            reveal(Tlsf::freelist_wf);
            assert forall|i: int| 0 <= i < self.shadow_freelist@.m[idx].len()
                implies self.all_blocks.contains(self.shadow_freelist@.m[idx][i]) by {
                assert(self.wf_free_node(idx, i));
            };
        }

        pub(crate) proof fn lemma_shadow_list_no_duplicates(self)
            requires
                self.wf_shadow(),
                self.all_blocks.wf(),
            ensures
                self.shadow_freelist_nodup()
        {
            reveal(Tlsf::shadow_freelist_nodup);
            self.all_blocks.lemma_wf_nodup();
            assert(self.is_ii());
            assert(self.shadow_freelist@.pi.is_injective());
            assert(ptrs_no_duplicates(self.all_blocks.ptrs@));
            assert forall|i: BlockIndex<FLLEN, SLLEN>,
                          j: BlockIndex<FLLEN, SLLEN>,
                          k: int,
                          l: int|
                (i, k) != (j, l) &&
                i.wf() && j.wf() &&
                0 <= k < self.shadow_freelist@.m[i].len() &&
                0 <= l < self.shadow_freelist@.m[j].len()
                implies self.shadow_freelist@.m[i][k] != self.shadow_freelist@.m[j][l]
            by {
                assert(0 <= self.shadow_freelist@.pi[(i, k)] < self.all_blocks.ptrs@.len());
                assert(0 <= self.shadow_freelist@.pi[(j, l)] < self.all_blocks.ptrs@.len());
                assert(self.shadow_freelist@.m[i][k]
                    == self.all_blocks.ptrs@[self.shadow_freelist@.pi[(i, k)]]);
                assert(self.shadow_freelist@.m[j][l]
                    == self.all_blocks.ptrs@[self.shadow_freelist@.pi[(j, l)]]);
                if self.shadow_freelist@.m[i][k] == self.shadow_freelist@.m[j][l] {
                    lemma_ptrs_no_duplicates_eq_index(
                        self.all_blocks.ptrs@,
                        self.shadow_freelist@.pi[(i, k)],
                        self.shadow_freelist@.pi[(j, l)],
                    );
                    assert(self.shadow_freelist@.pi[(i, k)] == self.shadow_freelist@.pi[(j, l)]);
                    assert(false);
                }
            };
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
            reveal(Tlsf::shadow_freelist_nodup);
            self.lemma_shadow_list_no_duplicates();
        }

        pub(crate) proof fn lemma_nodup_get(
            self,
            i: BlockIndex<FLLEN, SLLEN>, k: int,
            j: BlockIndex<FLLEN, SLLEN>, l: int,
        )
            requires
                self.shadow_freelist_nodup(),
                (i, k) != (j, l),
                i.wf(), j.wf(),
                0 <= k < self.shadow_freelist@.m[i].len(),
                0 <= l < self.shadow_freelist@.m[j].len(),
            ensures
                self.shadow_freelist@.m[i][k] != self.shadow_freelist@.m[j][l]
        {
            reveal(Tlsf::shadow_freelist_nodup);
        }

        proof fn lemma_ii_push_for_index_ensures(
            sfl: ShadowFreelist<FLLEN, SLLEN>,
            all_blocks: AllBlocks<FLLEN, SLLEN>,
            new_node_bi: BlockIndex<FLLEN, SLLEN>,
            new_node_ai: int
        )
            requires
                ptrs_no_duplicates(all_blocks.ptrs@),
                !sfl.pi.values().contains(new_node_ai),
                0 <= new_node_ai < all_blocks.ptrs@.len(),
                new_node_bi.wf(),
                sfl.shadow_freelist_has_all_wf_index(),
                is_identity_injection(sfl, all_blocks.ptrs@),
                all_blocks.wf_node(new_node_ai)
            ensures ({
                let new_sfl = sfl.ii_push_for_index(all_blocks, new_node_bi, new_node_ai);
                &&& is_identity_injection(new_sfl, all_blocks.ptrs@)
                &&& new_sfl.m[new_node_bi][0] == all_blocks.ptrs@[new_node_ai]
                &&& forall|i: int| 0 <= i < sfl.m[new_node_bi].len() ==> {
                            &&& sfl.m[new_node_bi][i] == new_sfl.m[new_node_bi][i + 1]
                            &&& sfl.pi[(new_node_bi, i)] == new_sfl.pi[(new_node_bi, i + 1)]
                        }
            })
        {
            let new_sfl = sfl.ii_push_for_index(all_blocks, new_node_bi, new_node_ai);
            assert(new_sfl.pi.is_injective()) by {
                assert forall|x: (BlockIndex<FLLEN, SLLEN>, int), y: (BlockIndex<FLLEN, SLLEN>, int)|
                    x != y && new_sfl.pi.dom().contains(x) && new_sfl.pi.dom().contains(y)
                        implies new_sfl.pi[x] != new_sfl.pi[y]
                by {
                    if x.0 == new_node_bi && x.1 == 0 {
                        assert(new_sfl.pi[x] == new_node_ai);
                        if y.0 == new_node_bi {
                            assert(sfl.pi.contains_key((new_node_bi, y.1 - 1)));
                        }
                    } else if y.0 == new_node_bi && y.1 == 0 {
                        assert(new_sfl.pi[y] == new_node_ai);
                        if x.0 == new_node_bi {
                            assert(sfl.pi.contains_key((new_node_bi, x.1 - 1)));
                        }
                    }
                };
            };
        }

        pub(crate) proof fn lemma_ii_remove_for_index_ensures(
            sfl: ShadowFreelist<FLLEN, SLLEN>,
            all_blocks: AllBlocks<FLLEN, SLLEN>,
            bi: BlockIndex<FLLEN, SLLEN>,
            rm_pos: int,
        )
            requires
                ptrs_no_duplicates(all_blocks.ptrs@),
                is_identity_injection(sfl, all_blocks.ptrs@),
                bi.wf(),
                0 <= rm_pos < sfl.m[bi].len(),
                forall|j: BlockIndex<FLLEN, SLLEN>, n: int|
                    j.wf() && 0 <= n < sfl.m[j].len()
                        ==> 0 <= #[trigger] sfl.pi[(j, n)] < all_blocks.ptrs@.len(),
            ensures ({
                let new_sfl = sfl.ii_remove_for_index(all_blocks, bi, rm_pos);
                &&& new_sfl.m[bi] == sfl.m[bi].remove(rm_pos)
                &&& is_identity_injection(new_sfl, all_blocks.ptrs@)
            })
        {
        }

        pub(crate) proof fn lemma_ii_shift_after_insert_ensures(
            sfl: ShadowFreelist<FLLEN, SLLEN>,
            old_ptrs: Seq<*mut BlockHdr>,
            insert_ai: int,
            new_ptr: *mut BlockHdr,
        )
            requires
                ptrs_no_duplicates(old_ptrs),
                ghost_pointer_ordered(old_ptrs),
                sfl.shadow_freelist_has_all_wf_index(),
                is_identity_injection(sfl, old_ptrs),
                0 <= insert_ai < old_ptrs.len(),
                (old_ptrs[insert_ai] as usize as int) < (new_ptr as usize as int),
                insert_ai + 1 < old_ptrs.len() ==> (new_ptr as usize as int) <= (old_ptrs[insert_ai + 1] as usize as int),
            ensures
                is_identity_injection(
                    sfl.ii_shift_after_insert(insert_ai),
                    add_ghost_pointer(old_ptrs, new_ptr),
                )
        {
            lemma_add_ghost_pointer_insert_after_index(old_ptrs, new_ptr, insert_ai);
            let ghost new_ptrs = add_ghost_pointer(old_ptrs, new_ptr);
            let ghost new_sfl = sfl.ii_shift_after_insert(insert_ai);

            assert(new_sfl.pi.is_injective()) by {
                assert forall|x: (BlockIndex<FLLEN, SLLEN>, int), y: (BlockIndex<FLLEN, SLLEN>, int)|
                    x != y && new_sfl.pi.dom().contains(x) && new_sfl.pi.dom().contains(y)
                        implies new_sfl.pi[x] != new_sfl.pi[y]
                by {
                    assert(sfl.pi.dom().contains(x));
                    assert(sfl.pi.dom().contains(y));
                    assert(sfl.pi[x] != sfl.pi[y]);
                    let ax = sfl.pi[x];
                    let ay = sfl.pi[y];
                    let fx = if insert_ai + 1 <= ax { ax + 1 } else { ax };
                    let fy = if insert_ai + 1 <= ay { ay + 1 } else { ay };
                    assert(new_sfl.pi[x] == fx);
                    assert(new_sfl.pi[y] == fy);
                    if ax < insert_ai + 1 {
                        if ay < insert_ai + 1 {
                            assert(fx == ax);
                            assert(fy == ay);
                        } else {
                            assert(fx == ax);
                            assert(fy == ay + 1);
                            assert(fx < insert_ai + 1);
                            assert(insert_ai + 1 <= fy);
                        }
                    } else {
                        if ay < insert_ai + 1 {
                            assert(fx == ax + 1);
                            assert(fy == ay);
                            assert(fy < insert_ai + 1);
                            assert(insert_ai + 1 <= fx);
                        } else {
                            assert(fx == ax + 1);
                            assert(fy == ay + 1);
                        }
                    }
                };
            };

            assert forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
                new_sfl.pi.contains_key((idx, m)) <==> idx.wf() && 0 <= m < new_sfl.m[idx].len()
            by {
                assert(new_sfl.pi.contains_key((idx, m)) == sfl.pi.contains_key((idx, m)));
                assert(sfl.shadow_freelist_has_all_wf_index());
                assert(sfl.m.contains_key(idx) <==> idx.wf());
                assert(new_sfl.m[idx] == sfl.m[idx]);
                assert(sfl.pi.contains_key((idx, m)) <==> idx.wf() && 0 <= m < sfl.m[idx].len());
            };

            assert forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
                idx.wf() && 0 <= m < new_sfl.m[idx].len() implies {
                    &&& 0 <= #[trigger] new_sfl.pi[(idx, m)] < new_ptrs.len()
                    &&& new_sfl.m[idx][m] == new_ptrs[new_sfl.pi[(idx, m)]]
                }
            by {
                assert(sfl.m.contains_key(idx));
                assert(new_sfl.m[idx] == sfl.m[idx]);
                assert(sfl.pi.contains_key((idx, m)));
                assert(0 <= #[trigger] sfl.pi[(idx, m)] < old_ptrs.len());
                assert(sfl.m[idx][m] == old_ptrs[sfl.pi[(idx, m)]]);
                let ai = sfl.pi[(idx, m)];
                let nai = new_sfl.pi[(idx, m)];
                assert(nai == if insert_ai + 1 <= ai { ai + 1 } else { ai });
                if insert_ai + 1 <= ai {
                    assert(nai == ai + 1);
                    assert(insert_ai + 1 < nai < new_ptrs.len());
                    lemma_add_ghost_pointer_index_map(old_ptrs, new_ptr, insert_ai, nai);
                    assert(new_ptrs[nai] == old_ptrs[nai - 1]);
                    assert(nai - 1 == ai);
                    assert(new_ptrs[nai] == old_ptrs[ai]);
                } else {
                    assert(nai == ai);
                    assert(0 <= nai <= insert_ai);
                    lemma_add_ghost_pointer_index_map(old_ptrs, new_ptr, insert_ai, nai);
                    assert(new_ptrs[nai] == old_ptrs[nai]);
                    assert(new_ptrs[nai] == old_ptrs[ai]);
                }
                assert(new_sfl.m[idx][m] == new_ptrs[new_sfl.pi[(idx, m)]]);
            };
        }

        /// After removing ptrs@[remove_ai], all pi indices > remove_ai shift down by 1.
        /// Inverse of lemma_ii_shift_after_insert_ensures.
        pub(crate) proof fn lemma_ii_shift_after_remove_ensures(
            sfl: ShadowFreelist<FLLEN, SLLEN>,
            old_ptrs: Seq<*mut BlockHdr>,
            remove_ai: int,
            removed_ptr: *mut BlockHdr,
        )
            requires
                ptrs_no_duplicates(old_ptrs),
                ghost_pointer_ordered(old_ptrs),
                sfl.shadow_freelist_has_all_wf_index(),
                is_identity_injection(sfl, old_ptrs),
                0 <= remove_ai < old_ptrs.len(),
                old_ptrs[remove_ai] == removed_ptr,
                // removed_ptr must not be in any freelist
                !sfl.pi.values().contains(remove_ai),
            ensures
                is_identity_injection(
                    sfl.ii_shift_after_remove(remove_ai),
                    remove_ghost_pointer(old_ptrs, removed_ptr),
                )
        {
            lemma_remove_ghost_pointer_index(old_ptrs, removed_ptr);
            lemma_remove_ghost_pointer_ensures(old_ptrs, removed_ptr);
            let ghost new_ptrs = remove_ghost_pointer(old_ptrs, removed_ptr);
            let ghost new_sfl = sfl.ii_shift_after_remove(remove_ai);

            // The remove index chosen by remove_ghost_pointer equals remove_ai
            // (since ptrs_no_duplicates guarantees unique index)
            let ghost rm_idx = choose|i: int| 0 <= i < old_ptrs.len() && old_ptrs[i] == removed_ptr;
            assert(rm_idx == remove_ai) by {
                lemma_ptrs_no_duplicates_eq_index(old_ptrs, rm_idx, remove_ai);
            };

            assert(new_sfl.pi.is_injective()) by {
                assert forall|x: (BlockIndex<FLLEN, SLLEN>, int), y: (BlockIndex<FLLEN, SLLEN>, int)|
                    x != y && new_sfl.pi.dom().contains(x) && new_sfl.pi.dom().contains(y)
                        implies new_sfl.pi[x] != new_sfl.pi[y]
                by {
                    assert(sfl.pi.dom().contains(x));
                    assert(sfl.pi.dom().contains(y));
                    assert(sfl.pi[x] != sfl.pi[y]);
                    let ax = sfl.pi[x];
                    let ay = sfl.pi[y];
                    // ax != remove_ai and ay != remove_ai since !pi.values().contains(remove_ai)
                    assert(ax != remove_ai);
                    assert(ay != remove_ai);
                    let fx = if ax > remove_ai { ax - 1 } else { ax };
                    let fy = if ay > remove_ai { ay - 1 } else { ay };
                    assert(new_sfl.pi[x] == fx);
                    assert(new_sfl.pi[y] == fy);
                    if ax > remove_ai {
                        if ay > remove_ai {
                            assert(fx == ax - 1);
                            assert(fy == ay - 1);
                        } else {
                            assert(fx == ax - 1);
                            assert(fy == ay);
                            assert(fy < remove_ai);
                            assert(fx >= remove_ai);
                        }
                    } else {
                        if ay > remove_ai {
                            assert(fx == ax);
                            assert(fy == ay - 1);
                            assert(fx < remove_ai);
                            assert(fy >= remove_ai);
                        } else {
                            assert(fx == ax);
                            assert(fy == ay);
                        }
                    }
                };
            };

            assert forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
                new_sfl.pi.contains_key((idx, m)) <==> idx.wf() && 0 <= m < new_sfl.m[idx].len()
            by {
                assert(new_sfl.pi.contains_key((idx, m)) == sfl.pi.contains_key((idx, m)));
                assert(new_sfl.m[idx] == sfl.m[idx]);
                assert(sfl.pi.contains_key((idx, m)) <==> idx.wf() && 0 <= m < sfl.m[idx].len());
            };

            assert forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
                idx.wf() && 0 <= m < new_sfl.m[idx].len() implies {
                    &&& 0 <= #[trigger] new_sfl.pi[(idx, m)] < new_ptrs.len()
                    &&& new_sfl.m[idx][m] == new_ptrs[new_sfl.pi[(idx, m)]]
                }
            by {
                assert(sfl.m.contains_key(idx));
                assert(new_sfl.m[idx] == sfl.m[idx]);
                assert(sfl.pi.contains_key((idx, m)));
                assert(0 <= #[trigger] sfl.pi[(idx, m)] < old_ptrs.len());
                assert(sfl.m[idx][m] == old_ptrs[sfl.pi[(idx, m)]]);
                let ai = sfl.pi[(idx, m)];
                assert(ai != remove_ai);
                let nai = new_sfl.pi[(idx, m)];
                assert(nai == if ai > remove_ai { ai - 1 } else { ai });
                if ai > remove_ai {
                    assert(nai == ai - 1);
                    assert(0 <= nai < new_ptrs.len());
                    lemma_remove_ghost_pointer_index_map(old_ptrs, removed_ptr, nai);
                    assert(nai >= remove_ai);
                    assert(new_ptrs[nai] == old_ptrs[nai + 1]);
                    assert(nai + 1 == ai);
                    assert(new_ptrs[nai] == old_ptrs[ai]);
                } else {
                    assert(nai == ai);
                    assert(ai < remove_ai);
                    assert(0 <= nai < new_ptrs.len());
                    lemma_remove_ghost_pointer_index_map(old_ptrs, removed_ptr, nai);
                    assert(nai < remove_ai);
                    assert(new_ptrs[nai] == old_ptrs[nai]);
                    assert(new_ptrs[nai] == old_ptrs[ai]);
                }
                assert(new_sfl.m[idx][m] == new_ptrs[new_sfl.pi[(idx, m)]]);
            };
        }

        /// Frame lemma: if old_self had all_freelist_wf(), and new_self
        /// only changed the freelist for modified_idx (with wf_shadow preserved),
        /// then new_self.all_freelist_wf().
        pub(crate) proof fn lemma_all_freelist_wf_frame(
            old_self: Self,
            new_self: Self,
            modified_idx: BlockIndex<FLLEN, SLLEN>,
        )
            requires
                old_self.all_freelist_wf(),
                new_self.wf_shadow(),
                modified_idx.wf(),
                new_self.freelist_wf(modified_idx),
                forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != modified_idx
                    ==> new_self.shadow_freelist@.m[bi] == old_self.shadow_freelist@.m[bi],
                forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != modified_idx
                    ==> new_self.first_free[bi.0 as int][bi.1 as int]
                        == old_self.first_free[bi.0 as int][bi.1 as int],
                forall|bi: BlockIndex<FLLEN, SLLEN>, n: int|
                    bi.wf() && bi != modified_idx
                    && 0 <= n < old_self.shadow_freelist@.m[bi].len()
                    ==> #[trigger] new_self.all_blocks.perms@[old_self.shadow_freelist@.m[bi][n]]
                        == old_self.all_blocks.perms@[old_self.shadow_freelist@.m[bi][n]],
            ensures
                new_self.wf_shadow(),
                forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() ==> new_self.freelist_wf(bi),
        {
            assert(new_self.is_ii()) by { assert(new_self.wf_shadow()); };
            assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() implies new_self.freelist_wf(bi) by {
                reveal(Tlsf::freelist_wf);
                if bi == modified_idx {
                    // from precondition new_self.freelist_wf(modified_idx)
                } else {
                    old_self.wf_index_in_freelist(bi);
                    assert(old_self.shadow_freelist@.m[bi] == new_self.shadow_freelist@.m[bi]);
                    assert(old_self.first_free[bi.0 as int][bi.1 as int]
                        == new_self.first_free[bi.0 as int][bi.1 as int]);
                    assert forall|n: int| 0 <= n < new_self.shadow_freelist@.m[bi].len()
                        implies new_self.wf_free_node(bi, n)
                    by {
                        assert(0 <= n < old_self.shadow_freelist@.m[bi].len());
                        old_self.lemma_freelist_wf_extract_wf_free_node(bi, n);
                        assert(old_self.all_blocks.perms@[old_self.shadow_freelist@.m[bi][n]]
                            == new_self.all_blocks.perms@[new_self.shadow_freelist@.m[bi][n]]);
                        old_self.lemma_wf_free_node_preserve_if_not_touched(new_self, bi, n);
                    };
                }
            };
        }



        /// Frame lemma: if shadow_freelist, first_free, and perms of all free nodes
        /// are unchanged, then all_freelist_wf is preserved.
        /// Used from allocate.rs where reveal(Tlsf::freelist_wf) is not available (closed).
        pub(crate) proof fn lemma_all_freelist_wf_perms_frame(
            old_self: Self,
            new_self: Self,
        )
            requires
                old_self.all_freelist_wf(),
                new_self.wf_shadow(),
                new_self.shadow_freelist@ == old_self.shadow_freelist@,
                forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf()
                    ==> new_self.first_free[bi.0 as int][bi.1 as int]
                        == old_self.first_free[bi.0 as int][bi.1 as int],
                forall|bi: BlockIndex<FLLEN, SLLEN>, n: int|
                    bi.wf() && 0 <= n < old_self.shadow_freelist@.m[bi].len()
                    ==> new_self.all_blocks.perms@[old_self.shadow_freelist@.m[bi][n]]
                        == old_self.all_blocks.perms@[old_self.shadow_freelist@.m[bi][n]],
            ensures
                new_self.wf_shadow(),
                forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() ==> new_self.freelist_wf(bi),
        {
            assert(new_self.is_ii()) by { assert(new_self.wf_shadow()); };
            assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf()
                implies new_self.freelist_wf(bi)
            by {
                reveal(Tlsf::freelist_wf);
                old_self.wf_index_in_freelist(bi);
                assert(new_self.shadow_freelist@.m[bi] == old_self.shadow_freelist@.m[bi]);
                assert(new_self.first_free[bi.0 as int][bi.1 as int]
                    == old_self.first_free[bi.0 as int][bi.1 as int]);
                assert forall|n: int| 0 <= n < new_self.shadow_freelist@.m[bi].len()
                    implies new_self.wf_free_node(bi, n)
                by {
                    old_self.lemma_freelist_wf_extract_wf_free_node(bi, n);
                    old_self.lemma_wf_free_node_preserve_if_not_touched(new_self, bi, n);
                };
            };
        }

        /// Big-step lemma: after popping the head of freelist[idx], proves
        /// wf_shadow(), freelist_wf for all indices, and bitmap_sync().
        /// Encapsulates all @.addr-heavy reasoning so allocate.rs call sites
        /// are free of raw_ptr triggers from forall|bi| loops.
        pub(crate) proof fn lemma_pop_head_preserves_wf(
            old_self: Self,
            new_self: Self,
            idx: BlockIndex<FLLEN, SLLEN>,
            next_free: *mut BlockHdr,   // = new_self.first_free[idx.0][idx.1]
        )
            requires
                old_self.all_freelist_wf(),
                old_self.bitmap_sync(),
                idx.wf(),
                old_self.shadow_freelist@.m[idx].len() > 0,
                // Shadow freelist: idx popped, others unchanged
                new_self.shadow_freelist@.m[idx] == old_self.shadow_freelist@.m[idx].remove(0),
                forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != idx
                    ==> new_self.shadow_freelist@.m[bi] == old_self.shadow_freelist@.m[bi],
                // first_free: idx → next_free, others unchanged
                new_self.first_free[idx.0 as int][idx.1 as int] == next_free,
                forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != idx
                    ==> new_self.first_free[bi.0 as int][bi.1 as int]
                        == old_self.first_free[bi.0 as int][bi.1 as int],
                // new_self invariants
                new_self.wf_shadow(),
                new_self.all_blocks.wf(),
                // Perm preservation for bi != idx freelist nodes
                forall|bi: BlockIndex<FLLEN, SLLEN>, n: int|
                    bi.wf() && bi != idx && 0 <= n < old_self.shadow_freelist@.m[bi].len()
                    ==> #[trigger] new_self.all_blocks.perms@[old_self.shadow_freelist@.m[bi][n]]
                        == old_self.all_blocks.perms@[old_self.shadow_freelist@.m[bi][n]],
                // Perm preservation for idx positions >= 2 (positions 0 and 1 handled specially)
                forall|n: int| 1 < n < old_self.shadow_freelist@.m[idx].len()
                    ==> new_self.all_blocks.perms@[old_self.shadow_freelist@.m[idx][n]]
                        == old_self.all_blocks.perms@[old_self.shadow_freelist@.m[idx][n]],
                // next_free conditions (when list had >= 2 elements → next_free was at old[1])
                old_self.shadow_freelist@.m[idx].len() > 1 ==> (
                    old_self.shadow_freelist@.m[idx][1] == next_free
                    && new_self.all_blocks.perms@[next_free].points_to
                        == old_self.all_blocks.perms@[next_free].points_to
                    && new_self.all_blocks.perms@[next_free].mem
                        == old_self.all_blocks.perms@[next_free].mem
                    && new_self.all_blocks.perms@[next_free].free_link_perm.unwrap().value().prev_free@.addr == 0
                    && new_self.all_blocks.perms@[next_free].free_link_perm.unwrap().value().next_free
                        == old_self.all_blocks.perms@[next_free].free_link_perm.unwrap().value().next_free
                ),
                // next_free is null when the old list had exactly 1 element
                old_self.shadow_freelist@.m[idx].len() == 1 ==> next_free@.addr == 0,
                // Bitmap conditions
                next_free@.addr == 0
                    ==> !nth_bit!(new_self.sl_bitmap[idx.0 as int], idx.1 as usize),
                next_free@.addr != 0
                    ==> new_self.sl_bitmap[idx.0 as int] == old_self.sl_bitmap[idx.0 as int],
                forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != idx
                    ==> nth_bit!(new_self.sl_bitmap[bi.0 as int], bi.1 as usize)
                        == nth_bit!(old_self.sl_bitmap[bi.0 as int], bi.1 as usize),
            ensures
                new_self.wf_shadow(),
                forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() ==> new_self.freelist_wf(bi),
                new_self.bitmap_sync(),
        {
            let ghost old_sfl = old_self.shadow_freelist@.m[idx];
            let ghost new_sfl = new_self.shadow_freelist@.m[idx];
            assert(new_sfl == old_sfl.remove(0));
            assert(new_self.is_ii()) by { assert(new_self.wf_shadow()); };

            // --- Step 1: Prove new_self.freelist_wf(idx) ---
            assert(new_self.freelist_wf(idx)) by {
                // Prove wf_free_node for all n in new freelist
                assert forall|n: int| 0 <= n < new_sfl.len()
                    implies new_self.wf_free_node(idx, n)
                by {
                    if n == 0 {
                        // new head = next_free (was at old position 1)
                        // next_free@.addr != 0 (since new_sfl.len() > 0)
                        new_self.lemma_shadow_ptr_nonnull_at(idx, 0);
                        assert(next_free@.addr != 0);
                        // From precondition: old_len == 1 ==> next_free@.addr == 0. Contrapositive:
                        assert(old_sfl.len() != 1);
                        assert(old_sfl.len() > 1);
                        assert(old_sfl[1] == next_free);
                        old_self.lemma_freelist_wf_extract_wf_free_node(idx, 1);
                        assert(old_self.wf_free_node(idx, 1));

                        // all_blocks.contains
                        assert(new_self.all_blocks.contains(next_free)) by {
                            assert(new_sfl[0] == next_free);
                            assert(0 <= new_self.shadow_freelist@.pi[(idx, 0)] < new_self.all_blocks.ptrs@.len());
                            assert(new_sfl[0] == new_self.all_blocks.ptrs@[new_self.shadow_freelist@.pi[(idx, 0)]]);
                        };
                        // is_free
                        assert(new_self.all_blocks.value_at(next_free).is_free()) by {
                            assert(new_self.all_blocks.perms@[next_free].points_to
                                == old_self.all_blocks.perms@[next_free].points_to);
                            assert(old_self.all_blocks.value_at(old_sfl[1]).is_free());
                        };
                        // prev_free@.addr == 0: from precondition
                        assert(new_self.all_blocks.perms@[next_free].free_link_perm.unwrap().value().prev_free@.addr == 0);
                        // next_free addr chain
                        old_self.lemma_wf_free_node_next_addr(idx, 1);
                        assert(Self::free_next_of(new_sfl, 0) == Self::free_next_of(old_sfl, 1));
                        let ghost nxt = new_self.all_blocks.perms@[next_free].free_link_perm.unwrap().value().next_free;
                        assert(nxt == old_self.all_blocks.perms@[next_free].free_link_perm.unwrap().value().next_free);
                        assert(nxt@.addr != 0
                                ==> Some(nxt) == Self::free_next_of(new_sfl, 0)) by {
                            reveal(AllBlocks::ptr_is_null);
                            assert(old_self.all_blocks.perms@[old_sfl[1]].free_link_perm.unwrap().value().next_free@.addr != 0
                                ==> Some(old_self.all_blocks.perms@[old_sfl[1]].free_link_perm.unwrap().value().next_free)
                                    == Self::free_next_of(old_sfl, 1));
                        };
                        assert(nxt@.addr == 0
                                ==> Self::free_next_of(new_sfl, 0) is None) by {
                            reveal(AllBlocks::ptr_is_null);
                            assert(old_self.all_blocks.perms@[old_sfl[1]].free_link_perm.unwrap().value().next_free@.addr == 0
                                ==> Self::free_next_of(old_sfl, 1) is None);
                        };
                        new_self.lemma_wf_free_node_head_from_addr_form(idx);
                    } else {
                        // n > 0: corresponds to old position n+1 >= 2
                        old_self.lemma_freelist_wf_extract_wf_free_node(idx, n + 1);
                        assert(old_self.wf_free_node(idx, n + 1));
                        assert(new_self.all_blocks.perms@[old_sfl[n + 1]]
                            == old_self.all_blocks.perms@[old_sfl[n + 1]]);
                        old_self.lemma_wf_free_node_preserve_remove_head(new_self, idx, n);
                    }
                };

                // Prove head address conditions for lemma_freelist_wf_from_addr_conditions
                assert(new_sfl.len() == 0 ==> new_self.first_free[idx.0 as int][idx.1 as int]@.addr == 0) by {
                    if new_sfl.len() == 0 {
                        // old_len == 1, so by precondition next_free@.addr == 0
                        assert(next_free@.addr == 0);
                    }
                };
                assert(new_sfl.len() > 0 ==> (
                    new_self.first_free[idx.0 as int][idx.1 as int]@.addr != 0
                    && new_self.first_free[idx.0 as int][idx.1 as int] == new_sfl.first()
                )) by {
                    if new_sfl.len() > 0 {
                        new_self.lemma_shadow_ptr_nonnull_at(idx, 0);
                        assert(new_self.first_free[idx.0 as int][idx.1 as int]@.addr != 0);
                        assert(new_self.first_free[idx.0 as int][idx.1 as int] == new_sfl.first());
                    }
                };
                new_self.lemma_freelist_wf_from_addr_conditions(idx);
            };

            // --- Step 2: Prove wf_shadow() + freelist_wf using frame lemma ---
            Self::lemma_all_freelist_wf_frame(old_self, new_self, idx);

            // --- Step 3: Prove bitmap_sync ---
            assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() implies
                (nth_bit!(new_self.sl_bitmap[bi.0 as int], bi.1 as usize)
                    <==> new_self.shadow_freelist@.m[bi].len() > 0)
            by {
                if bi == idx {
                    if next_free@.addr == 0 {
                        assert(!nth_bit!(new_self.sl_bitmap[idx.0 as int], idx.1 as usize));
                        assert(new_self.freelist_wf(idx));
                        new_self.lemma_freelist_len_zero_of_null_head(idx);
                    } else {
                        assert(nth_bit!(new_self.sl_bitmap[idx.0 as int], idx.1 as usize)) by {
                            assert(new_self.sl_bitmap[idx.0 as int] == old_self.sl_bitmap[idx.0 as int]);
                            assert(old_self.bitmap_sync());
                            assert(old_self.shadow_freelist@.m[idx].len() > 0);
                            assert(nth_bit!(old_self.sl_bitmap[idx.0 as int], idx.1 as usize));
                        };
                        assert(new_self.freelist_wf(idx));
                        new_self.lemma_freelist_len_nonzero_of_nonnull_head(idx);
                    }
                } else {
                    assert(new_self.shadow_freelist@.m[bi] == old_self.shadow_freelist@.m[bi]);
                    assert(old_self.bitmap_sync());
                    assert(nth_bit!(old_self.sl_bitmap[bi.0 as int], bi.1 as usize)
                        <==> old_self.shadow_freelist@.m[bi].len() > 0);
                    assert(nth_bit!(new_self.sl_bitmap[bi.0 as int], bi.1 as usize)
                        == nth_bit!(old_self.sl_bitmap[bi.0 as int], bi.1 as usize));
                }
            };
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
