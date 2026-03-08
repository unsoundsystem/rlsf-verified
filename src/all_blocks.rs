use crate::block::*;
use crate::block_index::BlockIndex;
use crate::block_index::GRANULARITY;
use crate::ordered_pointer_list::*;
use crate::parameters::SIZE_SIZE_MASK;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd::raw_ptr::*;
#[cfg(verus_keep_ghost)]
use vstd::relations::injective;

verus! {

    /// Tracks global structure of the header linkage and memory states
    pub(crate) struct AllBlocks<const FLLEN: usize, const SLLEN: usize> {
        /// Pointers for all blocks, ordered by address.
        pub ptrs: Ghost<Seq<*mut BlockHdr>>,
        /// Tracked permissions for all blocks, indexed by pointer.
        pub perms: Tracked<Map<*mut BlockHdr, BlockPerm>>,
    }

    impl<const FLLEN: usize, const SLLEN: usize> AllBlocks<FLLEN, SLLEN> {
        pub(crate) open spec fn value_at(self, ptr: *mut BlockHdr) -> BlockHdr
            recommends
            self.contains(ptr),
            self.perms@[ptr].points_to.is_init()
        {
            self.perms@[ptr].points_to.value()
        }

        pub(crate) open spec fn contains(self, ptr: *mut BlockHdr) -> bool {
            self.ptrs@.contains(ptr)
        }

        /// States that each block at `self.ptr[i]` is well-formed i.e.
        ///
        /// * Block is properly connected to the global list
        ///     * Ghost state `self.ptrs` properly reflecting physical state;
        ///       for each p: `self.ptrs[i]`,
        ///         * self.perms[p] is defined, `Init` and pointer matches p
        ///         * `self.ptrs` reflects the order of linked list;
        ///           let pr = self.perms[i],
        ///              * 0 < i <= self.ptrs.len():
        ///                  pr.value().prev_phys_block is Some(p') ==> p' == self.ptr[i-1]
        ///              * i == 0: pr.value().prev_phys_block is None
        pub(crate) open spec fn wf_node(self, i: int) -> bool
            recommends 0 <= i < self.ptrs@.len()
        {
            let ptr = self.ptrs@[i];
            // --- Well-formedness for tracked/ghost states
            &&& ptr@.addr != 0
            &&& 0 <= ptr@.addr
            // All blocks are GRANULARITY-aligned.
            &&& (ptr@.addr as int) % (GRANULARITY as int) == 0
            &&& self.perms@.contains_key(ptr)
            &&& ptr == self.perms@[ptr].points_to.ptr()
            &&& self.perms@[ptr].wf()

            // --- Glue invariants between physical state & tracked/ghost state
            // prev_phys_block invariant
            &&& self.value_at(ptr).prev_phys_block@.addr != 0 ==> (self.phys_prev_of(i)
                    matches Some(p) &&
                    p == self.value_at(ptr).prev_phys_block)
            &&& self.value_at(ptr).prev_phys_block@.addr == 0 ==> self.phys_prev_of(i) is None

            // if sentinel flag is present then ...
            &&& if self.value_at(ptr).is_sentinel() {
                // it's last element in ptrs
                &&& i == self.ptrs@.len() - 1
                // sentinel block has size of 0
                &&& self.value_at(ptr).size == 0
            } else {
                // there no zero-sized block except sentinel block
                &&& BlockIndex::<FLLEN, SLLEN>::valid_block_size((self.value_at(ptr).size & SIZE_SIZE_MASK) as int)
                &&& (self.value_at(ptr).size as int) + (ptr as int) < usize::MAX
                &&& self.phys_next_of(i) is Some
            }
            // if used flag is not present then it connected to freelist
            &&& if self.value_at(ptr).is_free() {
                self.perms@[ptr].free_link_perm matches Some(p)
                    && p.ptr() == get_freelink_ptr_spec(ptr)
            } else { true }

            // --- Invariants on tracked/ghost states
            // Next block address
            &&& self.phys_next_of(i) matches Some(next_ptr) ==> {
                &&& next_ptr@.addr == ptr@.addr + (self.value_at(ptr).size & SIZE_SIZE_MASK)
                &&& next_ptr@.provenance == ptr@.provenance
            }
            // No adjacent free blocks
            &&& if self.value_at(ptr).is_free() {
                self.phys_next_of(i) matches Some(next_ptr)
                    && !self.value_at(next_ptr).is_free()
            } else { true }

        }

        pub(crate) open spec fn phys_next_of(self, i: int) -> Option<*mut BlockHdr> {
            if self.ptrs@.len() - 1 == i {
                None
            } else {
                Some(self.ptrs@[i + 1])
            }
        }

        pub(crate) proof fn lemma_wf_nodup(self)
            requires self.wf()
            ensures ptrs_no_duplicates(self.ptrs@)
        {
            reveal(ptrs_no_duplicates);
            assert forall|i: int| 0 <= i < self.ptrs@.len() - 1
                implies (#[trigger] self.ptrs@[i] as int) < self.ptrs@[i + 1] as int
                by {
                    assert(self.wf_node(i));
                }
        }

        pub(crate) proof fn lemma_phys_next_is_distinct(self, i: int)
            requires
                self.wf(),
                0 <= i < self.ptrs@.len(),
                self.phys_next_of(i) is Some,
            ensures
                self.phys_next_of(i).unwrap() != self.ptrs@[i]
        {
            assert(self.wf_node(i));
            let ptr = self.ptrs@[i];
            let next_ptr = self.phys_next_of(i).unwrap();
            assert(self.phys_next_of(i) matches Some(p) ==> {
                &&& p@.addr == ptr@.addr + (self.value_at(ptr).size & SIZE_SIZE_MASK)
                &&& p@.provenance == ptr@.provenance
            });
            assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size((self.value_at(ptr).size & SIZE_SIZE_MASK) as int));
            assert((self.value_at(ptr).size & SIZE_SIZE_MASK) as int >= GRANULARITY as int);
            assert(0 < (self.value_at(ptr).size & SIZE_SIZE_MASK) as int);
            assert(next_ptr@.addr == ptr@.addr + (self.value_at(ptr).size & SIZE_SIZE_MASK));
            assert(next_ptr@.addr > ptr@.addr);
            assert(next_ptr != ptr);
        }

        pub(crate) proof fn lemma_phys_prev_is_distinct(self, i: int)
            requires
                self.wf(),
                0 <= i < self.ptrs@.len(),
                self.phys_prev_of(i) is Some,
            ensures
                self.phys_prev_of(i).unwrap() != self.ptrs@[i]
        {
            assert(0 < i);
            assert(self.wf_node(i - 1));
            let prev_ptr = self.phys_prev_of(i).unwrap();
            let ptr = self.ptrs@[i];
            assert(prev_ptr == self.ptrs@[i - 1]);
            assert(self.phys_next_of(i - 1) == Some(ptr));
            assert(self.phys_next_of(i - 1) matches Some(next_ptr) ==> {
                &&& next_ptr@.addr == prev_ptr@.addr + (self.value_at(prev_ptr).size & SIZE_SIZE_MASK)
                &&& next_ptr@.provenance == prev_ptr@.provenance
            });
            assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size((self.value_at(prev_ptr).size & SIZE_SIZE_MASK) as int));
            assert((self.value_at(prev_ptr).size & SIZE_SIZE_MASK) as int >= GRANULARITY as int);
            assert(0 < (self.value_at(prev_ptr).size & SIZE_SIZE_MASK) as int);
            assert(ptr@.addr == prev_ptr@.addr + (self.value_at(prev_ptr).size & SIZE_SIZE_MASK));
            assert(ptr@.addr > prev_ptr@.addr);
            assert(prev_ptr != ptr);
        }

        pub(crate) proof fn lemma_block_wf(self)
            requires self.wf(),
            ensures forall|i: int| 0 <= i < self.ptrs@.len()
                ==> self.perms@[self.ptrs@[i]].wf()
        {

        }

        pub(crate) proof fn lemma_node_is_wf(self, x: *mut BlockHdr)
            requires self.wf(), self.contains(x)
            ensures self.wf_node(self.get_ptr_internal_index(x))
        {}

        pub(crate) proof fn lemma_all_blocks_wf_after_replace_block_perm(
            old_ab: AllBlocks<FLLEN, SLLEN>,
            new_ab: AllBlocks<FLLEN, SLLEN>,
            block: *mut BlockHdr,
            new_perm: BlockPerm,
        )
            requires
                old_ab.ptrs@.contains(block),
                ghost_pointer_ordered(old_ab.ptrs@),
                ptrs_no_duplicates(old_ab.ptrs@),
                forall|i: int| 0 <= i < old_ab.ptrs@.len() && old_ab.ptrs@[i] != block ==> old_ab.wf_node(i),
                new_ab.ptrs@ == old_ab.ptrs@,
                new_ab.perms@ == old_ab.perms@.insert(block, new_perm),
                new_perm.points_to.ptr() == block,
                new_perm.wf(),
                !new_perm.points_to.value().is_free(),
                new_ab.wf_node(old_ab.get_ptr_internal_index(block)),
            ensures
                new_ab.wf(),
        {
            let bi = old_ab.get_ptr_internal_index(block);
            assert(ghost_pointer_ordered(new_ab.ptrs@));
            assert forall|i: int| 0 <= i < new_ab.ptrs@.len() implies new_ab.wf_node(i) by {
                if i == bi {
                    assert(new_ab.wf_node(i));
                } else {
                    assert(0 <= i < old_ab.ptrs@.len());
                    let ptr = old_ab.ptrs@[i];
                    assert(ptr == new_ab.ptrs@[i]);
                    assert(ptr != block) by {
                        if ptr == block {
                            assert(old_ab.ptrs@[i] == block);
                            assert(old_ab.ptrs@[bi] == block);
                            lemma_ptrs_no_duplicates_eq_index(old_ab.ptrs@, i, bi);
                            assert(i == bi);
                        }
                    };
                    assert(old_ab.wf_node(i));
                    assert(new_ab.perms@[ptr] == old_ab.perms@[ptr]);
                    assert(new_ab.value_at(ptr).is_free() ==> {
                        let next_ptr = new_ab.phys_next_of(i).unwrap();
                        !new_ab.value_at(next_ptr).is_free()
                    }) by {
                        if new_ab.value_at(ptr).is_free() {
                            assert(old_ab.wf_node(i));
                            assert(old_ab.value_at(ptr).is_free());
                            assert(old_ab.phys_next_of(i) is Some);
                            let old_next_ptr = old_ab.phys_next_of(i).unwrap();
                            let next_ptr = new_ab.phys_next_of(i).unwrap();
                            assert(next_ptr == old_next_ptr);
                            if next_ptr == block {
                                assert(!new_ab.value_at(next_ptr).is_free());
                            } else {
                                assert(old_ab.value_at(old_next_ptr).is_free() ==> {
                                    old_ab.phys_next_of(i) matches Some(n)
                                        && !old_ab.value_at(n).is_free()
                                });
                                assert(!old_ab.value_at(old_next_ptr).is_free());
                                assert(new_ab.value_at(next_ptr) == old_ab.value_at(old_next_ptr));
                                assert(!new_ab.value_at(next_ptr).is_free());
                            }
                        }
                    };
                    assert(new_ab.wf_node(i));
                }
            };
        }


        pub(crate) open spec fn phys_prev_of(self, i: int) -> Option<*mut BlockHdr> {
            if i == 0 {
                None
            } else {
                Some(self.ptrs@[i - 1])
            }
        }

        pub(crate) open spec fn is_sentinel_pointer(self, ptr: *mut BlockHdr) -> bool
            recommends self.wf(), self.contains(ptr)
        {
            self.value_at(ptr).is_sentinel()
        }

        /// Well-formedness for the global list structure.
        pub(crate) open spec fn wf(self) -> bool {
            // Each block at ptrs[i] is well-formed.
            &&& forall|i: int| 0 <= i < self.ptrs@.len() ==> self.wf_node(i)
            &&& ghost_pointer_ordered(self.ptrs@)
        }


        // free_list_pred(ab, seq![1, 2, 3], ptr)
        // <==> ab.value_at(ptr) == 1
        //      && free_list_pred(ab, seq![2, 3],
        //              ab.perms@[ptr].free_link_perm.unwrap().value().next_free)
        //


        pub(crate) proof fn lemma_contains(self, x: *mut BlockHdr)
            requires self.wf(), self.contains(x)
            ensures self.perms@.contains_key(x)
        {
            let i = self.get_ptr_internal_index(x);
            assert(self.wf_node(i));
        }

        pub(crate) open spec fn get_ptr_internal_index(self, x: *mut BlockHdr) -> int
            recommends exists|i: int| self.ptrs@[i] == x && 0 <= i < self.ptrs@.len()
        {
            choose|i: int| self.ptrs@[i] == x && 0 <= i < self.ptrs@.len()
        }


        pub const fn empty() -> Self {
            Self {
                ptrs: Ghost(Seq::empty()),
                perms: Tracked(Map::tracked_empty()),
            }
        }

    }

    #[cfg(verus_keep_ghost)]
    pub(crate) type Pi<const FLLEN: usize, const SLLEN: usize> = Map<(BlockIndex<FLLEN, SLLEN>, int), int>;

    #[verifier::reject_recursive_types(FLLEN)]
    #[verifier::reject_recursive_types(SLLEN)]
    pub(crate) struct ShadowFreelist<const FLLEN: usize, const SLLEN: usize> {
        pub(crate) m: Map<BlockIndex<FLLEN, SLLEN>, Seq<*mut BlockHdr>>,
        #[cfg(verus_keep_ghost)]
        /// Keep index in all_blocks for each shadow_freelist nodes.
        pub(crate) pi: Pi<FLLEN, SLLEN>
    }

    impl<const FLLEN: usize, const SLLEN: usize> ShadowFreelist<FLLEN, SLLEN> {
        // Add all_blocks.ptrs[new_node_ai] at the head of m and update pi
        pub(crate) open spec fn ii_push_for_index(self,
            all_blocks: AllBlocks<FLLEN, SLLEN>,
            new_node_bi: BlockIndex<FLLEN, SLLEN>,
            new_node_ai: int
        ) -> Self
        recommends
            is_identity_injection(self, all_blocks.ptrs@),
            !self.pi.values().contains(new_node_ai)
        {
            let old_len = self.m[new_node_bi].len();
            Self {
                m: self.m.insert(new_node_bi, seq![all_blocks.ptrs@[new_node_ai]].add(self.m[new_node_bi])),
                //                   ┌  self.pi[(i, n)]          if i != idx
                // self.pi[(i, n)] = ┤  self.pi[(i, n - 1)]      if i == idx and n > 0
                //                   └  new_node_ai              if i == idx and n == 0
                pi: Map::new(
                    |k: (BlockIndex<FLLEN, SLLEN>, int)| {
                        if k.0 == new_node_bi {
                            0 <= k.1 < old_len + 1
                        } else {
                            self.pi.contains_key(k)
                        }
                    },
                    |k: (BlockIndex<FLLEN, SLLEN>, int)| {
                        if k.0 == new_node_bi {
                            if k.1 == 0 {
                                new_node_ai
                            } else {
                                self.pi[(new_node_bi, k.1 - 1)]
                            }
                        } else {
                            self.pi[k]
                        }
                    }
                )
            }
        }

        // Remove m[rm_bi][rm_pos] and shift pi entries for rm_bi.
        pub(crate) open spec fn ii_remove_for_index(self,
            all_blocks: AllBlocks<FLLEN, SLLEN>,
            rm_bi: BlockIndex<FLLEN, SLLEN>,
            rm_pos: int
        ) -> Self
        recommends
            rm_bi.wf(),
            is_identity_injection(self, all_blocks.ptrs@),
            0 <= rm_pos < self.m[rm_bi].len()
        {
            let new_m_idx = self.m[rm_bi].remove(rm_pos);
            let old_len = self.m[rm_bi].len();
            let last_key = (rm_bi, old_len - 1);
            Self {
                m: self.m.insert(rm_bi, new_m_idx),
                // new_pi[(i, n)]:
                //   - unchanged when i != rm_bi
                //   - unchanged when i == rm_bi && n < rm_pos
                //   - shifted from old (n + 1) when i == rm_bi && n >= rm_pos
                pi: self.pi.map_entries(|k: (BlockIndex<FLLEN, SLLEN>, int), v: int|
                    if k.0 == rm_bi {
                        if k.1 < rm_pos {
                            self.pi[(rm_bi, k.1)]
                        } else if rm_pos <= k.1 < old_len - 1 {
                            self.pi[(rm_bi, k.1 + 1)]
                        } else {
                            arbitrary()
                        }
                    } else { v }
                ).remove(last_key)
            }
        }

        pub(crate) open spec fn contains(self, node: *mut BlockHdr) -> bool {
            exists|i: BlockIndex<FLLEN, SLLEN>| i.wf()
                && self.m[i].contains(node)
        }

        pub(crate) open spec fn shadow_freelist_has_all_wf_index(self) -> bool {
            forall|idx: BlockIndex<FLLEN, SLLEN>|
                self.m.contains_key(idx) <==> idx.wf()

        }

        pub(crate) proof fn lemma_sfl_not_contains_iff_pi_undefined(
            self,
            all_blocks: AllBlocks<FLLEN, SLLEN>,
            node: *mut BlockHdr,
        )
            requires
                all_blocks.wf(),
                all_blocks.ptrs@.contains(node),
                is_identity_injection(self, all_blocks.ptrs@),
                !self.contains(node)
            ensures
                !self.pi.values().contains(all_blocks.get_ptr_internal_index(node))
        {
            // not exists (ind, n), self.m[ind][n] == node
            // i.e. forall (ind, n), self.m[ind][n] != node
            // forall x in pi.values(), 0 <= x < self.all_blocks.ptrs@.len()
            //
            // follows from ii cond
        }

    }

    /// Identitiy injection
    ///
    /// If we have set of pointers and identity injection to well-formed AllBlocks structure,
    /// there are well-formed BlockPerms corresponding to exactly same set of pointers
    ///
    /// The benefit of maintaining this simple invariant is to facilitate the proof of intrusive
    /// structures by establishing connection between different *views* on the data structure.
    ///
    pub(crate) open spec fn is_identity_injection<const FLLEN: usize, const SLLEN: usize>(
        sfl: ShadowFreelist<FLLEN, SLLEN>,
        all_block_ptrs: Seq<*mut BlockHdr>) -> bool
        recommends
            ptrs_no_duplicates(all_block_ptrs),
            sfl.shadow_freelist_has_all_wf_index()
    {
        &&& sfl.pi.is_injective()
        // totality
        &&& forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
            sfl.pi.contains_key((idx, m)) <==> idx.wf() && 0 <= m < sfl.m[idx].len()

        &&& forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
            idx.wf() && 0 <= m < sfl.m[idx].len() ==> {
                &&& 0 <= #[trigger] sfl.pi[(idx, m)] < all_block_ptrs.len()
                &&& sfl.m[idx][m] == all_block_ptrs[sfl.pi[(idx, m)]]
            }
    }

}
