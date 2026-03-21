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
    pub struct AllBlocks<const FLLEN: usize, const SLLEN: usize> {
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

        /// Opaque null-check predicate to avoid raw_ptr trigger explosion in freelist specs.
        #[verifier::opaque]
        pub(crate) open spec fn ptr_is_null<T>(p: *mut T) -> bool {
            p@.addr == 0
        }

        /// Opaque wrapper for pointer address well-formedness facts to avoid raw_ptr trigger explosion.
        #[verifier::opaque]
        pub(crate) open spec fn wf_node_ptr(ptr: *mut BlockHdr) -> bool {
            &&& ptr@.addr != 0
            &&& 0 <= ptr@.addr
            &&& (ptr@.addr as int) % (GRANULARITY as int) == 0
        }

        /// Closed wrapper: physical next pointer has expected address and provenance.
        /// Prevents ptr@ terms from leaking into caller SMT context.
        pub(crate) closed spec fn phys_next_matches(
            next_ptr: *mut BlockHdr,
            cur_ptr: *mut BlockHdr,
            size: usize,
        ) -> bool {
            &&& next_ptr@.addr == cur_ptr@.addr + (size & SIZE_SIZE_MASK)
            &&& next_ptr@.provenance == cur_ptr@.provenance
        }

        /// Intro: raw addr/provenance facts → phys_next_matches atom.
        pub(crate) proof fn lemma_phys_next_matches_intro(
            next_ptr: *mut BlockHdr,
            cur_ptr: *mut BlockHdr,
            size: usize,
        )
            requires
                next_ptr@.addr == cur_ptr@.addr + (size & SIZE_SIZE_MASK),
                next_ptr@.provenance == cur_ptr@.provenance,
            ensures
                Self::phys_next_matches(next_ptr, cur_ptr, size),
        { }

        /// Elim: phys_next_matches atom → raw addr/provenance facts.
        /// Call inside `assert(...) by { ... }` to scope ptr@ term exposure.
        pub(crate) proof fn lemma_phys_next_matches_elim(
            next_ptr: *mut BlockHdr,
            cur_ptr: *mut BlockHdr,
            size: usize,
        )
            requires
                Self::phys_next_matches(next_ptr, cur_ptr, size),
            ensures
                next_ptr@.addr == cur_ptr@.addr + (size & SIZE_SIZE_MASK),
                next_ptr@.provenance == cur_ptr@.provenance,
        { }

        /// Bridge lemma: constructs wf_node_ptr from explicit addr/alignment facts.
        pub(crate) proof fn lemma_wf_node_ptr_from_facts(ptr: *mut BlockHdr)
            requires
                ptr@.addr != 0,
                0 <= ptr@.addr,
                (ptr@.addr as int) % (GRANULARITY as int) == 0,
            ensures
                Self::wf_node_ptr(ptr)
        {
            reveal(AllBlocks::wf_node_ptr);
        }

        /// Bridge lemma: derives raw pointer facts from wf_node.
        pub(crate) proof fn lemma_wf_node_ptr(self, i: int)
            requires
                self.wf(),
                0 <= i < self.ptrs@.len(),
            ensures
                self.ptrs@[i]@.addr != 0,
                0 <= self.ptrs@[i]@.addr,
                (self.ptrs@[i]@.addr as int) % (GRANULARITY as int) == 0,
                Self::wf_node_ptr(self.ptrs@[i]),
        {
            assert(self.wf_node(i));
            reveal(AllBlocks::wf_node_ptr);
        }

        /// Group B: Glue invariants between physical state & tracked/ghost state.
        /// No ptr@ terms — uses value_at(ptr) only.
        pub(crate) closed spec fn wf_node_glue(self, i: int) -> bool
            recommends 0 <= i < self.ptrs@.len()
        {
            let ptr = self.ptrs@[i];
            &&& self.value_at(ptr).prev_phys_block@.addr != 0 ==> (self.phys_prev_of(i)
                    matches Some(p) && p == self.value_at(ptr).prev_phys_block)
            &&& self.value_at(ptr).prev_phys_block@.addr == 0 ==> self.phys_prev_of(i) is None
            &&& if self.value_at(ptr).is_sentinel() {
                &&& i == self.ptrs@.len() - 1
                &&& (self.value_at(ptr).size & SIZE_SIZE_MASK) == 0
            } else {
                &&& BlockIndex::<FLLEN, SLLEN>::valid_block_size((self.value_at(ptr).size & SIZE_SIZE_MASK) as int)
                &&& (self.value_at(ptr).size as int) + (ptr as int) < usize::MAX
                &&& self.phys_next_of(i) is Some
            }
            &&& if self.value_at(ptr).is_free() {
                self.perms@[ptr].free_link_perm matches Some(p)
                    && p.ptr() == get_freelink_ptr_spec(ptr)
            } else { true }
        }

        /// Group C: Structural invariants involving ptr@ terms.
        /// Primary source of ptr@ trigger explosion — kept closed.
        pub(crate) closed spec fn wf_node_structural(self, i: int) -> bool
            recommends 0 <= i < self.ptrs@.len()
        {
            let ptr = self.ptrs@[i];
            &&& self.phys_next_of(i) matches Some(next_ptr) ==> {
                &&& next_ptr@.addr == ptr@.addr + (self.value_at(ptr).size & SIZE_SIZE_MASK)
                &&& next_ptr@.provenance == ptr@.provenance
            }
            &&& if self.value_at(ptr).is_free() {
                self.phys_next_of(i) matches Some(next_ptr)
                    && !self.value_at(next_ptr).is_free()
            } else { true }
        }

        /// States that each block at `self.ptr[i]` is well-formed.
        /// Composed of Group A (inline) + Group B (opaque) + Group C (opaque).
        pub(crate) open spec fn wf_node(self, i: int) -> bool
            recommends 0 <= i < self.ptrs@.len()
        {
            let ptr = self.ptrs@[i];
            // Group A (inline — no ptr@ terms)
            &&& Self::wf_node_ptr(ptr)
            &&& self.perms@.contains_key(ptr)
            &&& ptr == self.perms@[ptr].points_to.ptr()
            &&& self.perms@[ptr].wf()
            // Group B+C (opaque atoms)
            &&& self.wf_node_glue(i)
            &&& self.wf_node_structural(i)
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
            assert forall|i: int| 0 <= i < self.ptrs@.len() - 1
                implies (#[trigger] self.ptrs@[i] as int) < self.ptrs@[i + 1] as int
                by {
                    assert(self.wf_node(i));
                };
            lemma_ptrs_no_duplicates_from_ordered(self.ptrs@);
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
            assert forall|i: int| 0 <= i < self.ptrs@.len()
                implies self.perms@[self.ptrs@[i]].wf()
            by {
                assert(self.wf_node(i));
            };
        }

        pub(crate) proof fn lemma_node_is_wf(self, x: *mut BlockHdr)
            requires self.wf(), self.contains(x)
            ensures self.wf_node(self.get_ptr_internal_index(x))
        {
        }

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
                old_ab.pool_size_bounded(),
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
            Self::lemma_pool_size_bounded_transfer(&old_ab, &new_ab);
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

        /// Generalized version of lemma_all_blocks_wf_after_replace_block_perm.
        /// Instead of requiring perms@ == old.insert(block, new_perm), requires
        /// only that non-block nodes have preserved points_to, mem, and wf().
        /// This handles cases where next_free_candidate's free_link_perm also changes.
        pub(crate) proof fn lemma_replace_one_preserve_rest_wf(
            old_ab: AllBlocks<FLLEN, SLLEN>,
            new_ab: AllBlocks<FLLEN, SLLEN>,
            block: *mut BlockHdr,
        )
            requires
                old_ab.wf(),
                old_ab.ptrs@.contains(block),
                new_ab.ptrs@ == old_ab.ptrs@,
                !new_ab.value_at(block).is_free(),
                new_ab.wf_node(old_ab.get_ptr_internal_index(block)),
                forall|i: int| 0 <= i < old_ab.ptrs@.len() && old_ab.ptrs@[i] != block ==> ({
                    let p = old_ab.ptrs@[i];
                    &&& new_ab.perms@.contains_key(p)
                    &&& new_ab.perms@[p].points_to == old_ab.perms@[p].points_to
                    &&& new_ab.perms@[p].mem == old_ab.perms@[p].mem
                    &&& new_ab.perms@[p].wf()
                }),
            ensures
                new_ab.wf(),
        {
            let bi = old_ab.get_ptr_internal_index(block);
            old_ab.lemma_wf_nodup();
            assert(ghost_pointer_ordered(new_ab.ptrs@));
            Self::lemma_pool_size_bounded_transfer(&old_ab, &new_ab);
            assert forall|i: int| 0 <= i < new_ab.ptrs@.len() implies new_ab.wf_node(i) by {
                if i == bi {
                    assert(new_ab.wf_node(i));
                } else {
                    let ptr = new_ab.ptrs@[i];
                    assert(ptr != block) by {
                        if ptr == block {
                            assert(old_ab.ptrs@[i] == block);
                            assert(old_ab.ptrs@[bi] == block);
                            lemma_ptrs_no_duplicates_eq_index(old_ab.ptrs@, i, bi);
                        }
                    };
                    assert(old_ab.wf_node(i));
                    assert(new_ab.value_at(ptr) == old_ab.value_at(ptr));
                    assert(new_ab.value_at(ptr).is_free() ==> {
                        let next_ptr = new_ab.phys_next_of(i).unwrap();
                        !new_ab.value_at(next_ptr).is_free()
                    }) by {
                        if new_ab.value_at(ptr).is_free() {
                            assert(old_ab.value_at(ptr).is_free());
                            assert(old_ab.phys_next_of(i) is Some);
                            let old_next_ptr = old_ab.phys_next_of(i).unwrap();
                            let next_ptr = new_ab.phys_next_of(i).unwrap();
                            assert(next_ptr == old_next_ptr);
                            if next_ptr == block {
                                assert(!new_ab.value_at(next_ptr).is_free());
                            } else {
                                assert(new_ab.perms@[next_ptr].points_to == old_ab.perms@[next_ptr].points_to);
                                assert(!old_ab.value_at(old_next_ptr).is_free());
                                assert(new_ab.value_at(next_ptr) == old_ab.value_at(old_next_ptr));
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

        /// Hides the forall over wf_node from the external SMT context.
        pub(crate) closed spec fn all_nodes_wf(self) -> bool {
            forall|i: int| 0 <= i < self.ptrs@.len() ==> self.wf_node(i)
        }

        /// Pool size upper bound: the span from first block to sentinel
        /// is strictly less than the maximum block size.
        /// Ensures any block's physical size is within valid_block_size range.
        pub(crate) closed spec fn pool_size_bounded(self) -> bool {
            self.ptrs@.len() >= 2 ==>
                (self.ptrs@.last() as usize as int) - (self.ptrs@[0] as usize as int)
                    < pow2(FLLEN as nat) * GRANULARITY as int
        }

        /// Well-formedness for the global list structure.
        pub(crate) open spec fn wf(self) -> bool {
            &&& self.all_nodes_wf()
            &&& ghost_pointer_ordered(self.ptrs@)
            &&& self.pool_size_bounded()
        }

        /// Extract: wf() → wf_node(i), with reveal scoped to lemma body.
        pub(crate) proof fn lemma_wf_extract_node(&self, i: int)
            requires self.wf(), 0 <= i < self.ptrs@.len()
            ensures self.wf_node(i)
        {
        }

        /// Opaque atom extraction: provides wf_node_glue(i) without individual facts.
        pub(crate) proof fn lemma_wf_glue_atom(&self, i: int)
            requires self.wf(), 0 <= i < self.ptrs@.len()
            ensures self.wf_node_glue(i)
        {
            assert(self.wf_node(i));
        }

        /// Opaque atom extraction: provides wf_node_structural(i) without individual facts.
        /// No ptr@ terms leak to caller scope.
        pub(crate) proof fn lemma_wf_structural_atom(&self, i: int)
            requires self.wf(), 0 <= i < self.ptrs@.len()
            ensures self.wf_node_structural(i)
        {
            assert(self.wf_node(i));
        }

        /// Group A bridge: extracts perms contains + ptr match + perm.wf()
        /// without exposing ptr@ terms (no ptrs_mut_eq trigger).
        pub(crate) proof fn lemma_wf_perm_wf(&self, i: int)
            requires self.wf(), 0 <= i < self.ptrs@.len()
            ensures
                self.perms@.contains_key(self.ptrs@[i]),
                self.ptrs@[i] == self.perms@[self.ptrs@[i]].points_to.ptr(),
                self.perms@[self.ptrs@[i]].wf(),
        {
            assert(self.wf_node(i));
        }

        /// Group B extraction: wf() → individual glue facts + opaque atom.
        pub(crate) proof fn lemma_wf_glue_facts(&self, i: int)
            requires self.wf(), 0 <= i < self.ptrs@.len()
            ensures
                self.value_at(self.ptrs@[i]).prev_phys_block@.addr != 0
                    ==> (self.phys_prev_of(i) matches Some(p)
                        && p == self.value_at(self.ptrs@[i]).prev_phys_block),
                self.value_at(self.ptrs@[i]).prev_phys_block@.addr == 0
                    ==> self.phys_prev_of(i) is None,
                !self.value_at(self.ptrs@[i]).is_sentinel() ==> {
                    &&& BlockIndex::<FLLEN, SLLEN>::valid_block_size(
                        (self.value_at(self.ptrs@[i]).size & SIZE_SIZE_MASK) as int)
                    &&& (self.value_at(self.ptrs@[i]).size as int) + (self.ptrs@[i] as int) < usize::MAX
                    &&& self.phys_next_of(i) is Some
                },
                self.value_at(self.ptrs@[i]).is_sentinel() ==> {
                    &&& i == self.ptrs@.len() - 1
                    &&& (self.value_at(self.ptrs@[i]).size & SIZE_SIZE_MASK) == 0
                },
                self.value_at(self.ptrs@[i]).is_free() ==> (
                    self.perms@[self.ptrs@[i]].free_link_perm matches Some(p)
                        && p.ptr() == get_freelink_ptr_spec(self.ptrs@[i])
                ),
                self.wf_node_glue(i),
        {
            assert(self.wf_node(i));
        }

        /// Group C extraction: wf() → individual structural facts + opaque atom.
        /// Returns phys_next_matches atom instead of raw ptr@ terms to prevent
        /// ptrs_mut_eq broadcast trigger cascade in callers.
        pub(crate) proof fn lemma_wf_structural_facts(&self, i: int)
            requires self.wf(), 0 <= i < self.ptrs@.len()
            ensures
                self.phys_next_of(i) matches Some(next_ptr) ==>
                    Self::phys_next_matches(
                        next_ptr, self.ptrs@[i], self.value_at(self.ptrs@[i]).size),
                self.value_at(self.ptrs@[i]).is_free() ==> (
                    self.phys_next_of(i) matches Some(next_ptr)
                        && !self.value_at(next_ptr).is_free()
                ),
                self.wf_node_structural(i),
        {
            assert(self.wf_node(i));
        }

        /// Group B construction: individual facts → opaque atom.
        pub(crate) proof fn lemma_construct_wf_node_glue(&self, i: int)
            requires
                0 <= i < self.ptrs@.len(),
                self.perms@.contains_key(self.ptrs@[i]),
                self.perms@[self.ptrs@[i]].points_to.is_init(),
                ({
                    let ptr = self.ptrs@[i];
                    &&& self.value_at(ptr).prev_phys_block@.addr != 0 ==> (self.phys_prev_of(i)
                            matches Some(p) && p == self.value_at(ptr).prev_phys_block)
                    &&& self.value_at(ptr).prev_phys_block@.addr == 0 ==> self.phys_prev_of(i) is None
                    &&& if self.value_at(ptr).is_sentinel() {
                        &&& i == self.ptrs@.len() - 1
                        &&& (self.value_at(ptr).size & SIZE_SIZE_MASK) == 0
                    } else {
                        &&& BlockIndex::<FLLEN, SLLEN>::valid_block_size(
                            (self.value_at(ptr).size & SIZE_SIZE_MASK) as int)
                        &&& (self.value_at(ptr).size as int) + (ptr as int) < usize::MAX
                        &&& self.phys_next_of(i) is Some
                    }
                    &&& if self.value_at(ptr).is_free() {
                        self.perms@[ptr].free_link_perm matches Some(p)
                            && p.ptr() == get_freelink_ptr_spec(ptr)
                    } else { true }
                }),
            ensures self.wf_node_glue(i)
        {
        }

        /// Group C construction: individual facts → opaque atom.
        pub(crate) proof fn lemma_construct_wf_node_structural(&self, i: int)
            requires
                0 <= i < self.ptrs@.len(),
                self.perms@.contains_key(self.ptrs@[i]),
                self.perms@[self.ptrs@[i]].points_to.is_init(),
                ({
                    let ptr = self.ptrs@[i];
                    &&& self.phys_next_of(i) matches Some(next_ptr) ==>
                        Self::phys_next_matches(next_ptr, ptr, self.value_at(ptr).size)
                    &&& if self.value_at(ptr).is_free() {
                        self.phys_next_of(i) matches Some(next_ptr)
                            && !self.value_at(next_ptr).is_free()
                    } else { true }
                }),
            ensures self.wf_node_structural(i)
        {
        }

        /// Transfer lemma: derives wf_node components for new_ab from old_ab
        /// without leaking ptr@ terms to the caller scope.
        /// The value_at(next_ptr) precondition is only required when the node
        /// is free, since wf_node_structural's free-next check is the only consumer.
        pub(crate) proof fn lemma_transfer_wf_node(
            old_ab: &Self, new_ab: &Self, old_i: int, new_i: int
        )
            requires
                old_ab.wf(),
                0 <= old_i < old_ab.ptrs@.len(),
                0 <= new_i < new_ab.ptrs@.len(),
                old_ab.ptrs@[old_i] == new_ab.ptrs@[new_i],
                new_ab.perms@.contains_key(new_ab.ptrs@[new_i]),
                old_ab.perms@[old_ab.ptrs@[old_i]] == new_ab.perms@[new_ab.ptrs@[new_i]],
                old_ab.phys_prev_of(old_i) == new_ab.phys_prev_of(new_i),
                old_ab.phys_next_of(old_i) == new_ab.phys_next_of(new_i),
                (old_ab.value_at(old_ab.ptrs@[old_i]).is_free()
                    && old_ab.phys_next_of(old_i) is Some)
                    ==> old_ab.value_at(old_ab.phys_next_of(old_i).unwrap())
                        == new_ab.value_at(new_ab.phys_next_of(new_i).unwrap()),
            ensures
                new_ab.wf_node_glue(new_i),
                new_ab.wf_node_structural(new_i),
                Self::wf_node_ptr(new_ab.ptrs@[new_i]),
                new_ab.ptrs@[new_i] == new_ab.perms@[new_ab.ptrs@[new_i]].points_to.ptr(),
                new_ab.perms@[new_ab.ptrs@[new_i]].wf(),
        {
            assert(old_ab.wf_node(old_i));
        }

        /// Wrapper: derives new_ab.wf() from old_ab.wf() after block perm replacement.
        /// Caller does not need reveal(AllBlocks::all_nodes_wf).
        pub(crate) proof fn lemma_replace_block_perm_from_wf(
            old_ab: AllBlocks<FLLEN, SLLEN>,
            new_ab: AllBlocks<FLLEN, SLLEN>,
            block: *mut BlockHdr,
            new_perm: BlockPerm,
        )
            requires
                old_ab.wf(),
                old_ab.ptrs@.contains(block),
                new_ab.ptrs@ == old_ab.ptrs@,
                new_ab.perms@ == old_ab.perms@.insert(block, new_perm),
                new_perm.points_to.ptr() == block,
                new_perm.wf(),
                !new_perm.points_to.value().is_free(),
                new_ab.wf_node(old_ab.get_ptr_internal_index(block)),
            ensures
                new_ab.wf(),
        {
            old_ab.lemma_wf_nodup();
            Self::lemma_all_blocks_wf_after_replace_block_perm(
                old_ab, new_ab, block, new_perm);
        }

        /// Reconstruct: parts → wf(), with reveal scoped to lemma body.
        pub(crate) proof fn lemma_wf_from_nodes(&self)
            requires
                forall|i: int| 0 <= i < self.ptrs@.len() ==> self.wf_node(i),
                ghost_pointer_ordered(self.ptrs@),
                self.pool_size_bounded(),
            ensures self.wf()
        {
        }

        /// Bridge lemma: extract pool_size_bounded facts from wf().
        pub(crate) proof fn lemma_pool_size_bounded(&self)
            requires self.wf()
            ensures self.pool_size_bounded()
        { }

        /// Trivial case: pool_size_bounded holds when ptrs@ has fewer than 2 elements.
        pub(crate) proof fn lemma_pool_size_bounded_trivial(&self)
            requires self.ptrs@.len() < 2
            ensures self.pool_size_bounded()
        {
            reveal(AllBlocks::pool_size_bounded);
        }

        /// Construct pool_size_bounded from explicit span bound.
        pub(crate) proof fn lemma_pool_size_bounded_from_span(&self)
            requires
                self.ptrs@.len() >= 2 ==>
                    (self.ptrs@.last() as usize as int) - (self.ptrs@[0] as usize as int)
                        < pow2(FLLEN as nat) * GRANULARITY as int,
            ensures self.pool_size_bounded()
        {
            reveal(AllBlocks::pool_size_bounded);
        }

        /// Transfer: pool_size_bounded is preserved when ptrs@ is unchanged.
        pub(crate) proof fn lemma_pool_size_bounded_transfer(
            old_ab: &Self, new_ab: &Self)
            requires
                old_ab.pool_size_bounded(),
                new_ab.ptrs@ == old_ab.ptrs@,
            ensures
                new_ab.pool_size_bounded(),
        {
            reveal(AllBlocks::pool_size_bounded);
        }

        /// Transfer: pool_size_bounded is preserved when first and last
        /// elements of ptrs@ are preserved and the bound still holds.
        pub(crate) proof fn lemma_pool_size_bounded_from_sub(
            old_ab: &Self, new_ab: &Self)
            requires
                old_ab.pool_size_bounded(),
                old_ab.ptrs@.len() >= 2,
                new_ab.ptrs@.len() >= 2,
                new_ab.ptrs@[0] == old_ab.ptrs@[0],
                new_ab.ptrs@.last() == old_ab.ptrs@.last(),
            ensures
                new_ab.pool_size_bounded(),
        {
            reveal(AllBlocks::pool_size_bounded);
        }

        /// Bridge lemma: for any pair of adjacent blocks in the ordered list,
        /// the address span is bounded by the pool size.
        /// Requires pool_size_bounded and ghost_pointer_ordered separately,
        /// so it can be called before wf() is fully established.
        pub(crate) proof fn lemma_pool_bound_implies_span_bound(&self, i: int)
            requires
                ghost_pointer_ordered(self.ptrs@),
                self.pool_size_bounded(),
                self.ptrs@.len() >= 2,
                0 <= i < self.ptrs@.len() - 1,
            ensures
                (self.ptrs@[i + 1] as usize as int) - (self.ptrs@[i] as usize as int)
                    < pow2(FLLEN as nat) * GRANULARITY as int
        {
            reveal(AllBlocks::pool_size_bounded);
            lemma_ghost_pointer_ordered_index(self.ptrs@, 0, i);
            lemma_ghost_pointer_ordered_index(self.ptrs@, i + 1, self.ptrs@.len() as int - 1);
        }

        /// Generalized span bound: any pair (i, j) with i < j has span < pool bound.
        pub(crate) proof fn lemma_pool_bound_any_span(&self, i: int, j: int)
            requires
                ghost_pointer_ordered(self.ptrs@),
                self.pool_size_bounded(),
                self.ptrs@.len() >= 2,
                0 <= i < self.ptrs@.len(),
                0 <= j < self.ptrs@.len(),
                i < j,
            ensures
                (self.ptrs@[j] as usize as int) - (self.ptrs@[i] as usize as int)
                    < pow2(FLLEN as nat) * GRANULARITY as int
        {
            reveal(AllBlocks::pool_size_bounded);
            lemma_ghost_pointer_ordered_index(self.ptrs@, 0, i);
            lemma_ghost_pointer_ordered_index(self.ptrs@, j, self.ptrs@.len() as int - 1);
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
    pub struct ShadowFreelist<const FLLEN: usize, const SLLEN: usize> {
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

        /// Shift pi indices after inserting a new pointer at ptrs@[insert_ai+1].
        pub(crate) open spec fn ii_shift_after_insert(self, insert_ai: int) -> Self {
            Self {
                m: self.m,
                pi: self.pi.map_values(|ai: int| if insert_ai + 1 <= ai { ai + 1 } else { ai }),
            }
        }

        /// Shift pi indices after removing a pointer at ptrs@[remove_ai].
        pub(crate) open spec fn ii_shift_after_remove(self, remove_ai: int) -> Self {
            Self {
                m: self.m,
                pi: self.pi.map_values(|ai: int| if ai > remove_ai { (ai - 1) as int } else { ai }),
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
            all_blocks.lemma_wf_nodup();
            let k = all_blocks.get_ptr_internal_index(node);
            // Contrapositive: assume pi.values().contains(k) and derive contradiction
            if self.pi.values().contains(k) {
                let key = choose|key: (BlockIndex<FLLEN, SLLEN>, int)|
                    self.pi.dom().contains(key) && self.pi[key] == k;
                let (idx, m) = key;
                // is_identity_injection totality: pi.contains_key <==> idx.wf() && valid range
                assert(idx.wf() && 0 <= m < self.m[idx].len());
                // is_identity_injection correctness: m[idx][m] == ptrs@[pi[(idx,m)]]
                assert(self.m[idx][m] == all_blocks.ptrs@[k]);
                assert(all_blocks.ptrs@[k] == node);
                // Therefore node is in freelist bucket → self.contains(node) → contradiction
                assert(self.m[idx].contains(node));
                assert(self.contains(node));
            }
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
