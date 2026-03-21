use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::raw_ptr::{ptr_mut_write, ptr_ref, PointsTo, PointsToRaw};
#[cfg(verus_keep_ghost)]
use vstd::set_lib::set_int_range;

use crate::all_blocks::AllBlocks;
use crate::block::*;
use crate::block_index::BlockIndex;
use crate::ordered_pointer_list::*;
use crate::*;

verus! {

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    //#[verifier::external_body] // for spec debug
    pub fn deallocate(&mut self,
        ptr: *mut u8, align: usize,
        Tracked(token): Tracked<DeallocToken>, //NOTE: pattern matching to move out token
        Tracked(points_to): Tracked<PointsToRaw>, // permssion to previously allocated region
    )
    requires
        old(self).wf(),
        old(self).wf_dealloc(token),
        token.ptr == ptr,
        align == token.align,
        points_to.is_range(ptr as int, token.user_size),
        points_to.provenance() == ptr@.provenance,
    ensures self.wf()
    {
        proof { self.lemma_wf_components(); }
        let ghost block_ptr = self.user_block_map@[ptr];
        let block = unsafe { self.used_block_hdr_for_allocation(
            ptr, align, Tracked(points_to), Ghost(block_ptr), Ghost(token.user_size)) };
        unsafe { self.deallocate_block(block) };
    }

    #[inline]
    unsafe fn deallocate_block(&mut self, mut block: *mut BlockHdr)
    requires
        Self::parameter_validity(),
        old(self).all_blocks.wf(),
        old(self).all_freelist_wf(),
        old(self).bitmap_sync(),
        old(self).bitmap_wf(),
        old(self).size_class_condition(),
        old(self).all_blocks.contains(block),
        old(self).all_blocks.perms@.contains_key(block),
        old(self).all_blocks.perms@[block].points_to.is_init(),
        old(self).all_blocks.perms@[block].points_to.ptr() == block,
        old(self).all_blocks.perms@[block].points_to.value().size & SIZE_USED != 0,
        // mem covers full payload [block+BH, block+phys_size)
        old(self).all_blocks.perms@[block].mem.is_range(
            block as int + size_of::<BlockHdr>() as int,
            (old(self).all_blocks.perms@[block].points_to.value().size & SIZE_SIZE_MASK) as int
                - size_of::<BlockHdr>() as int),
        old(self).all_blocks.perms@[block].mem.provenance() == block@.provenance,
        old(self).all_blocks.perms@[block].overhead_mem.dom().is_empty(),
        old(self).all_blocks.perms@[block].pad_perm is None,
    ensures
        self.wf(),
    {
        let ghost block_i = self.all_blocks.get_ptr_internal_index(block);

        proof {
            self.all_blocks.lemma_node_is_wf(block);
            self.all_blocks.lemma_wf_perm_wf(block_i);
            self.all_blocks.lemma_wf_glue_facts(block_i);
            self.all_blocks.lemma_wf_structural_facts(block_i);
            self.all_blocks.lemma_wf_nodup();

            // Block is not sentinel: sentinel => size == 0, but SIZE_USED set => size >= 1
            assert(!self.all_blocks.value_at(block).is_sentinel()) by {
                if self.all_blocks.value_at(block).is_sentinel() {
                    assert(self.all_blocks.value_at(block).size == 0);
                    assert(0usize & SIZE_USED == 0) by (bit_vector)
                        requires SIZE_USED == 1usize;
                    assert(false);
                }
            };
            assert(self.all_blocks.phys_next_of(block_i) is Some);

            // Next phys facts
            let ghost next_i = block_i + 1;
            assert(0 <= next_i < self.all_blocks.ptrs@.len());
            self.all_blocks.lemma_wf_perm_wf(next_i);
            self.all_blocks.lemma_wf_glue_facts(next_i);
            self.all_blocks.lemma_wf_structural_facts(next_i);
            self.all_blocks.lemma_phys_next_is_distinct(block_i);

            // Prev phys facts (established now while wf() holds)
            if self.all_blocks.value_at(block).prev_phys_block@.addr != 0 {
                let ghost prev_i = block_i - 1;
                assert(0 <= prev_i < self.all_blocks.ptrs@.len());
                self.all_blocks.lemma_wf_perm_wf(prev_i);
                self.all_blocks.lemma_wf_glue_facts(prev_i);
                self.all_blocks.lemma_wf_structural_facts(prev_i);
            }
        }

        let ghost next_phys_ptr = self.all_blocks.phys_next_of(block_i).unwrap();

        // 1a. Read block header (extract-read-reinsert)
        let tracked mut block_perm =
            self.all_blocks.perms.borrow_mut().tracked_remove(block);
        let ghost block_size_val = block_perm.points_to.value().size;
        let block_hdr_ref = ptr_ref(block, Tracked(&block_perm.points_to));
        let block_prev_phys = block_hdr_ref.prev_phys_block;
        let next_phys_block = BlockHdr::next_phys_block(block, Tracked(&block_perm));
        // Compute size from pointer difference to avoid SIZE_SIZE_MASK exec-spec mismatch.
        // next_phys_block@.addr == block@.addr + (block_size_val & SIZE_SIZE_MASK) by postcondition,
        // so this gives size == (block_size_val & SIZE_SIZE_MASK) in spec.
        proof {
            // Overflow check: next_phys_block > block (from valid_block_size >= GRANULARITY > 0)
            self.all_blocks.perms.borrow_mut().tracked_insert(block, block_perm);
            AllBlocks::<FLLEN, SLLEN>::lemma_phys_next_matches_elim(
                next_phys_ptr, block, block_size_val);
            assert(next_phys_block == next_phys_ptr);
            assert(next_phys_block@.addr == block@.addr + (block_size_val & SIZE_SIZE_MASK) as int);
            // valid_block_size => (block_size_val & SIZE_SIZE_MASK) >= GRANULARITY > 0
            assert(block_size_val == self.all_blocks.value_at(block).size);
            assert((block_size_val & SIZE_SIZE_MASK) as int >= GRANULARITY as int);
            assert(next_phys_block@.addr > block@.addr);
        }
        let mut size: usize = (next_phys_block as usize) - (block as usize);
        proof {
            // size == (block_size_val & SIZE_SIZE_MASK) in spec
            assert(size == (block_size_val & SIZE_SIZE_MASK));
            // Glue bound
            assert((block_size_val as int) + (block@.addr as int) < usize::MAX as int);
        }

        // 1b. Read next_phys_block header and precompute next_next_phys
        proof {
            assert(self.all_blocks.perms@.contains_key(next_phys_block));
        }
        let tracked next_phys_perm: BlockPerm =
            self.all_blocks.perms.borrow_mut().tracked_remove(next_phys_block);
        let ghost next_phys_size_val = next_phys_perm.points_to.value().size;
        let next_phys_block_size_and_flags =
            ptr_ref(next_phys_block, Tracked(&next_phys_perm.points_to)).size;
        let next_next_phys_block = BlockHdr::next_phys_block(
            next_phys_block, Tracked(&next_phys_perm));
        proof {
            self.all_blocks.perms.borrow_mut().tracked_insert(next_phys_block, next_phys_perm);
            // Connect ghost value to value_at
            assert(next_phys_size_val == self.all_blocks.value_at(next_phys_block).size);
            // Capture next_phys bound from glue facts
            if !self.all_blocks.value_at(next_phys_block).is_sentinel() {
                assert((next_phys_size_val as int) + (next_phys_block@.addr as int) < usize::MAX as int);
                // Connect next_next_phys_block to ptrs@[block_i + 2]
                let ghost nnp = self.all_blocks.phys_next_of(block_i + 1).unwrap();
                AllBlocks::<FLLEN, SLLEN>::lemma_phys_next_matches_elim(
                    nnp, next_phys_block, next_phys_size_val);
                assert(next_next_phys_block == nnp);
            }
        }

        // 1c. Read prev_phys_block header (if exists)
        let mut prev_phys_block_size_and_flags: usize = SIZE_USED; // default: treated as used
        if block_prev_phys.addr() != 0 {
            proof {
                // prev is in perms: perms map is fully restored
                let ghost prev_i = block_i - 1;
                lemma_ptrs_no_duplicates_index_neq(
                    self.all_blocks.ptrs@, prev_i, block_i);
                lemma_ptrs_no_duplicates_index_neq(
                    self.all_blocks.ptrs@, prev_i, block_i + 1);
                assert(block_prev_phys != block);
                assert(block_prev_phys != next_phys_block);
                assert(self.all_blocks.perms@.contains_key(block_prev_phys));
            }
            let tracked prev_perm: BlockPerm =
                self.all_blocks.perms.borrow_mut().tracked_remove(block_prev_phys);
            prev_phys_block_size_and_flags =
                ptr_ref(block_prev_phys, Tracked(&prev_perm.points_to)).size;
            proof {
                let ghost prev_size_val = prev_perm.points_to.value().size;
                assert(prev_phys_block_size_and_flags == prev_size_val);
                self.all_blocks.perms.borrow_mut().tracked_insert(block_prev_phys, prev_perm);
                // Structural fact for prev: block@.addr = prev@.addr + (prev_size & mask)
                assert(prev_size_val == self.all_blocks.value_at(block_prev_phys).size);
                AllBlocks::<FLLEN, SLLEN>::lemma_phys_next_matches_elim(
                    block, block_prev_phys, prev_size_val);
                assert(block@.addr == block_prev_phys@.addr
                    + (prev_size_val & SIZE_SIZE_MASK) as int);
                // prev@.addr > 0
                assert(block_prev_phys@.addr > 0) by {
                    assert(block_prev_phys@.addr != 0);
                    assert(block_prev_phys@.addr >= 0);
                };
            }
        }

        // Perms map fully restored after all reads
        proof {
            assert(self.all_blocks.perms@ =~= old(self).all_blocks.perms@);
        }

        let ghost orig_block_ptr = block;
        let mut new_next_phys_block = next_phys_block;
        let ghost mut coalesced_with_next = false;
        let ghost mut coalesced_with_prev = false;
        // Snapshot of shadow_freelist right after first unlink (for tracing through second unlink)
        let ghost mut pre_prev_unlink_sfl = self.shadow_freelist@;

        // --- Next block coalescing ---
        if (next_phys_block_size_and_flags & SIZE_USED) == 0 {
            let next_phys_block_size = next_phys_block_size_and_flags;

            // Overflow proof: size + next_phys_block_size < usize::MAX
            proof {
                // next_phys_block_size == next_phys_size_val (from ptr_ref postcondition)
                assert(next_phys_block_size == next_phys_size_val);
                // For free blocks: size == size & SIZE_SIZE_MASK (from BlockPerm::wf())
                assert(next_phys_size_val == next_phys_size_val & SIZE_SIZE_MASK) by {
                    old(self).all_blocks.lemma_wf_perm_wf(block_i + 1);
                    assert(next_phys_size_val
                        == old(self).all_blocks.value_at(next_phys_block).size);
                };
                // next_phys_ptr@.addr == block@.addr + size
                // next_phys_size_val + next_phys_block@.addr < usize::MAX
                // So: next_phys_block_size + block@.addr + size < usize::MAX
                assert(block@.addr > 0) by {
                    assert(block@.addr != 0);
                    assert(block@.addr >= 0);
                };
                // next_phys_block_size + size < usize::MAX (since block@.addr > 0)
                assert(size + next_phys_block_size < usize::MAX);
            }
            size += next_phys_block_size;
            new_next_phys_block = next_next_phys_block;

            proof {
                assert(self.all_blocks.value_at(next_phys_block).is_free());
            }
            self.unlink_free_block(next_phys_block, next_phys_block_size, Ghost(Set::empty()));
            proof {
                coalesced_with_next = true;
                pre_prev_unlink_sfl = self.shadow_freelist@;
                assert(!pre_prev_unlink_sfl.contains(next_phys_block));
            }
        }

        // --- Previous block coalescing ---
        if block_prev_phys.addr() != 0 && (prev_phys_block_size_and_flags & SIZE_USED) == 0 {
            let prev_phys_block_size = prev_phys_block_size_and_flags;

            // Overflow proof: size + prev_phys_block_size < usize::MAX
            proof {
                // prev is free, so prev_size == prev_size & SIZE_SIZE_MASK (no flag bits)
                assert(prev_phys_block_size_and_flags
                    == prev_phys_block_size_and_flags & SIZE_SIZE_MASK) by {
                    old(self).all_blocks.lemma_wf_perm_wf(block_i - 1);
                };
                // Structural: block@.addr = prev@.addr + (prev_size & mask)
                // For free block: prev_phys_block_size = block@.addr - prev@.addr
                // prev@.addr > 0 (from structural facts)
                //
                // size + block@.addr < usize::MAX because:
                //   Without next coal: size = block_size_val & mask <= block_size_val,
                //     and block_size_val + block@.addr < usize::MAX
                //   With next coal: size = (block_size_val & mask) + next_phys_size,
                //     and next_phys_size + next_phys@.addr < usize::MAX,
                //     and next_phys@.addr = block@.addr + (block_size_val & mask) (structural)
                //     so size + block@.addr < usize::MAX
                //
                // Then: prev_size + size = size + block@.addr - prev@.addr < usize::MAX
                assert(prev_phys_block_size + size < usize::MAX);
            }
            size += prev_phys_block_size;
            block = block_prev_phys;

            let ghost prev_exceptions: Set<*mut BlockHdr> = if coalesced_with_next {
                Set::empty().insert(next_phys_block)
            } else {
                Set::empty()
            };

            // Ghost: index of block_prev_phys in its sfl bucket (for post-unlink proof)
            let ghost prev_sfl_bucket_idx: int;
            proof {
                assert(self.all_blocks.value_at(block_prev_phys).is_free());
                assert(self.all_blocks.contains(block_prev_phys));
                let ghost prev_i = block_i - 1;
                lemma_ptrs_no_duplicates_index_neq(
                    self.all_blocks.ptrs@, prev_i, block_i + 1);
                assert(!prev_exceptions.contains(block_prev_phys));
                // Prove block_prev_phys is in the sfl before unlink
                // (needed for post-unlink Seq::remove reasoning)
                reveal(Tlsf::free_blocks_in_freelist_except);
                let bp_idx = self.all_blocks.get_ptr_internal_index(block_prev_phys);
                assert(0 <= bp_idx < self.all_blocks.ptrs@.len());
                assert(self.all_blocks.ptrs@[bp_idx] == block_prev_phys);
                assert(self.shadow_freelist@.contains(block_prev_phys));
                // Locate it in the specific bucket via size_class_condition
                let actual_bi: BlockIndex<FLLEN, SLLEN> = choose|bi: BlockIndex<FLLEN, SLLEN>|
                    bi.wf() && self.shadow_freelist@.m[bi].contains(block_prev_phys);
                let j0: int = choose|j: int|
                    0 <= j < self.shadow_freelist@.m[actual_bi].len()
                    && self.shadow_freelist@.m[actual_bi][j] == block_prev_phys;
                self.lemma_size_class_at(actual_bi, j0);
                // actual_bi == map_floor_spec(prev_phys_block_size as usize) == prev_idx
                let ghost prev_idx = Self::map_floor_spec(prev_phys_block_size as usize);
                assert(actual_bi == prev_idx);
                assert(pre_prev_unlink_sfl.m[prev_idx].contains(block_prev_phys));
                prev_sfl_bucket_idx = j0;
            }

            self.unlink_free_block(block_prev_phys, prev_phys_block_size,
                Ghost(prev_exceptions));
            proof {
                coalesced_with_prev = true;
                // Prove next_phys_block remains not in sfl after second unlink
                if coalesced_with_next {
                    assert(!pre_prev_unlink_sfl.contains(next_phys_block));
                    // The second unlink removed block_prev_phys from bucket prev_idx.
                    // Postcondition gives:
                    //   self.sfl.m[prev_idx] == pre.m[prev_idx].remove(rm_i)
                    //   for bi != prev_idx: self.sfl.m[bi] == pre.m[bi]
                    let ghost prev_idx = Self::map_floor_spec(prev_phys_block_size as usize);
                    // rm_i was captured before the unlink as prev_sfl_bucket_idx
                    let ghost rm_i: int = prev_sfl_bucket_idx;
                    let ghost pre_bucket = pre_prev_unlink_sfl.m[prev_idx];
                    let ghost post_bucket = self.shadow_freelist@.m[prev_idx];
                    // Verify rm_i is valid (from pre-unlink proof)
                    assert(0 <= rm_i < pre_bucket.len());
                    assert(pre_bucket[rm_i] == block_prev_phys);
                    assert(post_bucket == pre_bucket.remove(rm_i));
                    // Prove: !post_bucket.contains(next_phys_block)
                    // by showing every element of post_bucket is in pre_bucket
                    assert(!post_bucket.contains(next_phys_block)) by {
                        pre_bucket.remove_ensures(rm_i);
                        if post_bucket.contains(next_phys_block) {
                            let j: int = choose|j: int|
                                0 <= j < post_bucket.len()
                                && post_bucket[j] == next_phys_block;
                            // From remove_ensures:
                            //   j < rm_i ==> post_bucket[j] == pre_bucket[j]
                            //   j >= rm_i ==> post_bucket[j] == pre_bucket[j+1]
                            if j < rm_i {
                                assert(pre_bucket[j] == next_phys_block);
                            } else {
                                assert(pre_bucket[j + 1] == next_phys_block);
                            }
                            // Either way, pre_bucket.contains(next_phys_block)
                            assert(pre_prev_unlink_sfl.contains(next_phys_block));
                            assert(false);
                        }
                    };
                    // Lift per-bucket to full sfl non-containment
                    assert forall|bi: BlockIndex<FLLEN, SLLEN>|
                        bi.wf() implies
                            !self.shadow_freelist@.m[bi].contains(next_phys_block)
                    by {
                        if bi != prev_idx {
                            assert(self.shadow_freelist@.m[bi] == pre_prev_unlink_sfl.m[bi]);
                            if pre_prev_unlink_sfl.m[bi].contains(next_phys_block) {
                                assert(pre_prev_unlink_sfl.contains(next_phys_block));
                                assert(false);
                            }
                        }
                        // bi == prev_idx case follows from !post_bucket.contains(next_phys_block) above
                    };
                    assert(!self.shadow_freelist@.contains(next_phys_block)) by {
                        if self.shadow_freelist@.contains(next_phys_block) {
                            let bi0: BlockIndex<FLLEN, SLLEN> = choose|bi: BlockIndex<FLLEN, SLLEN>|
                                bi.wf() && self.shadow_freelist@.m[bi].contains(next_phys_block);
                        }
                    };
                }
            }
        }

        let ghost post_unlink_perms = self.all_blocks.perms@;
        let ghost post_unlink_sfl = self.shadow_freelist@;
        let ghost post_unlink_ab = self.all_blocks;
        // Ghost booleans to preserve exclusion facts across mutations
        let ghost block_not_in_sfl: bool;
        let ghost orig_not_in_sfl: bool;
        let ghost next_not_in_sfl: bool;
        let ghost post_unlink_exceptions: Set<*mut BlockHdr> =
            if coalesced_with_prev && coalesced_with_next {
                set![next_phys_block, block]
            } else if coalesced_with_prev {
                set![block]
            } else if coalesced_with_next {
                set![next_phys_block]
            } else {
                Set::empty()
            };
        // Ghost snapshot of self for use via lemma_wf_free_node_preserve_if_not_touched
        let ghost post_unlink_tlsf: Tlsf<'pool, FLLEN, SLLEN> = *self;
        proof {
            assert(post_unlink_ab.wf());
            post_unlink_ab.lemma_wf_nodup();
            // size_class_condition held after unlinks (from postconditions / preconditions)
            assert(self.size_class_condition());
            reveal(Tlsf::size_class_condition);
            // Restate using immutable ghost variable to survive later mutations
            assert(forall |bi: BlockIndex<FLLEN, SLLEN>, k: int|
                post_unlink_sfl.m.contains_key(bi)
                    && 0 <= k < post_unlink_sfl.m[bi].len()
                ==> ({
                    let n = #[trigger] post_unlink_sfl.m[bi][k];
                    bi == Self::map_floor_spec(
                        post_unlink_perms[n].points_to.value().size as usize)
                    && bi.block_size_range().contains(
                        post_unlink_perms[n].points_to.value().size as int)
                })
            );

            // -- block not in shadow_freelist --
            if coalesced_with_prev {
                assert(!self.shadow_freelist@.contains(block));
            } else {
                assert(block == orig_block_ptr);
                assert(self.all_blocks.perms@[orig_block_ptr].points_to.value().size
                    == block_size_val);
                if self.shadow_freelist@.contains(orig_block_ptr) {
                    let bi0: BlockIndex<FLLEN, SLLEN> = choose|bi: BlockIndex<FLLEN, SLLEN>|
                        bi.wf() && self.shadow_freelist@.m[bi].contains(orig_block_ptr);
                    let j0: int = choose|j: int|
                        0 <= j < self.shadow_freelist@.m[bi0].len()
                        && self.shadow_freelist@.m[bi0][j] == orig_block_ptr;
                    self.lemma_all_freelist_wf_weak_extract_wf_free_node(
                        bi0, j0,
                        if coalesced_with_next { set![next_phys_block] }
                        else { Set::empty() });
                    assert(self.all_blocks.value_at(orig_block_ptr).is_free());
                    assert(false);
                }
            }
            block_not_in_sfl = !post_unlink_sfl.contains(block);
            assert(block_not_in_sfl);

            // -- orig_block_ptr not in shadow_freelist --
            if coalesced_with_prev {
                assert(self.all_blocks.perms@[orig_block_ptr].points_to.value().size
                    == block_size_val);
                if self.shadow_freelist@.contains(orig_block_ptr) {
                    let bi0: BlockIndex<FLLEN, SLLEN> = choose|bi: BlockIndex<FLLEN, SLLEN>|
                        bi.wf() && self.shadow_freelist@.m[bi].contains(orig_block_ptr);
                    let j0: int = choose|j: int|
                        0 <= j < self.shadow_freelist@.m[bi0].len()
                        && self.shadow_freelist@.m[bi0][j] == orig_block_ptr;
                    self.lemma_all_freelist_wf_weak_extract_wf_free_node(
                        bi0, j0,
                        if coalesced_with_next {
                            set![next_phys_block, block_prev_phys]
                        } else {
                            set![block_prev_phys]
                        });
                    assert(self.all_blocks.value_at(orig_block_ptr).is_free());
                    assert(false);
                }
            }
            orig_not_in_sfl = !post_unlink_sfl.contains(orig_block_ptr);
            assert(orig_not_in_sfl);

            // -- next_phys_block not in shadow_freelist (if coalesced_with_next) --
            // Proved right after second unlink (or trivially from first unlink if no second)
            if coalesced_with_next {
                if !coalesced_with_prev {
                    assert(post_unlink_sfl == pre_prev_unlink_sfl);
                }
                assert(!post_unlink_sfl.contains(next_phys_block));
            }
            next_not_in_sfl = !post_unlink_sfl.contains(next_phys_block);
            assert(coalesced_with_next ==> next_not_in_sfl);

            // === Step B captures: facts for all_freelist_wf_weak proof ===
            assert(self.all_freelist_wf_weak(post_unlink_exceptions));

            // B1 capture: shadow_ptrs_nonnull restated on immutable post_unlink_sfl
            reveal(Tlsf::shadow_ptrs_nonnull);
            assert(forall|idx: BlockIndex<FLLEN, SLLEN>, i: int|
                idx.wf() && 0 <= i < post_unlink_sfl.m[idx].len()
                ==> (#[trigger] post_unlink_sfl.m[idx][i])@.addr != 0);

            // B2 capture: first_free conditions from freelist_wf via bridge lemmas
            assert(forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf() ==>
                (post_unlink_sfl.m[idx].len() == 0
                    ==> self.first_free[idx.0 as int][idx.1 as int]@.addr == 0)
                && (post_unlink_sfl.m[idx].len() > 0
                    ==> self.first_free[idx.0 as int][idx.1 as int]@.addr != 0
                        && self.first_free[idx.0 as int][idx.1 as int]
                            == post_unlink_sfl.m[idx].first())
            ) by {
                assert forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf() implies
                    (post_unlink_sfl.m[idx].len() == 0
                        ==> self.first_free[idx.0 as int][idx.1 as int]@.addr == 0)
                    && (post_unlink_sfl.m[idx].len() > 0
                        ==> self.first_free[idx.0 as int][idx.1 as int]@.addr != 0
                            && self.first_free[idx.0 as int][idx.1 as int]
                                == post_unlink_sfl.m[idx].first())
                by {
                    if post_unlink_sfl.m[idx].len() == 0 {
                        self.freelist_empty(idx);
                    } else {
                        self.freelist_nonempty(idx);
                    }
                };
            };

            // B3 capture: free_blocks_in_freelist_except
            reveal(Tlsf::free_blocks_in_freelist_except);
            assert(forall|i: int| 0 <= i < post_unlink_ab.ptrs@.len()
                && (#[trigger] post_unlink_perms[post_unlink_ab.ptrs@[i]])
                    .points_to.value().is_free()
                && !post_unlink_exceptions.contains(post_unlink_ab.ptrs@[i])
                ==> post_unlink_sfl.contains(post_unlink_ab.ptrs@[i]));

            // B2 capture: nnpb not free in post-unlink state
            assert(!post_unlink_perms[new_next_phys_block]
                .points_to.value().is_free()) by {
                if coalesced_with_next {
                    // nnpb = next_next. next was free → structural: phys_next not free
                    post_unlink_ab.lemma_wf_structural_facts(block_i + 1);
                    assert(post_unlink_ab.value_at(next_phys_block).is_free());
                } else {
                    // nnpb = next_phys_block. Not free (otherwise we'd coalesce)
                    assert((next_phys_block_size_and_flags & SIZE_USED) != 0usize);
                }
            };

        }

        // After all unlinking: all perms in map, wf() holds (from last unlink postcondition
        // or from original preconditions if no unlink happened)

        // Index of block in ptrs@ (may be prev_phys if coalesced with prev)
        let ghost block_idx: int = if coalesced_with_prev { block_i - 1 } else { block_i };

        // Establish containment for block and new_next_phys_block
        // using post-unlink wf() state
        let ghost new_next_phys_idx = if coalesced_with_next {
            block_i + 2
        } else {
            block_i + 1
        };
        proof {
            // ptrs@ preserved through all operations
            assert(self.all_blocks.ptrs@ == old(self).all_blocks.ptrs@);

            // block is in perms (block may be original or prev_phys_block)
            assert(self.all_blocks.contains(block));
            self.all_blocks.lemma_contains(block);
            assert(self.all_blocks.perms@.contains_key(block));

            // new_next_phys_block is in perms
            // Case split to help solver connect to earlier facts
            if coalesced_with_next {
                // next was free (hence not sentinel), so phys_next_of(block_i+1) was Some
                // => block_i + 2 < ptrs@.len()
                // next_next_phys_block == ptrs@[block_i + 2] was proved earlier
                assert(new_next_phys_block == next_next_phys_block);
                assert(new_next_phys_idx == block_i + 2 as int);
            } else {
                assert(new_next_phys_block == next_phys_block);
                assert(new_next_phys_idx == block_i + 1 as int);
                assert(next_phys_block == next_phys_ptr);
            }
            assert(0 <= new_next_phys_idx < self.all_blocks.ptrs@.len());
            assert(self.all_blocks.ptrs@[new_next_phys_idx] == new_next_phys_block);
            assert(self.all_blocks.contains(new_next_phys_block));
            self.all_blocks.lemma_contains(new_next_phys_block);
            assert(self.all_blocks.perms@.contains_key(new_next_phys_block));

            // new_next_phys_block != block
            let ghost block_idx = if block == block_prev_phys && block_prev_phys@.addr != 0 {
                block_i - 1
            } else {
                block_i
            };
            lemma_ptrs_no_duplicates_index_neq(
                self.all_blocks.ptrs@, block_idx, new_next_phys_idx);
            assert(new_next_phys_block != block);

            // Establish perm.ptr() facts before extraction (while wf() holds)
            self.all_blocks.lemma_wf_perm_wf(block_idx);
            assert(self.all_blocks.perms@[block].points_to.ptr() == block);
            self.all_blocks.lemma_wf_perm_wf(new_next_phys_idx);
            assert(self.all_blocks.perms@[new_next_phys_block].points_to.ptr()
                == new_next_phys_block);

            // Capture next block (block_i+1) wf before extractions, for later use
            self.all_blocks.lemma_wf_perm_wf(block_i + 1);
            assert(self.all_blocks.perms@[next_phys_block].wf());

            // Capture block alignment (from wf_node_ptr, while wf() still holds)
            self.all_blocks.lemma_wf_node_ptr(block_idx);
            assert((block@.addr as int) % (GRANULARITY as int) == 0);
        }

        // Extract block_perm, read its prev_phys, write new header
        let tracked mut block_perm2 =
            self.all_blocks.perms.borrow_mut().tracked_remove(block);
        let final_prev_phys = ptr_ref(block, Tracked(&block_perm2.points_to)).prev_phys_block;
        ptr_mut_write(block, Tracked(&mut block_perm2.points_to), BlockHdr {
            size,
            prev_phys_block: final_prev_phys,
        });

        // Extract new_next_phys_block perm, update its prev_phys_block to point to block
        // After removing block from perms, nnpb entry is still there (block != nnpb)
        // and its ptr() is preserved from the wf fact established above
        proof {
            assert(self.all_blocks.perms@.contains_key(new_next_phys_block));
            assert(self.all_blocks.perms@[new_next_phys_block].points_to.ptr()
                == new_next_phys_block);
        }
        let tracked mut nnpb_perm =
            self.all_blocks.perms.borrow_mut().tracked_remove(new_next_phys_block);
        let nnpb_size = ptr_ref(new_next_phys_block,
            Tracked(&nnpb_perm.points_to)).size;
        ptr_mut_write(new_next_phys_block,
            Tracked(&mut nnpb_perm.points_to),
            BlockHdr {
                size: nnpb_size,
                prev_phys_block: block
            });

        // Re-insert nnpb_perm only (block_perm2 stays out for free_link_perm reconstruction)
        proof {
            self.all_blocks.perms.borrow_mut()
                .tracked_insert(new_next_phys_block, nnpb_perm);
        }

        // After header write: block_perm2.points_to has size = coalesced_size (free).
        // Need to set up free_link_perm and mem for BlockPerm::wf().

        // Determine whether prev was coalesced (exec bool for conditional with exec code)
        let prev_was_free: bool = block_prev_phys.addr() != 0
            && (prev_phys_block_size_and_flags & SIZE_USED) == 0;

        // Concrete sizes for proof (exec calls resolve global layout)
        let bhdr_size: usize = size_of::<BlockHdr>();
        let fl_size: usize = size_of::<FreeLink>();
        // Establish that size_of fits in usize (needed for spec-exec connection)
        vstd::layout::layout_for_type_is_valid::<BlockHdr>();
        vstd::layout::layout_for_type_is_valid::<FreeLink>();
        proof {
            // Activate global layout broadcast proofs for size_of/align_of
            broadcast use VERUS_layout_of_BlockHdr, VERUS_layout_of_FreeLink;
        }

        if !prev_was_free {
            // Case A: block = orig_block_ptr. free_link_perm was None (used block).
            // block_perm2.mem covers [block+BH, block+orig_phys_size) from postcondition.
            // Split FreeLink region [block+BH, block+BH+FL) from mem.
            proof {
                // Prove FreeLink region fits within mem
                assert(fl_size as int
                    <= (block_size_val & SIZE_SIZE_MASK) as int
                        - bhdr_size as int) by {
                    // valid_block_size => size >= GRANULARITY >= BH + FL
                    assert(bhdr_size == 16usize);
                    assert(fl_size == 16usize);
                    assert(GRANULARITY as usize >= bhdr_size + fl_size);
                    assert((block_size_val & SIZE_SIZE_MASK) as int
                        >= GRANULARITY as int);
                };
                assert(set_int_range(
                    block as int + bhdr_size as int,
                    block as int + bhdr_size as int + fl_size as int,
                ).subset_of(block_perm2.mem.dom())) by {
                    Self::lemma_range_subset_of_mem_dom(
                        block_perm2.mem,
                        block as int + bhdr_size as int,
                        block as int + (block_size_val & SIZE_SIZE_MASK) as int,
                        block as int + bhdr_size as int,
                        block as int + bhdr_size as int + fl_size as int,
                    );
                };
                let tracked (fl_raw, rest_mem) = block_perm2.mem.split(
                    set_int_range(
                        block as int + bhdr_size as int,
                        block as int + bhdr_size as int + fl_size as int));
                // fl_raw.is_range(block + BH, FL)
                assert(fl_raw.is_range(
                    block as int + bhdr_size as int, fl_size as int));
                // Alignment: block is GRANULARITY-aligned, BH=16, so block+BH is 8-aligned
                assert(((block as usize + bhdr_size) as int) % 8 == 0) by {
                    assert(block@.addr as int % (GRANULARITY as int) == 0);
                    assert(GRANULARITY == 32);
                    assert(bhdr_size == 16);
                    assert(((block as usize + 16usize) as int) % 8 == 0) by (nonlinear_arith)
                        requires block@.addr as int % 32 == 0;
                };
                let tracked fl_typed: PointsTo<FreeLink> = fl_raw.into_typed::<FreeLink>(
                    (block as usize + bhdr_size) as usize);
                block_perm2.free_link_perm = Some(fl_typed);
                block_perm2.mem = rest_mem;
            }
            // Write FreeLink to make it init (required by BlockPerm::wf)
            let freelink = get_freelink_ptr(block);
            {
                let tracked mut fl_perm =
                    block_perm2.free_link_perm.tracked_unwrap();
                ptr_mut_write(freelink, Tracked(&mut fl_perm), FreeLink {
                    next_free: null_bhdr(),
                    prev_free: null_bhdr(),
                });
                proof {
                    block_perm2.free_link_perm = Some(fl_perm);
                }
            }
        } else {
            // Case B: block = prev_phys_block. free_link_perm is already Some(init).
            // block_perm2.mem is [prev+BH+FL, prev+prev_size) from wf.
            // Absorb orig block's perm (header + mem).
            proof {
                // orig_block_ptr is still in perms (distinct from block and nnpb)
                assert(orig_block_ptr != block) by {
                    let ghost prev_i = block_i - 1;
                    lemma_ptrs_no_duplicates_index_neq(
                        self.all_blocks.ptrs@, block_i, prev_i);
                };
                assert(orig_block_ptr != new_next_phys_block) by {
                    lemma_ptrs_no_duplicates_index_neq(
                        self.all_blocks.ptrs@, block_i, new_next_phys_idx);
                };
                assert(self.all_blocks.perms@.contains_key(orig_block_ptr));
            }
            let tracked mut orig_bp =
                self.all_blocks.perms.borrow_mut().tracked_remove(orig_block_ptr);
            proof {
                // orig_bp.mem.is_range(orig+BH, orig_phys_size - BH) from postcondition
                // (preserved through unlink: unlink preserves perms@[p].mem)
                assert(orig_bp.mem.is_range(
                    orig_block_ptr as int + bhdr_size as int,
                    (block_size_val & SIZE_SIZE_MASK) as int
                        - bhdr_size as int));

                // block_perm2.mem = [block+BH+FL, block+prev_size) where block = prev
                // block + prev_size = orig_block_ptr (from structural: next = prev + prev_size)
                assert(orig_block_ptr as int == block as int
                    + prev_phys_block_size_and_flags as int);

                // block_perm2.mem is [block+BH+FL, orig_block_ptr)
                assert(block_perm2.mem.is_range(
                    block as int + bhdr_size as int + fl_size as int,
                    prev_phys_block_size_and_flags as int
                        - bhdr_size as int - fl_size as int));

                // Provenance: all adjacent blocks share provenance
                assert(orig_bp.mem.provenance() == block@.provenance);
                assert(block_perm2.mem.provenance() == block@.provenance);
                assert(orig_bp.points_to.ptr()@.provenance == block@.provenance);

                // Convert orig header to raw
                orig_bp.points_to.leak_contents();
                let tracked orig_hdr_raw = orig_bp.points_to.into_raw();
                // orig_hdr_raw.is_range(orig, BH)
                assert(orig_hdr_raw.is_range(orig_block_ptr as int, bhdr_size as int));
                assert(orig_hdr_raw.provenance() == block@.provenance);

                // Join: block_perm2.mem + orig_hdr + orig_mem
                // [block+BH+FL, orig) + [orig, orig+BH) + [orig+BH, orig+orig_phys_size)
                let tracked j1 = Self::lemma_join_adjacent_ranges_is_range(
                    block_perm2.mem,
                    orig_hdr_raw,
                    block as int + bhdr_size as int + fl_size as int,
                    orig_block_ptr as int,
                    orig_block_ptr as int + bhdr_size as int,
                );
                let tracked j2 = Self::lemma_join_adjacent_ranges_is_range(
                    j1,
                    orig_bp.mem,
                    block as int + bhdr_size as int + fl_size as int,
                    orig_block_ptr as int + bhdr_size as int,
                    orig_block_ptr as int
                        + (block_size_val & SIZE_SIZE_MASK) as int,
                );
                block_perm2.mem = j2;
            }
        }

        // Absorb next block if coalesced with next (both Case A and B)
        // Establish freelink addr for next block (exec needed for closed get_freelink_ptr_spec)
        let next_freelink = get_freelink_ptr(next_phys_block);
        if (next_phys_block_size_and_flags & SIZE_USED) == 0 {
            proof {
                // next_phys_block is still in perms
                assert(next_phys_block != block) by {
                    lemma_ptrs_no_duplicates_index_neq(
                        self.all_blocks.ptrs@, block_i + 1, block_idx);
                };
                assert(next_phys_block != new_next_phys_block) by {
                    lemma_ptrs_no_duplicates_index_neq(
                        self.all_blocks.ptrs@, block_i + 1, block_i + 2);
                };
                assert(self.all_blocks.perms@.contains_key(next_phys_block));
                // wf preserved through mutations (only different keys were modified)
                assert(self.all_blocks.perms@[next_phys_block].wf());
            }
            let tracked mut next_bp =
                self.all_blocks.perms.borrow_mut().tracked_remove(next_phys_block);
            proof {
                // next_bp == old perms@[next_phys_block], which was wf
                assert(next_bp.wf());
                // next_bp.free_link_perm is Some (from wf for free block)
                assert(next_bp.free_link_perm is Some);

                // Provenance matches block (adjacent blocks share provenance)
                assert(next_bp.points_to.ptr()@.provenance == block@.provenance);
                assert(next_bp.mem.provenance() == block@.provenance);

                // Current end of block_perm2.mem = next_phys_block
                assert(next_phys_block as int == orig_block_ptr as int
                    + (block_size_val & SIZE_SIZE_MASK) as int);

                // block_perm2.mem currently ends at next_phys_block
                assert(block_perm2.mem.is_range(
                    block as int + bhdr_size as int + fl_size as int,
                    next_phys_block as int - block as int
                        - bhdr_size as int - fl_size as int));
                assert(block_perm2.mem.provenance() == block@.provenance);

                // next block ranges
                // next_bp.mem = [next+BH+FL, next+next_size)
                assert(next_bp.mem.is_range(
                    next_phys_block as int + bhdr_size as int + fl_size as int,
                    next_phys_size_val as int - bhdr_size as int - fl_size as int));

                // Convert next header to raw
                next_bp.points_to.leak_contents();
                let tracked next_hdr_raw = next_bp.points_to.into_raw();
                assert(next_hdr_raw.is_range(next_phys_block as int, bhdr_size as int));
                assert(next_hdr_raw.provenance() == block@.provenance);

                // Convert next freelink to raw
                let tracked mut next_fl = next_bp.free_link_perm.tracked_unwrap();
                assert(next_fl.ptr() == get_freelink_ptr_spec(next_phys_block));
                assert(next_freelink == get_freelink_ptr_spec(next_phys_block));
                assert(next_fl.ptr() == next_freelink);
                assert(next_freelink as int == next_phys_block as int + bhdr_size as int);
                next_fl.leak_contents();
                let tracked next_fl_raw = next_fl.into_raw();
                // into_raw gives is_range(next_fl.ptr().addr(), size_of::<FreeLink>())
                // which equals is_range(next_phys_block + BH, FL)
                assert(next_fl_raw.is_range(
                    next_phys_block as int + bhdr_size as int, fl_size as int)) by {
                    assert(next_freelink as int == next_phys_block as int + bhdr_size as int);
                };
                assert(next_fl_raw.provenance() == block@.provenance) by {
                    assert(next_fl.ptr()@.provenance == next_bp.points_to.ptr()@.provenance);
                    assert(next_bp.points_to.ptr()@.provenance == block@.provenance);
                };

                // Join chain:
                // block_perm2.mem + next_hdr + next_fl + next_mem
                let tracked j1 = Self::lemma_join_adjacent_ranges_is_range(
                    block_perm2.mem,
                    next_hdr_raw,
                    block as int + bhdr_size as int + fl_size as int,
                    next_phys_block as int,
                    next_phys_block as int + bhdr_size as int,
                );
                let tracked j2 = Self::lemma_join_adjacent_ranges_is_range(
                    j1,
                    next_fl_raw,
                    block as int + bhdr_size as int + fl_size as int,
                    next_phys_block as int + bhdr_size as int,
                    next_phys_block as int + bhdr_size as int + fl_size as int,
                );
                let tracked j3 = Self::lemma_join_adjacent_ranges_is_range(
                    j2,
                    next_bp.mem,
                    block as int + bhdr_size as int + fl_size as int,
                    next_phys_block as int + bhdr_size as int + fl_size as int,
                    next_phys_block as int + next_phys_size_val as int,
                );
                block_perm2.mem = j3;
            }
        }

        // Re-insert block_perm2 with reconstructed free_link_perm and mem
        proof {
            self.all_blocks.perms.borrow_mut()
                .tracked_insert(block, block_perm2);
        }

        proof {
            // ptrs@ unchanged through header writes
            assert(self.all_blocks.ptrs@ == post_unlink_ab.ptrs@);
            // wf_shadow from unlink postcondition (sfl unchanged through header writes)
            assert(self.shadow_freelist@ == post_unlink_sfl);
            // Preconditions for ii_shift_after_remove_ensures
            assert(post_unlink_sfl.shadow_freelist_has_all_wf_index());
            assert(is_identity_injection(post_unlink_sfl, post_unlink_ab.ptrs@));
            assert(ghost_pointer_ordered(post_unlink_ab.ptrs@));
            assert(ptrs_no_duplicates(post_unlink_ab.ptrs@));

            if coalesced_with_next {
                let ghost pre_ptrs = self.all_blocks.ptrs@;
                let ghost rm_ai = block_i + 1; // next_phys_block is at block_i + 1
                assert(pre_ptrs[rm_ai] == next_phys_block);
                // next_phys_block was unlinked, so not in sfl (proved earlier)
                assert(next_not_in_sfl);
                assert(!post_unlink_sfl.contains(next_phys_block));
                assert(post_unlink_ab.ptrs@.contains(next_phys_block)) by {
                    assert(post_unlink_ab.ptrs@[block_i + 1] == next_phys_block);
                };
                post_unlink_sfl.lemma_sfl_not_contains_iff_pi_undefined(
                    post_unlink_ab, next_phys_block);
                // get_ptr_internal_index chooses some i with ptrs@[i] == next_phys_block
                // By no_duplicates, this equals block_i + 1
                let ghost k = post_unlink_ab.get_ptr_internal_index(next_phys_block);
                lemma_ptrs_no_duplicates_eq_index(
                    post_unlink_ab.ptrs@, k, rm_ai);
                assert(!self.shadow_freelist@.pi.values().contains(rm_ai));
                Self::lemma_ii_shift_after_remove_ensures(
                    self.shadow_freelist@, pre_ptrs, rm_ai, next_phys_block);
                self.all_blocks.ptrs@ = remove_ghost_pointer(pre_ptrs, next_phys_block);
                self.shadow_freelist@ = self.shadow_freelist@.ii_shift_after_remove(rm_ai);
            }
            if coalesced_with_prev {
                let ghost pre_ptrs = self.all_blocks.ptrs@;
                let ghost rm_ai: int = block_i;
                assert(pre_ptrs[rm_ai] == orig_block_ptr) by {
                    if coalesced_with_next {
                        // pre_ptrs = remove(old_ptrs, next_phys_block)
                        // orig was at block_i in old_ptrs, next was at block_i+1
                        // After removing block_i+1: len = old_len - 1, block_i < old_len - 1
                        lemma_remove_ghost_pointer_ensures(
                            post_unlink_ab.ptrs@, next_phys_block);
                        assert(0 <= rm_ai < remove_ghost_pointer(post_unlink_ab.ptrs@, next_phys_block).len()) by {
                            assert(rm_ai == block_i);
                            assert(block_i + 1 < post_unlink_ab.ptrs@.len());
                        };
                        lemma_remove_ghost_pointer_index_map(
                            post_unlink_ab.ptrs@, next_phys_block, rm_ai);
                        // rm_ai = block_i < block_i + 1 = idx of next_phys_block
                        // So result[block_i] == old[block_i] == orig_block_ptr
                    }
                };
                // Need ghost_pointer_ordered + ptrs_no_duplicates for pre_ptrs
                if coalesced_with_next {
                    lemma_remove_ghost_pointer_ensures(
                        post_unlink_ab.ptrs@, next_phys_block);
                    lemma_ptrs_no_duplicates_preserved_by_remove(
                        post_unlink_ab.ptrs@, next_phys_block);
                }
                // Establish is_identity_injection for current sfl and pre_ptrs
                assert(is_identity_injection(self.shadow_freelist@, pre_ptrs));
                // orig_block_ptr was never free (or was unlinked), so not in sfl
                assert(!self.shadow_freelist@.pi.values().contains(rm_ai)) by {
                    if self.shadow_freelist@.pi.values().contains(rm_ai) {
                        // Then there exists (idx, m) s.t. pi[(idx, m)] == rm_ai
                        let key = choose|key: (BlockIndex<FLLEN, SLLEN>, int)|
                            self.shadow_freelist@.pi.dom().contains(key)
                                && self.shadow_freelist@.pi[key] == rm_ai;
                        let (idx, m) = key;
                        // is_identity_injection: sfl.m[idx][m] == pre_ptrs[rm_ai] == orig_block_ptr
                        assert(is_identity_injection(self.shadow_freelist@, pre_ptrs));
                        assert(idx.wf() && 0 <= m < self.shadow_freelist@.m[idx].len());
                        assert(self.shadow_freelist@.m[idx][m] == pre_ptrs[rm_ai]);
                        assert(self.shadow_freelist@.m[idx][m] == orig_block_ptr);
                        assert(self.shadow_freelist@.m[idx].contains(orig_block_ptr));
                        assert(self.shadow_freelist@.contains(orig_block_ptr));
                        // sfl.m == post_unlink_sfl.m (only pi changed by ii_shift)
                        assert(self.shadow_freelist@.m == post_unlink_sfl.m);
                        assert(post_unlink_sfl.contains(orig_block_ptr));
                        // But orig_not_in_sfl was proved
                        assert(false);
                    }
                };
                Self::lemma_ii_shift_after_remove_ensures(
                    self.shadow_freelist@, pre_ptrs, rm_ai, orig_block_ptr);
                self.all_blocks.ptrs@ = remove_ghost_pointer(pre_ptrs, orig_block_ptr);
                self.shadow_freelist@ = self.shadow_freelist@.ii_shift_after_remove(rm_ai);
            }
        }

        proof {
            // block_perm2.mem is now [block+BH+FL, block+size)
            assert(self.all_blocks.perms@[block].mem.is_range(
                block as int + size_of::<BlockHdr>() as int
                    + size_of::<FreeLink>() as int,
                size as int - size_of::<BlockHdr>() as int
                    - size_of::<FreeLink>() as int));

            // The written header is free (no SIZE_USED bit)
            assert(self.all_blocks.perms@[block].points_to.value().is_free()) by {
                assert(self.all_blocks.perms@[block].points_to.value().size == size);
                // size came from pointer difference, GRANULARITY-aligned, no flag bits
                assert(size % GRANULARITY == 0) by {
                    // (block_size_val & SIZE_SIZE_MASK) was GRANULARITY-aligned
                    // next_phys_block_size was GRANULARITY-aligned (if coalesced)
                    // prev_phys_block_size was GRANULARITY-aligned (if coalesced)
                    // Their sum is GRANULARITY-aligned
                    assert((block_size_val & SIZE_SIZE_MASK) as int
                        % (GRANULARITY as int) == 0);
                };
                assert((size & SIZE_USED) == 0) by (bit_vector)
                    requires
                        size as int % 32 == 0,
                        SIZE_USED == 1usize,
                        GRANULARITY == 32usize;
            };

            // size == size & SIZE_SIZE_MASK (no flag bits)
            assert(size == size & SIZE_SIZE_MASK) by {
                assert(size as int % 32 == 0);
                assert((size & !31usize) == size) by (bit_vector)
                    requires size as int % 32 == 0;
                reveal(usize_trailing_zeros);
                reveal(u64_trailing_zeros);
                assert(SPEC_SIZE_SIZE_MASK == !31usize) by (compute);
            };

            // block_perm2.wf()
            assert(self.all_blocks.perms@[block].wf());

            // size >= GRANULARITY (from valid_block_size of original components)
            assert(size >= GRANULARITY) by {
                assert(size as int >= (block_size_val & SIZE_SIZE_MASK) as int);
                assert((block_size_val & SIZE_SIZE_MASK) as int >= GRANULARITY as int);
            };

            // --- ghost_pointer_ordered(ptrs@) after removals ---
            // Removal preserves ordering (lemma_remove_ghost_pointer_ensures)
            let ghost old_ptrs = old(self).all_blocks.ptrs@;
            old(self).all_blocks.lemma_wf_nodup();
            if coalesced_with_next {
                lemma_remove_ghost_pointer_ensures(old_ptrs, next_phys_block);
            }
            if coalesced_with_prev {
                let ghost inter_ptrs = if coalesced_with_next {
                    remove_ghost_pointer(old_ptrs, next_phys_block)
                } else {
                    old_ptrs
                };
                // Need ptrs_no_duplicates for intermediate ptrs and contains
                if coalesced_with_next {
                    assert(orig_block_ptr != next_phys_block) by {
                        lemma_ptrs_no_duplicates_index_neq(
                            old_ptrs, block_i, block_i + 1);
                    };
                    lemma_ptrs_no_duplicates_preserved_by_remove(
                        old_ptrs, next_phys_block);
                    lemma_remove_ghost_pointer_contains_old(
                        old_ptrs, next_phys_block, orig_block_ptr);
                }
                assert(inter_ptrs.contains(orig_block_ptr));
                lemma_remove_ghost_pointer_ensures(inter_ptrs, orig_block_ptr);
            }
            assert(ghost_pointer_ordered(self.all_blocks.ptrs@));

            // --- valid_block_size(size as int) ---
            // Pool bound approach: block and new_next_phys_block are in post_unlink_ab.ptrs@
            // with block_idx < new_next_phys_idx. The pool_size_bounded invariant bounds
            // the address span between any two ordered pointers, which equals size.
            assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int)) by {
                // 1. Derive size == new_next_phys_block@.addr - block@.addr
                //    using structural facts and free-block mask facts.
                //
                // next_phys_block@.addr == orig_block_ptr@.addr
                //           + (block_size_val & SIZE_SIZE_MASK)
                // And initially: size == block_size_val & SIZE_SIZE_MASK
                // So before any coalescing: size == next_phys_block@.addr - orig_block_ptr@.addr
                //
                // After next coal (if any):
                //   size += next_phys_block_size == next_phys_size_val
                //   And next_phys_size_val == next_phys_size_val & SIZE_SIZE_MASK (free block)
                //   next_next_phys@.addr == next_phys@.addr
                //             + (next_phys_size_val & SIZE_SIZE_MASK)
                //   So size == next_next_phys@.addr - orig_block_ptr@.addr
                //           == new_next_phys_block@.addr - orig_block_ptr@.addr
                //
                // After prev coal (if any):
                //   size += prev_phys_block_size == prev_phys_block_size_and_flags
                //   And prev is free: prev_size == prev_size & SIZE_SIZE_MASK
                //   orig_block_ptr@.addr == block_prev_phys@.addr
                //             + (prev_size & SIZE_SIZE_MASK)
                //   So prev_phys_block_size == orig_block_ptr@.addr - block_prev_phys@.addr
                //   And size == new_next_phys@.addr - block_prev_phys@.addr
                //           == new_next_phys@.addr - block@.addr (block = prev after coal)
                assert(size as int
                    == new_next_phys_block@.addr - block@.addr);

                // 2. Pool bound on post_unlink_ab
                assert(block_idx < new_next_phys_idx);
                assert(post_unlink_ab.ptrs@[block_idx] == block);
                assert(post_unlink_ab.ptrs@[new_next_phys_idx]
                    == new_next_phys_block);
                assert(post_unlink_ab.ptrs@.len() >= 2) by {
                    // at least block and new_next exist
                    assert(0 <= block_idx);
                    assert(new_next_phys_idx < post_unlink_ab.ptrs@.len());
                };
                post_unlink_ab.lemma_pool_bound_any_span(
                    block_idx, new_next_phys_idx);
                // gives: (new_next_phys as usize as int) - (block as usize as int)
                //        < pow2(FLLEN) * GRANULARITY
                // And ptr as usize as int == ptr@.addr, so:
                assert(size < pow2(FLLEN as nat) * GRANULARITY);
            };

            // --- all_blocks.wf() via lemma_wf_from_nodes ---
            // Need: forall|i| 0 <= i < ptrs@.len() ==> wf_node(i)
            let ghost new_ptrs = self.all_blocks.ptrs@;
            let ghost new_len = new_ptrs.len();
            let ghost block_new_idx: int = block_idx;
            let ghost nnpb_new_idx: int = block_idx + 1;

            // ---- Establish ptrs_no_duplicates for old and new ptrs ----
            post_unlink_ab.lemma_wf_nodup();
            assert(ptrs_no_duplicates(post_unlink_ab.ptrs@));
            // Derive no_dup for new_ptrs via preservation through removals
            if coalesced_with_next {
                lemma_ptrs_no_duplicates_preserved_by_remove(
                    post_unlink_ab.ptrs@, next_phys_block);
                lemma_remove_ghost_pointer_ensures(
                    post_unlink_ab.ptrs@, next_phys_block);
            }
            if coalesced_with_prev {
                let ghost inter = if coalesced_with_next {
                    remove_ghost_pointer(post_unlink_ab.ptrs@, next_phys_block)
                } else {
                    post_unlink_ab.ptrs@
                };
                if coalesced_with_next {
                    lemma_remove_ghost_pointer_contains_old(
                        post_unlink_ab.ptrs@, next_phys_block, orig_block_ptr);
                }
                lemma_ptrs_no_duplicates_preserved_by_remove(inter, orig_block_ptr);
                lemma_remove_ghost_pointer_ensures(inter, orig_block_ptr);
            }
            assert(ptrs_no_duplicates(new_ptrs));

            // Pre-resolve choose indices used by lemma_remove_ghost_pointer_index_map.
            // The ensures clause uses `let idx = choose|j| ls[j] == p` to branch on
            // `i < idx` vs `i >= idx`. Since ptrs_no_duplicates is closed, the solver
            // cannot automatically deduce idx equals the known concrete index. We resolve
            // this once here so all subsequent index_map calls become decidable.
            if coalesced_with_next {
                let ghost rm_idx = choose|j: int|
                    0 <= j < post_unlink_ab.ptrs@.len()
                    && post_unlink_ab.ptrs@[j] == next_phys_block;
                assert(post_unlink_ab.ptrs@[block_i + 1] == next_phys_block);
                lemma_ptrs_no_duplicates_eq_index(
                    post_unlink_ab.ptrs@, rm_idx, block_i + 1);
            }
            if coalesced_with_prev && coalesced_with_next {
                let ghost inter = remove_ghost_pointer(
                    post_unlink_ab.ptrs@, next_phys_block);
                // inter[block_i] == orig: block_i < block_i + 1 (removal point)
                lemma_remove_ghost_pointer_index_map(
                    post_unlink_ab.ptrs@, next_phys_block, block_i);
                assert(post_unlink_ab.ptrs@[block_i] == orig_block_ptr);
                let ghost rm_idx = choose|j: int|
                    0 <= j < inter.len() && inter[j] == orig_block_ptr;
                lemma_ptrs_no_duplicates_eq_index(inter, rm_idx, block_i);
            }
            if coalesced_with_prev && !coalesced_with_next {
                let ghost rm_idx = choose|j: int|
                    0 <= j < post_unlink_ab.ptrs@.len()
                    && post_unlink_ab.ptrs@[j] == orig_block_ptr;
                assert(post_unlink_ab.ptrs@[block_i] == orig_block_ptr);
                lemma_ptrs_no_duplicates_eq_index(
                    post_unlink_ab.ptrs@, rm_idx, block_i);
            }

            // ---- Index facts: establish ptrs@[block_new_idx] == block, etc. ----
            assert(0 <= block_new_idx) by {
                if coalesced_with_prev {
                    assert(block_idx == block_i - 1);
                    // block_prev_phys@.addr != 0 means block_i >= 1
                    assert(block_i >= 1);
                } else {
                    assert(block_idx == block_i);
                }
            };
            // new_ptrs comes from removals of post_unlink_ab.ptrs@
            // block is at block_new_idx and nnpb is at block_new_idx + 1
            assert(new_ptrs[block_new_idx] == block) by {
                if !coalesced_with_next && !coalesced_with_prev {
                    // No removals
                    assert(new_ptrs == post_unlink_ab.ptrs@);
                    assert(post_unlink_ab.ptrs@[block_i] == block);
                } else if coalesced_with_next && !coalesced_with_prev {
                    // Removed next at block_i + 1
                    lemma_remove_ghost_pointer_index_map(
                        post_unlink_ab.ptrs@, next_phys_block, block_i);
                    assert(block_i < block_i + 1);
                } else if !coalesced_with_next && coalesced_with_prev {
                    // Removed orig at block_i
                    lemma_remove_ghost_pointer_index_map(
                        post_unlink_ab.ptrs@, orig_block_ptr, block_i - 1);
                    assert(block_i - 1 < block_i);
                } else {
                    // Both: first removed next at block_i+1, then orig at block_i
                    let ghost inter_ptrs = remove_ghost_pointer(
                        post_unlink_ab.ptrs@, next_phys_block);
                    lemma_remove_ghost_pointer_index_map(
                        post_unlink_ab.ptrs@, next_phys_block, block_i - 1);
                    assert(block_i - 1 < block_i + 1);
                    // inter_ptrs[block_i-1] = old[block_i-1] = prev = block
                    assert(inter_ptrs[block_i - 1] == post_unlink_ab.ptrs@[block_i - 1]);
                    assert(post_unlink_ab.ptrs@[block_i - 1] == block_prev_phys);
                    assert(block == block_prev_phys);
                    assert(inter_ptrs[block_i - 1] == block);
                    lemma_remove_ghost_pointer_ensures(
                        post_unlink_ab.ptrs@, next_phys_block);
                    lemma_ptrs_no_duplicates_preserved_by_remove(
                        post_unlink_ab.ptrs@, next_phys_block);
                    lemma_remove_ghost_pointer_contains_old(
                        post_unlink_ab.ptrs@, next_phys_block, orig_block_ptr);
                    lemma_remove_ghost_pointer_index_map(
                        inter_ptrs, orig_block_ptr, block_i - 1);
                    // block_i - 1 < block_i (the index of orig in inter_ptrs)
                    assert(block_i - 1 < block_i);
                }
            };
            assert(new_ptrs[nnpb_new_idx] == new_next_phys_block) by {
                if !coalesced_with_next && !coalesced_with_prev {
                    assert(new_ptrs == post_unlink_ab.ptrs@);
                } else if coalesced_with_next && !coalesced_with_prev {
                    // Removed next at block_i+1. nnpb = next_next at block_i+2.
                    // new index = block_i + 1.
                    lemma_remove_ghost_pointer_ensures(
                        post_unlink_ab.ptrs@, next_phys_block);
                    lemma_remove_ghost_pointer_index_map(
                        post_unlink_ab.ptrs@, next_phys_block, block_i + 1);
                    // block_i + 1 >= block_i + 1, so new[block_i+1] = old[block_i+2] = nnpb
                } else if !coalesced_with_next && coalesced_with_prev {
                    // Removed orig at block_i. nnpb = next at block_i+1.
                    // new index = block_i.
                    lemma_remove_ghost_pointer_index_map(
                        post_unlink_ab.ptrs@, orig_block_ptr, block_i);
                    // block_i >= block_i, so new[block_i] = old[block_i+1] = next = nnpb
                } else {
                    // Both: nnpb = next_next at old block_i+2.
                    // After removing next at block_i+1: inter[block_i+1] = old[block_i+2] = nnpb
                    let ghost inter_ptrs = remove_ghost_pointer(
                        post_unlink_ab.ptrs@, next_phys_block);
                    lemma_remove_ghost_pointer_ensures(
                        post_unlink_ab.ptrs@, next_phys_block);
                    lemma_remove_ghost_pointer_index_map(
                        post_unlink_ab.ptrs@, next_phys_block, block_i + 1);
                    assert(inter_ptrs[block_i + 1] == new_next_phys_block);
                    // After removing orig at inter[block_i]: new[block_i] = inter[block_i+1]
                    lemma_ptrs_no_duplicates_preserved_by_remove(
                        post_unlink_ab.ptrs@, next_phys_block);
                    lemma_remove_ghost_pointer_contains_old(
                        post_unlink_ab.ptrs@, next_phys_block, orig_block_ptr);
                    lemma_remove_ghost_pointer_index_map(
                        inter_ptrs, orig_block_ptr, block_i);
                    // block_i >= block_i, so new[block_i] = inter[block_i+1] = nnpb
                }
            };
            assert(nnpb_new_idx < new_len) by {
                // nnpb was at new_next_phys_idx in old ptrs, which was < old len
                // Removals reduce len by 0/1/2, but nnpb is not removed
                assert(0 <= nnpb_new_idx < new_len);
            };
            assert(0 <= block_new_idx);
            assert(block_new_idx < nnpb_new_idx);

            // ---- nnpb is not free ----
            let ghost nnpb_not_free: bool = !self.all_blocks.value_at(
                new_next_phys_block).is_free();
            assert(nnpb_not_free) by {
                // nnpb's size field is nnpb_size (written with same value during header writes)
                assert(self.all_blocks.value_at(new_next_phys_block).size == nnpb_size);
                if coalesced_with_next {
                    // nnpb = next_next. In old state, next was free, so by structural
                    // wf_node, next's phys_next (= nnpb) was not free.
                    post_unlink_ab.lemma_wf_structural_facts(block_i + 1);
                    // old value_at(nnpb).size had SIZE_USED set. nnpb_size == that value.
                } else {
                    // nnpb = next_phys_block. We didn't coalesce because SIZE_USED was set.
                    assert((next_phys_block_size_and_flags & SIZE_USED) != 0usize);
                    // nnpb_size == next_phys_block_size_and_flags (read from same block)
                }
            };

            // ---- Prove phys_next_matches(nnpb, block, size) ----
            // nnpb@.addr == block@.addr + (size & SIZE_SIZE_MASK)
            // We proved size == size & SIZE_SIZE_MASK above.
            // And block + size == nnpb physically (from coalescence structure).
            assert(new_next_phys_block@.addr == block@.addr + size) by {
                // block@.addr + size = orig@.addr + ... = nnpb@.addr
                // From structural facts.
                if coalesced_with_prev {
                    // block = prev. prev@.addr + prev_size = orig@.addr.
                    // orig@.addr + orig_size = next@.addr.
                    // If coalesced_with_next: next@.addr + next_size = nnpb@.addr.
                    // size = prev_size + orig_size (+ next_size if next).
                    // block@.addr + size = prev@.addr + prev_size + orig_size (+ next_size)
                    //   = next@.addr (+ next_size) = nnpb@.addr.
                    post_unlink_ab.lemma_wf_structural_facts(block_i - 1);
                    AllBlocks::<FLLEN, SLLEN>::lemma_phys_next_matches_elim(
                        orig_block_ptr, block_prev_phys,
                        post_unlink_ab.value_at(block_prev_phys).size);
                    post_unlink_ab.lemma_wf_structural_facts(block_i);
                    AllBlocks::<FLLEN, SLLEN>::lemma_phys_next_matches_elim(
                        next_phys_block, orig_block_ptr,
                        post_unlink_ab.value_at(orig_block_ptr).size);
                    if coalesced_with_next {
                        post_unlink_ab.lemma_wf_structural_facts(block_i + 1);
                        AllBlocks::<FLLEN, SLLEN>::lemma_phys_next_matches_elim(
                            next_next_phys_block, next_phys_block,
                            post_unlink_ab.value_at(next_phys_block).size);
                    }
                } else {
                    // block = orig.
                    post_unlink_ab.lemma_wf_structural_facts(block_i);
                    AllBlocks::<FLLEN, SLLEN>::lemma_phys_next_matches_elim(
                        next_phys_block, orig_block_ptr,
                        post_unlink_ab.value_at(orig_block_ptr).size);
                    if coalesced_with_next {
                        post_unlink_ab.lemma_wf_structural_facts(block_i + 1);
                        AllBlocks::<FLLEN, SLLEN>::lemma_phys_next_matches_elim(
                            next_next_phys_block, next_phys_block,
                            post_unlink_ab.value_at(next_phys_block).size);
                    }
                }
            };
            assert(new_next_phys_block@.provenance == block@.provenance);
            AllBlocks::<FLLEN, SLLEN>::lemma_phys_next_matches_intro(
                new_next_phys_block, block, size);

            // ---- prev_phys_block of block matches phys_prev_of(block_new_idx) ----
            // final_prev_phys was read from block's old header. In post_unlink_ab,
            // wf_node_glue ensures it matches phys_prev_of(block_idx) in old ptrs.
            // The node at block_new_idx - 1 in new ptrs is the same as at block_idx - 1 in old ptrs.
            assert(self.all_blocks.value_at(block).prev_phys_block == final_prev_phys);
            // Connect final_prev_phys to old state
            assert(final_prev_phys == post_unlink_ab.value_at(block).prev_phys_block);
            // Extract glue facts from old state for block
            post_unlink_ab.lemma_wf_glue_facts(block_idx);
            assert(
                (final_prev_phys@.addr != 0) ==>
                    (self.all_blocks.phys_prev_of(block_new_idx) matches Some(p)
                        && p == final_prev_phys)
            ) by {
                if final_prev_phys@.addr != 0 {
                    assert(block_new_idx > 0);
                    // old state: ptrs[block_idx - 1] == final_prev_phys
                    assert(post_unlink_ab.phys_prev_of(block_idx) matches Some(p)
                        && p == final_prev_phys);
                    assert(post_unlink_ab.ptrs@[block_idx - 1] == final_prev_phys);
                    // block_idx - 1 is before all removed indices
                    // (block_idx - 1 < block_i for both, < block_i for prev only,
                    //  < block_i + 1 for next only)
                    if !coalesced_with_next && !coalesced_with_prev {
                        // No removals
                    } else if coalesced_with_next && !coalesced_with_prev {
                        assert(block_idx - 1 < block_i + 1);
                        lemma_remove_ghost_pointer_index_map(
                            post_unlink_ab.ptrs@, next_phys_block, block_idx - 1);
                    } else if !coalesced_with_next && coalesced_with_prev {
                        assert(block_idx - 1 < block_i);
                        lemma_remove_ghost_pointer_index_map(
                            post_unlink_ab.ptrs@, orig_block_ptr, block_idx - 1);
                    } else {
                        assert(block_idx - 1 < block_i + 1);
                        assert(block_idx - 1 < block_i);
                        let ghost inter_ptrs = remove_ghost_pointer(
                            post_unlink_ab.ptrs@, next_phys_block);
                        lemma_remove_ghost_pointer_index_map(
                            post_unlink_ab.ptrs@, next_phys_block, block_idx - 1);
                        lemma_remove_ghost_pointer_ensures(
                            post_unlink_ab.ptrs@, next_phys_block);
                        lemma_ptrs_no_duplicates_preserved_by_remove(
                            post_unlink_ab.ptrs@, next_phys_block);
                        lemma_remove_ghost_pointer_contains_old(
                            post_unlink_ab.ptrs@, next_phys_block, orig_block_ptr);
                        lemma_remove_ghost_pointer_index_map(
                            inter_ptrs, orig_block_ptr, block_idx - 1);
                    }
                    assert(new_ptrs[block_new_idx - 1] == final_prev_phys);
                }
            };
            assert(
                final_prev_phys@.addr == 0 ==>
                    self.all_blocks.phys_prev_of(block_new_idx) is None
            ) by {
                if final_prev_phys@.addr == 0 {
                    assert(block_idx == 0);
                    assert(block_new_idx == 0);
                }
            };

            // ---- size + block < usize::MAX ----
            assert((size as int) + (block as int) < (usize::MAX as int)) by {
                // From overflow proofs during coalescing
                // block@.addr > 0 was established earlier
                // size is the sum of coalesced block sizes and their addresses are contiguous
                assert(size as int + block as int
                    <= new_next_phys_block as int);
                assert((new_next_phys_block as int) < (usize::MAX as int));
            };

            // ---- wf_node for block ----
            assert(self.all_blocks.wf_node(block_new_idx)) by {
                AllBlocks::<FLLEN, SLLEN>::lemma_wf_node_ptr_from_facts(block);
                assert(self.all_blocks.perms@.contains_key(block));
                assert(block == self.all_blocks.perms@[block].points_to.ptr());
                assert(self.all_blocks.perms@[block].wf());
                // block is not sentinel: size % 32 == 0 implies size & SIZE_SENTINEL == 0
                assert(!self.all_blocks.value_at(block).is_sentinel()) by {
                    assert(self.all_blocks.value_at(block).size == size);
                    assert(size as int % 32 == 0);
                    assert((size & SIZE_SENTINEL) == 0usize) by (bit_vector)
                        requires
                            size as int % 32 == 0,
                            SIZE_SENTINEL == 2usize;
                };
                self.all_blocks.lemma_construct_wf_node_glue(block_new_idx);
                self.all_blocks.lemma_construct_wf_node_structural(block_new_idx);
            };

            // ---- nnpb prev_phys_block conditions ----
            // value_at(nnpb).prev_phys_block == block, phys_prev_of(nnpb_new_idx) = Some(block)
            assert(self.all_blocks.value_at(new_next_phys_block).prev_phys_block == block);
            assert(self.all_blocks.phys_prev_of(nnpb_new_idx) matches Some(p) && p == block) by {
                assert(new_ptrs[nnpb_new_idx - 1] == block);
            };

            // ---- nnpb: sentinel or non-sentinel conditions ----
            // In old state, nnpb had certain properties (valid_block_size, etc.)
            // These are preserved since nnpb_size == old size.
            // If nnpb is sentinel: i == len - 1 && size == 0
            // If not: valid_block_size, size + ptr < usize::MAX, phys_next is Some
            let ghost nnpb_is_sentinel: bool =
                self.all_blocks.value_at(new_next_phys_block).is_sentinel();
            assert(nnpb_is_sentinel ==> {
                &&& nnpb_new_idx == new_len - 1
                &&& self.all_blocks.value_at(new_next_phys_block).size == 0usize
            }) by {
                if nnpb_is_sentinel {
                    // nnpb_size == old nnpb size. sentinel has size 0.
                    // In old state, nnpb was at new_next_phys_idx. If sentinel there,
                    // it was last, and size was 0.
                    post_unlink_ab.lemma_wf_glue_facts(new_next_phys_idx);
                    // old: sentinel ==> new_next_phys_idx == old_len - 1 && size == 0
                    // new_len = old_len - num_removals. nnpb_new_idx = new_next_phys_idx - num_removals.
                    // So nnpb_new_idx == new_len - 1. ✓
                }
            };
            assert(!nnpb_is_sentinel ==> {
                &&& BlockIndex::<FLLEN, SLLEN>::valid_block_size(
                    (self.all_blocks.value_at(new_next_phys_block).size & SIZE_SIZE_MASK) as int)
                &&& (self.all_blocks.value_at(new_next_phys_block).size as int)
                    + (new_next_phys_block as int) < (usize::MAX as int)
                &&& self.all_blocks.phys_next_of(nnpb_new_idx) is Some
            }) by {
                if !nnpb_is_sentinel {
                    post_unlink_ab.lemma_wf_glue_facts(new_next_phys_idx);
                    // valid_block_size and size + ptr < usize::MAX from old state
                    // phys_next_of: nnpb_new_idx + 1 < new_len
                    // In old: new_next_phys_idx + 1 < old_len.
                    // nnpb_new_idx + 1 = (new_next_phys_idx - num_removals) + 1
                    //                  = new_next_phys_idx + 1 - num_removals
                    //                  < old_len - num_removals = new_len. ✓
                }
            };

            // ---- wf_node for nnpb ----
            assert(self.all_blocks.wf_node(nnpb_new_idx)) by {
                // wf_node_ptr: from old state
                post_unlink_ab.lemma_wf_node_ptr(new_next_phys_idx);
                // nnpb ptr didn't change
                assert(AllBlocks::<FLLEN, SLLEN>::wf_node_ptr(new_next_phys_block));
                assert(self.all_blocks.perms@.contains_key(new_next_phys_block));
                assert(new_next_phys_block
                    == self.all_blocks.perms@[new_next_phys_block].points_to.ptr());
                assert(self.all_blocks.perms@[new_next_phys_block].wf());
                self.all_blocks.lemma_construct_wf_node_glue(nnpb_new_idx);
                // For structural: phys_next_matches from old state
                assert(self.all_blocks.phys_next_of(nnpb_new_idx) matches Some(next_ptr)
                    ==> AllBlocks::<FLLEN, SLLEN>::phys_next_matches(
                        next_ptr, new_next_phys_block,
                        self.all_blocks.value_at(new_next_phys_block).size)
                ) by {
                    if self.all_blocks.phys_next_of(nnpb_new_idx) is Some {
                        let next_ptr = self.all_blocks.phys_next_of(nnpb_new_idx).unwrap();
                        // next_ptr = new_ptrs[nnpb_new_idx + 1]
                        // In old state, old_ptrs[new_next_phys_idx + 1] was phys_next of nnpb
                        post_unlink_ab.lemma_wf_structural_facts(new_next_phys_idx);
                        let ghost old_next = post_unlink_ab.ptrs@[new_next_phys_idx + 1];
                        // phys_next_matches(old_next, nnpb, old_size) from old structural
                        // old_size == nnpb_size (nnpb's size was read/rewritten)
                        assert(self.all_blocks.value_at(new_next_phys_block).size == nnpb_size);
                        assert(nnpb_size == post_unlink_ab.value_at(new_next_phys_block).size);
                        // Show next_ptr == old_next via index mapping
                        // nnpb_new_idx + 1 is after all removed indices, so maps directly
                        if !coalesced_with_next && !coalesced_with_prev {
                            assert(next_ptr == old_next);
                        } else if coalesced_with_next && !coalesced_with_prev {
                            // new_next_phys_idx = block_i + 2
                            // nnpb_new_idx + 1 = block_i + 2, removal was at block_i + 1
                            // new[block_i + 2] maps to old[block_i + 3] = old[new_next_phys_idx + 1]
                            lemma_remove_ghost_pointer_index_map(
                                post_unlink_ab.ptrs@, next_phys_block, nnpb_new_idx + 1);
                        } else if !coalesced_with_next && coalesced_with_prev {
                            // new_next_phys_idx = block_i + 1
                            // nnpb_new_idx + 1 = block_i + 1, removal was at block_i
                            // new[block_i + 1] maps to old[block_i + 2] = old[new_next_phys_idx + 1]
                            lemma_remove_ghost_pointer_index_map(
                                post_unlink_ab.ptrs@, orig_block_ptr, nnpb_new_idx + 1);
                        } else {
                            // new_next_phys_idx = block_i + 2
                            // nnpb_new_idx + 1 = block_i + 1
                            // After removing next at block_i+1: inter[block_i+1] = old[block_i+2]
                            // wait, nnpb is at block_i in new ptrs, so nnpb+1 = block_i + 1
                            let ghost inter_ptrs = remove_ghost_pointer(
                                post_unlink_ab.ptrs@, next_phys_block);
                            lemma_remove_ghost_pointer_ensures(
                                post_unlink_ab.ptrs@, next_phys_block);
                            // inter[block_i + 1] = old[block_i + 2] since block_i+1 >= block_i+1
                            lemma_remove_ghost_pointer_index_map(
                                post_unlink_ab.ptrs@, next_phys_block, block_i + 1);
                            assert(inter_ptrs[block_i + 1] ==
                                post_unlink_ab.ptrs@[block_i + 2]);
                            // After removing orig at inter[block_i]:
                            // new[block_i + 1] maps to... but wait, nnpb_new_idx = block_i
                            // nnpb_new_idx + 1 = block_i + 1
                            // In inter_ptrs, orig is at block_i. block_i + 1 >= block_i.
                            // So new[block_i + 1 - 1] = inter[block_i + 1] => wrong direction
                            // Actually: new[j] where j >= block_i maps to inter[j + 1]
                            lemma_ptrs_no_duplicates_preserved_by_remove(
                                post_unlink_ab.ptrs@, next_phys_block);
                            lemma_remove_ghost_pointer_contains_old(
                                post_unlink_ab.ptrs@, next_phys_block, orig_block_ptr);
                            lemma_remove_ghost_pointer_index_map(
                                inter_ptrs, orig_block_ptr, block_i);
                            // block_i >= block_i, so new[block_i] = inter[block_i + 1]
                            // = old[block_i + 2] = old[new_next_phys_idx]
                            // But we need new[nnpb_new_idx + 1] = new[block_i + 1]
                            // Hmm, block_i + 1 > block_i, so:
                            lemma_remove_ghost_pointer_index_map(
                                inter_ptrs, orig_block_ptr, block_i + 1);
                            // block_i + 1 >= block_i, so new[block_i+1] = inter[block_i+2]
                            // And inter[block_i + 2] = old[block_i + 3] since block_i+2 > block_i+1
                            lemma_remove_ghost_pointer_index_map(
                                post_unlink_ab.ptrs@, next_phys_block, block_i + 2);
                            assert(inter_ptrs[block_i + 2] ==
                                post_unlink_ab.ptrs@[block_i + 3]);
                            assert(next_ptr == post_unlink_ab.ptrs@[block_i + 3]);
                            assert(old_next == post_unlink_ab.ptrs@[block_i + 3]);
                        }
                        assert(next_ptr == old_next);
                    }
                };
                self.all_blocks.lemma_construct_wf_node_structural(nnpb_new_idx);
            };

            // ---- wf_node for other nodes via transfer ----
            // Pre-establish facts needed inside the forall
            let ghost old_ptrs = post_unlink_ab.ptrs@;
            let ghost old_len = old_ptrs.len();
            // Pre-establish non-containment of removed blocks in new_ptrs
            if coalesced_with_prev {
                assert(!new_ptrs.contains(orig_block_ptr));
            }
            if coalesced_with_next {
                if coalesced_with_prev {
                    let ghost inter = remove_ghost_pointer(old_ptrs, next_phys_block);
                    if new_ptrs.contains(next_phys_block) {
                        lemma_remove_ghost_pointer_contains_reverse(
                            inter, orig_block_ptr, next_phys_block);
                    }
                }
                assert(!new_ptrs.contains(next_phys_block));
            }
            assert forall|i: int| 0 <= i < new_len
                && i != block_new_idx && i != nnpb_new_idx
                implies self.all_blocks.wf_node(i) by {
                // Compute old_i based on which removals happened
                // Removals: next at old[block_i+1] (if coal_next), orig at old[block_i] (if coal_prev)
                // Both removals are at indices >= block_i, so:
                //   i < block_i (if coal_prev) or i <= block_i (if !coal_prev): old_i = i
                //   otherwise: old_i = i + num_removed
                let ghost old_i: int = if !coalesced_with_next && !coalesced_with_prev {
                    i
                } else if coalesced_with_next && !coalesced_with_prev {
                    // Removed next at block_i + 1. block_idx = block_i, nnpb_idx = block_i+1.
                    // i != block_i and i != block_i+1, so i < block_i or i >= block_i+2.
                    if i <= block_i { i } else { i + 1 }
                } else if !coalesced_with_next && coalesced_with_prev {
                    // Removed orig at block_i. block_idx = block_i-1, nnpb_idx = block_i.
                    // i != block_i-1 and i != block_i, so i < block_i-1 or i >= block_i+1.
                    if i < block_i { i } else { i + 1 }
                } else {
                    // Both: removed next at block_i+1 then orig at block_i.
                    // block_idx = block_i-1, nnpb_idx = block_i.
                    // i != block_i-1 and i != block_i, so i < block_i-1 or i > block_i.
                    if i < block_i { i } else { i + 2 }
                };

                // Establish: old_ptrs[old_i] == new_ptrs[i] via index_map
                assert(0 <= old_i < old_len);
                if !coalesced_with_next && !coalesced_with_prev {
                    assert(old_ptrs[old_i] == new_ptrs[i]);
                } else if coalesced_with_next && !coalesced_with_prev {
                    lemma_remove_ghost_pointer_index_map(
                        old_ptrs, next_phys_block, i);
                } else if !coalesced_with_next && coalesced_with_prev {
                    lemma_remove_ghost_pointer_index_map(
                        old_ptrs, orig_block_ptr, i);
                } else {
                    let ghost inter_ptrs = remove_ghost_pointer(old_ptrs, next_phys_block);
                    lemma_remove_ghost_pointer_ensures(old_ptrs, next_phys_block);
                    lemma_ptrs_no_duplicates_preserved_by_remove(old_ptrs, next_phys_block);
                    lemma_remove_ghost_pointer_contains_old(
                        old_ptrs, next_phys_block, orig_block_ptr);
                    if i < block_i {
                        // i < block_i < block_i + 1: inter[i] = old[i], new[i] = inter[i]
                        lemma_remove_ghost_pointer_index_map(old_ptrs, next_phys_block, i);
                        lemma_remove_ghost_pointer_index_map(inter_ptrs, orig_block_ptr, i);
                    } else {
                        // i > block_i: new[i] = inter[i+1] = old[i+2]
                        lemma_remove_ghost_pointer_index_map(inter_ptrs, orig_block_ptr, i);
                        // inter[i+1]: i+1 >= block_i + 1, so inter[i+1] = old[i+2]
                        lemma_remove_ghost_pointer_index_map(old_ptrs, next_phys_block, i + 1);
                    }
                }
                assert(old_ptrs[old_i] == new_ptrs[i]);
                let ghost ptr = new_ptrs[i];

                // ptr is not block, nnpb, orig, or next (from no_dup + index exclusion)
                assert(ptr != block) by {
                    if ptr == block {
                        lemma_ptrs_no_duplicates_eq_index(new_ptrs, i, block_new_idx);
                    }
                };
                assert(ptr != new_next_phys_block) by {
                    if ptr == new_next_phys_block {
                        lemma_ptrs_no_duplicates_eq_index(new_ptrs, i, nnpb_new_idx);
                    }
                };
                // ptr is also not orig or next (removed from ptrs@ or equal to block/nnpb)
                assert(ptr != orig_block_ptr) by {
                    if !coalesced_with_prev {
                        // block == orig, and ptr != block
                    } else {
                        // orig removed from new_ptrs
                        assert(!new_ptrs.contains(orig_block_ptr));
                    }
                };
                assert(ptr != next_phys_block) by {
                    if !coalesced_with_next {
                        // nnpb == next, and ptr != nnpb
                    } else {
                        // next removed from new_ptrs
                        assert(!new_ptrs.contains(next_phys_block));
                    }
                };
                // perms@ unchanged for ptr (not among modified/removed keys)
                // removed/inserted block and nnpb
                // removed orig (if coal_prev) and next (if coal_next), then inserted block
                post_unlink_ab.lemma_wf_perm_wf(old_i);
                assert(post_unlink_ab.perms@.contains_key(ptr));
                assert(self.all_blocks.perms@.contains_key(ptr));
                assert(post_unlink_ab.perms@[ptr] == self.all_blocks.perms@[ptr]);

                // phys_prev_of and phys_next_of match between old and new
                // Because old_i and i have the same relative position to their neighbors
                assert(post_unlink_ab.phys_prev_of(old_i)
                    == self.all_blocks.phys_prev_of(i)) by {
                    if old_i == 0 {
                        assert(i == 0);
                    } else {
                        // old_ptrs[old_i - 1] == new_ptrs[i - 1]
                        // Use index_map for i - 1
                        if !coalesced_with_next && !coalesced_with_prev {
                            // trivial
                        } else if coalesced_with_next && !coalesced_with_prev {
                            lemma_remove_ghost_pointer_index_map(
                                old_ptrs, next_phys_block, i - 1);
                        } else if !coalesced_with_next && coalesced_with_prev {
                            lemma_remove_ghost_pointer_index_map(
                                old_ptrs, orig_block_ptr, i - 1);
                        } else {
                            let ghost inter_ptrs = remove_ghost_pointer(
                                old_ptrs, next_phys_block);
                            if i - 1 < block_i {
                                lemma_remove_ghost_pointer_index_map(
                                    old_ptrs, next_phys_block, i - 1);
                                lemma_remove_ghost_pointer_index_map(
                                    inter_ptrs, orig_block_ptr, i - 1);
                            } else {
                                lemma_remove_ghost_pointer_index_map(
                                    inter_ptrs, orig_block_ptr, i - 1);
                                lemma_remove_ghost_pointer_index_map(
                                    old_ptrs, next_phys_block, i);
                            }
                        }
                    }
                };
                assert(post_unlink_ab.phys_next_of(old_i)
                    == self.all_blocks.phys_next_of(i)) by {
                    if old_i == old_len - 1 {
                        // sentinel: phys_next is None in both
                        assert(i == new_len - 1);
                    } else {
                        // old_ptrs[old_i + 1] == new_ptrs[i + 1]
                        if !coalesced_with_next && !coalesced_with_prev {
                            // trivial
                        } else if coalesced_with_next && !coalesced_with_prev {
                            lemma_remove_ghost_pointer_index_map(
                                old_ptrs, next_phys_block, i + 1);
                        } else if !coalesced_with_next && coalesced_with_prev {
                            lemma_remove_ghost_pointer_index_map(
                                old_ptrs, orig_block_ptr, i + 1);
                        } else {
                            let ghost inter_ptrs = remove_ghost_pointer(
                                old_ptrs, next_phys_block);
                            if i + 1 < block_i {
                                lemma_remove_ghost_pointer_index_map(
                                    old_ptrs, next_phys_block, i + 1);
                                lemma_remove_ghost_pointer_index_map(
                                    inter_ptrs, orig_block_ptr, i + 1);
                            } else {
                                lemma_remove_ghost_pointer_index_map(
                                    inter_ptrs, orig_block_ptr, i + 1);
                                lemma_remove_ghost_pointer_index_map(
                                    old_ptrs, next_phys_block, i + 2);
                            }
                        }
                    }
                };

                // Free-next value: if this node is free and has phys_next,
                // then next's value must match. The only modified values are at
                // block and nnpb. The node before block (at block_new_idx - 1)
                // is not free (otherwise we'd have coalesced with prev).
                // No other "other" node has phys_next pointing to block or nnpb.
                assert(
                    (post_unlink_ab.value_at(ptr).is_free()
                        && post_unlink_ab.phys_next_of(old_i) is Some)
                    ==> post_unlink_ab.value_at(
                            post_unlink_ab.phys_next_of(old_i).unwrap())
                        == self.all_blocks.value_at(
                            self.all_blocks.phys_next_of(i).unwrap())
                ) by {
                    if post_unlink_ab.value_at(ptr).is_free()
                        && post_unlink_ab.phys_next_of(old_i) is Some {
                        let ghost next_ptr = self.all_blocks.phys_next_of(i).unwrap();
                        // next_ptr == old_ptrs[old_i + 1] (from phys_next match above)
                        // If next_ptr == block or nnpb, values differ.
                        // But: if this node is free, old wf_structural says next is not free.
                        // And for next == block: in old state, block was either used (not free)
                        // or was the prev block (free, but then i = block_new_idx - 1).
                        // For i = block_new_idx - 1: not free (would have coalesced).
                        // So next_ptr != block for free nodes (except block_new_idx - 1 which isn't free).
                        // next_ptr != nnpb: only block_new_idx has phys_next = nnpb.
                        // But i != block_new_idx. So next_ptr != nnpb.
                        assert(next_ptr != new_next_phys_block) by {
                            if next_ptr == new_next_phys_block {
                                // phys_next_of(i) = Some(new_ptrs[i+1]) = Some(nnpb)
                                // So new_ptrs[i+1] == nnpb == new_ptrs[nnpb_new_idx]
                                // By no_dup: i+1 == nnpb_new_idx, so i == block_new_idx.
                                // But i != block_new_idx. Contradiction.
                                lemma_ptrs_no_duplicates_eq_index(
                                    new_ptrs, i + 1, nnpb_new_idx);
                            }
                        };
                        // next_ptr's perms unchanged (it's not block or nnpb)
                        // So value_at matches.
                        if next_ptr == block {
                            // i + 1 == block_new_idx, so i == block_new_idx - 1
                            lemma_ptrs_no_duplicates_eq_index(
                                new_ptrs, i + 1, block_new_idx);
                            assert(i == block_new_idx - 1);
                            // Node at block_new_idx - 1 is NOT free. Contradiction.
                            if coalesced_with_prev {
                                // block_new_idx = block_i - 1, i = block_i - 2
                                // wf_structural: if free, phys_next (= block_prev_phys) not free
                                // But block_prev_phys IS free (we coalesced). Contradiction.
                                post_unlink_ab.lemma_wf_structural_facts(old_i);
                                assert(post_unlink_ab.value_at(block_prev_phys).is_free());
                            } else {
                                // ptr = block_prev_phys which is not free
                                // (else we would have coalesced)
                                assert(prev_phys_block_size_and_flags & SIZE_USED != 0usize);
                                assert(prev_phys_block_size_and_flags
                                    == post_unlink_ab.value_at(block_prev_phys).size);
                            }
                            assert(false);
                        }
                        // next_ptr is neither block nor nnpb, so perms are unchanged
                        assert(post_unlink_ab.perms@[next_ptr]
                            == self.all_blocks.perms@[next_ptr]);
                    }
                };

                assert(self.all_blocks.perms@.contains_key(ptr));
                AllBlocks::<FLLEN, SLLEN>::lemma_transfer_wf_node(
                    &post_unlink_ab, &self.all_blocks, old_i, i);
            };

            // ---- combine and finish ----
            assert forall|i: int| 0 <= i < new_len
                implies self.all_blocks.wf_node(i) by {
            };
            // pool_size_bounded: first and last of ptrs@ are preserved through removals.
            // Sentinel (last) is never removed (not free, not the deallocated block).
            // First block (index 0) is never removed (prev coal requires block_i >= 1,
            // next coal removes block_i + 1 >= 1).
            assert(self.all_blocks.pool_size_bounded()) by {
                post_unlink_ab.lemma_pool_size_bounded();
                if post_unlink_ab.ptrs@.len() < 2 {
                    self.all_blocks.lemma_pool_size_bounded_trivial();
                } else if !coalesced_with_next && !coalesced_with_prev {
                    AllBlocks::<FLLEN, SLLEN>::lemma_pool_size_bounded_transfer(
                        &post_unlink_ab, &self.all_blocks);
                } else {
                    // After removals: first and last preserved → use from_sub
                    // new_ptrs[0] == post_unlink_ab.ptrs@[0]
                    // new_ptrs.last() == post_unlink_ab.ptrs@.last()
                    assert(new_ptrs.len() >= 2) by {
                        // block and new_next_phys_block are still in new_ptrs
                        assert(new_ptrs.contains(block));
                        assert(new_ptrs.contains(new_next_phys_block));
                        assert(block != new_next_phys_block);
                    };
                    // Show first element preserved
                    assert(new_ptrs[0] == post_unlink_ab.ptrs@[0]) by {
                        if coalesced_with_next && !coalesced_with_prev {
                            // Removed next_phys_block at index block_i + 1 >= 1
                            lemma_remove_ghost_pointer_index_map(
                                post_unlink_ab.ptrs@, next_phys_block, 0);
                        } else if !coalesced_with_next && coalesced_with_prev {
                            // Removed orig_block_ptr at index block_i >= 1
                            lemma_remove_ghost_pointer_index_map(
                                post_unlink_ab.ptrs@, orig_block_ptr, 0);
                        } else {
                            // Both: first remove next (idx block_i+1), then orig (idx block_i)
                            let ghost inter = remove_ghost_pointer(
                                post_unlink_ab.ptrs@, next_phys_block);
                            lemma_remove_ghost_pointer_index_map(
                                post_unlink_ab.ptrs@, next_phys_block, 0);
                            // inter[0] == post_unlink_ab.ptrs@[0]
                            lemma_remove_ghost_pointer_index_map(
                                inter, orig_block_ptr, 0);
                            // new_ptrs[0] == inter[0]
                        }
                    };
                    // Show last element preserved
                    assert(new_ptrs.last() == post_unlink_ab.ptrs@.last()) by {
                        let ghost old_last_idx = post_unlink_ab.ptrs@.len() as int - 1;
                        if coalesced_with_next && !coalesced_with_prev {
                            let ghost rm_idx = block_i + 1;
                            let ghost res = remove_ghost_pointer(
                                post_unlink_ab.ptrs@, next_phys_block);
                            assert(rm_idx < old_last_idx) by {
                                // next is not sentinel (it's free)
                                post_unlink_ab.lemma_wf_glue_facts(block_i + 1);
                                post_unlink_ab.lemma_wf_glue_facts(old_last_idx);
                            };
                            lemma_remove_ghost_pointer_index_map(
                                post_unlink_ab.ptrs@, next_phys_block,
                                res.len() as int - 1);
                        } else if !coalesced_with_next && coalesced_with_prev {
                            let ghost rm_idx = block_i;
                            let ghost res = remove_ghost_pointer(
                                post_unlink_ab.ptrs@, orig_block_ptr);
                            assert(rm_idx < old_last_idx) by {
                                post_unlink_ab.lemma_wf_glue_facts(old_last_idx);
                                // sentinel is at last index; orig is not sentinel
                            };
                            lemma_remove_ghost_pointer_index_map(
                                post_unlink_ab.ptrs@, orig_block_ptr,
                                res.len() as int - 1);
                        } else {
                            // Both removals
                            let ghost inter = remove_ghost_pointer(
                                post_unlink_ab.ptrs@, next_phys_block);
                            // next at block_i+1, sentinel at old_last_idx
                            assert(block_i + 1 < old_last_idx) by {
                                post_unlink_ab.lemma_wf_glue_facts(block_i + 1);
                                post_unlink_ab.lemma_wf_glue_facts(old_last_idx);
                            };
                            lemma_remove_ghost_pointer_index_map(
                                post_unlink_ab.ptrs@, next_phys_block,
                                inter.len() as int - 1);
                            // inter.last() == post_unlink.last()
                            // Then remove orig from inter
                            lemma_remove_ghost_pointer_index_map(
                                inter, orig_block_ptr,
                                new_ptrs.len() as int - 1);
                        }
                    };
                    AllBlocks::<FLLEN, SLLEN>::lemma_pool_size_bounded_from_sub(
                        &post_unlink_ab, &self.all_blocks);
                }
            };
            self.all_blocks.lemma_wf_from_nodes();

            // --- ptrs@ non-containment for removed blocks ---
            // (needed by B3 proof below)
            if coalesced_with_next {
                lemma_remove_ghost_pointer_ensures(old_ptrs, next_phys_block);
                assert(!remove_ghost_pointer(old_ptrs, next_phys_block)
                    .contains(next_phys_block));
                if coalesced_with_prev {
                    let ghost inter = remove_ghost_pointer(old_ptrs, next_phys_block);
                    if self.all_blocks.ptrs@.contains(next_phys_block) {
                        lemma_remove_ghost_pointer_contains_reverse(
                            inter, orig_block_ptr, next_phys_block);
                    }
                }
                assert(!self.all_blocks.ptrs@.contains(next_phys_block));
            }
            if coalesced_with_prev {
                if coalesced_with_next {
                    let ghost inter = remove_ghost_pointer(old_ptrs, next_phys_block);
                    lemma_remove_ghost_pointer_ensures(inter, orig_block_ptr);
                } else {
                    lemma_remove_ghost_pointer_ensures(old_ptrs, orig_block_ptr);
                }
                assert(!self.all_blocks.ptrs@.contains(orig_block_ptr));
            }

            // --- all_freelist_wf_weak(set![block]) ---
            // Proved from post-unlink captures + perms preservation + sfl.m unchanged.

            // B1: wf_shadow()
            assert(self.wf_shadow()) by {
                // shadow_freelist_has_all_wf_index: m unchanged
                assert(self.shadow_freelist@.shadow_freelist_has_all_wf_index()) by {
                    assert(self.shadow_freelist@.m == post_unlink_sfl.m);
                    assert(post_unlink_sfl.shadow_freelist_has_all_wf_index());
                };
                // shadow_ptrs_nonnull: m unchanged, captured after unlinking
                assert(self.shadow_ptrs_nonnull()) by {
                    reveal(Tlsf::shadow_ptrs_nonnull);
                    assert(self.shadow_freelist@.m == post_unlink_sfl.m);
                };
                // is_identity_injection: maintained by ii_shift_after_remove
                assert(is_identity_injection(
                    self.shadow_freelist@, self.all_blocks.ptrs@));
            };

            // B2: freelist_wf for all indices
            // Pre-establish ptrs@ non-containment for sfl node distinctness
            assert(!post_unlink_sfl.contains(block)) by {
                assert(block_not_in_sfl);
            };

            assert forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf()
                implies self.freelist_wf(idx) by {
                // Prove wf_free_node(idx, n) for each entry using preserve lemma
                assert forall|n: int|
                    0 <= n < self.shadow_freelist@.m[idx].len()
                    implies self.wf_free_node(idx, n) by {
                    let node = self.shadow_freelist@.m[idx][n];
                    // sfl.m unchanged
                    assert(self.shadow_freelist@.m[idx] == post_unlink_sfl.m[idx]);
                    assert(node == post_unlink_sfl.m[idx][n]);

                    // node != block, nnpb, orig, next → perms preserved
                    assert(node != block) by {
                        if node == block {
                            assert(post_unlink_sfl.m[idx].contains(block));
                            assert(post_unlink_sfl.contains(block));
                            assert(block_not_in_sfl);
                            assert(false);
                        }
                    };
                    assert(node != new_next_phys_block) by {
                        if node == new_next_phys_block {
                            // post_unlink_tlsf.wf_free_node gives is_free for node
                            post_unlink_tlsf.lemma_all_freelist_wf_weak_extract_wf_free_node(
                                idx, n, post_unlink_exceptions);
                            assert(post_unlink_perms[node].points_to.value().is_free());
                            assert(!post_unlink_perms[new_next_phys_block]
                                .points_to.value().is_free());
                            assert(false);
                        }
                    };
                    assert(node != orig_block_ptr) by {
                        if coalesced_with_prev {
                            assert(orig_not_in_sfl);
                            assert(!post_unlink_sfl.contains(orig_block_ptr));
                            if node == orig_block_ptr {
                                assert(post_unlink_sfl.m[idx].contains(orig_block_ptr));
                                assert(post_unlink_sfl.contains(orig_block_ptr));
                                assert(false);
                            }
                        } else {
                            assert(orig_block_ptr == block);
                        }
                    };
                    assert(node != next_phys_block) by {
                        if coalesced_with_next {
                            assert(next_not_in_sfl);
                            assert(!post_unlink_sfl.contains(next_phys_block));
                            if node == next_phys_block {
                                assert(post_unlink_sfl.m[idx].contains(next_phys_block));
                                assert(post_unlink_sfl.contains(next_phys_block));
                                assert(false);
                            }
                        }
                    };

                    // perms preserved for this node
                    assert(self.all_blocks.perms@[node] == post_unlink_perms[node]);
                    // sfl.m[idx] unchanged
                    assert(post_unlink_tlsf.shadow_freelist@.m[idx]
                        == self.shadow_freelist@.m[idx]);
                    // post_unlink_tlsf had wf_free_node(idx, n) from all_freelist_wf_weak
                    post_unlink_tlsf.lemma_all_freelist_wf_weak_extract_wf_free_node(
                        idx, n, post_unlink_exceptions);
                    // is_ii holds for current self
                    assert(self.is_ii());
                    // Transfer wf_free_node from post_unlink_tlsf to self
                    post_unlink_tlsf.lemma_wf_free_node_preserve_if_not_touched(
                        *self, idx, n);
                };

                // first_free conditions (captured after unlinking, first_free unchanged)
                assert(self.shadow_freelist@.m[idx] == post_unlink_sfl.m[idx]);
                self.lemma_freelist_wf_from_addr_conditions(idx);
            };

            // B3: free_blocks_in_freelist_except(set![block])
            assert(self.free_blocks_in_freelist_except(set![block])) by {
                reveal(Tlsf::free_blocks_in_freelist_except);
                assert forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                    && self.all_blocks.value_at(self.all_blocks.ptrs@[i]).is_free()
                    && !set![block].contains(self.all_blocks.ptrs@[i])
                    implies self.shadow_freelist@.contains(
                        self.all_blocks.ptrs@[i]) by {
                    let ptr = self.all_blocks.ptrs@[i];
                    // ptr != block (from !set![block].contains)
                    // ptr != nnpb (nnpb not free, ptr is free)
                    assert(ptr != new_next_phys_block) by {
                        if ptr == new_next_phys_block {
                            // nnpb is not free in current state
                            assert(nnpb_not_free);
                            assert(false);
                        }
                    };
                    // ptr != orig (removed from ptrs@ if coalesced_with_prev)
                    if coalesced_with_prev {
                        assert(!self.all_blocks.ptrs@.contains(orig_block_ptr));
                    } else {
                        assert(orig_block_ptr == block);
                    }
                    assert(ptr != orig_block_ptr);
                    // ptr != next (removed from ptrs@ if coalesced_with_next)
                    if coalesced_with_next {
                        assert(!self.all_blocks.ptrs@.contains(next_phys_block));
                    }
                    assert(ptr != next_phys_block);
                    // perms preserved → is_free same as post-unlink
                    assert(self.all_blocks.perms@[ptr]
                        == post_unlink_perms[ptr]);
                    assert(post_unlink_perms[ptr]
                        .points_to.value().is_free());
                    // ptr in post_unlink ptrs@: survived removal
                    // Use index mapping to find old index
                    assert(post_unlink_ab.ptrs@.contains(ptr)) by {
                        // current ptrs@ is subset of post_unlink ptrs@
                        // ptr is in current ptrs@ at index i
                        // Map i back: removals only removed next and/or orig
                        if !coalesced_with_next && !coalesced_with_prev {
                            assert(self.all_blocks.ptrs@ == post_unlink_ab.ptrs@);
                        } else if coalesced_with_next && !coalesced_with_prev {
                            lemma_remove_ghost_pointer_contains_reverse(
                                post_unlink_ab.ptrs@,
                                next_phys_block, ptr);
                        } else if !coalesced_with_next && coalesced_with_prev {
                            lemma_remove_ghost_pointer_contains_reverse(
                                post_unlink_ab.ptrs@,
                                orig_block_ptr, ptr);
                        } else {
                            // both: ptrs@ = remove(remove(old, next), orig)
                            let ghost inter = remove_ghost_pointer(
                                post_unlink_ab.ptrs@, next_phys_block);
                            lemma_remove_ghost_pointer_contains_reverse(
                                inter, orig_block_ptr, ptr);
                            lemma_remove_ghost_pointer_contains_reverse(
                                post_unlink_ab.ptrs@,
                                next_phys_block, ptr);
                        }
                    };
                    // ptr not in post_unlink_exceptions
                    assert(!post_unlink_exceptions.contains(ptr)) by {
                        // exceptions ⊆ {next_phys_block, block}
                        // ptr != next (proved above)
                        // ptr != block (from !set![block].contains)
                    };
                    // From B3 capture: post_unlink_sfl.contains(ptr)
                    assert(post_unlink_sfl.contains(ptr));
                    // sfl.m unchanged → current sfl.contains(ptr)
                    assert(self.shadow_freelist@.m == post_unlink_sfl.m);
                    assert(self.shadow_freelist@.contains(ptr));
                };
            };

            assert(self.all_freelist_wf_weak(set![block]));

            // --- shadow_freelist.m unchanged since unlinking (only pi shifted) ---
            assert(self.shadow_freelist@.m == post_unlink_sfl.m);

            // --- size_class_condition preserved ---
            // For each freelist node n:
            //   - n != block, orig, next (from !post_unlink_sfl.contains + wf index)
            //   - perms@[n].size == post_unlink_perms[n].size (unchanged or nnpb size preserved)
            assert(self.size_class_condition()) by {
                reveal(Tlsf::size_class_condition);
                assert forall |bi: BlockIndex<FLLEN, SLLEN>, k: int|
                    self.shadow_freelist@.m.contains_key(bi)
                        && 0 <= k < self.shadow_freelist@.m[bi].len()
                    implies
                        bi == Self::map_floor_spec(
                            self.all_blocks.perms@[
                                #[trigger] self.shadow_freelist@.m[bi][k]
                            ].points_to.value().size as usize)
                        && bi.block_size_range().contains(
                            self.all_blocks.perms@[
                                self.shadow_freelist@.m[bi][k]
                            ].points_to.value().size as int)
                by {
                    let n = self.shadow_freelist@.m[bi][k];
                    // bi.wf() from shadow_freelist_has_all_wf_index
                    assert(bi.wf()) by {
                        assert(post_unlink_sfl.shadow_freelist_has_all_wf_index());
                    };
                    // n == post_unlink_sfl.m[bi][k] (shadow_freelist unchanged)
                    assert(n == post_unlink_sfl.m[bi][k]);
                    // n != block: from !post_unlink_sfl.contains(block) + bi.wf()
                    assert(!post_unlink_sfl.m[bi].contains(block)) by {
                        if post_unlink_sfl.m[bi].contains(block) {
                            assert(post_unlink_sfl.contains(block));
                        }
                    };
                    assert(n != block);
                    // Use wf_free_node to get all_blocks.contains(n), i.e. ptrs@.contains(n)
                    // orig and next were removed from ptrs@ during ghost update
                    self.lemma_all_freelist_wf_weak_extract_wf_free_node(
                        bi, k, set![block]);
                    assert(self.all_blocks.ptrs@.contains(n));
                    // n != orig_block_ptr: orig removed from ptrs@ if coalesced_with_prev
                    if coalesced_with_prev {
                        assert(!self.all_blocks.ptrs@.contains(orig_block_ptr));
                    } else {
                        assert(orig_block_ptr == block);
                    }
                    assert(n != orig_block_ptr);
                    // n != next_phys_block: next removed from ptrs@ if coalesced_with_next
                    if coalesced_with_next {
                        assert(!self.all_blocks.ptrs@.contains(next_phys_block));
                        assert(n != next_phys_block);
                    }
                    // n's perms size is preserved from post_unlink_perms
                    if n == new_next_phys_block {
                        // nnpb: only prev_phys_block changed, size preserved
                        assert(self.all_blocks.perms@[n].points_to.value().size
                            == post_unlink_perms[n].points_to.value().size);
                    } else {
                        // Other nodes: perms@ unchanged through header writes and ghost update
                        assert(self.all_blocks.perms@[n] == post_unlink_perms[n]);
                    }
                };
            };

            // --- !shadow_freelist.contains(block) ---
            assert(!self.shadow_freelist@.contains(block)) by {
                // sfl.m == post_unlink_sfl.m, and contains only depends on m
                assert(self.shadow_freelist@.m == post_unlink_sfl.m);
                if self.shadow_freelist@.contains(block) {
                    let bi0: BlockIndex<FLLEN, SLLEN> = choose|bi: BlockIndex<FLLEN, SLLEN>|
                        bi.wf() && self.shadow_freelist@.m[bi].contains(block);
                    assert(post_unlink_sfl.m[bi0].contains(block));
                    assert(post_unlink_sfl.contains(block));
                    assert(false);
                }
            };

            // --- all_blocks.contains(block) ---
            // block is in the new ptrs@ (it was not removed — only next and orig were removed)
            assert(self.all_blocks.ptrs@.contains(block)) by {
                if coalesced_with_prev {
                    // block = prev at old index block_i - 1.
                    // Removals were next (block_i + 1) and orig (block_i).
                    // block_i - 1 < block_i, so block is preserved.
                    assert(block != next_phys_block) by {
                        lemma_ptrs_no_duplicates_index_neq(
                            old_ptrs, block_i - 1, block_i + 1);
                    };
                    assert(block != orig_block_ptr) by {
                        lemma_ptrs_no_duplicates_index_neq(
                            old_ptrs, block_i - 1, block_i);
                    };
                    if coalesced_with_next {
                        lemma_remove_ghost_pointer_contains_old(
                            old_ptrs, next_phys_block, block);
                        let ghost inter = remove_ghost_pointer(old_ptrs, next_phys_block);
                        lemma_ptrs_no_duplicates_preserved_by_remove(
                            old_ptrs, next_phys_block);
                        lemma_remove_ghost_pointer_contains_old(
                            inter, orig_block_ptr, block);
                    } else {
                        // Only orig was removed (no next coalesce)
                        // Actually, if no next coalesce, only prev was unlinked, no ptrs removal for next
                        // ptrs@ removals: only orig_block_ptr (if coalesced_with_prev)
                        assert(old_ptrs.contains(block));
                        lemma_remove_ghost_pointer_contains_old(
                            old_ptrs, orig_block_ptr, block);
                    }
                } else {
                    // block = orig. It was not removed from ptrs@.
                    // Removals: only next (if coalesced_with_next)
                    if coalesced_with_next {
                        assert(block != next_phys_block) by {
                            lemma_ptrs_no_duplicates_index_neq(
                                old_ptrs, block_i, block_i + 1);
                        };
                        lemma_remove_ghost_pointer_contains_old(
                            old_ptrs, next_phys_block, block);
                    }
                    // If no coalescing at all, ptrs@ is unchanged
                }
            };
            assert(self.all_blocks.contains(block));
        }

        self.link_free_block(size, block);
    }


    /// Ownership/containment conditions for deallocation
    pub closed spec fn wf_dealloc_base(&self, tok: DeallocToken) -> bool {
        let block_ptr = self.user_block_map@[tok.ptr];
        &&& self.user_block_map@.contains_key(tok.ptr)
        &&& self.all_blocks.contains(block_ptr)
        &&& self.all_blocks.perms@.contains_key(block_ptr)
        &&& !self.all_blocks.perms@[block_ptr].points_to.value().is_free()
        &&& tok.ptr@.provenance == block_ptr@.provenance
    }

    /// Memory layout for aligned allocation (align >= GRANULARITY)
    pub closed spec fn wf_dealloc_granularity_aligned(&self, tok: DeallocToken) -> bool {
        let block_ptr = self.user_block_map@[tok.ptr];
        let bp = self.all_blocks.perms@[block_ptr];
        let phys_size = (bp.points_to.value().size & SPEC_SIZE_SIZE_MASK) as int;
        let BH = size_of::<BlockHdr>() as int;
        let pad_size = vstd::layout::size_of::<UsedBlockPad>() as int;
        &&& tok.user_size > 0
        &&& tok.ptr@.addr >= block_ptr@.addr + BH + pad_size
        &&& tok.ptr@.addr + tok.user_size <= block_ptr@.addr + phys_size
        // bp.mem: tail region [ptr+user_size, block+phys_size)
        &&& bp.mem.provenance() == block_ptr@.provenance
        &&& bp.mem.is_range(tok.ptr@.addr + tok.user_size,
                block_ptr@.addr + phys_size - tok.ptr@.addr - tok.user_size)
        // overhead_mem: gap [block+BH, ptr-pad_size)
        &&& bp.overhead_mem.provenance() == block_ptr@.provenance
        &&& bp.overhead_mem.is_range(block_ptr@.addr + BH,
                tok.ptr@.addr - pad_size - block_ptr@.addr - BH)
        // pad_perm: UsedBlockPad at [ptr-pad_size, ptr)
        &&& bp.pad_perm matches Some(pp)
        &&& pp.is_init()
        &&& pp.value().block_hdr == block_ptr
        &&& pp.ptr()@.provenance == tok.ptr@.provenance
        &&& pp.ptr()@.addr == tok.ptr@.addr - pad_size
    }

    /// Memory layout for unaligned allocation (align < GRANULARITY)
    pub closed spec fn wf_dealloc_granularity_unaligned(&self, tok: DeallocToken) -> bool {
        let block_ptr = self.user_block_map@[tok.ptr];
        let bp = self.all_blocks.perms@[block_ptr];
        let phys_size = (bp.points_to.value().size & SPEC_SIZE_SIZE_MASK) as int;
        let BH = size_of::<BlockHdr>() as int;
        &&& tok.user_size > 0
        &&& tok.ptr@.addr + tok.user_size <= block_ptr@.addr + phys_size
        &&& block_ptr@.addr == tok.ptr@.addr - (GRANULARITY / 2) as int
        // bp.mem: tail region [ptr+user_size, block+phys_size)
        &&& bp.mem.provenance() == block_ptr@.provenance
        &&& bp.mem.is_range(tok.ptr@.addr + tok.user_size,
                block_ptr@.addr + phys_size - tok.ptr@.addr - tok.user_size)
        // overhead_mem/pad_perm: empty
        &&& bp.overhead_mem.dom().is_empty()
        &&& bp.pad_perm is None
    }

    /// Validity of blocks being deallocated
    pub closed spec fn wf_dealloc(&self, tok: DeallocToken) -> bool {
        &&& self.wf_dealloc_base(tok)
        &&& tok.align >= GRANULARITY ==> self.wf_dealloc_granularity_aligned(tok)
        &&& tok.align < GRANULARITY ==> self.wf_dealloc_granularity_unaligned(tok)
    }

    // --- Bridge lemmas (called from allocate) ---

    pub(crate) proof fn lemma_establish_wf_dealloc_base(&self, tok: DeallocToken)
        requires
            self.user_block_map@.contains_key(tok.ptr),
            self.all_blocks.contains(self.user_block_map@[tok.ptr]),
            self.all_blocks.perms@.contains_key(self.user_block_map@[tok.ptr]),
            !self.all_blocks.perms@[self.user_block_map@[tok.ptr]].points_to.value().is_free(),
            tok.ptr@.provenance == self.user_block_map@[tok.ptr]@.provenance,
        ensures
            self.wf_dealloc_base(tok),
    {}

    pub(crate) proof fn lemma_establish_wf_dealloc_granularity_aligned(&self, tok: DeallocToken)
        requires
            self.user_block_map@.contains_key(tok.ptr),
            self.all_blocks.perms@.contains_key(self.user_block_map@[tok.ptr]),
            ({
                let block_ptr = self.user_block_map@[tok.ptr];
                let bp = self.all_blocks.perms@[block_ptr];
                let phys_size = (bp.points_to.value().size & SPEC_SIZE_SIZE_MASK) as int;
                let BH = size_of::<BlockHdr>() as int;
                let pad_size = vstd::layout::size_of::<UsedBlockPad>() as int;
                &&& tok.user_size > 0
                &&& tok.ptr@.addr >= block_ptr@.addr + BH + pad_size
                &&& tok.ptr@.addr + tok.user_size <= block_ptr@.addr + phys_size
                &&& bp.mem.provenance() == block_ptr@.provenance
                &&& bp.mem.is_range(tok.ptr@.addr + tok.user_size,
                        block_ptr@.addr + phys_size - tok.ptr@.addr - tok.user_size)
                &&& bp.overhead_mem.provenance() == block_ptr@.provenance
                &&& bp.overhead_mem.is_range(block_ptr@.addr + BH,
                        tok.ptr@.addr - pad_size - block_ptr@.addr - BH)
                &&& bp.pad_perm matches Some(pp)
                &&& pp.is_init()
                &&& pp.value().block_hdr == block_ptr
                &&& pp.ptr()@.provenance == tok.ptr@.provenance
                &&& pp.ptr()@.addr == tok.ptr@.addr - pad_size
            }),
        ensures
            self.wf_dealloc_granularity_aligned(tok),
    {}

    pub(crate) proof fn lemma_establish_wf_dealloc_granularity_unaligned(&self, tok: DeallocToken)
        requires
            self.user_block_map@.contains_key(tok.ptr),
            self.all_blocks.perms@.contains_key(self.user_block_map@[tok.ptr]),
            ({
                let block_ptr = self.user_block_map@[tok.ptr];
                let bp = self.all_blocks.perms@[block_ptr];
                let phys_size = (bp.points_to.value().size & SPEC_SIZE_SIZE_MASK) as int;
                let BH = size_of::<BlockHdr>() as int;
                &&& tok.user_size > 0
                &&& tok.ptr@.addr + tok.user_size <= block_ptr@.addr + phys_size
                &&& block_ptr@.addr == tok.ptr@.addr - (GRANULARITY / 2) as int
                &&& bp.mem.provenance() == block_ptr@.provenance
                &&& bp.mem.is_range(tok.ptr@.addr + tok.user_size,
                        block_ptr@.addr + phys_size - tok.ptr@.addr - tok.user_size)
                &&& bp.overhead_mem.dom().is_empty()
                &&& bp.pad_perm is None
            }),
        ensures
            self.wf_dealloc_granularity_unaligned(tok),
    {}

    pub(crate) proof fn lemma_establish_wf_dealloc(&self, tok: DeallocToken)
        requires
            self.wf_dealloc_base(tok),
            tok.align >= GRANULARITY ==> self.wf_dealloc_granularity_aligned(tok),
            tok.align < GRANULARITY ==> self.wf_dealloc_granularity_unaligned(tok),
        ensures
            self.wf_dealloc(tok),
    {}

    // --- Elimination lemmas (called from used_block_hdr_for_allocation) ---

    pub(crate) proof fn lemma_wf_dealloc_implies_base(&self, tok: DeallocToken)
        requires self.wf_dealloc(tok)
        ensures ({
            let block_ptr = self.user_block_map@[tok.ptr];
            &&& self.user_block_map@.contains_key(tok.ptr)
            &&& self.all_blocks.contains(block_ptr)
            &&& self.all_blocks.perms@.contains_key(block_ptr)
            &&& !self.all_blocks.perms@[block_ptr].points_to.value().is_free()
            &&& tok.ptr@.provenance == block_ptr@.provenance
        })
    {}

    pub(crate) proof fn lemma_wf_dealloc_implies_aligned(&self, tok: DeallocToken)
        requires self.wf_dealloc(tok), tok.align >= GRANULARITY
        ensures ({
            let block_ptr = self.user_block_map@[tok.ptr];
            let bp = self.all_blocks.perms@[block_ptr];
            let phys_size = (bp.points_to.value().size & SPEC_SIZE_SIZE_MASK) as int;
            let BH = size_of::<BlockHdr>() as int;
            let pad_size = vstd::layout::size_of::<UsedBlockPad>() as int;
            &&& tok.user_size > 0
            &&& tok.ptr@.addr >= block_ptr@.addr + BH + pad_size
            &&& tok.ptr@.addr + tok.user_size <= block_ptr@.addr + phys_size
            &&& bp.mem.provenance() == block_ptr@.provenance
            &&& bp.mem.is_range(tok.ptr@.addr + tok.user_size,
                    block_ptr@.addr + phys_size - tok.ptr@.addr - tok.user_size)
            &&& bp.overhead_mem.provenance() == block_ptr@.provenance
            &&& bp.overhead_mem.is_range(block_ptr@.addr + BH,
                    tok.ptr@.addr - pad_size - block_ptr@.addr - BH)
            &&& bp.pad_perm matches Some(pp)
            &&& pp.is_init()
            &&& pp.value().block_hdr == block_ptr
            &&& pp.ptr()@.provenance == tok.ptr@.provenance
            &&& pp.ptr()@.addr == tok.ptr@.addr - pad_size
        })
    {}

    pub(crate) proof fn lemma_wf_dealloc_implies_unaligned(&self, tok: DeallocToken)
        requires self.wf_dealloc(tok), tok.align < GRANULARITY
        ensures ({
            let block_ptr = self.user_block_map@[tok.ptr];
            let bp = self.all_blocks.perms@[block_ptr];
            let phys_size = (bp.points_to.value().size & SPEC_SIZE_SIZE_MASK) as int;
            let BH = size_of::<BlockHdr>() as int;
            &&& tok.user_size > 0
            &&& tok.ptr@.addr + tok.user_size <= block_ptr@.addr + phys_size
            &&& block_ptr@.addr == tok.ptr@.addr - (GRANULARITY / 2) as int
            &&& bp.mem.provenance() == block_ptr@.provenance
            &&& bp.mem.is_range(tok.ptr@.addr + tok.user_size,
                    block_ptr@.addr + phys_size - tok.ptr@.addr - tok.user_size)
            &&& bp.overhead_mem.dom().is_empty()
            &&& bp.pad_perm is None
        })
    {}

    #[inline]
    unsafe fn used_block_hdr_for_allocation(
        &mut self,
        ptr: *mut u8,
        align: usize,
        Tracked(user_mem): Tracked<PointsToRaw>,
        Ghost(block_ptr): Ghost<*mut BlockHdr>,
        Ghost(user_size): Ghost<int>,
    ) -> (r: *mut UsedBlockHdr)
    requires
        old(self).wf(),
        old(self).wf_dealloc(DeallocToken { ptr, user_size, align }),
        block_ptr == old(self).user_block_map@[ptr],
        user_mem.is_range(ptr as int, user_size),
        user_mem.provenance() == ptr@.provenance,
    ensures
        self.all_blocks.wf(),
        self.all_freelist_wf(),
        self.bitmap_sync(),
        self.bitmap_wf(),
        self.size_class_condition(),
        self.all_blocks.contains(r),
        self.all_blocks.perms@.contains_key(r),
        self.all_blocks.perms@[r].points_to.is_init(),
        self.all_blocks.perms@[r].points_to.ptr() == r,
        self.all_blocks.perms@[r].points_to.value().size & SIZE_USED != 0,
        // mem covers full payload [r+BH, r+phys_size) (user_mem joined back)
        self.all_blocks.perms@[r].mem.is_range(
            r as int + size_of::<BlockHdr>() as int,
            (self.all_blocks.perms@[r].points_to.value().size & SIZE_SIZE_MASK) as int
                - size_of::<BlockHdr>() as int),
        self.all_blocks.perms@[r].mem.provenance() == r@.provenance,
        self.all_blocks.perms@[r].overhead_mem.dom().is_empty(),
        self.all_blocks.perms@[r].pad_perm is None,
    {
        let ghost tok = DeallocToken { ptr, user_size, align };
        let ghost old_self = *self;
        proof {
            self.lemma_wf_components();
            self.lemma_wf_dealloc_implies_base(tok);
        }
        if align >= GRANULARITY {
            proof {
                self.lemma_wf_dealloc_implies_aligned(tok);
            }
            let ghost old_ab = self.all_blocks;
            let ghost block = block_ptr;
            let tracked mut bp = self.all_blocks.perms.borrow_mut().tracked_remove(block);
            proof {
                // bp == old_ab.perms@[block_ptr]
                // Establish bp.points_to.is_init() from old_ab.wf()
                let ghost bi = old_ab.get_ptr_internal_index(block);
                old_ab.lemma_wf_extract_node(bi);
                assert(old_ab.perms@[block].wf());
                assert(bp.points_to.is_init());
                assert(bp.points_to.ptr() == block);
            }
            let tracked pad_perm = bp.pad_perm.tracked_unwrap();
            let pad_ptr = UsedBlockPad::get_for_allocation(ptr);
            let block = ptr_ref(pad_ptr, Tracked(&pad_perm)).block_hdr;
            proof {
                let ghost phys_size = (bp.points_to.value().size & SPEC_SIZE_SIZE_MASK) as int;
                let ghost BH = size_of::<BlockHdr>() as int;
                let ghost pad_size = vstd::layout::size_of::<UsedBlockPad>() as int;

                // block read from pad == block_ptr
                assert(block == block_ptr);

                pad_perm.leak_contents();
                let tracked pad_raw = pad_perm.into_raw();

                // Provenance facts
                assert(pad_raw.provenance() == block@.provenance) by {
                    assert(ptr@.provenance == block@.provenance);
                };
                assert(user_mem.provenance() == block@.provenance) by {
                    assert(user_mem.provenance() == ptr@.provenance);
                    assert(ptr@.provenance == block@.provenance);
                };

                // Join ordering: block+BH <= ptr-pad_size (from spec: ptr >= block+BH+pad_size)
                assert(block as int + BH <= ptr as int - pad_size);

                // Join 1: overhead_mem [block+BH, ptr-pad_size) + pad_raw [ptr-pad_size, ptr)
                let tracked j1 = Self::lemma_join_adjacent_ranges_is_range(
                    bp.overhead_mem, pad_raw,
                    block as int + BH,
                    ptr as int - pad_size,
                    ptr as int);

                // Join 2: j1 [block+BH, ptr) + user_mem [ptr, ptr+user_size)
                let tracked j2 = Self::lemma_join_adjacent_ranges_is_range(
                    j1, user_mem,
                    block as int + BH,
                    ptr as int,
                    ptr as int + user_size);

                // Join 3: j2 [block+BH, ptr+user_size) + bp.mem [ptr+user_size, block+phys_size)
                let tracked j3 = Self::lemma_join_adjacent_ranges_is_range(
                    j2, bp.mem,
                    block as int + BH,
                    ptr as int + user_size,
                    block as int + phys_size);

                bp.mem = j3;
                bp.pad_perm = None;
                bp.overhead_mem = PointsToRaw::empty(block@.provenance);

                assert(bp.wf()) by {
                    assert(!bp.points_to.value().is_free());
                    assert(bp.mem.provenance() == block@.provenance);
                    assert(bp.points_to.ptr() == block);
                    assert(bp.mem.provenance() == bp.points_to.ptr()@.provenance);
                };
            }
            proof { self.all_blocks.perms.borrow_mut().tracked_insert(block, bp); }
            proof {
                let ghost bi = old_ab.get_ptr_internal_index(block);

                // Prove perms@ extensional equality: remove(block).insert(block,bp) == old.insert(block,bp)
                assert(self.all_blocks.perms@ =~= old_ab.perms@.insert(block, bp)) by {
                    assert forall |p: *mut BlockHdr|
                        self.all_blocks.perms@.dom().contains(p)
                            == old_ab.perms@.insert(block, bp).dom().contains(p)
                    by {};
                    assert forall |p: *mut BlockHdr|
                        self.all_blocks.perms@.dom().contains(p)
                            implies #[trigger] self.all_blocks.perms@[p]
                                == old_ab.perms@.insert(block, bp)[p]
                    by {
                        if p == block {
                        } else {
                            assert(self.all_blocks.perms@[p] == old_ab.perms@.remove(block)[p]);
                            assert(old_ab.perms@.remove(block)[p] == old_ab.perms@[p]);
                        }
                    };
                };

                // Prove all_blocks.wf() via replace lemma
                old_ab.lemma_wf_extract_node(bi);
                old_ab.lemma_wf_glue_facts(bi);
                old_ab.lemma_wf_structural_facts(bi);

                assert(self.all_blocks.value_at(block) == old_ab.value_at(block));
                assert(self.all_blocks.phys_prev_of(bi) == old_ab.phys_prev_of(bi));
                assert(self.all_blocks.phys_next_of(bi) == old_ab.phys_next_of(bi));
                assert(!self.all_blocks.value_at(block).is_free());

                assert(self.all_blocks.value_at(block).prev_phys_block@.addr != 0 ==> (
                    self.all_blocks.phys_prev_of(bi) matches Some(p)
                        && p == self.all_blocks.value_at(block).prev_phys_block));
                assert(self.all_blocks.value_at(block).prev_phys_block@.addr == 0
                    ==> self.all_blocks.phys_prev_of(bi) is None);
                assert(self.all_blocks.phys_next_of(bi) matches Some(next_ptr) ==>
                    AllBlocks::<FLLEN, SLLEN>::phys_next_matches(
                        next_ptr, block, self.all_blocks.value_at(block).size));

                self.all_blocks.lemma_construct_wf_node_glue(bi);
                self.all_blocks.lemma_construct_wf_node_structural(bi);

                AllBlocks::<FLLEN, SLLEN>::lemma_replace_block_perm_from_wf(
                    old_ab, self.all_blocks, block, bp);

                // Frame: all_freelist_wf, size_class_condition, bitmap preserved
                assert(self.wf_shadow()) by {
                    assert(old_self.wf_shadow());
                    assert(self.shadow_freelist == old_self.shadow_freelist);
                    Self::lemma_shadow_ptrs_nonnull_frame(old_self, *self);
                    assert(self.all_blocks.ptrs@ == old_self.all_blocks.ptrs@);
                };
                assert forall|bi2: BlockIndex<FLLEN, SLLEN>, n: int|
                    bi2.wf() && 0 <= n < old_self.shadow_freelist@.m[bi2].len()
                    implies #[trigger] self.all_blocks.perms@[old_self.shadow_freelist@.m[bi2][n]]
                        == old_self.all_blocks.perms@[old_self.shadow_freelist@.m[bi2][n]]
                by {
                    let node = old_self.shadow_freelist@.m[bi2][n];
                    if node == block {
                        old_self.wf_index_in_freelist(bi2);
                        old_self.lemma_freelist_wf_extract_wf_free_node(bi2, n);
                        assert(old_self.all_blocks.value_at(node).is_free());
                        assert(!old_self.all_blocks.perms@[block].points_to.value().is_free());
                        assert(false);
                    }
                    // node != block: perms unchanged
                };
                Self::lemma_all_freelist_wf_perms_frame(old_self, *self);
                // free_blocks_in_freelist: points_to unchanged for all ptrs@ entries
                assert(self.free_blocks_in_freelist()) by {
                    assert(old_self.free_blocks_in_freelist());
                    Self::lemma_free_blocks_in_freelist_except_perms_frame(old_self, *self, Set::empty());
                };
                // size_class_condition via frame lemma
                assert(!old_self.shadow_freelist@.contains(block)) by {
                    if old_self.shadow_freelist@.contains(block) {
                        let bi3 = choose|bi3: BlockIndex<FLLEN, SLLEN>| bi3.wf()
                            && old_self.shadow_freelist@.m[bi3].contains(block);
                        let n2 = choose|n2: int| 0 <= n2 < old_self.shadow_freelist@.m[bi3].len()
                            && old_self.shadow_freelist@.m[bi3][n2] == block;
                        old_self.wf_index_in_freelist(bi3);
                        old_self.lemma_freelist_wf_extract_wf_free_node(bi3, n2);
                        assert(old_self.all_blocks.value_at(block).is_free());
                        assert(!old_self.all_blocks.perms@[block].points_to.value().is_free());
                        assert(false);
                    }
                };
                assert(Self::perms_size_unchanged_for_freelist(
                    old_self.shadow_freelist@, old_self.all_blocks, self.all_blocks, block)) by {
                    reveal(Tlsf::perms_size_unchanged_for_freelist);
                    assert forall|bi3: BlockIndex<FLLEN, SLLEN>, i2: int|
                        bi3.wf() && 0 <= i2 < old_self.shadow_freelist@.m[bi3].len()
                            && old_self.shadow_freelist@.m[bi3][i2] != block
                        implies self.all_blocks.perms@[old_self.shadow_freelist@.m[bi3][i2]].points_to.value().size
                            == old_self.all_blocks.perms@[old_self.shadow_freelist@.m[bi3][i2]].points_to.value().size
                    by {
                        let node = old_self.shadow_freelist@.m[bi3][i2];
                        assert(self.all_blocks.perms@[node] == old_self.all_blocks.perms@[node]);
                    };
                };
                Self::lemma_size_class_perm_change_preserved(old_self, *self, block);
            }
            block
        } else {
            proof {
                self.lemma_wf_dealloc_implies_unaligned(tok);
            }
            let ghost old_ab = self.all_blocks;
            let is_exposed = expose_provenance(ptr);
            let block_addr = ptr as usize - (GRANULARITY / 2);
            let block: *mut UsedBlockHdr = with_exposed_provenance(block_addr, is_exposed);
            proof {
                // block == block_ptr
                assert(block == block_ptr) by {
                    assert(block@.addr == ptr as int - (GRANULARITY / 2) as int);
                    assert(block_ptr@.addr == ptr as int - (GRANULARITY / 2) as int);
                    assert(block@.provenance == ptr@.provenance);
                    assert(block_ptr@.provenance == ptr@.provenance);
                };
            }
            proof {
                let tracked mut bp = self.all_blocks.perms.borrow_mut().tracked_remove(block);

                // Establish bp.points_to.is_init() from old_ab.wf()
                let ghost bi = old_ab.get_ptr_internal_index(block);
                old_ab.lemma_wf_extract_node(bi);
                assert(old_ab.perms@[block].wf());
                assert(bp.points_to.is_init());
                assert(bp.points_to.ptr() == block);

                let ghost phys_size = (bp.points_to.value().size & SPEC_SIZE_SIZE_MASK) as int;
                let ghost BH = size_of::<BlockHdr>() as int;

                assert(user_mem.provenance() == block@.provenance) by {
                    assert(user_mem.provenance() == ptr@.provenance);
                    assert(ptr@.provenance == block@.provenance);
                };
                assert(bp.mem.provenance() == block@.provenance);

                // ptr == block + BH == block + GRANULARITY/2
                assert(ptr as int == block as int + BH) by {
                    assert(block as int == ptr as int - (GRANULARITY / 2) as int);
                    if usize::BITS == 64 {
                        assert(BH == 16);
                        assert(GRANULARITY == 32);
                    } else {
                        assert(BH == 8);
                        assert(GRANULARITY == 16);
                    }
                };

                let tracked joined = Self::lemma_join_adjacent_ranges_is_range(
                    user_mem, bp.mem,
                    ptr as int,
                    ptr as int + user_size,
                    block as int + phys_size);

                assert(joined.is_range(block as int + BH, phys_size - BH)) by {
                    assert(ptr as int == block as int + BH);
                };

                bp.mem = joined;
                bp.overhead_mem = PointsToRaw::empty(block@.provenance);
                bp.pad_perm = None;

                assert(bp.wf()) by {
                    assert(!bp.points_to.value().is_free());
                    assert(bp.mem.provenance() == block@.provenance);
                    assert(bp.points_to.ptr() == block);
                    assert(bp.mem.provenance() == bp.points_to.ptr()@.provenance);
                };

                self.all_blocks.perms.borrow_mut().tracked_insert(block, bp);

                // Prove perms@ extensional equality
                assert(self.all_blocks.perms@ =~= old_ab.perms@.insert(block, bp)) by {
                    assert forall |p: *mut BlockHdr|
                        self.all_blocks.perms@.dom().contains(p)
                            == old_ab.perms@.insert(block, bp).dom().contains(p)
                    by {};
                    assert forall |p: *mut BlockHdr|
                        self.all_blocks.perms@.dom().contains(p)
                            implies #[trigger] self.all_blocks.perms@[p]
                                == old_ab.perms@.insert(block, bp)[p]
                    by {
                        if p == block {
                        } else {
                            assert(self.all_blocks.perms@[p] == old_ab.perms@.remove(block)[p]);
                            assert(old_ab.perms@.remove(block)[p] == old_ab.perms@[p]);
                        }
                    };
                };

                // Prove all_blocks.wf()
                old_ab.lemma_wf_glue_facts(bi);
                old_ab.lemma_wf_structural_facts(bi);

                assert(self.all_blocks.value_at(block) == old_ab.value_at(block));
                assert(self.all_blocks.phys_prev_of(bi) == old_ab.phys_prev_of(bi));
                assert(self.all_blocks.phys_next_of(bi) == old_ab.phys_next_of(bi));
                assert(!self.all_blocks.value_at(block).is_free());

                assert(self.all_blocks.value_at(block).prev_phys_block@.addr != 0 ==> (
                    self.all_blocks.phys_prev_of(bi) matches Some(p)
                        && p == self.all_blocks.value_at(block).prev_phys_block));
                assert(self.all_blocks.value_at(block).prev_phys_block@.addr == 0
                    ==> self.all_blocks.phys_prev_of(bi) is None);
                assert(self.all_blocks.phys_next_of(bi) matches Some(next_ptr) ==>
                    AllBlocks::<FLLEN, SLLEN>::phys_next_matches(
                        next_ptr, block, self.all_blocks.value_at(block).size));

                self.all_blocks.lemma_construct_wf_node_glue(bi);
                self.all_blocks.lemma_construct_wf_node_structural(bi);

                AllBlocks::<FLLEN, SLLEN>::lemma_replace_block_perm_from_wf(
                    old_ab, self.all_blocks, block, bp);

                // Frame: wf_shadow, all_freelist_wf, size_class_condition, bitmap preserved
                assert(self.wf_shadow()) by {
                    assert(old_self.wf_shadow());
                    assert(self.shadow_freelist == old_self.shadow_freelist);
                    Self::lemma_shadow_ptrs_nonnull_frame(old_self, *self);
                    assert(self.all_blocks.ptrs@ == old_self.all_blocks.ptrs@);
                };
                assert forall|bi2: BlockIndex<FLLEN, SLLEN>, n: int|
                    bi2.wf() && 0 <= n < old_self.shadow_freelist@.m[bi2].len()
                    implies #[trigger] self.all_blocks.perms@[old_self.shadow_freelist@.m[bi2][n]]
                        == old_self.all_blocks.perms@[old_self.shadow_freelist@.m[bi2][n]]
                by {
                    let node = old_self.shadow_freelist@.m[bi2][n];
                    if node == block {
                        old_self.wf_index_in_freelist(bi2);
                        old_self.lemma_freelist_wf_extract_wf_free_node(bi2, n);
                        assert(old_self.all_blocks.value_at(node).is_free());
                        assert(!old_self.all_blocks.perms@[block].points_to.value().is_free());
                        assert(false);
                    }
                };
                Self::lemma_all_freelist_wf_perms_frame(old_self, *self);
                assert(self.free_blocks_in_freelist()) by {
                    assert(old_self.free_blocks_in_freelist());
                    Self::lemma_free_blocks_in_freelist_except_perms_frame(old_self, *self, Set::empty());
                };
                // size_class_condition via frame lemma
                assert(!old_self.shadow_freelist@.contains(block)) by {
                    if old_self.shadow_freelist@.contains(block) {
                        let bi3 = choose|bi3: BlockIndex<FLLEN, SLLEN>|
                            bi3.wf()
                            && old_self.shadow_freelist@.m.contains_key(bi3)
                            && old_self.shadow_freelist@.m[bi3].contains(block);
                        let n2 = choose|n2: int| 0 <= n2 < old_self.shadow_freelist@.m[bi3].len()
                            && old_self.shadow_freelist@.m[bi3][n2] == block;
                        old_self.wf_index_in_freelist(bi3);
                        old_self.lemma_freelist_wf_extract_wf_free_node(bi3, n2);
                        assert(old_self.all_blocks.value_at(block).is_free());
                        assert(!old_self.all_blocks.perms@[block].points_to.value().is_free());
                        assert(false);
                    }
                };
                assert(Self::perms_size_unchanged_for_freelist(
                    old_self.shadow_freelist@, old_self.all_blocks, self.all_blocks, block)) by {
                    reveal(Tlsf::perms_size_unchanged_for_freelist);
                    assert forall|bi3: BlockIndex<FLLEN, SLLEN>, i2: int|
                        bi3.wf() && 0 <= i2 < old_self.shadow_freelist@.m[bi3].len()
                            && old_self.shadow_freelist@.m[bi3][i2] != block
                        implies self.all_blocks.perms@[old_self.shadow_freelist@.m[bi3][i2]].points_to.value().size
                            == old_self.all_blocks.perms@[old_self.shadow_freelist@.m[bi3][i2]].points_to.value().size
                    by {
                        let node = old_self.shadow_freelist@.m[bi3][i2];
                        assert(self.all_blocks.perms@[node] == old_self.all_blocks.perms@[node]);
                    };
                };
                Self::lemma_size_class_perm_change_preserved(old_self, *self, block);
            }
            block
        }
    }

}

} // verus!
