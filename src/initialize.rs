use vstd::prelude::*;

use crate::bits::*;
use core::mem;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
use vstd::pervasive::*;
use vstd::raw_ptr::{
    expose_provenance, ptr_mut_write, with_exposed_provenance, PointsTo, PointsToRaw,
};
#[cfg(verus_keep_ghost)]
use vstd::set_lib::set_int_range;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::bits::u64_trailing_zeros;

use crate::all_blocks::*;
use crate::block::*;
use crate::block_index::BlockIndex;
use crate::ordered_pointer_list::*;
use crate::parameters::*;
use crate::*;

verus! {

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    /// Inserts a free memory block into the TLSF allocator.
    ///
    /// `insert_free_block_ptr` provides NonNull<[u8]> based interface, but Verus doesn't handle
    /// subtle properties like "dereferencing the length field of slice pointer doesn't dereference
    /// the entire slice pointer (thus safe)".
    ///
    /// TODO: Wrap the address based interface with slice pointer based one out of Verus world.
    //#[verifier::external_body] // for spec debug
    pub unsafe fn insert_free_block_ptr_aligned(
        &mut self,
        start: *mut u8,
        size: usize,
        Tracked(points_to_block): Tracked<PointsToRaw>
    ) -> (r: Option<usize>)
    requires
        points_to_block.is_range(start as usize as int, size as int),
        points_to_block.provenance() == start@.provenance,
        start as usize as int % GRANULARITY as int == 0,
        start as usize != 0,
        size as int % GRANULARITY as int == 0,
        old(self).wf(),
        // TODO: generalize to support multiple pool regions
        old(self).all_blocks.ptrs@.len() == 0,
        size as int <= Self::max_pool_size_spec() as int,
    ensures
        self.wf(),
    {
        let tracked mut mem_remains = points_to_block;

        let mut size_remains = size;
        let mut cursor = start as usize;

        #[cfg(feature = "std")]
        let mut sentinel_tmp = null_bhdr();

        proof {
            self.lemma_wf_components();
        }

        // Platform-specific layout facts (unprovable in Verus)
        assume(size_of::<BlockHdr>() == 16);
        assume(size_of::<BlockHdr>() as usize as int == size_of::<BlockHdr>());
        assume(vstd::layout::size_of::<BlockHdr>() == 16);
        assume(vstd::layout::size_of::<BlockHdr>() as usize as int == vstd::layout::size_of::<BlockHdr>());
        assume(vstd::layout::align_of::<BlockHdr>() == 8);
        assume(vstd::layout::align_of::<BlockHdr>() as usize as int == vstd::layout::align_of::<BlockHdr>());
        assume(size_of::<FreeLink>() == 16);
        assume(size_of::<FreeLink>() as usize as int == size_of::<FreeLink>());
        assume(vstd::layout::size_of::<FreeLink>() == 16);
        assume(vstd::layout::size_of::<FreeLink>() as usize as int == vstd::layout::size_of::<FreeLink>());
        assume(vstd::layout::align_of::<FreeLink>() == 8);
        assume(vstd::layout::align_of::<FreeLink>() as usize as int == vstd::layout::align_of::<FreeLink>());

        let ghost mut first_iter = true;

        while size_remains >= GRANULARITY * 2
            invariant
                self.wf(),
                Self::parameter_validity(),
                size_remains as int % GRANULARITY as int == 0,
                size_remains <= size,
                start as usize != 0,
                start as usize as int % GRANULARITY as int == 0,
                size as int <= Self::max_pool_size_spec() as int,
                // Layout invariants
                size_of::<BlockHdr>() == 16,
                size_of::<BlockHdr>() as usize as int == size_of::<BlockHdr>(),
                vstd::layout::size_of::<BlockHdr>() == 16,
                vstd::layout::size_of::<BlockHdr>() as usize as int == vstd::layout::size_of::<BlockHdr>(),
                vstd::layout::align_of::<BlockHdr>() == 8,
                vstd::layout::align_of::<BlockHdr>() as usize as int == vstd::layout::align_of::<BlockHdr>(),
                size_of::<FreeLink>() == 16,
                size_of::<FreeLink>() as usize as int == size_of::<FreeLink>(),
                vstd::layout::size_of::<FreeLink>() == 16,
                vstd::layout::size_of::<FreeLink>() as usize as int == vstd::layout::size_of::<FreeLink>(),
                vstd::layout::align_of::<FreeLink>() == 8,
                vstd::layout::align_of::<FreeLink>() as usize as int == vstd::layout::align_of::<FreeLink>(),
                // Single-iteration: first_iter XOR done
                first_iter || size_remains == 0,
                first_iter ==> size_remains == size,
                first_iter ==> self.all_blocks.ptrs@.len() == 0,
                // Guarded by size_remains > 0 (cursor may wrap to 0 when done)
                size_remains > 0 ==> mem_remains.is_range(cursor as int, size_remains as int),
                size_remains > 0 ==> mem_remains.provenance() == start@.provenance,
                size_remains > 0 ==> cursor as int % GRANULARITY as int == 0,
                size_remains > 0 ==> cursor != 0,
                size_remains > 0 ==> size_remains as int + cursor as int == start as int + size as int,
                size_remains > 0 ==> cursor as int >= start as int,
            decreases size_remains
        {
            proof {
                self.lemma_wf_components();
                assert(first_iter);
            }
            let chunk_size: usize;
            let max_ps = Self::max_pool_size();
            if size_remains <= max_ps {
                chunk_size = size_remains;
            } else {
                chunk_size = max_ps;
            }

            assert(chunk_size >= GRANULARITY * 2);
            assert(chunk_size <= size_remains);
            assert(chunk_size <= max_ps);
            assert(chunk_size == size_remains);
            assert(chunk_size % GRANULARITY == 0);

            // Prove valid_block_size(chunk_size - GRANULARITY)
            proof {
                Self::lemma_max_pool_size_spec_value();
                Self::lemma_parameter_validity_implies_block_index_parameter_validity();
                let gran_int: int = GRANULARITY as int;
                let chunk_int: int = chunk_size as int;
                let mps_int: int = Self::max_pool_size_spec() as int;
                assert(chunk_int <= mps_int);
                assert(chunk_int - gran_int >= gran_int);
                assert((chunk_int - gran_int) % gran_int == 0) by {
                    assert(chunk_int % gran_int == 0);
                    assert(gran_int % gran_int == 0);
                };
                assert(chunk_int - gran_int < pow2(FLLEN as nat) * gran_int);
            }

            // Split mem_remains into header + freelink + rest
            let tracked mut new_header: PointsTo<BlockHdr>;
            let tracked mut new_header_frelink: PointsTo<FreeLink>;
            proof {
                assert(size_of::<BlockHdr>() as int == 16);
                assert(size_of::<FreeLink>() as int == 16);
                assert(size_remains as int >= (GRANULARITY * 2) as int);
                assert(mem_remains.is_range(cursor as int, size_remains as int));
                assert(cursor as int + size_of::<BlockHdr>() as int
                    <= cursor as int + size_remains as int);
                assert(set_int_range(cursor as int, cursor as int + size_of::<BlockHdr>() as int)
                    .subset_of(mem_remains.dom())) by {
                    assert forall |a: int|
                        set_int_range(cursor as int, cursor as int + size_of::<BlockHdr>() as int).contains(a)
                        implies mem_remains.dom().contains(a) by {
                        assert(cursor as int <= a && a < cursor as int + size_of::<BlockHdr>() as int);
                        assert(a < cursor as int + size_remains as int);
                    }
                };
                let tracked (h1, m) =
                    mem_remains.split(
                        set_int_range(cursor as int, cursor as int
                            + size_of::<BlockHdr>() as int));
                let tracked (h2, m) =
                    m.split(
                        set_int_range(cursor as int + size_of::<BlockHdr>(),
                            cursor as int + size_of::<BlockHdr>() + size_of::<FreeLink>()));
                mem_remains = m;

                // Prove into_typed preconditions via layout invariants
                assert(h1.is_range(cursor as int, vstd::layout::size_of::<BlockHdr>() as int)) by {
                    assert(h1.dom() == set_int_range(cursor as int,
                        cursor as int + size_of::<BlockHdr>() as int));
                    assert(size_of::<BlockHdr>() as int == vstd::layout::size_of::<BlockHdr>() as int);
                };
                assert(cursor as int % (vstd::layout::align_of::<BlockHdr>() as int) == 0) by {
                    assert(cursor as int % (GRANULARITY as int) == 0);
                    assert(vstd::layout::align_of::<BlockHdr>() as int == 8);
                };
                new_header = h1.into_typed(cursor);

                let ghost freelink_addr: int = cursor as int + size_of::<BlockHdr>() as int;
                assert(h2.is_range(freelink_addr, vstd::layout::size_of::<FreeLink>() as int)) by {
                    assert(h2.dom() == set_int_range(freelink_addr,
                        freelink_addr + size_of::<FreeLink>() as int));
                    assert(size_of::<FreeLink>() as int == vstd::layout::size_of::<FreeLink>() as int);
                };
                assert(freelink_addr % (vstd::layout::align_of::<FreeLink>() as int) == 0) by {
                    assert(cursor as int % 8 == 0);
                    assert(size_of::<BlockHdr>() as int == 16);
                    assert(vstd::layout::align_of::<FreeLink>() as int == 8);
                };
                new_header_frelink = h2.into_typed(
                    (cursor + mem::size_of::<BlockHdr>()) as usize);
            }

            let prov = expose_provenance(start);
            let mut block = with_exposed_provenance(cursor, prov);

            let ghost free_block_size: usize = (chunk_size - GRANULARITY) as usize;

            assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(chunk_size - GRANULARITY));

            // Write header and freelink
            ptr_mut_write(block, Tracked(&mut new_header),
                    BlockHdr {
                        size: chunk_size - GRANULARITY,
                        prev_phys_block: null_bhdr(),
                    });
            ptr_mut_write(get_freelink_ptr(block), Tracked(&mut new_header_frelink),
                FreeLink {
                    next_free: null_bhdr(),
                    prev_free: null_bhdr(),
                });

            let tracked mut new_block_perm = BlockPerm {
                points_to: new_header,
                free_link_perm: Some(new_header_frelink),
                mem: PointsToRaw::empty(Provenance::null()),
                overhead_mem: PointsToRaw::empty(Provenance::null()),
                pad_perm: None,
            };
            let mut sentinel_block = BlockHdr::next_phys_block(block, Tracked(&new_block_perm));

            #[cfg(feature = "std")]
            {
                sentinel_tmp = sentinel_block;
            }

            // Split sentinel header from mem_remains
            let ghost sentinel_addr: int = cursor as int + (chunk_size - GRANULARITY) as int;
            let tracked (sentinel_perm, m) = mem_remains.split(
                set_int_range(sentinel_addr, sentinel_addr + size_of::<BlockHdr>() as int));
            proof {
                mem_remains = m;
            }

            proof {
                // Sentinel alignment
                assert(sentinel_addr % (GRANULARITY as int) == 0);
                assert(sentinel_addr % (align_of::<BlockHdr>() as int) == 0) by {
                    assert(GRANULARITY == 32) by (compute);
                    assert(sentinel_addr % 8 == 0) by (nonlinear_arith)
                        requires sentinel_addr % 32 == 0;
                };

                // Prove sentinel_block@.addr == sentinel_addr
                let free_size: usize = (chunk_size - GRANULARITY) as usize;
                assert((free_size & SIZE_SIZE_MASK) == free_size) by {
                    reveal(usize_trailing_zeros);
                    reveal(u64_trailing_zeros);
                    assert(SPEC_SIZE_SIZE_MASK == !31usize) by (compute);
                    assert((free_size & !31usize) == free_size) by (bit_vector)
                        requires free_size % 32 == 0;
                };
                assert(sentinel_block@.addr == sentinel_addr);
            }

            // Prove into_typed preconditions for sentinel
            proof {
                assert(sentinel_perm.is_range(sentinel_addr, vstd::layout::size_of::<BlockHdr>() as int)) by {
                    assert(sentinel_perm.dom() == set_int_range(sentinel_addr,
                        sentinel_addr + size_of::<BlockHdr>() as int));
                    assert(size_of::<BlockHdr>() as int == vstd::layout::size_of::<BlockHdr>() as int);
                };
            }
            let tracked mut sentinel_perm =
                sentinel_perm.into_typed((cursor + (chunk_size - GRANULARITY)) as usize);

            proof {
                assert(sentinel_perm.ptr() == sentinel_block);
            }

            ptr_mut_write(sentinel_block,
                Tracked(&mut sentinel_perm),
                BlockHdr {
                    size: SIZE_USED | SIZE_SENTINEL,
                    prev_phys_block: block,
                });

            // Split free block body and sentinel overhead from mem_remains
            let tracked mut sentinel_overhead: PointsToRaw;
            proof {
                let tracked (free_body_mem, m) = mem_remains.split(
                    set_int_range(
                        cursor as int + size_of::<BlockHdr>() as int + size_of::<FreeLink>() as int,
                        cursor as int + (chunk_size - GRANULARITY) as int));
                let tracked (overhead, m) = m.split(
                    set_int_range(
                        sentinel_addr + size_of::<BlockHdr>() as int,
                        cursor as int + chunk_size as int));
                mem_remains = m;
                new_block_perm.mem = free_body_mem;
                sentinel_overhead = overhead;
            }

            proof {
                let ghost old_ptrs = self.all_blocks.ptrs@;
                let ghost old_sfl = self.shadow_freelist@;

                // sfl.m[idx].len() == 0 for all wf idx (from is_identity_injection + ptrs@.len() == 0)
                assert forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf()
                    implies old_sfl.m[idx].len() == 0
                by {
                    if old_sfl.m[idx].len() > 0 {
                        assert(old_sfl.pi.contains_key((idx, 0int)));
                        assert(0 <= old_sfl.pi[(idx, 0int)] < old_ptrs.len());
                    }
                };
                // first_free[idx] is null for all wf idx (from freelist_wf + empty sfl)
                assert forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf()
                    implies AllBlocks::<FLLEN, SLLEN>::ptr_is_null(
                        self.first_free[idx.0 as int][idx.1 as int])
                by {
                    self.wf_index_in_freelist(idx);
                    self.lemma_extract_first_free_null(idx);
                };

                let ghost saved_fl_bitmap = self.fl_bitmap;
                let ghost saved_sl_bitmap = self.sl_bitmap;

                let tracked sentinel_block_perm = BlockPerm {
                    points_to: sentinel_perm,
                    free_link_perm: None,
                    mem: PointsToRaw::empty(sentinel_block@.provenance),
                    overhead_mem: sentinel_overhead,
                    pad_perm: None,
                };

                // Build ptrs@: [] → [block] → [block, sentinel]
                lemma_add_ghost_pointer_ensures(old_ptrs, block);
                let ghost ptrs_after_free = add_ghost_pointer(old_ptrs, block);
                lemma_add_ghost_pointer_ensures(ptrs_after_free, sentinel_block);
                let ghost ptrs_after_both = add_ghost_pointer(ptrs_after_free, sentinel_block);

                self.all_blocks.ptrs@ = ptrs_after_both;

                self.all_blocks.perms.borrow_mut().tracked_insert(block, new_block_perm);
                self.all_blocks.perms.borrow_mut().tracked_insert(sentinel_block, sentinel_block_perm);

                // Free block is_free
                assert(new_block_perm.points_to.value().is_free()) by {
                    assert(new_block_perm.points_to.value().size == free_block_size);
                    Self::lemma_mark_used_preserves_size_bits(free_block_size);
                    assert((free_block_size & SIZE_USED) == 0usize) by (bit_vector)
                        requires free_block_size as int % 2 == 0, SIZE_USED == 1usize;
                };

                assert(new_block_perm.wf()) by {
                    assert(new_block_perm.points_to.is_init());
                    Self::lemma_mark_used_preserves_size_bits(free_block_size);
                    assert((new_block_perm.points_to.value().size & SIZE_SIZE_MASK)
                        == new_block_perm.points_to.value().size);
                };

                assert(sentinel_block_perm.wf()) by {
                    assert(sentinel_block_perm.points_to.is_init());
                    assert(!sentinel_block_perm.points_to.value().is_free()) by {
                        assert(sentinel_block_perm.points_to.value().size == SIZE_USED | SIZE_SENTINEL);
                        assert(((SIZE_USED | SIZE_SENTINEL) & SIZE_USED) != 0usize) by (bit_vector)
                            requires SIZE_USED == 1usize, SIZE_SENTINEL == 2usize;
                    };
                };

                assert(sentinel_block_perm.points_to.value().is_sentinel()) by {
                    assert(sentinel_block_perm.points_to.value().size == SIZE_USED | SIZE_SENTINEL);
                    assert(((SIZE_USED | SIZE_SENTINEL) & SIZE_SENTINEL) != 0usize) by (bit_vector)
                        requires SIZE_USED == 1usize, SIZE_SENTINEL == 2usize;
                };

                assert(((SIZE_USED | SIZE_SENTINEL) & SIZE_SIZE_MASK) == 0usize) by {
                    reveal(usize_trailing_zeros);
                    reveal(u64_trailing_zeros);
                    assert(SPEC_SIZE_SIZE_MASK == !31usize) by (compute);
                    assert(SIZE_USED == 1usize) by (compute);
                    assert(SIZE_SENTINEL == 2usize) by (compute);
                    assert(((1usize | 2usize) & !31usize) == 0usize) by (bit_vector);
                };

                AllBlocks::<FLLEN, SLLEN>::lemma_wf_node_ptr_from_facts(block);
                AllBlocks::<FLLEN, SLLEN>::lemma_wf_node_ptr_from_facts(sentinel_block);

                AllBlocks::<FLLEN, SLLEN>::lemma_phys_next_matches_intro(
                    sentinel_block, block, self.all_blocks.value_at(block).size);

                assert(ghost_pointer_ordered(self.all_blocks.ptrs@));

                // Concrete sequence: ptrs@ == [block, sentinel]
                assert(old_ptrs.len() == 0);
                assert(old_ptrs =~= Seq::<*mut BlockHdr>::empty());
                lemma_add_ghost_pointer_empty(block);
                assert(ptrs_after_free.len() == 1);
                assert(ptrs_after_free[0] == block);
                assert(sentinel_block as usize as int > block as usize as int) by {
                    assert(sentinel_block@.addr == sentinel_addr);
                    assert(block@.addr == cursor as int);
                    assert(sentinel_addr > cursor as int);
                };
                assert(ptrs_after_free =~= seq![block]);
                lemma_add_ghost_pointer_append_to_singleton(block, sentinel_block);
                assert(ptrs_after_both.len() == 2);
                assert(ptrs_after_both[0] == block);
                assert(ptrs_after_both[1] == sentinel_block);
                assert(self.all_blocks.ptrs@.len() == 2);
                assert(self.all_blocks.ptrs@[0] == block);
                assert(self.all_blocks.ptrs@[1] == sentinel_block);

                let ghost block_idx = self.all_blocks.get_ptr_internal_index(block);
                let ghost sentinel_idx = self.all_blocks.get_ptr_internal_index(sentinel_block);
                assert(block_idx == 0);
                assert(sentinel_idx == 1);

                assert(self.all_blocks.phys_prev_of(0) is None);
                assert(self.all_blocks.phys_next_of(0) == Some(sentinel_block));
                assert(self.all_blocks.phys_prev_of(1) == Some(block));
                assert(self.all_blocks.phys_next_of(1) is None);

                assert(((chunk_size - GRANULARITY) as int) + (cursor as int) < usize::MAX as int);

                assert(!self.all_blocks.value_at(block).is_sentinel()) by {
                    assert(self.all_blocks.value_at(block).size == free_block_size);
                    assert(free_block_size % GRANULARITY == 0);
                    assert(free_block_size >= GRANULARITY);
                    assert(((free_block_size) & SIZE_SENTINEL) == 0usize) by (bit_vector)
                        requires free_block_size % 32 == 0, free_block_size >= 32,
                            SIZE_SENTINEL == 2usize;
                };
                self.all_blocks.lemma_construct_wf_node_glue(block_idx);
                self.all_blocks.lemma_construct_wf_node_structural(block_idx);

                assert(self.all_blocks.value_at(sentinel_block).prev_phys_block == block);
                assert(block@.addr != 0);
                self.all_blocks.lemma_construct_wf_node_glue(sentinel_idx);
                self.all_blocks.lemma_construct_wf_node_structural(sentinel_idx);

                assert(self.all_blocks.wf_node(block_idx));
                assert(self.all_blocks.wf_node(sentinel_idx));

                assert forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                    implies self.all_blocks.wf_node(i)
                by {
                    if i == 0 {
                        assert(self.all_blocks.wf_node(0));
                    } else {
                        assert(i == 1);
                        assert(self.all_blocks.wf_node(1));
                    }
                };

                // pool_size_bounded
                assert(self.all_blocks.ptrs@.last() == sentinel_block);
                assert(self.all_blocks.ptrs@[0] == block);
                assert((sentinel_block as usize as int) - (block as usize as int)
                    == (chunk_size - GRANULARITY) as int);
                Self::lemma_max_pool_size_spec_value();
                let ghost mps = Self::max_pool_size_spec();
                assert((chunk_size - GRANULARITY) < mps);
                self.all_blocks.lemma_pool_size_bounded_from_span();

                self.all_blocks.lemma_wf_from_nodes();
                assert(self.all_blocks.contains(block));

                // !shadow_freelist.contains(block)
                assert(!self.shadow_freelist@.contains(block)) by {
                    if self.shadow_freelist@.contains(block) {
                        let i: BlockIndex<FLLEN, SLLEN> = choose|i: BlockIndex<FLLEN, SLLEN>|
                            i.wf() && self.shadow_freelist@.m[i].contains(block);
                        assert(self.shadow_freelist@.m[i].len() == 0);
                    }
                };

                assert(self.all_blocks.perms@[block].points_to.value().is_free());
                assert(self.all_blocks.perms@[block].points_to.value().size == free_block_size);

                // wf_shadow: shadow_freelist unchanged, is_identity_injection with new ptrs@
                reveal(Tlsf::shadow_ptrs_nonnull);
                assert(self.shadow_ptrs_nonnull());
                assert(is_identity_injection(self.shadow_freelist@, self.all_blocks.ptrs@)) by {
                    assert(self.shadow_freelist@.pi.is_injective());
                    assert forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
                        self.shadow_freelist@.pi.contains_key((idx, m)) <==>
                            (idx.wf() && 0 <= m < self.shadow_freelist@.m[idx].len())
                    by {};
                    assert forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
                        idx.wf() && 0 <= m < self.shadow_freelist@.m[idx].len()
                        implies ({
                            &&& 0 <= #[trigger] self.shadow_freelist@.pi[(idx, m)]
                                < self.all_blocks.ptrs@.len()
                            &&& self.shadow_freelist@.m[idx][m]
                                == self.all_blocks.ptrs@[self.shadow_freelist@.pi[(idx, m)]]
                        })
                    by {
                        assert(self.shadow_freelist@.m[idx].len() == 0);
                    };
                };
                assert(self.wf_shadow());

                // freelist_wf for all wf idx
                assert forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf()
                    implies self.freelist_wf(idx)
                by {
                    self.lemma_freelist_wf_from_empty(idx);
                };

                // free_blocks_in_freelist_except(set![block])
                assert forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                    && self.all_blocks.value_at(self.all_blocks.ptrs@[i]).is_free()
                    && !set![block].contains(self.all_blocks.ptrs@[i])
                    implies self.shadow_freelist@.contains(self.all_blocks.ptrs@[i])
                by {
                    if i == 0 {
                        assert(set![block].contains(self.all_blocks.ptrs@[0]));
                    } else {
                        assert(i == 1);
                        assert(!self.all_blocks.value_at(sentinel_block).is_free());
                    }
                };
                self.lemma_free_blocks_in_freelist_except_intro(set![block]);

                assert(self.all_freelist_wf_weak(set![block]));

                assert(self.fl_bitmap == saved_fl_bitmap);
                assert(self.sl_bitmap == saved_sl_bitmap);
                assert(self.bitmap_wf());
                assert(self.bitmap_sync());

                // size_class_condition: vacuously true since sfl.m[idx].len() == 0
                reveal(Tlsf::size_class_condition);
                assert(self.size_class_condition()) by {
                    assert(self.shadow_freelist@.shadow_freelist_has_all_wf_index());
                    assert forall|idx: BlockIndex<FLLEN, SLLEN>, i: int|
                        self.shadow_freelist@.m.contains_key(idx)
                            && 0 <= i < self.shadow_freelist@.m[idx].len()
                        implies
                            idx == Self::map_floor_spec(
                                self.all_blocks.perms@[
                                    self.shadow_freelist@.m[idx][i]
                                ].points_to.value().size as usize)
                            && idx.block_size_range().contains(
                                self.all_blocks.perms@[
                                    self.shadow_freelist@.m[idx][i]
                                ].points_to.value().size as int)
                    by {
                        assert(idx.wf());
                        assert(self.shadow_freelist@.m[idx].len() == 0);
                    }
                };
            }

            self.link_free_block(chunk_size - GRANULARITY, block);

            assert(size_remains == chunk_size);
            size_remains -= chunk_size;
            cursor = cursor.wrapping_add(chunk_size);

            proof {
                first_iter = false;
                if size_remains > 0 {
                    assert(cursor as int == (cursor - chunk_size) as int + chunk_size as int);
                    assert(cursor as int % GRANULARITY as int == 0);
                    assert(cursor != 0);
                    assert(size_remains as int + cursor as int == start as int + size as int);
                    assert(cursor as int >= start as int);
                }
            }
        }

        Some(cursor.wrapping_sub(start as usize))
    }
}

} // verus!
