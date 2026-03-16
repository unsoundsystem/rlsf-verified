use vstd::prelude::*;

use crate::bits::*;
use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::{logarithm::log, power::pow, power2::pow2};
use vstd::calc_macro::calc;
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
use vstd::pervasive::*;
use vstd::raw_ptr::{
    expose_provenance, ptr_mut_write, ptr_ref, with_exposed_provenance, IsExposed, Metadata,
    PointsTo, PointsToRaw, Provenance,
};
#[cfg(verus_keep_ghost)]
use vstd::raw_ptr::{ptr_from_data, PtrData};
#[cfg(verus_keep_ghost)]
use vstd::set_lib::set_int_range;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::bits::u64_trailing_zeros;
use vstd::{bytes::*, seq::*, seq_lib::*};
//#[cfg(verus_keep_ghost)]
//use crate::bits::bit_scan_forward;
use crate::block_index::BlockIndex;
//use crate::rational_numbers::{Rational, rational_number_facts, rational_number_properties};
use core::hint::unreachable_unchecked;
use vstd::array::*;
//use ghost_tlsf::{UsedInfo, Block, BlockPerm};
use crate::all_blocks::*;
use crate::block::*;
use crate::ordered_pointer_list::*;
use crate::parameters::*;
use crate::unverified_api::*;
use crate::*;
use core::ptr::null;

verus! {


impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    pub fn allocate(&mut self, size: usize, align: usize /* layout: Layout */) ->
        (r: (Option<(*mut u8, Tracked<PointsToRaw>, Tracked<DeallocToken>)>))
        requires
            /* TODO: Allocation precondition
             * - already initialized
             * */
            BlockIndex::<FLLEN, SLLEN>::parameter_validity(),
            old(self).wf(),
            is_power_of_two(align as int),
            // this assumption might be weak: UsedBlockHdr overhead no considered
            align < pow2(FLLEN as nat) * GRANULARITY as int,
            // In the spec of GlobalAlloc, zero-sized allocation is UB, so we avoid it explicitly
            size > 0,
            size as int <= Self::max_allocatable_size(),
            size as int + align as int + mem::size_of::<UsedBlockHdr>() as int + (GRANULARITY as int - 1)
                <= Self::max_allocatable_size(),
            size as int + align.saturating_sub(GRANULARITY / 2) as int + mem::size_of::<UsedBlockHdr>() as int + (GRANULARITY as int - 1)
                <= Self::max_allocatable_size(),
        ensures
            r matches Some((ptr, points_to, tok)) ==> ({
                /* NOTE: Allocation correctness
                 * - resulting pointer
                 *      - alignment
                 *      - provenance is same as the initial block
                 *      - points_to has size as requested
                 *      - consistent with PointsToRaw
                 *          - start address
                 *      - TODO: resulting size is multiple of GRANULARITY
                 *      - TODO: if GRANULARITY <= align, UsedBlockPad works properly
                 * */
                &&& self.wf_dealloc(tok@)
                &&& ptr@.provenance == points_to@.provenance()
                //&&& ptr@.metadata == Metadata::Thin
                &&& {
                    // The permission object returned for user
                    &&& !points_to@.dom().is_empty()
                    &&& exists|s: int| s >= size as int && #[trigger] points_to@.is_range(ptr as usize as int, s)
                 }
                &&& ptr.addr() % align == 0
                &&& self.is_root_provenance(ptr)
            }),
            // TODO: state that if allocation failes, there is no bitmap present for it
            r matches None ==> *old(self) == *self,
            self.wf(),
    {
        assume(size_of::<usize>() == 8);
        assume(size_of::<BlockHdr>() == 16);
        assume(vstd::layout::align_of::<BlockHdr>() == 8);
        assume(size_of::<FreeLink>() == 16);
        assume(vstd::layout::align_of::<FreeLink>() == 8);
        assume(size_of::<UsedBlockHdr>() == 16);
        assume(size_of::<UsedBlockPad>() == 8);
        assume(vstd::layout::size_of::<UsedBlockPad>() == 8);
        assume(vstd::layout::align_of::<UsedBlockPad>() == 8);
        unsafe {

            // The extra bytes consumed by the header and padding.
            //
            // After choosing a free block, we need to adjust the payload's location
            // to meet the alignment requirement. Every block is aligned to
            // `GRANULARITY` bytes. `size_of::<UsedBlockHdr>` is `GRANULARITY / 2`
            // bytes, so the address immediately following `UsedBlockHdr` is only
            // aligned to `GRANULARITY / 2` bytes. Consequently, we need to insert
            // a padding containing at most `max(align - GRANULARITY / 2, 0)` bytes.
            proof {
                //assert(forall|x: usize, y: usize| x.saturating_sub(y) <= usize::MAX - y);
                // align is at most 2^63
                //assert(GRANULARITY == size_of::<usize>() * 4);
                //assert(size_of::<BlockHdr>() == size_of::<usize>() * 2);
                //assert(size_of::<UsedBlockHdr>() == size_of::<usize>() * 2);
                //assert(size_of::<UsedBlockHdr>() == GRANULARITY / 2);
            }

            //self.print_stat();
            let max_overhead =
                align.saturating_sub(GRANULARITY / 2).checked_add(mem::size_of::<UsedBlockHdr>())?;
            // Search for a suitable free block
            let size_overhead = size.checked_add(max_overhead)?;
            proof {
                assert(size_overhead > 0);
            }
            let search_size_raw = size_overhead.checked_add(GRANULARITY - 1)?;
            let search_size = search_size_raw & !(GRANULARITY - 1);
            proof {
                let hdr = mem::size_of::<UsedBlockHdr>();
                Self::lemma_checked_add_eq(align.saturating_sub(GRANULARITY / 2), hdr, max_overhead);
                Self::lemma_checked_add_eq(size, max_overhead, size_overhead);
                Self::lemma_checked_add_eq(size_overhead, (GRANULARITY - 1) as usize, search_size_raw);
                granularity_is_power_of_two();
                lemma_round_down_pow2(search_size_raw, GRANULARITY);
                assert(search_size == search_size_raw & !((GRANULARITY - 1) as usize));
                assert(search_size <= search_size_raw);
                assert(search_size as int <= search_size_raw as int);
                assert(search_size_raw as int
                    == size as int + align.saturating_sub(GRANULARITY / 2) as int + hdr as int + (GRANULARITY as int - 1));
                assert(search_size as int
                    <= size as int + align.saturating_sub(GRANULARITY / 2) as int + hdr as int + (GRANULARITY as int - 1));
                assert(search_size as int <= Self::max_allocatable_size()) by {
                    assert(size as int + align.saturating_sub(GRANULARITY / 2) as int + hdr as int + (GRANULARITY as int - 1)
                        <= Self::max_allocatable_size());
                };

                assert(0 <= size_overhead + (GRANULARITY - 1) <= usize::MAX);
                granularity_is_power_of_two();
                lemma_round_up_pow2(size_overhead, GRANULARITY);
                assert((((size_overhead + (GRANULARITY - 1)) as usize) & !((GRANULARITY - 1) as usize)) % GRANULARITY == 0);
                assert(search_size % GRANULARITY == 0);
                assert(search_size >= GRANULARITY);
            }
            //self.print_stat();
            let idx = self.search_suitable_free_block_list_for_allocation(search_size)?;
            //#[cfg(feature = "std")]
            //{
                //use std::println;
                //println!("hah?");
            //}
            let BlockIndex(fl, sl) = idx;

            let tracked mut old_head_perm: BlockPerm;
            let tracked mut new_head_perm: BlockPerm; // permission for next_free
            let ghost mut ab_before_final_remove = old(self).all_blocks;
            let ghost mut tlsf_before_final_remove = *self;


            // Get a free block: `block`
            //let first_free = self.first_free[fl][sl].unwrap();
            let block = self.first_free[fl][sl]; // ==> null i.e. bimap outdated
            let ghost block_id = self.all_blocks.get_ptr_internal_index(block);
            proof {
                self.wf_index_in_freelist(idx);
                self.freelist_nonempty(idx);
                self.all_blocks.lemma_contains(block);
                //assert(self.all_blocks.wf_node(block_id));
                //assert(self.all_blocks.perms@[block].points_to.is_init());
                self.all_blocks.lemma_wf_node_ptr(block_id);
            }
            let ghost selected_block_size = self.all_blocks.perms@[block].points_to.value().size;
            assert(block@.addr != 0);
            let block_prov = expose_provenance(block);
            let Tracked(block_prov_for_root) = block_prov;

            proof {
                assert(self.all_blocks.wf_node(block_id));
                assert(block == old(self).all_blocks.perms@[block].points_to.ptr());
                old_head_perm = self.all_blocks.perms.borrow_mut().tracked_remove(block);
                assert(old_head_perm == old(self).all_blocks.perms@[block]);
                assert(old_head_perm.wf());
            }

            // NOTE: it is safe to assume that there is a block next to this `block`
            //      there is always sentinel block
            let mut next_phys_block = BlockHdr::next_phys_block(block, Tracked(&old_head_perm));
            let size_and_flags = ptr_ref(block, Tracked(&old_head_perm.points_to)).size;
            let block_size = size_and_flags;
            //debug_assert_eq!(size, size_and_flags & SIZE_SIZE_MASK);
            proof {
                assert(block_size == old_head_perm.points_to.value().size);
                assert(old_head_perm == old(self).all_blocks.perms@[block]);
                assert(old(self).all_blocks.perms@[block].points_to.value().size == selected_block_size);
                assert(search_size as int <= block_size as int) by {
                    old(self).lemma_size_class_at(idx, 0);
                    assert(idx.block_size_range().contains(selected_block_size as int));
                    assert(search_size as int <= idx.block_size_range().start());
                };
                assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size((block_size & SIZE_SIZE_MASK) as int));
            }



            //debug_assert!(size >= search_size);

            // Unlink the free block. We are not using `unlink_free_block` because
            // we already know `(fl, sl)` and that `block.prev_free` is `None`.
            let block_freelink = get_freelink_ptr(block);
            proof { old(self).lemma_freelist_wf_extract_wf_free_node(idx, 0); }
            assert(old(self).wf_free_node(idx, 0));
            let tracked block_freelink_perm = old_head_perm.free_link_perm.tracked_unwrap();
            let next_free_candidate = ptr_ref(block_freelink, Tracked(&block_freelink_perm)).next_free;
            self.set_freelist(idx, next_free_candidate);
            let ghost perms_after_removing_block = self.all_blocks.perms@;
            proof {
                let ghost pre_sfl = self.shadow_freelist@;
                assert(pre_sfl.shadow_freelist_has_all_wf_index()) by {
                    assert(old(self).wf_shadow());
                    assert(pre_sfl == old(self).shadow_freelist@);
                    assert(old(self).shadow_freelist@.shadow_freelist_has_all_wf_index());
                };
                old(self).all_blocks.lemma_wf_nodup();
                assert(ptrs_no_duplicates(old(self).all_blocks.ptrs@));
                Self::lemma_ii_remove_for_index_ensures(pre_sfl, self.all_blocks, idx, 0);
                self.shadow_freelist@ = pre_sfl.ii_remove_for_index(self.all_blocks, idx, 0);
                assert(is_identity_injection(self.shadow_freelist@, self.all_blocks.ptrs@));
                assert(self.shadow_freelist@.shadow_freelist_has_all_wf_index()) by {
                    assert forall |bi: BlockIndex<FLLEN, SLLEN>|
                        self.shadow_freelist@.m.contains_key(bi) <==> bi.wf()
                    by {
                        assert(self.shadow_freelist@.m.contains_key(bi) == pre_sfl.m.contains_key(bi));
                    };
                };
            }

            let mut next_next_free_candidate = null_bhdr();
            if next_free_candidate != null_bhdr() {
                let next_free = next_free_candidate;
                proof {
                    assert(old(self).shadow_freelist@.m[idx].len() > 1) by {
                        old(self).lemma_freelist_wf_extract_wf_free_node(idx, 0);
                        assert(old(self).wf_free_node(idx, 0));
                        old(self).lemma_freelist_len_gt1_from_nonnull_next(idx);
                    };
                    old(self).lemma_freelist_wf_extract_wf_free_node(idx, 1);
                    assert(old(self).wf_free_node(idx, 1));
                    assert(old(self).all_blocks.wf_node(self.all_blocks.get_ptr_internal_index(next_free)));
                    new_head_perm = self.all_blocks.perms.borrow_mut().tracked_remove(next_free);
                    assert(self.all_blocks.perms@ == perms_after_removing_block.remove(next_free));
                    assert(new_head_perm == old(self).all_blocks.perms@[next_free]);
                }

                let next_free_link = get_freelink_ptr(next_free);
                let tracked mut next_free_link_perm = new_head_perm.free_link_perm.tracked_unwrap();
                next_next_free_candidate = ptr_ref(next_free_link, Tracked(&next_free_link_perm)).next_free;
                ptr_mut_write(next_free_link,
                    Tracked(&mut next_free_link_perm),
                    FreeLink {
                        next_free: next_next_free_candidate,
                        prev_free: null_bhdr(),
                    },
                    );
                proof {
                    self.all_blocks.perms.borrow_mut().tracked_insert(next_free, BlockPerm {
                        points_to: new_head_perm.points_to,
                        free_link_perm: Some(next_free_link_perm),
                        mem: new_head_perm.mem,
                    });
                    assert(self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free
                        == next_next_free_candidate);
                    assert(self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().prev_free@.addr == 0);
                }
            } else {
                // The free list is now empty - update the bitmap
                self.clear_bit_for_sl(idx);
            }
            proof {
                assert(next_free_candidate@.addr != 0 ==>
                    self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free
                        == next_next_free_candidate)
                by {
                    if next_free_candidate@.addr != 0 {
                        assert(self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free
                            == next_next_free_candidate);
                    }
                };
                assert(next_free_candidate@.addr != 0 ==> (
                    self.all_blocks.perms@[next_free_candidate].points_to
                        == old(self).all_blocks.perms@[next_free_candidate].points_to
                    && self.all_blocks.perms@[next_free_candidate].mem
                        == old(self).all_blocks.perms@[next_free_candidate].mem
                )) by {
                    if next_free_candidate@.addr != 0 {
                        old(self).lemma_freelist_wf_extract_wf_free_node(idx, 1);
                        assert(old(self).wf_free_node(idx, 1));
                        assert(new_head_perm == old(self).all_blocks.perms@[next_free_candidate]);
                        assert(self.all_blocks.perms@[next_free_candidate].points_to == new_head_perm.points_to);
                        assert(self.all_blocks.perms@[next_free_candidate].mem == new_head_perm.mem);
                    }
                };
            }

            proof {
                old_head_perm.free_link_perm = Some(block_freelink_perm);
            }

            //// Decide the starting address of the payload
            let unaligned_ptr =
                with_exposed_provenance((block as usize).wrapping_add(size_of::<UsedBlockHdr>()), block_prov);
            let ptr = round_up(unaligned_ptr, align);

            #[cfg(feature = "std")]
            {
                if align < GRANULARITY {
                    assert_eq!(unaligned_ptr, ptr);
                } else {
                    assert!(unaligned_ptr != ptr);
                }
            }
            //if align < GRANULARITY {
                //assert(unaligned_ptr ==  ptr.as_ptr());
            //} else {
                //assert(unaligned_ptr != ptr.as_ptr());
            //}

            //// Calculate the actual overhead and the final block size of the
            //// used block being created here
            let overhead = ptr as usize - block as usize;
            assert(overhead <= max_overhead) by {
                let ghost b = block@.addr;
                let ghost u = unaligned_ptr@.addr;
                let ghost p = ptr@.addr;
                assert(old(self).all_blocks.wf_node(block_id));
                assert(b % GRANULARITY == 0);
                assert(p >= u);
                assert(p < u + align);

                if align < GRANULARITY {
                    if usize::BITS == 64 {
                        assert(GRANULARITY == 32);
                        assert(u == b + size_of::<UsedBlockHdr>());
                        assert(align <= 16) by {
                            lemma_pow2_value_in_usize(align);
                            assert(align < 32);
                        };
                        assert(u % align == 0) by {
                            assert(align == 1 || align == 2 || align == 4 || align == 8 || align == 16) by {
                                lemma_pow2_value_in_usize(align);
                                assert(align <= 16);
                            };
                        };
                        assert(p == u) by {
                            let ghost pi: int = p as int;
                            let ghost ui: int = u as int;
                            let ghost ai: int = align as int;
                            assert(pi == p);
                            assert(ui == u);
                            assert(ai == align);
                            if p != u {
                                let ghost d = pi - ui;
                                assert(pi > ui);
                                assert(0 < d);
                                assert(d < ai);
                                assert(d % ai == 0) by {
                                    vstd::arithmetic::div_mod::lemma_mod_equivalence(pi, ui, ai);
                                    assert(pi % ai == ui % ai);
                                };
                                assert(d / ai == 0) by {
                                    vstd::arithmetic::div_mod::lemma_basic_div(d, ai);
                                };
                                assert(d == ai * (d / ai) + d % ai) by {
                                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(d, ai);
                                };
                                assert(d == 0);
                                assert(false);
                            }
                        };
                    } else {
                        assert(GRANULARITY == 16);
                        assert(u == b + size_of::<UsedBlockHdr>());
                        assert(align <= 8) by {
                            lemma_pow2_value_in_usize(align);
                            assert(align < 16);
                        };
                        assert(b % align == 0) by {
                            assert(align == 1 || align == 2 || align == 4 || align == 8) by {
                                lemma_pow2_value_in_usize(align);
                                assert(align <= 8);
                            };
                        };
                        assert(u % align == 0) by {
                            assert(align == 1 || align == 2 || align == 4 || align == 8) by {
                                lemma_pow2_value_in_usize(align);
                                assert(align <= 8);
                            };
                        };
                        assert(p == u) by {
                            let ghost pi: int = p as int;
                            let ghost ui: int = u as int;
                            let ghost ai: int = align as int;
                            assert(pi == p);
                            assert(ui == u);
                            assert(ai == align);
                            assert(pi % ai == 0) by {
                                assert(pi == p as int);
                                assert(ai == align as int);
                                assert(p % align == 0);
                            };
                            assert(ui % ai == 0) by {
                                assert(ui == u as int);
                                assert(ai == align as int);
                                assert(u % align == 0);
                            };
                            if p != u {
                                let ghost d = pi - ui;
                                assert(pi > ui);
                                assert(0 < d);
                                assert(d < ai);
                                assert(d % ai == 0) by {
                                    vstd::arithmetic::div_mod::lemma_mod_equivalence(pi, ui, ai);
                                    assert(pi % ai == ui % ai);
                                };
                                assert(d / ai == 0) by {
                                    vstd::arithmetic::div_mod::lemma_basic_div(d, ai);
                                };
                                assert(d == ai * (d / ai) + d % ai) by {
                                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(d, ai);
                                };
                                assert(d == 0);
                                assert(false);
                            }
                        };
                    }
                    assert(overhead <= max_overhead);
                } else {
                    if usize::BITS == 64 {
                        assert(GRANULARITY == 32);
                        assert(align % 32 == 0) by {
                            lemma_pow2_value_in_usize(align);
                        };
                        assert(p % 32 == 0) by (bit_vector)
                            requires
                                p % align == 0,
                                align > 0,
                                align % 32 == 0;
                        assert(overhead % 32 == 0) by (bit_vector)
                            requires
                                p % 32 == 0,
                                b % 32 == 0,
                                overhead == p - b;
                        assert(overhead <= align) by {
                            if !(overhead <= align) {
                                assert(align < overhead);
                                assert(overhead < align + size_of::<UsedBlockHdr>());
                                assert(overhead % 32 == 0);
                                assert(false);
                            }
                        };
                            assert(max_overhead == align) by {
                                assert(GRANULARITY / 2 == 16);
                                assert(max_overhead == align.saturating_sub(16) + 16);
                                assert(align.saturating_sub(16) == align - 16);
                            };
                    } else {
                        assert(GRANULARITY == 16);
                        assert(align % 16 == 0) by {
                            lemma_pow2_value_in_usize(align);
                        };
                        assert(p % 16 == 0) by (bit_vector)
                            requires
                                p % align == 0,
                                align > 0,
                                align % 16 == 0;
                        assert(overhead % 16 == 0) by (bit_vector)
                            requires
                                p % 16 == 0,
                                b % 16 == 0,
                                overhead == p - b;
                        assert(overhead <= align) by {
                            if !(overhead <= align) {
                                assert(align < overhead);
                                assert(overhead < align + 8);
                                assert(overhead % 16 == 0);
                                assert(false);
                            }
                        };
                        assert(max_overhead == align) by {
                            assert(GRANULARITY / 2 == 8);
                            assert(align.saturating_sub(8) == align - 8);
                            assert(max_overhead == (align - 8) + 8);
                        };
                    }
                    assert(overhead <= max_overhead);
                }
            };

            let new_size = overhead + size;
            let new_size = (new_size + GRANULARITY - 1) & !(GRANULARITY - 1);
            assert(new_size <= search_size) by {
                //lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                //assert(new_size == overhead + size);
                assert(overhead + size <= size_overhead);
                lemma_round_up_pow2_monotonic((overhead + size) as usize, size_overhead, GRANULARITY);
            };

            // Permission object for `ptr`, the pointer returned to the user
            let tracked mut new_block_perm = old_head_perm;
            proof {
                assert(new_block_perm.points_to.ptr() == block);
                assert(old_head_perm.wf());
                assert(new_block_perm.mem.provenance() == block@.provenance);
            }
            if new_size == block_size {
                // The allocation completely fills this free block.
                // Updating `next_phys_block.prev_phys_block` is unnecessary in this
                // case because it's still supposed to point to `block`.
                {
                    //// Turn `block` into a used memory block and initialize the used block
                    //// header. `prev_phys_block` is already set.
                    let prev_phys_block = ptr_ref(block, Tracked(&new_block_perm.points_to)).prev_phys_block;
                    ptr_mut_write(block, Tracked(&mut new_block_perm.points_to),
                    BlockHdr {
                        size: new_size | SIZE_USED,
                        prev_phys_block
                    });
                }
                proof {
                    assert(new_size % GRANULARITY == 0) by {
                        granularity_is_power_of_two();
                        lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                    };
                    assert((new_block_perm.points_to.value().size & SIZE_USED) == SIZE_USED) by {
                        assert(new_block_perm.points_to.value().size == (new_size | SIZE_USED));
                        assert(((new_size | SIZE_USED) & SIZE_USED) == SIZE_USED) by (bit_vector)
                            requires SIZE_USED == 1;
                    };
                    assert(!(new_block_perm.points_to.value().is_free()));
                }
                {
                    let freelink = get_freelink_ptr(block);
                    let tracked mut freelink_perm = new_block_perm.free_link_perm.tracked_unwrap();
                    proof {
                        freelink_perm.leak_contents();
                    }
                    proof {
                        assert(freelink == get_freelink_ptr_spec(block));
                        assert(freelink as int == block as int + size_of::<BlockHdr>() as int);
                        assert(freelink_perm.ptr() == freelink);
                        let tracked freelink_raw = freelink_perm.into_raw();
                        assume(freelink_raw.is_range(freelink as int, size_of::<FreeLink>() as int));
                        let tracked payload_mem = new_block_perm.mem;
                        assert(freelink_raw.is_range(
                            block as int + size_of::<BlockHdr>() as int,
                            size_of::<FreeLink>() as int
                        ));
                        assert(payload_mem.is_range(
                            block as int + size_of::<BlockHdr>() as int + size_of::<FreeLink>() as int,
                            new_size as int - size_of::<BlockHdr>() as int - size_of::<FreeLink>() as int
                        )) by {
                            assert(new_size == block_size);
                            assert(old_head_perm.wf());
                            assert(payload_mem == old_head_perm.mem);
                            assert(old_head_perm.points_to.ptr() == block);
                        };
                        new_block_perm.mem = Self::lemma_join_adjacent_ranges_is_range(
                            freelink_raw,
                            payload_mem,
                            block as int + size_of::<BlockHdr>() as int,
                            block as int + size_of::<BlockHdr>() as int + size_of::<FreeLink>() as int,
                            block as int + new_size as int,
                        );
                        assert(new_block_perm.mem.is_range(
                            block as int + size_of::<BlockHdr>() as int,
                            new_size as int - size_of::<BlockHdr>() as int
                        ));
                        new_block_perm.free_link_perm = None;
                    }
                    assert(new_block_perm.mem.is_range(
                        block as int + size_of::<BlockHdr>() as int,
                        new_size as int - size_of::<BlockHdr>() as int
                    ));
                    assert(new_block_perm.mem.dom() == set_int_range(
                        block as int + size_of::<BlockHdr>() as int,
                        block as int + new_size as int
                    )) by {
                        assert(new_block_perm.mem.is_range(
                            block as int + size_of::<BlockHdr>() as int,
                            new_size as int - size_of::<BlockHdr>() as int
                        ));
                    };
                }
            } else {
                // The allocation partially fills this free block. Create a new
                // free block header at `block + new_size..block + new_size + size_of::<BlockHdr>()`
                // of length (`new_free_block_size`).
                let bhdr_size = size_of::<BlockHdr>();
                let freelink_size = size_of::<FreeLink>();
                let new_free_block: *mut BlockHdr =
                    with_exposed_provenance(block as usize + new_size, block_prov);
                let new_freelink = get_freelink_ptr(new_free_block);
                let new_free_block_size = block_size - new_size;

                // m1 = [block + overhead, block + new_size): return it for this request,
                // m2 = [block + new_size, block + block_size): going to create a new free block from it
                let tracked (m1, m2) = new_block_perm.mem.split(
                    set_int_range(
                        block as int + bhdr_size as int + freelink_size as int,
                        block as int + new_size));
                let tracked mut new_free_block_perm;

                proof {
                    let ghost mem_start = block as int + bhdr_size as int + freelink_size as int;
                    let ghost mem_end = block as int + block_size as int;
                    assert((new_size as int) + bhdr_size as int + freelink_size as int
                        <= new_block_perm.points_to.value().size as int) by {
                        assert(new_size % GRANULARITY == 0) by {
                            granularity_is_power_of_two();
                            lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                        };
                    };
                    assert((overhead + size) as usize <= new_size) by {
                        granularity_is_power_of_two();
                        lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                    };
                    assert(new_size >= size_of::<BlockHdr>() + size_of::<FreeLink>()) by {
                        if usize::BITS == 64 {
                            assert(GRANULARITY == 32);
                        } else {
                            assert(GRANULARITY == 16);
                        }
                        assert(new_size % GRANULARITY == 0) by {
                            granularity_is_power_of_two();
                            lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                        };
                        assert(new_size > 0);
                    };
                    let tracked (new_block_header_perm, m3) =
                        m2.split(set_int_range(new_free_block as int, new_free_block as int + bhdr_size as int));

                    let tracked (new_header_freelink, mem) =
                        m3.split(set_int_range(get_freelink_ptr_spec(new_free_block) as int,
                            get_freelink_ptr_spec(new_free_block) as int + size_of::<FreeLink>() as int));
                    let ghost new_header_freelink_prov = new_header_freelink.provenance();

                    assert(new_size % GRANULARITY == 0) by {
                        granularity_is_power_of_two();
                        lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                    };
                    // Requested region
                    new_block_perm.mem = m1;

                    let tracked new_header_freelink_typed =
                        new_header_freelink.into_typed::<FreeLink>(new_freelink as usize);
                    new_free_block_perm = BlockPerm {
                        points_to: new_block_header_perm.into_typed::<BlockHdr>(new_free_block.addr()),
                        free_link_perm: Some(new_header_freelink_typed),
                        mem,
                    };
                    assert(new_free_block_perm.free_link_perm.unwrap().ptr() == get_freelink_ptr_spec(new_free_block)) by {
                        assert(new_freelink == get_freelink_ptr_spec(new_free_block));
                        assert(new_free_block_perm.free_link_perm.unwrap().ptr() == new_freelink);
                    };
                }
                {
                    let freelink = get_freelink_ptr(block);
                    let tracked mut freelink_perm = new_block_perm.free_link_perm.tracked_unwrap();
                    proof {
                        freelink_perm.leak_contents();
                    }
                    proof {
                        let tracked freelink_raw = freelink_perm.into_raw();
                        let tracked payload_mem = new_block_perm.mem;
                        assert(payload_mem.is_range(
                            block as int + size_of::<BlockHdr>() as int + size_of::<FreeLink>() as int,
                            new_size as int - size_of::<BlockHdr>() as int - size_of::<FreeLink>() as int
                        )) by {
                            assert(payload_mem == m1);
                        };
                        new_block_perm.mem = Self::lemma_join_adjacent_ranges_is_range(
                            freelink_raw,
                            payload_mem,
                            block as int + size_of::<BlockHdr>() as int,
                            block as int + size_of::<BlockHdr>() as int + size_of::<FreeLink>() as int,
                            block as int + new_size as int,
                        );
                        assert(new_block_perm.mem.is_range(
                            block as int + size_of::<BlockHdr>() as int,
                            new_size as int - size_of::<BlockHdr>() as int
                        ));
                        new_block_perm.free_link_perm = None;
                    }
                    assert(new_block_perm.mem.is_range(
                        block as int + size_of::<BlockHdr>() as int,
                        new_size as int - size_of::<BlockHdr>() as int
                    ));
                    assert(new_block_perm.mem.dom() == set_int_range(
                        block as int + size_of::<BlockHdr>() as int,
                        block as int + new_size as int
                    )) by {
                        assert(new_block_perm.mem.is_range(
                            block as int + size_of::<BlockHdr>() as int,
                            new_size as int - size_of::<BlockHdr>() as int
                        ));
                    };
                }

                // equals to divided permission above
                let ghost next_phys_block_ind = self.all_blocks.get_ptr_internal_index(next_phys_block);
                let ghost perms_before_split_update = self.all_blocks.perms@;
                proof {
                    old(self).all_blocks.lemma_contains(next_phys_block);
                }
                let tracked next_phys_block_perm = self.all_blocks.perms.borrow_mut()
                    .tracked_remove(next_phys_block);

                proof {
                    assert(old(self).all_blocks.wf_node(next_phys_block_ind));
                    assert(next_phys_block_perm.wf());
                }
                // Update `next_phys_block.prev_phys_block` to point to this new
                // free block
                // Invariant: No two adjacent free blocks
                //debug_assert!((next_phys_block.as_ref().size & SIZE_USED) != 0);

                {
                    //// Turn `block` into a used memory block and initialize the used block
                    //// header. `prev_phys_block` is already set.
                    let prev_phys_block = ptr_ref(block, Tracked(&new_block_perm.points_to)).prev_phys_block;
                    ptr_mut_write(block, Tracked(&mut new_block_perm.points_to),
                    BlockHdr {
                        size: new_size | SIZE_USED,
                        prev_phys_block
                    });
                }
                let next_size = ptr_ref(next_phys_block, Tracked(&next_phys_block_perm.points_to)).size;
                ptr_mut_write(next_phys_block, Tracked(&mut next_phys_block_perm.points_to),
                    BlockHdr {
                        size: next_size,
                        prev_phys_block: new_free_block
                    });

                // Create the new free block header
                ptr_mut_write(new_free_block, Tracked(&mut new_free_block_perm.points_to),
                    BlockHdr {
                        size: new_free_block_size,
                        prev_phys_block: block,
                    });
                let tracked mut new_free_link_perm = new_free_block_perm.free_link_perm.tracked_unwrap();
                ptr_mut_write(new_freelink, Tracked(&mut new_free_link_perm), FreeLink {
                    next_free: null_bhdr(),
                    prev_free: null_bhdr(),
                });
                proof {
                    new_free_block_perm.free_link_perm = Some(new_free_link_perm);
                }
                // NOTE: This unwrap panics when invalid size is provided
                {
                    proof {
                        let ghost old_ptrs = old(self).all_blocks.ptrs@;
                        let ghost sfl_before_shift =
                            old(self).shadow_freelist@.ii_remove_for_index(old(self).all_blocks, idx, 0);
                        assert(self.all_blocks.perms@ == perms_before_split_update.remove(next_phys_block));
                        assert(old_ptrs[block_id] == block);
                        assert((block as usize as int) < (new_free_block as usize as int)) by {
                            assert(new_free_block as int == block as int + new_size as int);
                            assert(new_size > 0);
                        };
                        assert(block_id + 1 < old_ptrs.len() ==> (new_free_block as usize as int) <= (old_ptrs[block_id + 1] as usize as int)) by {
                            if block_id + 1 < old_ptrs.len() {
                                assert(old(self).all_blocks.wf_node(block_id));
                                assert(old(self).all_blocks.phys_next_of(block_id) is Some);
                                assert(old(self).all_blocks.phys_next_of(block_id).unwrap() == old_ptrs[block_id + 1]);
                                assert((old_ptrs[block_id + 1] as usize as int) == (block as usize as int) + block_size as int);
                                assert((new_free_block as usize as int) == (block as usize as int) + new_size as int);
                                assert(new_size <= block_size);
                            }
                        };
                        old(self).all_blocks.lemma_wf_nodup();
                        assert(ptrs_no_duplicates(old_ptrs));
                        assert(old(self).shadow_freelist@.shadow_freelist_has_all_wf_index()) by {
                            assert(old(self).wf_shadow());
                        };
                        assert(sfl_before_shift.shadow_freelist_has_all_wf_index()) by {
                            assert forall |bi: BlockIndex<FLLEN, SLLEN>|
                                sfl_before_shift.m.contains_key(bi) <==> bi.wf()
                            by {
                                assert(sfl_before_shift.m.contains_key(bi)
                                    == old(self).shadow_freelist@.m.contains_key(bi));
                            };
                        };
                        Self::lemma_ii_remove_for_index_ensures(old(self).shadow_freelist@, old(self).all_blocks, idx, 0);
                        assert(is_identity_injection(sfl_before_shift, old_ptrs));
                        Self::lemma_ii_shift_after_insert_ensures(
                            sfl_before_shift,
                            old_ptrs,
                            block_id,
                            new_free_block,
                        );
                        self.all_blocks.ptrs@ = add_ghost_pointer(old_ptrs, new_free_block);
                        self.shadow_freelist@ = ShadowFreelist {
                            m: sfl_before_shift.m,
                            pi: sfl_before_shift.pi.map_values(|ai: int| if block_id + 1 <= ai { ai + 1 } else { ai }),
                        };
                        assert(self.all_blocks.contains(new_free_block)) by {
                            lemma_add_ghost_pointer_ensures(old(self).all_blocks.ptrs@, new_free_block);
                            assert(self.all_blocks.ptrs@.contains(new_free_block));
                        };
                        assert(new_free_block_perm.points_to.value().is_free()) by {
                            if usize::BITS == 64 {
                                lemma_mod_by_multiple(new_free_block_size as int, 16, 2);
                            } else {
                                lemma_mod_by_multiple(new_free_block_size as int, 8, 2);
                            }
                            assert((new_free_block_size & SIZE_USED) == 0usize) by (bit_vector)
                                requires new_free_block_size as int % 2 == 0, SIZE_USED == 1;
                        };
                        assert(new_free_block_perm.wf()) by {
                            assert(new_free_block_perm.points_to.value().size == new_free_block_size);
                            Self::lemma_mark_used_preserves_size_bits(new_free_block_size);
                            assert((new_free_block_perm.points_to.value().size & SIZE_SIZE_MASK)
                                == new_free_block_perm.points_to.value().size);
                        };
                        let ghost perms_after_remove_next_phys = self.all_blocks.perms@;
                        self.all_blocks.perms.borrow_mut().tracked_insert(block, new_block_perm);
                        let ghost perms_after_insert_block = self.all_blocks.perms@;
                        self.all_blocks.perms.borrow_mut().tracked_insert(next_phys_block, next_phys_block_perm);
                        let ghost perms_after_insert_next_phys = self.all_blocks.perms@;
                        self.all_blocks.perms.borrow_mut().tracked_insert(new_free_block, new_free_block_perm);
                        assert(self.all_blocks.perms.dom().contains(block));
                        assert(self.all_blocks.perms.dom().contains(new_free_block));
                        assert(self.all_blocks.perms@[new_free_block].points_to.value().is_free());
                        if next_free_candidate@.addr != 0 {
                            assert(next_free_candidate != block) by {
                                old(self).lemma_freelist_wf_extract_wf_free_node(idx, 0);
                                assert(old(self).wf_free_node(idx, 0));
                                old(self).lemma_wf_free_node_next_addr(idx, 0);
                                assert(Some(next_free_candidate) == Self::free_next_of(old(self).shadow_freelist@.m[idx], 0));
                                assert(old(self).shadow_freelist@.m[idx][0] == block);
                                assert(old(self).shadow_freelist@.m[idx].len() > 1);
                                assert(Self::free_next_of(old(self).shadow_freelist@.m[idx], 0)
                                    == Some(old(self).shadow_freelist@.m[idx][1]));
                                assert(next_free_candidate == old(self).shadow_freelist@.m[idx][1]);
                                old(self).lemma_shadow_list_no_duplicates();
                                old(self).lemma_nodup_get(idx, 0, idx, 1);
                                assert(block != old(self).shadow_freelist@.m[idx][1]);
                            };
                            assert(next_free_candidate != next_phys_block) by {
                                if next_free_candidate == next_phys_block {
                                    assert(old(self).all_blocks.wf_node(block_id));
                                    assert(old(self).all_blocks.value_at(block).is_free());
                                    assert(old(self).all_blocks.phys_next_of(block_id) is Some);
                                    assert(old(self).all_blocks.phys_next_of(block_id).unwrap() == next_phys_block);
                                    assert(!old(self).all_blocks.value_at(next_phys_block).is_free());
                                    assert(old(self).all_blocks.value_at(next_free_candidate).is_free());
                                    assert(false);
                                }
                            };
                            assert(next_free_candidate != new_free_block) by {
                                if next_free_candidate == new_free_block {
                                    old(self).lemma_freelist_wf_extract_wf_free_node(idx, 1);
                                    assert(old(self).wf_free_node(idx, 1));
                                    assert(old(self).all_blocks.contains(next_free_candidate));
                                    assert(old_ptrs.contains(next_free_candidate));
                                    let ghost ci = old(self).all_blocks.get_ptr_internal_index(next_free_candidate);
                                    assert(0 <= ci < old_ptrs.len());
                                    assert(old_ptrs[ci] == next_free_candidate);
                                    assert(old_ptrs[block_id] == block);
                                    old(self).all_blocks.lemma_wf_nodup();
                                    assert(ptrs_no_duplicates(old_ptrs));
                                    assert(ci != block_id) by {
                                        if ci == block_id {
                                            assert(old_ptrs[ci] == old_ptrs[block_id]);
                                            assert(next_free_candidate == block);
                                            assert(false);
                                        }
                                    };
                                    assert(ghost_pointer_ordered(old_ptrs));
                                    if ci < block_id {
                                        lemma_ghost_pointer_ordered_index(old_ptrs, ci, block_id);
                                        assert((next_free_candidate as usize as int) < (block as usize as int));
                                        assert((block as usize as int) < (new_free_block as usize as int)) by {
                                            assert(new_free_block as int == block as int + new_size as int);
                                            assert(new_size > 0);
                                        };
                                        assert((next_free_candidate as usize as int) < (new_free_block as usize as int));
                                        assert(false);
                                    } else {
                                        assert(block_id < ci);
                                        if ci == block_id + 1 {
                                            assert(old_ptrs[ci] == old_ptrs[block_id + 1]);
                                            assert(old(self).all_blocks.wf_node(block_id));
                                            assert(old(self).all_blocks.phys_next_of(block_id) is Some);
                                            assert(old(self).all_blocks.phys_next_of(block_id).unwrap() == old_ptrs[block_id + 1]);
                                            assert(old_ptrs[block_id + 1] == next_phys_block);
                                            assert(next_free_candidate == next_phys_block);
                                            assert(false);
                                        } else {
                                            assert(block_id + 1 < ci);
                                            lemma_ghost_pointer_ordered_index(old_ptrs, block_id + 1, ci);
                                            assert((old_ptrs[block_id + 1] as usize as int) < (next_free_candidate as usize as int));
                                            assert((new_free_block as usize as int) < (old_ptrs[block_id + 1] as usize as int)) by {
                                                assert(old(self).all_blocks.wf_node(block_id));
                                                assert(old(self).all_blocks.phys_next_of(block_id) is Some);
                                                assert(old(self).all_blocks.phys_next_of(block_id).unwrap() == old_ptrs[block_id + 1]);
                                                assert((old_ptrs[block_id + 1] as usize as int) == (block as usize as int) + block_size as int);
                                                assert((new_free_block as usize as int) == (block as usize as int) + new_size as int);
                                                assert(new_size < block_size);
                                            };
                                            assert((new_free_block as usize as int) < (next_free_candidate as usize as int));
                                            assert(false);
                                        }
                                    }
                                }
                            };
                        }
                    }

                    //assert(self.all_blocks.wf_node(next_phys_block_ind));
                    //assert(self.all_blocks.wf_node(next_phys_block_ind - 1));
                    assert(self.all_blocks.wf()) by {
                        // {{{
                        let ghost old_ptrs = old(self).all_blocks.ptrs@;
                        lemma_add_ghost_pointer_ensures(old(self).all_blocks.ptrs@, new_free_block);
                        old(self).all_blocks.lemma_wf_nodup();
                        assert(ptrs_no_duplicates(old_ptrs));
                        assert(0 <= block_id < old_ptrs.len());
                        assert(old_ptrs[block_id] == block);
                        assert((block as usize as int) < (new_free_block as usize as int)) by {
                            assert(new_free_block as int == block as int + new_size as int);
                            assert(new_size > 0);
                        };
                        assert(block_id + 1 < old_ptrs.len() ==> (new_free_block as usize as int) <= (old_ptrs[block_id + 1] as usize as int)) by {
                            if block_id + 1 < old_ptrs.len() {
                                assert(old(self).all_blocks.wf_node(block_id));
                                assert(old(self).all_blocks.phys_next_of(block_id) is Some);
                                assert(old(self).all_blocks.phys_next_of(block_id).unwrap() == old_ptrs[block_id + 1]);
                                assert((old_ptrs[block_id + 1] as usize as int) == (block as usize as int) + block_size as int);
                                assert((new_free_block as usize as int) == (block as usize as int) + new_size as int);
                                assert(new_size <= block_size);
                            }
                        };
                        assert(old_ptrs[block_id + 1] == next_phys_block) by {
                            assert(old(self).all_blocks.wf_node(block_id));
                            assert(old(self).all_blocks.phys_next_of(block_id) is Some);
                            let next_ptr = old(self).all_blocks.phys_next_of(block_id).unwrap();
                            assert(next_ptr == old_ptrs[block_id + 1]);
                            assert(next_ptr@.addr == block@.addr + (old(self).all_blocks.value_at(block).size & SIZE_SIZE_MASK));
                            assert(next_ptr@.provenance == block@.provenance);
                            assert(next_phys_block@.addr == block@.addr + (old_head_perm.points_to.value().size & SIZE_SIZE_MASK));
                            assert(next_phys_block@.provenance == block@.provenance);
                            assert(old(self).all_blocks.value_at(block).size == old_head_perm.points_to.value().size);
                            assert(next_ptr@.addr == next_phys_block@.addr);
                            assert(next_ptr@.provenance == next_phys_block@.provenance);
                        };
                        lemma_add_ghost_pointer_insert_after_index(old_ptrs, new_free_block, block_id);
                        assert(0 <= block_id < self.all_blocks.ptrs@.len());
                        assert(next_phys_block_ind == block_id + 1) by {
                            assert(old_ptrs[block_id + 1] == next_phys_block);
                            assert(old_ptrs[next_phys_block_ind] == next_phys_block);
                            old(self).all_blocks.lemma_wf_nodup();
                            assert(ptrs_no_duplicates(old_ptrs));
                            lemma_ptrs_no_duplicates_eq_index(old_ptrs, block_id + 1, next_phys_block_ind);
                        };
                        assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(new_size as int)) by {
                            assert(old(self).all_blocks.wf_node(block_id));
                            assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size((block_size & SIZE_SIZE_MASK) as int));
                            assert(new_size % GRANULARITY == 0) by {
                                granularity_is_power_of_two();
                                lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                            };
                            assert(new_size <= block_size);
                            assert(GRANULARITY <= new_size) by {
                                if usize::BITS == 64 {
                                    assert(GRANULARITY == 32);
                                } else {
                                    assert(GRANULARITY == 16);
                                }
                                assert(size_of::<BlockHdr>() + size_of::<FreeLink>() == GRANULARITY) by (compute);
                                assert(new_size >= size_of::<BlockHdr>() + size_of::<FreeLink>());
                            };
                        };
                        assert forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                            implies self.all_blocks.wf_node(i)
                        by {
                            // {{{
                            let ptr = self.all_blocks.ptrs@[i];
                            if ptr == block {
                                assert(self.all_blocks.ptrs@[block_id] == block);
                                assert(self.all_blocks.ptrs@[block_id + 1] == new_free_block);
                                assert(i <= block_id) by {
                                    if block_id + 1 <= i {
                                        lemma_ghost_pointer_ordered_index(self.all_blocks.ptrs@, block_id + 1, i);
                                        assert((self.all_blocks.ptrs@[block_id + 1] as usize as int)
                                            <= (self.all_blocks.ptrs@[i] as usize as int));
                                        assert((new_free_block as usize as int)
                                            <= (self.all_blocks.ptrs@[i] as usize as int));
                                        assert((self.all_blocks.ptrs@[i] as usize as int)
                                            == (block as usize as int));
                                        assert((block as usize as int) < (new_free_block as usize as int));
                                    }
                                };
                                assert(i >= block_id) by {
                                    if i < block_id {
                                        assert(self.all_blocks.ptrs@[i] == old_ptrs[i]);
                                        assert(self.all_blocks.ptrs@[block_id] == old_ptrs[block_id]);
                                        assert(old_ptrs[i] == block);
                                        assert(old_ptrs[block_id] == block);
                                        lemma_ptrs_no_duplicates_eq_index(old_ptrs, i, block_id);
                                        assert(false);
                                    }
                                };
                                assert(i == block_id);
                                assert(self.all_blocks.wf_node(i)) by {
                                    assert(i == block_id);
                                    assert(ptr == block);
                                    assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(new_size as int));
                                    assert(self.all_blocks.value_at(ptr).size == (new_size | SIZE_USED));
                                    Self::lemma_mark_used_preserves_size_bits(new_size);
                                    assert((self.all_blocks.value_at(ptr).size & SIZE_SIZE_MASK) == new_size);
                                    assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(
                                        (self.all_blocks.value_at(ptr).size & SIZE_SIZE_MASK) as int));
                                    assert(!self.all_blocks.value_at(ptr).is_sentinel()) by {
                                        assert(new_size % GRANULARITY == 0) by {
                                            granularity_is_power_of_two();
                                            lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                                        };
                                        if usize::BITS == 64 {
                                            lemma_mod_by_multiple(new_size as int, 8, 4);
                                        } else {
                                            lemma_mod_by_multiple(new_size as int, 4, 4);
                                        }
                                        assert((((new_size | SIZE_USED) & SIZE_SENTINEL) == 0usize)) by (bit_vector)
                                            requires SIZE_USED == 1, SIZE_SENTINEL == 2, new_size as int % 4 == 0;
                                        assert(self.all_blocks.value_at(ptr).size == (new_size | SIZE_USED));
                                    };
                                    assert(!self.all_blocks.value_at(ptr).is_free()) by {
                                        assert(self.all_blocks.value_at(ptr).size == (new_size | SIZE_USED));
                                        assert(((new_size | SIZE_USED) & SIZE_USED) == SIZE_USED) by (bit_vector)
                                            requires SIZE_USED == 1;
                                    };
                                    assert(self.all_blocks.value_at(ptr).is_free() ==> {
                                        self.all_blocks.phys_next_of(i) matches Some(next_ptr)
                                            && !self.all_blocks.value_at(next_ptr).is_free()
                                    }) by {
                                        if self.all_blocks.value_at(ptr).is_free() {
                                            assert(false);
                                        }
                                    };
                                    assert(new_size < block_size);
                                    assert((self.all_blocks.value_at(ptr).size as int) + (ptr as int) < usize::MAX) by {
                                        assert(old(self).all_blocks.wf_node(block_id));
                                        assert((old(self).all_blocks.value_at(block).size as int) + (block as int) < usize::MAX);
                                        assert(old(self).all_blocks.value_at(block).size == block_size);
                                        assert(new_size % GRANULARITY == 0) by {
                                            granularity_is_power_of_two();
                                            lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                                        };
                                        assert(block_size % GRANULARITY == 0);
                                        assert(new_size + GRANULARITY <= block_size);
                                        assert((new_size | SIZE_USED) <= new_size + 1) by (bit_vector)
                                            requires SIZE_USED == 1;
                                        assert(new_size + 1 <= block_size);
                                        assert((new_size | SIZE_USED) <= block_size);
                                        assert(((new_size | SIZE_USED) as int) + (block as int) < (usize::MAX as int));
                                    };
                                };
                            } else if ptr == next_phys_block {
                                assert(i == next_phys_block_ind + 1) by {
                                    assert(self.all_blocks.ptrs@ == add_ghost_pointer(old_ptrs, new_free_block));
                                    lemma_add_ghost_pointer_insert_after_index(old_ptrs, new_free_block, block_id);
                                    old(self).all_blocks.lemma_wf_nodup();
                                    assert(ptrs_no_duplicates(old_ptrs));

                                    if i <= block_id {
                                        assert(self.all_blocks.ptrs@[i] == old_ptrs[i]);
                                        assert(old_ptrs[i] == next_phys_block);
                                        assert(old_ptrs[block_id + 1] == next_phys_block);
                                        lemma_ptrs_no_duplicates_eq_index(old_ptrs, i, block_id + 1);
                                        assert(i == block_id + 1);
                                        assert(false);
                                    } else if i == block_id + 1 {
                                        assert(self.all_blocks.ptrs@[i] == new_free_block);
                                        assert(old(self).all_blocks.wf_node(block_id));
                                        assert(old(self).all_blocks.phys_next_of(block_id) is Some);
                                        assert(old(self).all_blocks.phys_next_of(block_id).unwrap() == next_phys_block);
                                        assert((new_free_block as usize as int) == (block as usize as int) + new_size as int);
                                        assert((next_phys_block as usize as int) == (block as usize as int) + block_size as int);
                                        assert(new_size < block_size);
                                        assert((new_free_block as usize as int) < (next_phys_block as usize as int));
                                        assert(new_free_block != next_phys_block);
                                        assert(false);
                                    } else {
                                        assert(block_id + 1 < i);
                                        assert(self.all_blocks.ptrs@[i] == old_ptrs[i - 1]);
                                        assert(old_ptrs[i - 1] == next_phys_block);
                                        assert(old_ptrs[block_id + 1] == next_phys_block);
                                        lemma_ptrs_no_duplicates_eq_index(old_ptrs, i - 1, block_id + 1);
                                        assert(i - 1 == block_id + 1);
                                    }
                                    old(self).all_blocks.lemma_wf_nodup();
                                    assert(next_phys_block_ind == block_id + 1);
                                    assert(i == block_id + 2);
                                };
                                assert(self.all_blocks.wf_node(i)) by {
                                    assert(old(self).all_blocks.wf_node(next_phys_block_ind));
                                    assert(i == block_id + 2);
                                    assert(self.all_blocks.phys_prev_of(i) == Some(new_free_block));
                                    assert(self.all_blocks.value_at(ptr).prev_phys_block == new_free_block);
                                    assert(self.all_blocks.phys_next_of(i) == old(self).all_blocks.phys_next_of(next_phys_block_ind));
                                    assert(self.all_blocks.value_at(ptr).prev_phys_block@.addr != 0 ==> (
                                        self.all_blocks.phys_prev_of(i) matches Some(p)
                                            && p == self.all_blocks.value_at(ptr).prev_phys_block
                                    )) by {
                                        if self.all_blocks.value_at(ptr).prev_phys_block@.addr != 0 {
                                            assert(self.all_blocks.phys_prev_of(i) matches Some(p)
                                                && p == self.all_blocks.value_at(ptr).prev_phys_block);
                                        }
                                    };
                                    assert(self.all_blocks.phys_next_of(i) matches Some(next_ptr) ==> {
                                        &&& next_ptr@.addr == ptr@.addr + (self.all_blocks.value_at(ptr).size & SIZE_SIZE_MASK)
                                        &&& next_ptr@.provenance == ptr@.provenance
                                    }) by {
                                        if self.all_blocks.phys_next_of(i) matches Some(next_ptr) {
                                            let next_ptr = self.all_blocks.phys_next_of(i).unwrap();
                                            let old_next_ptr = old(self).all_blocks.phys_next_of(next_phys_block_ind).unwrap();
                                            assert(next_ptr == old_next_ptr);
                                            assert(old(self).all_blocks.wf_node(next_phys_block_ind));
                                            assert(old(self).all_blocks.phys_next_of(next_phys_block_ind) matches Some(old_p) ==> {
                                                &&& old_p@.addr == next_phys_block@.addr
                                                    + (old(self).all_blocks.value_at(next_phys_block).size & SIZE_SIZE_MASK)
                                                &&& old_p@.provenance == next_phys_block@.provenance
                                            });
                                            assert(old_next_ptr@.addr == next_phys_block@.addr
                                                + (old(self).all_blocks.value_at(next_phys_block).size & SIZE_SIZE_MASK));
                                            assert(old_next_ptr@.provenance == next_phys_block@.provenance);
                                            assert(ptr == next_phys_block);
                                            assert(self.all_blocks.value_at(ptr).size
                                                == old(self).all_blocks.value_at(next_phys_block).size);
                                            assert((self.all_blocks.value_at(ptr).size & SIZE_SIZE_MASK)
                                                == (old(self).all_blocks.value_at(next_phys_block).size & SIZE_SIZE_MASK));
                                            assert(next_ptr@.addr == ptr@.addr
                                                + (self.all_blocks.value_at(ptr).size & SIZE_SIZE_MASK));
                                            assert(next_ptr@.provenance == ptr@.provenance);
                                        }
                                    };
                                    assert(!self.all_blocks.value_at(ptr).is_free()) by {
                                        assert(!old(self).all_blocks.value_at(next_phys_block).is_free());
                                        assert(self.all_blocks.value_at(ptr).size
                                            == old(self).all_blocks.value_at(next_phys_block).size);
                                    };
                                };
                            } else if ptr == new_free_block {
                                assert(i == block_id + 1) by {
                                    assert(self.all_blocks.ptrs@ == add_ghost_pointer(old_ptrs, new_free_block));
                                    lemma_add_ghost_pointer_insert_point(old_ptrs, new_free_block, block_id);
                                    assert(self.all_blocks.ptrs@[block_id + 1] == new_free_block);
                                    assert(ghost_pointer_ordered(self.all_blocks.ptrs@));
                                    assert((block as usize as int) < (new_free_block as usize as int)) by {
                                        assert(new_free_block as int == block as int + new_size as int);
                                        assert(new_size > 0);
                                    };
                                    assert((new_free_block as usize as int) < (next_phys_block as usize as int)) by {
                                        assert(new_free_block as int == block as int + new_size as int);
                                        assert(next_phys_block as int == block as int + block_size as int);
                                        assert(new_size < block_size);
                                    };
                                    assert(!(i < block_id + 1)) by {
                                        if i < block_id + 1 {
                                            if i < block_id {
                                                assert(0 <= i < self.all_blocks.ptrs@.len());
                                                assert(0 <= block_id < self.all_blocks.ptrs@.len());
                                                lemma_ghost_pointer_ordered_index(self.all_blocks.ptrs@, i, block_id);
                                                assert((ptr as usize as int) <= (block as usize as int));
                                                assert((block as usize as int) < (new_free_block as usize as int));
                                                assert(ptr == new_free_block);
                                                assert(false);
                                            } else {
                                                assert(i == block_id);
                                                assert(ptr == self.all_blocks.ptrs@[block_id]);
                                                assert(ptr == block);
                                                assert((block as usize as int) < (new_free_block as usize as int));
                                                assert(ptr == new_free_block);
                                                assert(false);
                                            }
                                        }
                                    };
                                    assert(!(block_id + 1 < i)) by {
                                        if block_id + 1 < i {
                                            if i == block_id + 2 {
                                                assert(ptr == self.all_blocks.ptrs@[block_id + 2]);
                                                assert(ptr == next_phys_block);
                                                assert((new_free_block as usize as int) < (next_phys_block as usize as int));
                                                assert(ptr == new_free_block);
                                                assert(false);
                                            } else {
                                                assert(block_id + 2 < i);
                                                assert(0 <= block_id + 2 < self.all_blocks.ptrs@.len());
                                                assert(0 <= i < self.all_blocks.ptrs@.len());
                                                lemma_ghost_pointer_ordered_index(self.all_blocks.ptrs@, block_id + 2, i);
                                                assert((next_phys_block as usize as int) <= (ptr as usize as int));
                                                assert((new_free_block as usize as int) < (next_phys_block as usize as int));
                                                assert(ptr == new_free_block);
                                                assert(false);
                                            }
                                        }
                                    };
                                    assert(block_id + 1 <= i);
                                    assert(i <= block_id + 1);
                                    assert(i == block_id + 1);
                                };
                                assert(new_free_block@.addr != 0) by {
                                    assert(block@.addr != 0);
                                    assert(new_size > 0);
                                };
                                assert(0 <= new_free_block@.addr);
                                assert((new_free_block@.addr as int) % (GRANULARITY as int) == 0) by {
                                    assert(block@.addr % GRANULARITY == 0) by {
                                        old(self).all_blocks.lemma_wf_node_ptr(block_id);
                                    };
                                    assert(new_size % GRANULARITY == 0) by {
                                        granularity_is_power_of_two();
                                        lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                                    };
                                };
                                AllBlocks::<FLLEN, SLLEN>::lemma_wf_node_ptr_from_facts(new_free_block);
                                assert(self.all_blocks.wf_node(i)) by {
                                    assert(i == block_id + 1);
                                    assert(ptr == new_free_block);
                                    assert(self.all_blocks.perms@[ptr].wf()) by {
                                        assert(ptr == new_free_block);
                                        assert(self.all_blocks.perms@[new_free_block].wf());
                                    };
                                    assert(self.all_blocks.value_at(ptr).size == new_free_block_size);
                                    Self::lemma_mark_used_preserves_size_bits(new_free_block_size);
                                    assert((self.all_blocks.value_at(ptr).size & SIZE_SIZE_MASK) == new_free_block_size);
                                    assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(
                                        (self.all_blocks.value_at(ptr).size & SIZE_SIZE_MASK) as int));
                                    assert(!self.all_blocks.value_at(ptr).is_sentinel()) by {
                                        if usize::BITS == 64 {
                                            lemma_mod_by_multiple(new_free_block_size as int, 8, 4);
                                        } else {
                                            lemma_mod_by_multiple(new_free_block_size as int, 4, 4);
                                        }
                                        assert(((new_free_block_size & SIZE_SENTINEL) == 0usize)) by (bit_vector)
                                            requires SIZE_SENTINEL == 2, new_free_block_size as int % 4 == 0;
                                        assert(self.all_blocks.value_at(ptr).size == new_free_block_size);
                                    };
                                    assert(old(self).all_blocks.wf_node(block_id));
                                    assert(block_id + 1 < old_ptrs.len());
                                    assert(block_id + 2 < self.all_blocks.ptrs@.len());
                                    assert(self.all_blocks.ptrs@[block_id + 2] == next_phys_block);
                                    assert(self.all_blocks.phys_next_of(i) is Some);
                                    assert(self.all_blocks.phys_next_of(i).unwrap() == next_phys_block);
                                    assert(!self.all_blocks.value_at(self.all_blocks.phys_next_of(i).unwrap()).is_free()) by {
                                        assert(old(self).all_blocks.wf_node(block_id));
                                        assert(old(self).all_blocks.phys_next_of(block_id) is Some);
                                        assert(old(self).all_blocks.phys_next_of(block_id).unwrap() == next_phys_block);
                                        assert(!old(self).all_blocks.value_at(next_phys_block).is_free());
                                        assert(self.all_blocks.value_at(next_phys_block).size
                                            == old(self).all_blocks.value_at(next_phys_block).size);
                                    };
                                    assert(self.all_blocks.value_at(ptr).is_free() ==> {
                                        self.all_blocks.phys_next_of(i) matches Some(next_ptr)
                                            && !self.all_blocks.value_at(next_ptr).is_free()
                                    }) by {
                                        if self.all_blocks.value_at(ptr).is_free() {
                                            assert(self.all_blocks.phys_next_of(i) is Some);
                                            let next_ptr = self.all_blocks.phys_next_of(i).unwrap();
                                            assert(next_ptr == next_phys_block);
                                            assert(!self.all_blocks.value_at(next_ptr).is_free());
                                        }
                                    };
                                };
                            } else {
                                assert(old(self).all_blocks.ptrs@.contains(ptr)) by {
                                    assert(self.all_blocks.ptrs@.contains(ptr));
                                    assert(self.all_blocks.ptrs@ == add_ghost_pointer(old(self).all_blocks.ptrs@, new_free_block));
                                    assert(add_ghost_pointer(old(self).all_blocks.ptrs@, new_free_block).contains(ptr));
                                    assert(ptr != new_free_block);
                                    assert(i != block_id + 1) by {
                                        if i == block_id + 1 {
                                            assert(self.all_blocks.ptrs@[block_id + 1] == new_free_block);
                                            assert(ptr == self.all_blocks.ptrs@[i]);
                                            assert(ptr == new_free_block);
                                        }
                                    };
                                    if i <= block_id {
                                        assert(self.all_blocks.ptrs@[i] == old_ptrs[i]);
                                        assert(ptr == old_ptrs[i]);
                                        assert(old_ptrs.contains(ptr));
                                    } else {
                                        assert(block_id + 1 < i);
                                        assert(self.all_blocks.ptrs@[i] == old_ptrs[i - 1]);
                                        assert(ptr == old_ptrs[i - 1]);
                                        assert(old_ptrs.contains(ptr));
                                    }
                                };
                                let ghost old_i = old(self).all_blocks.get_ptr_internal_index(ptr);
                                assert(old(self).all_blocks.wf_node(old_i));
                                assert(self.all_blocks.wf_node(i)) by {
                                    assert(old(self).all_blocks.wf_node(old_i));
                                    assert(old(self).all_blocks.value_at(block).is_free()) by {
                                        old(self).freelist_nonempty(idx);
                                        old(self).lemma_freelist_wf_extract_wf_free_node(idx, 0);
                                        assert(old(self).wf_free_node(idx, 0));
                                        assert(old(self).shadow_freelist@.m[idx].first()
                                            == old(self).first_free[idx.0 as int][idx.1 as int]);
                                        assert(old(self).first_free[idx.0 as int][idx.1 as int] == block);
                                        assert(old(self).shadow_freelist@.m[idx][0]
                                            == old(self).shadow_freelist@.m[idx].first());
                                        assert(old(self).all_blocks.value_at(old(self).shadow_freelist@.m[idx][0]).is_free());
                                    };
                                    assert(self.all_blocks.ptrs@[block_id] == block);
                                    assert(self.all_blocks.ptrs@[block_id + 1] == new_free_block);
                                    assert(self.all_blocks.ptrs@[block_id + 2] == next_phys_block);
                                    assert(i != block_id + 1) by {
                                        if i == block_id + 1 {
                                            assert(ptr == self.all_blocks.ptrs@[block_id + 1]);
                                            assert(ptr == new_free_block);
                                        }
                                    };
                                    assert(i < block_id || block_id + 1 < i) by {
                                        if !(i < block_id || block_id + 1 < i) {
                                            assert(i == block_id || i == block_id + 1);
                                            if i == block_id {
                                                assert(ptr == self.all_blocks.ptrs@[block_id]);
                                                assert(ptr == block);
                                            } else {
                                                assert(ptr == self.all_blocks.ptrs@[block_id + 1]);
                                                assert(ptr == new_free_block);
                                            }
                                        }
                                    };
                                    if i < block_id {
                                        assert(self.all_blocks.ptrs@[i] == old_ptrs[i]);
                                        assert(ptr == old_ptrs[i]);
                                        assert(old(self).all_blocks.wf_node(i));
                                        assert(self.all_blocks.value_at(ptr) == old(self).all_blocks.value_at(ptr));
                                        assert(self.all_blocks.phys_prev_of(i) == old(self).all_blocks.phys_prev_of(i));
                                        assert(self.all_blocks.phys_next_of(i) == old(self).all_blocks.phys_next_of(i));
                                        assert(self.all_blocks.value_at(ptr).prev_phys_block@.addr != 0 ==> (
                                            self.all_blocks.phys_prev_of(i) matches Some(p)
                                                && p == self.all_blocks.value_at(ptr).prev_phys_block
                                        ));
                                        assert(self.all_blocks.phys_next_of(i) matches Some(next_ptr) ==> {
                                            &&& next_ptr@.addr == ptr@.addr + (self.all_blocks.value_at(ptr).size & SIZE_SIZE_MASK)
                                            &&& next_ptr@.provenance == ptr@.provenance
                                        });
                                        assert(self.all_blocks.value_at(ptr).is_free() ==> {
                                            self.all_blocks.phys_next_of(i) matches Some(next_ptr)
                                                && !self.all_blocks.value_at(next_ptr).is_free()
                                        }) by {
                                            if self.all_blocks.value_at(ptr).is_free() {
                                                assert(old(self).all_blocks.value_at(ptr).is_free());
                                                assert(old(self).all_blocks.wf_node(i));
                                                assert(old(self).all_blocks.phys_next_of(i) matches Some(next_ptr)
                                                    && !old(self).all_blocks.value_at(next_ptr).is_free());
                                                let next_ptr = old(self).all_blocks.phys_next_of(i).unwrap();
                                                assert(self.all_blocks.phys_next_of(i) is Some);
                                                assert(self.all_blocks.phys_next_of(i).unwrap() == next_ptr);
                                                if next_ptr == block {
                                                    assert(!old(self).all_blocks.value_at(next_ptr).is_free());
                                                    assert(old(self).all_blocks.value_at(block).is_free());
                                                    assert(false);
                                                } else if next_ptr == next_phys_block {
                                                    assert(self.all_blocks.value_at(next_ptr).size
                                                        == old(self).all_blocks.value_at(next_ptr).size);
                                                } else {
                                                    assert(next_ptr == old_ptrs[i + 1]);
                                                    assert(i + 1 < old_ptrs.len());
                                                    assert(old(self).all_blocks.wf_node(i + 1));
                                                    assert(self.all_blocks.ptrs@[i + 1] == old_ptrs[i + 1]);
                                                    assert(next_ptr != block);
                                                    assert(next_ptr != next_phys_block);
                                                    assert(i < block_id);
                                                    assert(i + 1 < block_id) by {
                                                        if i + 1 == block_id {
                                                            assert(old_ptrs[block_id] == block);
                                                            assert(next_ptr == old_ptrs[block_id]);
                                                            assert(next_ptr == block);
                                                        }
                                                    };
                                                    assert(ghost_pointer_ordered(old_ptrs));
                                                    assert(0 <= i + 1 < old_ptrs.len());
                                                    assert(0 <= block_id < old_ptrs.len());
                                                    lemma_ghost_pointer_ordered_index(old_ptrs, i + 1, block_id);
                                                    assert((next_ptr as usize as int) <= (block as usize as int));
                                                    assert((block as usize as int) < (new_free_block as usize as int));
                                                    assert(next_ptr != new_free_block) by {
                                                        if next_ptr == new_free_block {
                                                            assert((new_free_block as usize as int) <= (block as usize as int));
                                                            assert((block as usize as int) < (new_free_block as usize as int));
                                                            assert(false);
                                                        }
                                                    };
                                                    assert(self.all_blocks.perms@[next_ptr]
                                                        == old(self).all_blocks.perms@[next_ptr]);
                                                }
                                                assert(!self.all_blocks.value_at(next_ptr).is_free());
                                            }
                                        };
                                    } else {
                                        assert(block_id + 1 < i);
                                        assert(i != block_id + 2) by {
                                            if i == block_id + 2 {
                                                assert(ptr == self.all_blocks.ptrs@[block_id + 2]);
                                                assert(ptr == next_phys_block);
                                            }
                                        };
                                        assert(block_id + 2 < i);
                                        assert(self.all_blocks.ptrs@[i] == old_ptrs[i - 1]);
                                        assert(ptr == old_ptrs[i - 1]);
                                        assert(old(self).all_blocks.wf_node(i - 1));
                                        assert(self.all_blocks.value_at(ptr) == old(self).all_blocks.value_at(ptr));
                                        assert(self.all_blocks.phys_prev_of(i) == old(self).all_blocks.phys_prev_of(i - 1));
                                        assert(self.all_blocks.phys_next_of(i) == old(self).all_blocks.phys_next_of(i - 1));
                                        assert(self.all_blocks.value_at(ptr).prev_phys_block@.addr != 0 ==> (
                                            self.all_blocks.phys_prev_of(i) matches Some(p)
                                                && p == self.all_blocks.value_at(ptr).prev_phys_block
                                        ));
                                        assert(self.all_blocks.phys_next_of(i) matches Some(next_ptr) ==> {
                                            &&& next_ptr@.addr == ptr@.addr + (self.all_blocks.value_at(ptr).size & SIZE_SIZE_MASK)
                                            &&& next_ptr@.provenance == ptr@.provenance
                                        });
                                        assert(self.all_blocks.value_at(ptr).is_free() ==> {
                                            self.all_blocks.phys_next_of(i) matches Some(next_ptr)
                                                && !self.all_blocks.value_at(next_ptr).is_free()
                                        }) by {
                                            if self.all_blocks.value_at(ptr).is_free() {
                                                assert(old(self).all_blocks.value_at(ptr).is_free());
                                                assert(old(self).all_blocks.wf_node(i - 1));
                                                assert(old(self).all_blocks.phys_next_of(i - 1) matches Some(next_ptr)
                                                    && !old(self).all_blocks.value_at(next_ptr).is_free());
                                                let next_ptr = old(self).all_blocks.phys_next_of(i - 1).unwrap();
                                                assert(self.all_blocks.phys_next_of(i) is Some);
                                                assert(self.all_blocks.phys_next_of(i).unwrap() == next_ptr);
                                                if next_ptr == block {
                                                    assert(!old(self).all_blocks.value_at(next_ptr).is_free());
                                                    assert(old(self).all_blocks.value_at(block).is_free());
                                                    assert(false);
                                                } else if next_ptr == next_phys_block {
                                                    assert(self.all_blocks.value_at(next_ptr).size
                                                        == old(self).all_blocks.value_at(next_ptr).size);
                                                } else {
                                                    assert(next_ptr == old_ptrs[i]);
                                                    assert(i < old_ptrs.len());
                                                    assert(old(self).all_blocks.wf_node(i));
                                                    assert(self.all_blocks.ptrs@[i + 1] == old_ptrs[i]);
                                                    assert(next_ptr != block);
                                                    assert(next_ptr != next_phys_block);
                                                    assert(ghost_pointer_ordered(old_ptrs));
                                                    assert(0 <= block_id + 1 < old_ptrs.len());
                                                    assert(0 <= i < old_ptrs.len());
                                                    lemma_ghost_pointer_ordered_index(old_ptrs, block_id + 1, i);
                                                    assert((next_phys_block as usize as int) <= (next_ptr as usize as int));
                                                    assert((new_free_block as usize as int) < (next_phys_block as usize as int)) by {
                                                        assert(new_free_block as int == block as int + new_size as int);
                                                        assert(next_phys_block as int == block as int + block_size as int);
                                                        assert(new_size < block_size);
                                                    };
                                                    assert(next_ptr != new_free_block) by {
                                                        if next_ptr == new_free_block {
                                                            assert((next_phys_block as usize as int) <= (new_free_block as usize as int));
                                                            assert((new_free_block as usize as int) < (next_phys_block as usize as int));
                                                            assert(false);
                                                        }
                                                    };
                                                    assert(self.all_blocks.perms@[next_ptr]
                                                        == old(self).all_blocks.perms@[next_ptr]);
                                                }
                                                assert(!self.all_blocks.value_at(next_ptr).is_free());
                                            }
                                        };
                                    }
                                };
                            }
                            // }}}
                        };
                        // }}}
                    };
                    // --- Prove all_freelist_wf + bitmap_sync via big-step lemma ---
                    // Pre-establish facts used by both perm-equality foralls below (called ONCE).
                    assert(next_free_candidate@.addr != 0 ==>
                        old(self).shadow_freelist@.m[idx].len() > 1
                        && next_free_candidate == old(self).shadow_freelist@.m[idx][1]) by {
                        if next_free_candidate@.addr != 0 {
                            old(self).lemma_freelist_wf_extract_wf_free_node(idx, 0);
                            assert(old(self).wf_free_node(idx, 0));
                            old(self).lemma_freelist_len_gt1_from_nonnull_next(idx);
                            old(self).lemma_wf_free_node_next_addr(idx, 0);
                        }
                    };
                    // shadow_freelist_nodup: established once, used by both foralls via lemma_nodup_get
                    proof { old(self).lemma_shadow_list_no_duplicates(); }
                    // m[idx][0] == block (for lemma_nodup_get(bi,n,idx,0))
                    assert(old(self).shadow_freelist@.m[idx][0] == block) by {
                        old(self).wf_index_in_freelist(idx);
                        old(self).freelist_nonempty(idx);
                    };
                    // next_phys_block is NOT in any old freelist (proved once, not per-node)
                    assert forall|bi: BlockIndex<FLLEN, SLLEN>, k: int|
                        bi.wf() && 0 <= k < old(self).shadow_freelist@.m[bi].len()
                        implies #[trigger] old(self).shadow_freelist@.m[bi][k] != next_phys_block
                    by {
                        if old(self).shadow_freelist@.m[bi][k] == next_phys_block {
                            old(self).wf_index_in_freelist(bi);
                            old(self).lemma_freelist_wf_extract_wf_free_node(bi, k);
                            assert(old(self).wf_free_node(bi, k));
                            assert(old(self).all_blocks.value_at(old(self).shadow_freelist@.m[bi][k]).is_free());
                            assert(!old(self).all_blocks.value_at(next_phys_block).is_free());
                            assert(false);
                        }
                    };
                    assert(self.shadow_ptrs_nonnull()) by {
                        let ghost sfl_before_shift =
                            old(self).shadow_freelist@.ii_remove_for_index(old(self).all_blocks, idx, 0);
                        Self::lemma_ii_remove_for_index_ensures(old(self).shadow_freelist@, old(self).all_blocks, idx, 0);
                        assert(self.shadow_freelist@.m[idx] == sfl_before_shift.m[idx]);
                        assert(sfl_before_shift.m[idx] == old(self).shadow_freelist@.m[idx].remove(0));
                        Self::lemma_shadow_ptrs_nonnull_after_pop(*old(self), *self, idx);
                    };
                    assert(self.wf_shadow());
                    // Perm preservation for bi != idx freelist nodes
                    assert forall|bi: BlockIndex<FLLEN, SLLEN>, n: int|
                        bi.wf() && bi != idx && 0 <= n < old(self).shadow_freelist@.m[bi].len()
                        implies #[trigger] self.all_blocks.perms@[old(self).shadow_freelist@.m[bi][n]]
                            == old(self).all_blocks.perms@[old(self).shadow_freelist@.m[bi][n]]
                    by {
                        let ghost old_ptrs = old(self).all_blocks.ptrs@;
                        let node = old(self).shadow_freelist@.m[bi][n];
                        // node != block (= m[idx][0]): cross-list uniqueness
                        assert(node != block) by {
                            old(self).lemma_nodup_get(bi, n, idx, 0);
                        };
                        // node != next_phys_block (from pre-proved forall)
                        assert(node != next_phys_block);
                        // node != new_free_block (not in old ptrs)
                        assert(node != new_free_block) by {
                            if node == new_free_block {
                                assert(old(self).all_blocks.ptrs@.contains(node)) by {
                                    assert(old(self).is_ii());
                                    assert(0 <= old(self).shadow_freelist@.pi[(bi, n)] < old_ptrs.len());
                                    assert(old(self).shadow_freelist@.m[bi][n]
                                        == old_ptrs[old(self).shadow_freelist@.pi[(bi, n)]]);
                                };
                                let i = choose|i: int| 0 <= i < old_ptrs.len() && old_ptrs[i] == new_free_block;
                                assert(ghost_pointer_ordered(old_ptrs));
                                assert(0 <= block_id + 1 < old_ptrs.len());
                                if i <= block_id {
                                    lemma_ghost_pointer_ordered_index(old_ptrs, i, block_id);
                                } else {
                                    lemma_ghost_pointer_ordered_index(old_ptrs, block_id + 1, i);
                                }
                                assert(false);
                            }
                        };
                        assert(self.all_blocks.perms@[node] == old(self).all_blocks.perms@[node]) by {
                            if next_free_candidate@.addr != 0 {
                                // node != nfc (= m[idx][1]): cross-list uniqueness
                                assert(old(self).shadow_freelist@.m[idx].len() > 1);
                                assert(next_free_candidate == old(self).shadow_freelist@.m[idx][1]);
                                old(self).lemma_nodup_get(bi, n, idx, 1);
                                assert(node != next_free_candidate);
                            }
                        };
                    };
                    // Perm preservation for idx positions >= 2
                    assert forall|n: int| 1 < n < old(self).shadow_freelist@.m[idx].len()
                        implies self.all_blocks.perms@[old(self).shadow_freelist@.m[idx][n]]
                            == old(self).all_blocks.perms@[old(self).shadow_freelist@.m[idx][n]]
                    by {
                        let ghost old_ptrs = old(self).all_blocks.ptrs@;
                        let node = old(self).shadow_freelist@.m[idx][n];
                        // node != block (pos 0): same-list uniqueness
                        assert(node != block) by {
                            old(self).lemma_nodup_get(idx, 0, idx, n);
                        };
                        // node != next_phys_block (from pre-proved forall)
                        assert(node != next_phys_block);
                        assert(node != new_free_block) by {
                            if node == new_free_block {
                                assert(old(self).all_blocks.ptrs@.contains(node)) by {
                                    assert(old(self).is_ii());
                                    assert(0 <= old(self).shadow_freelist@.pi[(idx, n)] < old_ptrs.len());
                                    assert(old(self).shadow_freelist@.m[idx][n]
                                        == old_ptrs[old(self).shadow_freelist@.pi[(idx, n)]]);
                                };
                                let i = choose|i: int| 0 <= i < old_ptrs.len() && old_ptrs[i] == new_free_block;
                                assert(ghost_pointer_ordered(old_ptrs));
                                assert(0 <= block_id + 1 < old_ptrs.len());
                                if i <= block_id {
                                    lemma_ghost_pointer_ordered_index(old_ptrs, i, block_id);
                                } else {
                                    lemma_ghost_pointer_ordered_index(old_ptrs, block_id + 1, i);
                                }
                                assert(false);
                            }
                        };
                        assert(self.all_blocks.perms@[node] == old(self).all_blocks.perms@[node]) by {
                            if next_free_candidate@.addr != 0 {
                                // node != nfc (= m[idx][1]): same-list uniqueness
                                assert(old(self).shadow_freelist@.m[idx].len() > 1);
                                assert(next_free_candidate == old(self).shadow_freelist@.m[idx][1]);
                                old(self).lemma_nodup_get(idx, 1, idx, n);
                                assert(node != next_free_candidate);
                            }
                        };
                    };
                    // next_free conditions: old[1] == next_free, perms partially preserved
                    assert(old(self).shadow_freelist@.m[idx].len() > 1 ==> (
                        old(self).shadow_freelist@.m[idx][1] == next_free_candidate
                        && self.all_blocks.perms@[next_free_candidate].points_to
                            == old(self).all_blocks.perms@[next_free_candidate].points_to
                        && self.all_blocks.perms@[next_free_candidate].mem
                            == old(self).all_blocks.perms@[next_free_candidate].mem
                        && self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().prev_free@.addr == 0
                        && self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free
                            == old(self).all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free
                    )) by {
                        if old(self).shadow_freelist@.m[idx].len() > 1 {
                            old(self).lemma_freelist_wf_extract_wf_free_node(idx, 0);
                            old(self).lemma_wf_free_node_next_addr(idx, 0);
                            assert(Some(next_free_candidate) == Self::free_next_of(old(self).shadow_freelist@.m[idx], 0));
                            assert(next_free_candidate == old(self).shadow_freelist@.m[idx][1]);
                            assert(next_free_candidate@.addr != 0);
                            assert(self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free
                                == next_next_free_candidate);
                            assert(next_next_free_candidate
                                == old(self).all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free) by {
                                assert(new_head_perm == old(self).all_blocks.perms@[next_free_candidate]);
                            };
                        }
                    };
                    // Singleton list → next_free is null
                    assert(old(self).shadow_freelist@.m[idx].len() == 1 ==> next_free_candidate@.addr == 0) by {
                        if next_free_candidate@.addr != 0 {
                            old(self).lemma_freelist_wf_extract_wf_free_node(idx, 0);
                            old(self).lemma_freelist_len_gt1_from_nonnull_next(idx);
                        }
                    };
                    // Call big-step lemma: proves all_freelist_wf() + bitmap_sync()
                    proof { Self::lemma_pop_head_preserves_wf(*old(self), *self, idx, next_free_candidate); }
                    assert(self.all_freelist_wf());
                    assert(self.bitmap_wf());
                    assert(self.bitmap_sync());
                    assert(!(self.shadow_freelist.contains(new_free_block))) by {
                        // {{{
                        let ghost old_ptrs = old(self).all_blocks.ptrs@;
                        let ghost sfl_after_remove =
                            old(self).shadow_freelist@.ii_remove_for_index(old(self).all_blocks, idx, 0);
                        Self::lemma_ii_remove_for_index_ensures(old(self).shadow_freelist@, old(self).all_blocks, idx, 0);

                        assert(!old_ptrs.contains(new_free_block)) by {
                            if old_ptrs.contains(new_free_block) {
                                let i = choose|i: int| 0 <= i < old_ptrs.len() && old_ptrs[i] == new_free_block;
                                assert(ghost_pointer_ordered(old_ptrs));
                                assert(0 <= block_id + 1 < old_ptrs.len());
                                if i <= block_id {
                                    lemma_ghost_pointer_ordered_index(old_ptrs, i, block_id);
                                } else {
                                    lemma_ghost_pointer_ordered_index(old_ptrs, block_id + 1, i);
                                }
                                assert(old_ptrs[i] == new_free_block);
                                assert(false);
                            }
                        };

                        assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf()
                            implies !self.shadow_freelist@.m[bi].contains(new_free_block)
                        by {
                            if self.shadow_freelist@.m[bi].contains(new_free_block) {
                                let n = choose|n: int| 0 <= n < self.shadow_freelist@.m[bi].len()
                                    && self.shadow_freelist@.m[bi][n] == new_free_block;
                                assert(self.shadow_freelist@.m[bi] == sfl_after_remove.m[bi]);
                                assert(sfl_after_remove.m[bi][n] == new_free_block);
                                assert(old(self).shadow_freelist@.m[bi].contains(new_free_block)) by {
                                    if bi == idx {
                                        assert(sfl_after_remove.m[bi] == old(self).shadow_freelist@.m[bi].remove(0));
                                        assert(old(self).shadow_freelist@.m[bi].remove(0).contains(new_free_block));
                                    } else {
                                        assert(sfl_after_remove.m[bi] == old(self).shadow_freelist@.m[bi]);
                                        assert(old(self).shadow_freelist@.m[bi].contains(new_free_block));
                                    }
                                };
                                assert(old_ptrs.contains(new_free_block)) by {
                                    let m = choose|m: int| 0 <= m < old(self).shadow_freelist@.m[bi].len()
                                        && old(self).shadow_freelist@.m[bi][m] == new_free_block;
                                    assert(old(self).is_ii());
                                    assert(0 <= old(self).shadow_freelist@.pi[(bi, m)] < old_ptrs.len());
                                    assert(old(self).shadow_freelist@.m[bi][m]
                                        == old_ptrs[old(self).shadow_freelist@.pi[(bi, m)]]);
                                };
                                assert(false);
                            }
                        };
                        // }}}
                    };

                    //proof {
                        //assert(new_free_block_size == self.all_blocks.perms@[new_free_block].points_to.value().size);
                        //assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(new_free_block_size as int));
                    //}

                    let new_block_idx = Self::map_floor(new_free_block_size).unwrap();
                    let ghost ptrs_before_link = self.all_blocks.ptrs@;
                    proof {
                        assert(old(self).size_class_condition());
                        assert(Self::shadow_freelist_popped_at(old(self).shadow_freelist@, self.shadow_freelist@, idx)) by {
                            reveal(Tlsf::shadow_freelist_popped_at);
                            assert(self.shadow_freelist@.m[idx] == old(self).shadow_freelist@.m[idx].remove(0));
                            assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != idx
                                implies self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]
                            by {
                                assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]);
                            };
                        };
                        assert(Self::perms_size_unchanged_for_freelist(old(self).shadow_freelist@, old(self).all_blocks, self.all_blocks, block)) by {
                            reveal(Tlsf::perms_size_unchanged_for_freelist);
                            let ghost old_ptrs_g = old(self).all_blocks.ptrs@;
                            assert(!old_ptrs_g.contains(new_free_block)) by {
                                if old_ptrs_g.contains(new_free_block) {
                                    let i = choose|i: int| 0 <= i < old_ptrs_g.len() && old_ptrs_g[i] == new_free_block;
                                    assert(ghost_pointer_ordered(old_ptrs_g));
                                    assert(0 <= block_id + 1 < old_ptrs_g.len());
                                    if i <= block_id {
                                        lemma_ghost_pointer_ordered_index(old_ptrs_g, i, block_id);
                                    } else {
                                        lemma_ghost_pointer_ordered_index(old_ptrs_g, block_id + 1, i);
                                    }
                                    assert(false);
                                }
                            };
                            assert forall|bi: BlockIndex<FLLEN, SLLEN>, i: int|
                                bi.wf() && 0 <= i < old(self).shadow_freelist@.m[bi].len() && old(self).shadow_freelist@.m[bi][i] != block
                                    implies self.all_blocks.perms@[old(self).shadow_freelist@.m[bi][i]].points_to.value().size
                                        == old(self).all_blocks.perms@[old(self).shadow_freelist@.m[bi][i]].points_to.value().size
                            by {
                                let node = old(self).shadow_freelist@.m[bi][i];
                                old(self).wf_index_in_freelist(bi);
                                old(self).lemma_freelist_wf_extract_wf_free_node(bi, i);
                                assert(node != next_phys_block) by {
                                    if node == next_phys_block {
                                        assert(old(self).wf_free_node(bi, i));
                                        assert(old(self).all_blocks.wf_node(block_id));
                                        assert(old(self).all_blocks.value_at(block).is_free());
                                        assert(old(self).all_blocks.phys_next_of(block_id) is Some);
                                        assert(old(self).all_blocks.phys_next_of(block_id).unwrap() == next_phys_block);
                                        assert(!old(self).all_blocks.value_at(next_phys_block).is_free());
                                        assert(old(self).all_blocks.value_at(node).is_free());
                                        assert(false);
                                    }
                                };
                                assert(node != new_free_block) by {
                                    assert(!old_ptrs_g.contains(new_free_block));
                                    assert(old_ptrs_g.contains(node)) by {
                                        assert(is_identity_injection(old(self).shadow_freelist@, old_ptrs_g));
                                        let ghost j = old(self).shadow_freelist@.pi[(bi, i)];
                                        assert(0 <= j < old_ptrs_g.len());
                                        assert(old(self).shadow_freelist@.m[bi][i] == old_ptrs_g[j]);
                                        assert(old_ptrs_g[j] == node);
                                    };
                                };
                                if next_free_candidate@.addr != 0 && node == next_free_candidate {
                                    assert(next_free_candidate@.addr != 0 ==> (
                                        self.all_blocks.perms@[next_free_candidate].points_to
                                            == old(self).all_blocks.perms@[next_free_candidate].points_to
                                        && self.all_blocks.perms@[next_free_candidate].mem
                                            == old(self).all_blocks.perms@[next_free_candidate].mem
                                    ));
                                } else {
                                    if next_free_candidate@.addr != 0 {
                                        assert(node != next_free_candidate);
                                    }
                                    assert(self.all_blocks.perms@[node] == perms_after_removing_block[node]);
                                    assert(perms_after_removing_block[node] == old(self).all_blocks.perms@[node]);
                                }
                            };
                        };
                        old(self).lemma_shadow_list_no_duplicates();
                        Self::lemma_size_class_after_pop(*old(self), *self, idx, block);
                    }

                    self.link_free_block(new_block_idx, new_free_block);

                    proof {
                        let ghost old_ptrs = old(self).all_blocks.ptrs@;
                        assert(old_ptrs[block_id] == block);
                        assert(old_ptrs.contains(block));
                        lemma_add_ghost_pointer_ensures(old_ptrs, new_free_block);
                        assert(ptrs_before_link == add_ghost_pointer(old_ptrs, new_free_block));
                        assert(ptrs_before_link.contains(block));
                        assert(self.all_blocks.ptrs@ == ptrs_before_link);
                        assert(self.all_blocks.ptrs@.contains(block));
                        self.all_blocks.lemma_contains(block);
                        assert(self.all_blocks.perms@.contains_key(block));
                        tlsf_before_final_remove = *self;
                        ab_before_final_remove = self.all_blocks;
                        new_block_perm = self.all_blocks.perms.borrow_mut().tracked_remove(block);
                        assert(new_block_perm == ab_before_final_remove.perms@[block]);
                    }
                }
            }
            //proof { admit(); } // -----------------------
            proof {
                assert(new_block_perm.points_to.value().size == (new_size | SIZE_USED));
                assert(!new_block_perm.points_to.value().is_free()) by {
                    assert(((new_size | SIZE_USED) & SIZE_USED) == SIZE_USED) by (bit_vector)
                        requires SIZE_USED == 1;
                    assert((new_block_perm.points_to.value().size & SIZE_USED) == SIZE_USED);
                };
            }

            //// Place a `UsedBlockPad` (used by `used_block_hdr_for_allocation`)
            let ghost mem_dom_before_pad = new_block_perm.mem.dom();
            proof {
                assert(mem_dom_before_pad
                    == set_int_range(
                        block as int + size_of::<BlockHdr>() as int,
                        block as int + new_size as int,
                    )) by {
                    assert(new_block_perm.mem.is_range(
                        block as int + size_of::<BlockHdr>() as int,
                        new_size as int - size_of::<BlockHdr>() as int
                    ));
                };
            }
            if align >= GRANULARITY {
                let pad_ptr = UsedBlockPad::get_for_allocation(ptr);
                let pad_addr = pad_ptr as usize;
                proof {
                    let ghost ptr_v = ptr@;
                    let ghost block_v = block@;
                    let ghost pad_v = pad_ptr@;
                    let ghost mem_start = block as int + size_of::<BlockHdr>() as int;
                    let ghost mem_end = block as int + new_size as int;
                    let ghost pad_size = vstd::layout::size_of::<UsedBlockPad>() as int;
                    assert(ptr_v.addr >= pad_size) by {
                        assert(pad_size == 8);
                        assert(size_of::<UsedBlockHdr>() as int >= pad_size);
                        assert(ptr_v.addr >= block_v.addr + size_of::<UsedBlockHdr>() as int);
                        assert(block_v.addr != 0);
                        assert(block_v.addr > 0);
                    };
                    assert(ptr_v.addr >= pad_size ==> pad_v.addr == ptr_v.addr - pad_size);
                    assert(pad_v.addr + pad_size == ptr_v.addr);
                    assert(pad_addr as int == pad_v.addr);
                    assert(pad_addr as int + pad_size == ptr_v.addr);

                    assert((ptr_v.addr as int) % align as int == 0);
                    if usize::BITS == 64 {
                        let ghost p = ptr_v.addr as int;
                        let ghost b = block_v.addr as int;
                        assert(GRANULARITY == 32);
                        assert(align % 32 == 0) by {
                            lemma_pow2_value_in_usize(align);
                        };
                        assert(p % 32 == 0) by {
                            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(align as int, 32);
                            assert(align as int == 32 * ((align as int) / 32)) by {
                                assert((align as int) % 32 == 0);
                            };
                            assert(p % (32 * ((align as int) / 32)) == 0);
                            lemma_mod_by_multiple(p, (align as int) / 32, 32);
                        };
                        assert(b % 32 == 0) by {
                            assert(b % GRANULARITY as int == 0);
                            assert(GRANULARITY as int == 32);
                        };
                        assert(ptr_v.addr >= block_v.addr + 16);
                        assert(ptr_v.addr < block_v.addr + 16 + align as int);
                        assert(ptr_v.addr >= block_v.addr + 32) by {
                            if ptr_v.addr < block_v.addr + 32 {
                                assert(0 <= ptr_v.addr - block_v.addr < 32);
                                assert((p - b) % 32 == 0) by {
                                    vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(p, 32);
                                };
                                assert(ptr_v.addr - block_v.addr >= 16);
                                assert(false);
                            }
                        };
                        assert(p % 8 == 0) by {
                            lemma_mod_by_multiple(p, 4, 8);
                        };
                        assert((pad_addr + 8) % 8 == 0) by {
                            assert(pad_addr as int + 8 == ptr_v.addr);
                        };
                        assert(pad_addr as int % 8 == 0) by {
                            vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish((pad_addr as int) + 8, 8);
                            assert(((pad_addr as int) + 8) % 8 == 0);
                        };
                        assert((pad_addr as int) % vstd::layout::align_of::<UsedBlockPad>() as int == 0);
                    } else {
                        let ghost p = ptr_v.addr as int;
                        let ghost b = block_v.addr as int;
                        assert(GRANULARITY == 16);
                        assert(align % 16 == 0) by {
                            lemma_pow2_value_in_usize(align);
                        };
                        assert(p % 16 == 0) by {
                            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(align as int, 16);
                            assert(align as int == 16 * ((align as int) / 16)) by {
                                assert((align as int) % 16 == 0);
                            };
                            assert(p % (16 * ((align as int) / 16)) == 0);
                            lemma_mod_by_multiple(p, (align as int) / 16, 16);
                        };
                        assert(b % 16 == 0) by {
                            assert(b % GRANULARITY as int == 0);
                            assert(GRANULARITY as int == 16);
                        };
                        assert(ptr_v.addr >= block_v.addr + 8);
                        assert(ptr_v.addr < block_v.addr + 8 + align as int);
                        assert(ptr_v.addr >= block_v.addr + 16) by {
                            if ptr_v.addr < block_v.addr + 16 {
                                assert(0 <= ptr_v.addr - block_v.addr < 16);
                                assert((p - b) % 16 == 0) by {
                                    vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(p, 16);
                                };
                                assert(ptr_v.addr - block_v.addr >= 8);
                                assert(false);
                            }
                        };
                        assert((pad_addr + 4) % 4 == 0) by {
                            assert(pad_addr as int + 4 == ptr_v.addr);
                        };
                        assert(pad_addr as int % 4 == 0) by {
                            vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish((pad_addr as int) + 4, 4);
                            assert(((pad_addr as int) + 4) % 4 == 0);
                        };
                        assert((pad_addr as int) % vstd::layout::align_of::<UsedBlockPad>() as int == 0);
                    }

                    assert(set_int_range(
                        pad_addr as int,
                        pad_addr as int + pad_size,
                    ).subset_of(new_block_perm.mem.dom())) by {
                        assert(mem_start <= pad_addr as int) by {
                            assert(pad_addr as int + pad_size == ptr_v.addr);
                            assert(ptr_v.addr >= block_v.addr + size_of::<UsedBlockHdr>() as int);
                            assert(size_of::<UsedBlockHdr>() as int >= size_of::<BlockHdr>() as int);
                        };
                        assert(pad_addr as int + pad_size <= mem_end) by {
                            assert(ptr_v.addr <= block_v.addr + new_size as int);
                        };
                        if new_size == block_size {
                            assert(new_block_perm.mem.is_range(mem_start, mem_end - mem_start));
                        } else {
                            assert(new_block_perm.mem.is_range(mem_start, mem_end - mem_start));
                        }
                        Self::lemma_range_subset_of_mem_dom(
                            new_block_perm.mem,
                            mem_start,
                            mem_end,
                            pad_addr as int,
                            pad_addr as int + pad_size,
                        );
                    };
                }
                let tracked (pad_raw, mem_rest) = new_block_perm.mem.split(
                    set_int_range(
                        pad_addr as int,
                        pad_addr as int + vstd::layout::size_of::<UsedBlockPad>() as int,
                    ),
                );
                proof {
                    assert(pad_raw.is_range(pad_addr as int, vstd::layout::size_of::<UsedBlockPad>() as int)) by {
                        assert(pad_raw.dom()
                            == set_int_range(pad_addr as int, pad_addr as int + vstd::layout::size_of::<UsedBlockPad>() as int));
                    };
                }
                let tracked mut pad_perm = pad_raw.into_typed::<UsedBlockPad>(pad_addr);
                proof {
                    assert(pad_perm.ptr()@ == pad_ptr@) by {
                        assert(pad_perm.ptr()@.addr == pad_ptr@.addr) by {
                            assert(pad_perm.ptr()@.addr == pad_addr as int);
                            assert(pad_ptr@.addr == pad_addr as int);
                        };
                        assert(pad_perm.ptr()@.provenance == pad_ptr@.provenance) by {
                            assert(pad_perm.ptr()@.provenance == pad_raw.provenance());
                            assert(pad_raw.provenance() == new_block_perm.mem.provenance());
                            assert(new_block_perm.mem.provenance() == block@.provenance) by {
                                if new_size == block_size {
                                    assert(old_head_perm.wf());
                                    assert(old_head_perm.mem.provenance() == old_head_perm.points_to.ptr()@.provenance);
                                    assert(old_head_perm.points_to.ptr() == block);
                                    assert(old_head_perm.mem.provenance() == block@.provenance);
                                    assert(new_block_perm.mem.provenance() == old_head_perm.mem.provenance());
                                } else {
                                    assert(new_block_perm.mem.provenance() == block@.provenance);
                                }
                            };
                            assert(ptr@.provenance == block@.provenance);
                            assert(pad_ptr@.provenance == ptr@.provenance);
                        };
                    };
                    assert(pad_perm.ptr() == pad_ptr);
                }
                ptr_mut_write(pad_ptr, Tracked(&mut pad_perm), UsedBlockPad { block_hdr: block });
                proof {
                    let ghost pad_size = vstd::layout::size_of::<UsedBlockPad>() as int;
                    let ghost pad_lo = ptr as int - pad_size;
                    self.used_info.pad_perms.borrow_mut().tracked_insert(ptr, pad_perm);
                    new_block_perm.mem = mem_rest;
                    assert(new_block_perm.mem.dom() == mem_dom_before_pad.difference(
                        set_int_range(
                            pad_lo,
                            ptr as int,
                        ),
                    ));
                }
            }
            //proof {
                //admit(); //-------------------------------------------------------------
            //}

            let ghost hdr_end = block as int + size_of::<BlockHdr>() as int;
            let ghost overhead_hi = if align >= GRANULARITY {
                ptr as int - vstd::layout::size_of::<UsedBlockPad>() as int
            } else {
                ptr as int
            };
            proof {
                assert(set_int_range(hdr_end, overhead_hi).subset_of(new_block_perm.mem.dom())) by {
                    if align >= GRANULARITY {
                        let ghost pad_size = vstd::layout::size_of::<UsedBlockPad>() as int;
                        let ghost pad_lo = ptr as int - pad_size;
                        assert(new_block_perm.mem.dom() == mem_dom_before_pad.difference(set_int_range(pad_lo, ptr as int)));
                        assert(overhead_hi == pad_lo);
                        assert forall |a:int|
                            #[trigger] set_int_range(hdr_end, overhead_hi).contains(a)
                            implies new_block_perm.mem.dom().contains(a)
                        by {
                            assert(hdr_end <= a < overhead_hi);
                            assert(mem_dom_before_pad.contains(a));
                            assert(!set_int_range(pad_lo, ptr as int).contains(a)) by {
                                assert(a < pad_lo);
                            };
                            assert(new_block_perm.mem.dom().contains(a));
                        };
                    } else {
                        assert(hdr_end <= overhead_hi) by {
                            assert(ptr as int >= block as int + size_of::<UsedBlockHdr>() as int);
                            assert(size_of::<UsedBlockHdr>() as int >= size_of::<BlockHdr>() as int);
                        };
                        Self::lemma_range_subset_of_mem_dom(
                            new_block_perm.mem,
                            block as int + size_of::<BlockHdr>() as int,
                            block as int + new_size as int,
                            hdr_end,
                            overhead_hi,
                        );
                    }
                };
            }
            let tracked (overhead_mem, mem_after_overhead) =
                new_block_perm.mem.split(set_int_range(hdr_end, overhead_hi));
            proof {
                self.used_info.overhead_perms.borrow_mut().tracked_insert(ptr, overhead_mem);
            }

            let ghost ret_lo = ptr as int;
            let ghost ret_hi = ptr as int + size as int;
            proof {
                assert(set_int_range(ret_lo, ret_hi).subset_of(mem_after_overhead.dom())) by {
                    assert(mem_after_overhead.dom() == new_block_perm.mem.dom().difference(set_int_range(hdr_end, overhead_hi)));
                    assert forall |a:int|
                        #[trigger] set_int_range(ret_lo, ret_hi).contains(a)
                        implies mem_after_overhead.dom().contains(a)
                    by {
                        assert(ret_lo <= a < ret_hi);
                        assert(ptr as int == block as int + overhead as int);
                        assert(a < block as int + overhead as int + size as int);
                        assert(a < block as int + new_size as int) by {
                            assert((overhead + size) as usize <= new_size) by {
                                granularity_is_power_of_two();
                                lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                            };
                        };
                        assert(a >= block as int + size_of::<BlockHdr>() as int);
                        assert(new_block_perm.mem.dom().contains(a));
                        assert(!set_int_range(hdr_end, overhead_hi).contains(a)) by {
                            if align >= GRANULARITY {
                                assert(overhead_hi == ptr as int - vstd::layout::size_of::<UsedBlockPad>() as int);
                                assert(a >= ptr as int);
                            } else {
                                assert(overhead_hi == ptr as int);
                                assert(a >= ptr as int);
                            }
                        };
                        assert(mem_after_overhead.dom().contains(a));
                    };
                };
            }
            let tracked (ret_mem, mem_rest2) = mem_after_overhead.split(set_int_range(ret_lo, ret_hi));
            proof {
                let ghost perms_without_block = self.all_blocks.perms@;
                assert(ret_mem.is_range(ret_lo, ret_hi - ret_lo)) by {
                    assert(ret_mem.dom() == set_int_range(ret_lo, ret_hi));
                };
                assert(!ret_mem.dom().is_empty()) by {
                    assert(size > 0);
                    assert(set_int_range(ret_lo, ret_hi).contains(ret_lo));
                    assert(ret_mem.dom().contains(ret_lo));
                };
                assert(exists|s: int| s >= size as int && #[trigger] ret_mem.is_range(ptr as usize as int, s)) by {
                    let s = size as int;
                    assert(s >= size as int);
                    assert(ret_mem.is_range(ptr as usize as int, s));
                };
                assert(mem_rest2.provenance() == mem_after_overhead.provenance());
                new_block_perm.mem = mem_rest2;
                assert(new_block_perm.points_to.value().size == (new_size | SIZE_USED));
                assert(!new_block_perm.points_to.value().is_free()) by {
                    assert(((new_size | SIZE_USED) & SIZE_USED) == SIZE_USED) by (bit_vector)
                        requires SIZE_USED == 1;
                    assert((new_block_perm.points_to.value().size & SIZE_USED) == SIZE_USED);
                };
                assert(new_block_perm.wf()) by {
                    assert(!new_block_perm.points_to.value().is_free());
                };
                self.all_blocks.perms.borrow_mut().tracked_insert(block, new_block_perm);
                if new_size < block_size {
                    let ghost bi = ab_before_final_remove.get_ptr_internal_index(block);
                    let ghost perms_after_insert = self.all_blocks.perms@;
                    assert(perms_without_block == ab_before_final_remove.perms@.remove(block));
                    assert(perms_after_insert == perms_without_block.insert(block, new_block_perm));
                    assert(perms_after_insert == ab_before_final_remove.perms@.insert(block, new_block_perm)) by {
                        assert forall|p: *mut BlockHdr|
                            perms_after_insert.contains_key(p)
                                == ab_before_final_remove.perms@.insert(block, new_block_perm).contains_key(p)
                        by {};
                        assert forall|p: *mut BlockHdr|
                            perms_after_insert.contains_key(p)
                                implies perms_after_insert[p] == ab_before_final_remove.perms@.insert(block, new_block_perm)[p]
                        by {
                            if perms_after_insert.contains_key(p) {
                                if p == block {
                                    assert(perms_after_insert[p] == new_block_perm);
                                    assert(ab_before_final_remove.perms@.insert(block, new_block_perm)[p] == new_block_perm);
                                } else {
                                    assert(perms_after_insert[p] == perms_without_block[p]);
                                    assert(perms_without_block[p] == ab_before_final_remove.perms@[p]);
                                    assert(ab_before_final_remove.perms@.insert(block, new_block_perm)[p]
                                        == ab_before_final_remove.perms@[p]);
                                }
                            }
                        };
                    };
                    assert(self.all_blocks.ptrs@ == ab_before_final_remove.ptrs@);
                    assert(ghost_pointer_ordered(ab_before_final_remove.ptrs@));
                    ab_before_final_remove.lemma_wf_nodup();
                    assert(ptrs_no_duplicates(ab_before_final_remove.ptrs@));
                    assert(self.all_blocks.wf_node(bi)) by {
                        let ptr = self.all_blocks.ptrs@[bi];
                        assert(ab_before_final_remove.wf());
                        assert(ab_before_final_remove.wf_node(bi));
                        assert(ptr == ab_before_final_remove.ptrs@[bi]);
                        assert(ptr == block);
                        assert(self.all_blocks.perms@[ptr] == new_block_perm);
                        assert(new_block_perm.points_to == ab_before_final_remove.perms@[ptr].points_to);
                        assert(self.all_blocks.value_at(ptr) == ab_before_final_remove.value_at(ptr));
                        assert(self.all_blocks.wf_node(bi));
                    };
                    AllBlocks::<FLLEN, SLLEN>::lemma_all_blocks_wf_after_replace_block_perm(
                        ab_before_final_remove,
                        self.all_blocks,
                        block,
                        new_block_perm,
                    );
                    assert(self.all_blocks.wf());
                } else {
                    assert(self.all_blocks.wf()) by {
                        assert(self.all_blocks.ptrs@ == old(self).all_blocks.ptrs@);
                        assert(ghost_pointer_ordered(self.all_blocks.ptrs@));
                        old(self).all_blocks.lemma_wf_nodup();
                        assert(ptrs_no_duplicates(self.all_blocks.ptrs@));
                        assert forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                            implies self.all_blocks.wf_node(i)
                        by {
                            let ptr = self.all_blocks.ptrs@[i];
                            if ptr == block {
                                assert(i == block_id) by {
                                    assert(old(self).all_blocks.ptrs@[block_id] == block);
                                    assert(self.all_blocks.ptrs@[i] == old(self).all_blocks.ptrs@[i]);
                                    assert(old(self).all_blocks.ptrs@[i] == block);
                                    old(self).all_blocks.lemma_wf_nodup();
                                    lemma_ptrs_no_duplicates_eq_index(old(self).all_blocks.ptrs@, i, block_id);
                                };
                                assert(old(self).all_blocks.wf_node(block_id));
                                old(self).all_blocks.lemma_wf_node_ptr(block_id);
                                assert(self.all_blocks.perms@[block] == new_block_perm);
                                assert(self.all_blocks.perms@[block].points_to.ptr() == block);
                                assert(self.all_blocks.perms@[block].wf());
                                assert(block@.addr != 0);
                                assert((block@.addr as int) % (GRANULARITY as int) == 0);
                                assert(self.all_blocks.perms@.contains_key(block));
                                assert(!self.all_blocks.value_at(block).is_free());
                                assert((new_size | SIZE_USED) & SIZE_SIZE_MASK == new_size) by {
                                    Self::lemma_mark_used_preserves_size_bits(new_size);
                                };
                                assert(self.all_blocks.value_at(block).size == (new_size | SIZE_USED));
                                assert((self.all_blocks.value_at(block).size & SIZE_SIZE_MASK) == new_size);
                                assert((self.all_blocks.value_at(block).size & SIZE_SENTINEL) == 0) by {
                                    assert(new_size % GRANULARITY == 0) by {
                                        granularity_is_power_of_two();
                                        lemma_round_up_pow2((overhead + size) as usize, GRANULARITY);
                                    };
                                    if usize::BITS == 64 {
                                        assert(GRANULARITY == 32);
                                        lemma_mod_by_multiple(new_size as int, 8, 4);
                                    } else {
                                        assert(GRANULARITY == 16);
                                        lemma_mod_by_multiple(new_size as int, 4, 4);
                                    }
                                    assert((((new_size | SIZE_USED) & SIZE_SENTINEL) == 0usize)) by (bit_vector)
                                        requires SIZE_USED == 1, SIZE_SENTINEL == 2, new_size as int % 4 == 0;
                                };
                                assert(!self.all_blocks.value_at(block).is_sentinel());
                                assert(new_size == block_size);
                                assert((self.all_blocks.value_at(block).size & SIZE_SIZE_MASK)
                                    == (old(self).all_blocks.value_at(block).size & SIZE_SIZE_MASK)) by {
                                    assert(old(self).all_blocks.value_at(block).size == block_size);
                                    assert((old(self).all_blocks.value_at(block).size & SIZE_SIZE_MASK) == block_size);
                                };
                                assert(self.all_blocks.phys_next_of(i) == old(self).all_blocks.phys_next_of(block_id));
                                assert(self.all_blocks.phys_next_of(i) matches Some(next_ptr) ==> {
                                    &&& next_ptr@.addr == block@.addr + (self.all_blocks.value_at(block).size & SIZE_SIZE_MASK)
                                    &&& next_ptr@.provenance == block@.provenance
                                }) by {
                                    if self.all_blocks.phys_next_of(i) matches Some(next_ptr) {
                                        let next_ptr = self.all_blocks.phys_next_of(i).unwrap();
                                        assert(old(self).all_blocks.phys_next_of(block_id) matches Some(old_next_ptr));
                                        let old_next_ptr = old(self).all_blocks.phys_next_of(block_id).unwrap();
                                        assert(next_ptr == old_next_ptr);
                                        assert(old(self).all_blocks.wf_node(block_id));
                                        assert(old(self).all_blocks.phys_next_of(block_id) matches Some(p) ==> {
                                            &&& p@.addr == block@.addr + (old(self).all_blocks.value_at(block).size & SIZE_SIZE_MASK)
                                            &&& p@.provenance == block@.provenance
                                        });
                                        assert(next_ptr@.addr == block@.addr + (self.all_blocks.value_at(block).size & SIZE_SIZE_MASK));
                                        assert(next_ptr@.provenance == block@.provenance);
                                    }
                                };
                                assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(
                                    (self.all_blocks.value_at(block).size & SIZE_SIZE_MASK) as int));
                                assert((self.all_blocks.value_at(block).size as int) + (block as int) < usize::MAX as int) by {
                                    assert(old(self).all_blocks.wf_node(block_id));
                                    assert(old(self).all_blocks.value_at(block).size == block_size);
                                    assert((old(self).all_blocks.value_at(block).size as int) + (block as int) < usize::MAX as int);
                                    assert((block_size as int) + (block as int) < usize::MAX as int);
                                    assert((self.all_blocks.value_at(block).size as int) <= (block_size as int) + 1) by {
                                        assert(self.all_blocks.value_at(block).size == (new_size | SIZE_USED));
                                        assert(new_size == block_size);
                                        assert((new_size | SIZE_USED) <= new_size + 1) by (bit_vector)
                                            requires SIZE_USED == 1;
                                    };
                                    assert((block_size as int) + 1 < usize::MAX as int) by {
                                        assert((block_size as int) + (block as int) + 1 <= usize::MAX as int) by {
                                            assert((block_size as int) + (block as int) < usize::MAX as int);
                                        };
                                        assert((block_size as int) + (block as int) != (usize::MAX as int) - 1) by {
                                            assert((block_size as int) + (block as int) == old(self).all_blocks.phys_next_of(block_id).unwrap()@.addr);
                                            assert(old(self).all_blocks.phys_next_of(block_id) is Some);
                                            let next_ptr = old(self).all_blocks.phys_next_of(block_id).unwrap();
                                            assert(old(self).all_blocks.wf());
                                            let next_i = block_id + 1;
                                            assert(0 <= next_i < old(self).all_blocks.ptrs@.len());
                                            assert(old(self).all_blocks.ptrs@[next_i] == next_ptr);
                                            assert(old(self).all_blocks.wf_node(next_i));
                                            assert((next_ptr@.addr as int) % (GRANULARITY as int) == 0);
                                            if usize::BITS == 64 {
                                                assert(GRANULARITY == 32);
                                                assert(((usize::MAX as int) - 1) % 32 != 0) by (compute);
                                            } else {
                                                assert(GRANULARITY == 16);
                                                assert(((usize::MAX as int) - 1) % 16 != 0) by (compute);
                                            }
                                            if (block_size as int) + (block as int) == (usize::MAX as int) - 1 {
                                                assert((next_ptr@.addr as int) % (GRANULARITY as int) != 0);
                                                assert(false);
                                            }
                                        };
                                        assert((block_size as int) + (block as int) + 1 < usize::MAX as int);
                                    };
                                    assert((self.all_blocks.value_at(block).size as int) + (block as int)
                                        <= (block_size as int) + (block as int) + 1);
                                };
                                assert(self.all_blocks.phys_next_of(i) is Some);
                                assert(self.all_blocks.value_at(block).prev_phys_block@.addr != 0 ==> (
                                    self.all_blocks.phys_prev_of(i) matches Some(p)
                                        && p == self.all_blocks.value_at(block).prev_phys_block
                                ));
                                assert(self.all_blocks.value_at(block).prev_phys_block@.addr == 0
                                    ==> self.all_blocks.phys_prev_of(i) is None);
                                assert(self.all_blocks.wf_node(i));
                            } else {
                                assert(old(self).all_blocks.wf_node(i));
                                assert(self.all_blocks.value_at(ptr) == old(self).all_blocks.value_at(ptr));
                                if next_free_candidate@.addr != 0 && ptr == next_free_candidate {
                                    assert(self.all_blocks.perms@[ptr].points_to
                                        == old(self).all_blocks.perms@[ptr].points_to);
                                    assert(self.all_blocks.perms@[ptr].mem
                                        == old(self).all_blocks.perms@[ptr].mem);
                                } else {
                                    assert(self.all_blocks.perms@[ptr] == old(self).all_blocks.perms@[ptr]);
                                }
                                assert(self.all_blocks.wf_node(i));
                            }
                        };
                    };
                }
            }
            self.root_provenances = Tracked(Some(block_prov_for_root));
            proof {
                assert(self.all_blocks.wf());
                old(self).lemma_shadow_list_no_duplicates();
                if new_size == block_size {
                    // Pre-establish block == m[idx][0] and nfc == m[idx][1] when nfc != null.
                    // These are used cheaply inside foralls via lemma_nodup_get.
                    assert(old(self).shadow_freelist@.m[idx][0] == block) by {
                        old(self).wf_index_in_freelist(idx);
                        old(self).freelist_nonempty(idx);
                    };
                    assert(next_free_candidate@.addr != 0 ==> (
                        old(self).shadow_freelist@.m[idx].len() > 1
                        && next_free_candidate == old(self).shadow_freelist@.m[idx][1])) by {
                        if next_free_candidate@.addr != 0 {
                            old(self).lemma_freelist_wf_extract_wf_free_node(idx, 0);
                            assert(old(self).wf_free_node(idx, 0));
                            old(self).lemma_freelist_len_gt1_from_nonnull_next(idx);
                            old(self).lemma_wf_free_node_next_addr(idx, 0);
                        }
                    };
                    Self::lemma_shadow_ptrs_nonnull_after_pop(*old(self), *self, idx);
                    assert(self.wf_shadow());
                    // Perm preservation for bi != idx freelist nodes
                    assert forall|bi: BlockIndex<FLLEN, SLLEN>, n: int|
                        bi.wf() && bi != idx && 0 <= n < old(self).shadow_freelist@.m[bi].len()
                        implies #[trigger] self.all_blocks.perms@[old(self).shadow_freelist@.m[bi][n]]
                            == old(self).all_blocks.perms@[old(self).shadow_freelist@.m[bi][n]]
                    by {
                        let node = old(self).shadow_freelist@.m[bi][n];
                        // node != block (= m[idx][0]): cross-list uniqueness via lemma_nodup_get
                        assert(node != block) by {
                            old(self).lemma_nodup_get(bi, n, idx, 0);
                        };
                        // node != next_free_candidate (= m[idx][1] when addr != 0)
                        if next_free_candidate@.addr != 0 {
                            old(self).lemma_nodup_get(bi, n, idx, 1);
                            assert(node != next_free_candidate);
                        }
                        assert(self.all_blocks.perms@[node] == old(self).all_blocks.perms@[node]) by {
                            if next_free_candidate@.addr != 0 {
                                assert(node != next_free_candidate);
                                assert(self.all_blocks.perms@[node] == perms_after_removing_block[node]);
                            } else {
                                assert(self.all_blocks.perms@[node] == perms_after_removing_block[node]);
                            }
                            assert(perms_after_removing_block[node] == old(self).all_blocks.perms@[node]);
                        };
                    };
                    // Perm preservation for idx positions >= 2
                    assert forall|n: int| 1 < n < old(self).shadow_freelist@.m[idx].len()
                        implies self.all_blocks.perms@[old(self).shadow_freelist@.m[idx][n]]
                            == old(self).all_blocks.perms@[old(self).shadow_freelist@.m[idx][n]]
                    by {
                        let node = old(self).shadow_freelist@.m[idx][n];
                        assert(node != block) by {
                            old(self).lemma_nodup_get(idx, 0, idx, n);
                        };
                        if next_free_candidate@.addr != 0 {
                            old(self).lemma_nodup_get(idx, 1, idx, n);
                            assert(node != next_free_candidate);
                        }
                        assert(self.all_blocks.perms@[node] == old(self).all_blocks.perms@[node]) by {
                            if next_free_candidate@.addr != 0 {
                                assert(node != next_free_candidate);
                                assert(self.all_blocks.perms@[node] == perms_after_removing_block[node]);
                            } else {
                                assert(self.all_blocks.perms@[node] == perms_after_removing_block[node]);
                            }
                            assert(perms_after_removing_block[node] == old(self).all_blocks.perms@[node]);
                        };
                    };
                    // next_free conditions
                    assert(old(self).shadow_freelist@.m[idx].len() > 1 ==> (
                        old(self).shadow_freelist@.m[idx][1] == next_free_candidate
                        && self.all_blocks.perms@[next_free_candidate].points_to
                            == old(self).all_blocks.perms@[next_free_candidate].points_to
                        && self.all_blocks.perms@[next_free_candidate].mem
                            == old(self).all_blocks.perms@[next_free_candidate].mem
                        && self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().prev_free@.addr == 0
                        && self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free
                            == old(self).all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free
                    )) by {
                        if old(self).shadow_freelist@.m[idx].len() > 1 {
                            old(self).lemma_freelist_wf_extract_wf_free_node(idx, 0);
                            old(self).lemma_wf_free_node_next_addr(idx, 0);
                            assert(Some(next_free_candidate) == Self::free_next_of(old(self).shadow_freelist@.m[idx], 0));
                            assert(next_free_candidate == old(self).shadow_freelist@.m[idx][1]);
                            assert(next_free_candidate@.addr != 0);
                            assert(self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free
                                == next_next_free_candidate);
                            assert(next_next_free_candidate
                                == old(self).all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free) by {
                                assert(new_head_perm == old(self).all_blocks.perms@[next_free_candidate]);
                            };
                        }
                    };
                    // Singleton list -> next_free is null
                    assert(old(self).shadow_freelist@.m[idx].len() == 1 ==> next_free_candidate@.addr == 0) by {
                        if next_free_candidate@.addr != 0 {
                            old(self).lemma_freelist_wf_extract_wf_free_node(idx, 0);
                            old(self).lemma_freelist_len_gt1_from_nonnull_next(idx);
                        }
                    };
                    // Call big-step lemma: proves all_freelist_wf() + bitmap_sync()
                    Self::lemma_pop_head_preserves_wf(*old(self), *self, idx, next_free_candidate);
                    assert(self.all_freelist_wf());
                    let ghost sfl_after_remove =
                        old(self).shadow_freelist@.ii_remove_for_index(old(self).all_blocks, idx, 0);
                    Self::lemma_ii_remove_for_index_ensures(old(self).shadow_freelist@, old(self).all_blocks, idx, 0);
                    assert(self.shadow_freelist@ == sfl_after_remove);
                    assert(old(self).size_class_condition());
                    assert(Self::shadow_freelist_popped_at(old(self).shadow_freelist@, self.shadow_freelist@, idx)) by {
                        reveal(Tlsf::shadow_freelist_popped_at);
                        assert(self.shadow_freelist@.m[idx] == old(self).shadow_freelist@.m[idx].remove(0));
                        assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() && bi != idx
                            implies self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]
                        by {
                            assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]);
                        };
                    };
                    assert(Self::perms_size_unchanged_for_freelist(old(self).shadow_freelist@, old(self).all_blocks, self.all_blocks, block)) by {
                        reveal(Tlsf::perms_size_unchanged_for_freelist);
                        assert forall|bi: BlockIndex<FLLEN, SLLEN>, i: int|
                            bi.wf() && 0 <= i < old(self).shadow_freelist@.m[bi].len() && old(self).shadow_freelist@.m[bi][i] != block
                                implies self.all_blocks.perms@[old(self).shadow_freelist@.m[bi][i]].points_to.value().size
                                    == old(self).all_blocks.perms@[old(self).shadow_freelist@.m[bi][i]].points_to.value().size
                        by {
                            let node = old(self).shadow_freelist@.m[bi][i];
                            if next_free_candidate@.addr != 0 && node == next_free_candidate {
                                assert(next_free_candidate@.addr != 0 ==> (
                                    self.all_blocks.perms@[next_free_candidate].points_to
                                        == old(self).all_blocks.perms@[next_free_candidate].points_to
                                    && self.all_blocks.perms@[next_free_candidate].mem
                                        == old(self).all_blocks.perms@[next_free_candidate].mem
                                ));
                            } else {
                                if next_free_candidate@.addr != 0 {
                                    assert(node != next_free_candidate);
                                    assert(self.all_blocks.perms@[node] == perms_after_removing_block[node]);
                                } else {
                                    assert(self.all_blocks.perms@[node] == perms_after_removing_block[node]);
                                }
                                assert(perms_after_removing_block[node] == old(self).all_blocks.perms@[node]);
                            }
                        };
                    };
                    Self::lemma_size_class_after_pop(*old(self), *self, idx, block);
                }
                if new_size < block_size {
                    assert(self.all_freelist_wf()) by {
                        assert(self.shadow_freelist@ == tlsf_before_final_remove.shadow_freelist@);
                        assert(self.wf_shadow()) by {
                            assert(tlsf_before_final_remove.wf_shadow());
                            Self::lemma_shadow_ptrs_nonnull_frame(tlsf_before_final_remove, *self);
                        };
                        assert forall|bi: BlockIndex<FLLEN, SLLEN>, n: int|
                            bi.wf() && 0 <= n < tlsf_before_final_remove.shadow_freelist@.m[bi].len()
                            implies self.all_blocks.perms@[tlsf_before_final_remove.shadow_freelist@.m[bi][n]]
                                == tlsf_before_final_remove.all_blocks.perms@[tlsf_before_final_remove.shadow_freelist@.m[bi][n]]
                        by {
                            let node = tlsf_before_final_remove.shadow_freelist@.m[bi][n];
                            assert(node != block) by {
                                if node == block {
                                    tlsf_before_final_remove.wf_index_in_freelist(bi);
                                    tlsf_before_final_remove.lemma_freelist_wf_extract_wf_free_node(bi, n);
                                    assert(tlsf_before_final_remove.all_blocks.value_at(block).is_free());
                                    assert(!tlsf_before_final_remove.all_blocks.value_at(block).is_free());
                                    assert(false);
                                }
                            };
                            assert(self.all_blocks.perms@[node] == tlsf_before_final_remove.all_blocks.perms@[node]);
                        };
                        Self::lemma_all_freelist_wf_perms_frame(tlsf_before_final_remove, *self);
                    };
                    assert(self.size_class_condition()) by {
                        assert(tlsf_before_final_remove.size_class_condition());
                        assert(!tlsf_before_final_remove.shadow_freelist@.contains(block)) by {
                            assert(self.shadow_freelist@ == tlsf_before_final_remove.shadow_freelist@);
                            assert forall|bi: BlockIndex<FLLEN, SLLEN>, n: int|
                                bi.wf() && 0 <= n < tlsf_before_final_remove.shadow_freelist@.m[bi].len()
                                    implies tlsf_before_final_remove.shadow_freelist@.m[bi][n] != block
                            by {
                                let node = tlsf_before_final_remove.shadow_freelist@.m[bi][n];
                                assert(node == self.shadow_freelist@.m[bi][n]);
                                if node == block {
                                    tlsf_before_final_remove.wf_index_in_freelist(bi);
                                    tlsf_before_final_remove.lemma_freelist_wf_extract_wf_free_node(bi, n);
                                    assert(tlsf_before_final_remove.wf_free_node(bi, n));
                                    assert(tlsf_before_final_remove.all_blocks.value_at(block).is_free());
                                    assert(!tlsf_before_final_remove.all_blocks.value_at(block).is_free());
                                    assert(false);
                                }
                            };
                        };
                        assert(Self::perms_size_unchanged_for_freelist(tlsf_before_final_remove.shadow_freelist@, tlsf_before_final_remove.all_blocks, self.all_blocks, block)) by {
                            reveal(Tlsf::perms_size_unchanged_for_freelist);
                            assert forall|bi: BlockIndex<FLLEN, SLLEN>, i: int|
                                bi.wf() && 0 <= i < tlsf_before_final_remove.shadow_freelist@.m[bi].len() && tlsf_before_final_remove.shadow_freelist@.m[bi][i] != block
                                    implies self.all_blocks.perms@[tlsf_before_final_remove.shadow_freelist@.m[bi][i]].points_to.value().size
                                        == tlsf_before_final_remove.all_blocks.perms@[tlsf_before_final_remove.shadow_freelist@.m[bi][i]].points_to.value().size
                            by {
                                let node = tlsf_before_final_remove.shadow_freelist@.m[bi][i];
                                assert(self.all_blocks.perms@[node] == tlsf_before_final_remove.all_blocks.perms@[node]);
                            };
                        };
                        Self::lemma_size_class_perm_change_preserved(tlsf_before_final_remove, *self, block);
                    };
                    assert(self.bitmap_wf());
                    assert(self.bitmap_sync());
                } else {
                    assert(new_size == block_size);
                    assert(self.all_freelist_wf());
                    assert(self.size_class_condition()) by {
                        Self::lemma_size_class_after_pop(*old(self), *self, idx, block);
                    };
                    assert(self.bitmap_wf());
                    assert(self.bitmap_sync());
                }
                assert(self.wf());
            }
            proof {
                self.lemma_wf_dealloc_token();
                assert(ptr.addr() % align == 0);
                assert(self.is_root_provenance(ptr));
                assert(ptr@.provenance == ret_mem.provenance()) by {
                    assert(ret_mem.provenance() == mem_after_overhead.provenance());
                    assert(mem_after_overhead.provenance() == new_block_perm.mem.provenance());
                    assert(new_block_perm.mem.provenance() == block@.provenance);
                    assert(ptr@.provenance == block@.provenance);
                };
                assert(!ret_mem.dom().is_empty());
                assert(exists|s: int| s >= size as int && #[trigger] ret_mem.is_range(ptr as usize as int, s));
            }

            //self.print_stat();
            let r = Some((ptr, Tracked(ret_mem), Tracked(DeallocToken)));
            proof {
                assert(r is Some);
                assert(r matches Some((_, _, tok)) ==> self.wf_dealloc(tok@)) by {
                    self.lemma_wf_dealloc_token();
                };
            }
            r
        }
    }
}
} // verus!
