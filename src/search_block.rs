use vstd::prelude::*;

verus! {

use crate::bits::*;
use crate::block_index::BlockIndex;
use crate::parameters::*;
use crate::Tlsf;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::bits::{axiom_u64_trailing_zeros, u64_trailing_zeros};

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    /// Search for a non-empty free block list for allocation.
    //#[verifier::external_body] // debug
    #[inline(always)]
    pub(crate) fn search_suitable_free_block_list_for_allocation(
        &self,
        min_size: usize,
    ) -> (r: Option<BlockIndex<FLLEN,SLLEN>>)
        requires self.wf(),
            Self::parameter_validity(),
            min_size >= GRANULARITY,
            min_size % GRANULARITY == 0,
            min_size as int <= Self::max_allocatable_size(),
            self.bitmap_wf(),
            self.bitmap_sync(),
        ensures
            self.bitmap_wf(),
            self.bitmap_sync(),
            r matches Some(idx) ==> idx.wf() &&
            {
                &&& min_size as int <= idx.block_size_range().start()
                &&& self.shadow_freelist@.m[idx].len() > 0
            }
        // None ==> invalid size requested or there no free entry
    {
        proof {
            Self::lemma_parameter_validity_implies_block_index_parameter_validity();
            assert(BlockIndex::<FLLEN, SLLEN>::parameter_validity());
        }
        let idx = Self::map_ceil(min_size)?; // NOTE: return None if invalid size requested
        let BlockIndex(mut fl, mut sl) = idx;
        assert(min_size <= idx.block_size_range().start());

        // Search in range `(fl, sl..SLLEN)`
        let sl_start = sl;
        let sl_row = self.sl_bitmap[fl];
        sl = bit_scan_forward(sl_row, sl_start as u32) as usize;
        if sl < SLLEN {
            let new_idx = BlockIndex::<FLLEN, SLLEN>(fl, sl);
            proof {
                assert(idx.1 <= sl);
                assert(new_idx.wf());
                assert(sl < usize::BITS) by {
                    assert(sl < SLLEN);
                    assert(Self::parameter_validity());
                    assert(0 < SLLEN <= usize::BITS);
                };
                assert((0x1usize & (sl_row >> sl)) == 1usize);
                assert(self.shadow_freelist@.m[new_idx].len() > 0) by {
                    assert(self.bitmap_sync());
                    assert((0x1usize & (self.sl_bitmap[new_idx.0 as int] >> new_idx.1)) == 1usize);
                }
                if idx.1 < sl {
                    assert(idx.block_index_lt(new_idx));
                    assert(idx.block_size_range().start() <= new_idx.block_size_range().start()) by {
                        BlockIndex::<FLLEN, SLLEN>::lemma_block_size_range_start_mono_same_fl(idx, new_idx);
                    };
                    assert(min_size as int <= new_idx.block_size_range().start()) by {
                        assert(min_size <= idx.block_size_range().start());
                    };
                } else {
                    assert(idx.1 == sl);
                    assert(new_idx == idx);
                    assert(min_size as int <= new_idx.block_size_range().start()) by {
                        assert(min_size <= idx.block_size_range().start());
                    };
                }
            }

            assert(min_size <= idx.block_size_range().start());
            return Some(BlockIndex(fl, sl));
        }
        // Search in range `(fl + 1.., ..)`
        proof {
            assert(fl < FLLEN);
            assert(FLLEN < usize::BITS) by {
                assert(Self::parameter_validity());
                assert(0 < FLLEN < usize::BITS - Self::granularity_log2_spec());
                assert(0 <= Self::granularity_log2_spec()) by {
                    Self::granularity_basics();
                };
            };
            assert(fl + 1 < usize::BITS);
            assert((fl as u32) + 1 < usize::BITS);
        }
        let fl_start = fl + 1;
        let fl_bits = self.fl_bitmap;
        fl = bit_scan_forward(fl_bits, fl_start as u32) as usize;
        if fl < FLLEN {
            let sl_row = self.sl_bitmap[fl];
            sl = sl_row.trailing_zeros() as usize;
            proof {
                assert(fl_start <= fl);
                assert(idx.0 < fl) by {
                    assert(fl_start == idx.0 + 1);
                };
                assert(fl < usize::BITS) by {
                    assert(fl < FLLEN);
                    assert(Self::parameter_validity());
                    assert(0 < FLLEN < usize::BITS - Self::granularity_log2_spec());
                    assert(0 <= Self::granularity_log2_spec()) by {
                        Self::granularity_basics();
                    };
                };
                assert((0x1usize & (fl_bits >> fl)) == 1usize);
                assert(sl_row != 0) by {
                    let idx0 = BlockIndex::<FLLEN, SLLEN>(fl, 0);
                    assert(idx0.wf());
                    assert(self.bitmap_wf());
                    assert(!(sl_row == 0));
                };
                assert(sl < usize::BITS) by {
                    assert(usize::BITS == 64) by (compute);
                    assert(sl == usize_trailing_zeros(sl_row) as usize);
                    assert(usize_trailing_zeros(sl_row) == u64_trailing_zeros(sl_row as u64) as u32);
                    axiom_u64_trailing_zeros(sl_row as u64);
                    assert(u64_trailing_zeros(sl_row as u64) < 64) by {
                        if !(u64_trailing_zeros(sl_row as u64) < 64) {
                            assert(u64_trailing_zeros(sl_row as u64) == 64);
                            assert(sl_row as u64 == 0);
                            assert(sl_row == 0);
                            assert(false);
                        }
                    };
                };
                assert((0x1usize & (sl_row >> sl)) == 1usize) by {
                    assert(usize::BITS == 64) by (compute);
                    assert(sl == usize_trailing_zeros(sl_row) as usize);
                    assert(usize_trailing_zeros(sl_row) == u64_trailing_zeros(sl_row as u64) as u32);
                    axiom_u64_trailing_zeros(sl_row as u64);
                    assert((sl_row as u64 >> u64_trailing_zeros(sl_row as u64) as u64) & 1u64 == 1u64);
                    assert((sl_row as u64 >> sl as u64) & 1u64 == 1u64);
                    assert(((sl_row >> sl) as u64) == ((sl_row as u64) >> (sl as u64))) by (bit_vector);
                    assert((((sl_row >> sl) & 1usize) as u64) == (((sl_row as u64) >> (sl as u64)) & 1u64)) by (bit_vector);
                    assert((0x1usize & (sl_row >> sl)) == 1usize) by (bit_vector)
                        requires (((sl_row >> sl) & 1usize) as u64) == 1u64;
                };
                assert(sl < SLLEN) by {
                    if !(sl < SLLEN) {
                        assert(sl >= SLLEN);
                        assert(self.bitmap_wf());
                        assert(!((0x1usize & (sl_row >> sl)) == 1usize));
                        assert(false);
                    }
                };
            }

            let new_idx = BlockIndex::<FLLEN, SLLEN>(fl, sl);
            proof {
                assert(new_idx.wf());
                assert(idx.0 < fl);
                assert(idx.block_index_lt(new_idx));
                assert(idx.0 == 0 ==> new_idx.0 != 0) by {
                    assert(new_idx.0 == fl);
                    if idx.0 == 0 {
                        assert(0 < fl);
                    }
                };
                assert(BlockIndex::<FLLEN, SLLEN>::parameter_validity()) by {
                    assert(Self::parameter_validity());
                    assert(0 < FLLEN < usize::BITS - Self::granularity_log2_spec());
                    assert(0 < SLLEN <= usize::BITS);
                    assert(is_power_of_two(SLLEN as int));
                    if usize::BITS == 64 {
                        assert(GRANULARITY == 32);
                    }
                    if usize::BITS == 32 {
                        assert(GRANULARITY == 16);
                    }
                };
                BlockIndex::<FLLEN, SLLEN>::lemma_block_size_range_mono(idx, new_idx);
                assert(idx.block_size_range().start() <= new_idx.block_size_range().start()) by {
                    idx.lemma_bsr_wf();
                    assert(idx.block_size_range().start() <= idx.block_size_range().end());
                    assert(idx.block_size_range().end() <= new_idx.block_size_range().start());
                };
                assert(min_size as int <= new_idx.block_size_range().start()) by {
                    assert(min_size <= idx.block_size_range().start());
                };
                assert(self.shadow_freelist@.m[new_idx].len() > 0) by {
                    assert(self.bitmap_sync());
                    assert((0x1usize & (self.sl_bitmap[new_idx.0 as int] >> new_idx.1)) == 1usize);
                }
            }
            assert(min_size <= idx.block_size_range().start());
            Some(BlockIndex(fl, sl))
        } else {
            None
        }
    }
}

}
