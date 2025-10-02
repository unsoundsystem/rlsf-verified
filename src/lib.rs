#![feature(const_mut_refs)]
#![feature(const_replace)]
#![feature(strict_provenance)]

mod bits;
mod block_index;
//mod rational_numbers;
mod relation_utils;
mod half_open_range;
mod linked_list;
mod ghost_tlsf;
mod parameters;
mod mapping;
mod bitmap;

use vstd::prelude::*;

verus! {
use vstd::raw_ptr::{
    ptr_mut_read, ptr_mut_write, ptr_ref2, ptr_ref,
    PointsToRaw, PointsTo, Metadata, Provenance,
    expose_provenance, with_exposed_provenance
};
use vstd::set_lib::set_int_range;
use vstd::calc_macro::calc;
use std::marker::PhantomData;
use vstd::{seq::*, seq_lib::*, bytes::*};
use vstd::arithmetic::{logarithm::log, power2::pow2, power::pow};
use core::alloc::Layout;
use core::mem;
use crate::bits::{
    lemma_pow2_increases,
    lemma_pow2_values,
    lemma_log2_values,
    log2_using_leading_zeros_usize,
    usize_trailing_zeros, is_power_of_two,
    bit_scan_forward, usize_leading_trailing_zeros, usize_leading_zeros,
    granularity_is_power_of_two, mask_higher_bits_leq_mask,
    bit_mask_is_mod_for_pow2, lemma_usize_rotr_mask_lower,
    lemma_pow2_log2_div_is_one, log2_power_in_range,
    lemma_log2_distributes, usize_rotate_right, low_mask_usize,
    lemma_div_by_powlog, lemma_powlog_leq, log2_power_ordered,
    log2_is_strictly_ordered_if_rhs_is_pow2, lemma_div_before_mult_pow2,
    lemma_duplicate_low_mask_usize, lemma_usize_shr_is_div,
    lemma_pow2_div_sub, lemma_u64_trailing_zeros_same,
    lemma_usize_trailing_zero_be_log2, usize_trailing_zeros_is_log2_when_pow2_given
};
use crate::block_index::BlockIndex;
//use crate::rational_numbers::{Rational, rational_number_facts, rational_number_properties};
use crate::linked_list::DLL;
use vstd::array::*;
use core::hint::unreachable_unchecked;
use ghost_tlsf::{UsedInfo, Block};
use vstd::std_specs::bits::u64_trailing_zeros;

pub struct Tlsf<'pool, const FLLEN: usize, const SLLEN: usize> {
    pub fl_bitmap: usize,
    /// `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
    pub sl_bitmap: [usize; FLLEN],
    pub first_free: [[DLL; SLLEN]; FLLEN],
    pub used_info: UsedInfo,

    pub _phantom: PhantomData<&'pool ()>,



    pub valid_range: Ghost<Set<int>>, // represents region managed by this allocator

    // ordered by address
    pub all_blocks: Ghost<Seq<Block>>,
    // FIXME: reflect acutual status of Tlsf field
    //      * option 1: move related filed to Tlsf
    //      * option 2: wf paramter taking Tlsf
    //      * option 3: ensure the condion in Tlsf method

    // provenance of initially added blocks
    // NOTE: Assuming that there is only single memory pool and once the pool registered, no more
    //       new region could be registered to extend.
    pub root_provenances: Ghost<Option<Provenance>>,
}

#[cfg(target_pointer_width = "64")]
global size_of usize == 8;

/// Hardcoding the result of `size_of::<usize>()` to use `GRANULARITY` in both spec/exec modes
// the following doesn't work
//pub const GRANULARITY: usize = core::mem::size_of::<usize>() * 4;
//pub const GRANULARITY: usize = vstd::layout::size_of::<usize>() as usize * 4;
#[cfg(target_pointer_width = "64")]
pub const GRANULARITY: usize = 8 * 4;

//pub const GRANULARITY_LOG2: u32 = ex_usize_trailing_zeros(GRANULARITY);

const SIZE_USED: usize = 1;
const SIZE_SENTINEL: usize = 2;
// FIXME: cannot call function `lib::bits::ex_usize_trailing_zeros` with mode exec
// https://verus-lang.github.io/verus/guide/const.html#specexec-consts
spec const SPEC_SIZE_SIZE_MASK: usize =
    !(((1usize << usize_trailing_zeros(GRANULARITY)) as usize - 1usize) as usize);
#[verifier::when_used_as_spec(SPEC_SIZE_SIZE_MASK)]
exec const SIZE_SIZE_MASK: usize =  !((1 << GRANULARITY.trailing_zeros()) - 1);

#[repr(C)]
struct BlockHdr {
    /// The size of the whole memory block, including the header.
    ///
    ///  - `bit[0]` ([`SIZE_USED`]) indicates whether the block is a used memory
    ///    block or not.
    ///
    ///  - `bit[1]` ([`SIZE_LAST_IN_POOL`]) indicates whether the block is the
    ///    last one of the pool or not.
    ///
    ///  - `bit[GRANULARITY_LOG2..]` ([`SIZE_SIZE_MASK`]) represents the size.
    ///
    size: usize,
    prev_phys_block: Option<*mut BlockHdr>,
}

impl BlockHdr {
}

enum BlockPerm {
    Used(Tracked<PointsTo<UsedBlockHdr>>),
    Free(Tracked<PointsTo<FreeBlockHdr>>)
}

impl BlockPerm {
    pub closed spec fn bhdr_ptr(self) -> *mut BlockHdr {
        match self {
            BlockPerm::Used(perm) => perm@.ptr() as *mut BlockHdr,
            BlockPerm::Free(perm) => perm@.ptr() as *mut BlockHdr
        }
    }
}

#[repr(C)]
struct UsedBlockHdr {
    common: BlockHdr,
}

#[repr(C)]
struct UsedBlockPad {
    block_hdr: *mut UsedBlockHdr,
}

impl UsedBlockPad {
    //#[verifier::external_body] // debug
    #[inline]
    fn get_for_allocation(ptr: *mut u8) -> (r: *mut Self) {
        let Tracked(is_exposed) = expose_provenance(ptr);
        // FIXME: this subtraction was wrapping_sub
        let ptr = with_exposed_provenance(
            ptr as usize - size_of::<FreeBlockHdr>(),
            Tracked(is_exposed));
        ptr
    }
}


#[repr(C)]
struct FreeBlockHdr {
    common: BlockHdr,
    next_free: Option<*mut FreeBlockHdr>,
    prev_free: Option<*mut FreeBlockHdr>,
}

impl FreeBlockHdr {
    spec fn wf(self) -> bool {
        // FIXME(blocking): bit mask formalization
        arbitrary()
        //self.common.
    }
}

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    /// well-formedness of Tlsf structure
    /// * freelist well-formedness
    ///   * TODO: blocks connected to freelist ordered by start address
    /// * bitmap is consistent with the freelist
    /// * TODO: blocks stored in the list have proper size as calculated from their index
    pub closed spec fn wf(self) -> bool {
        &&& self.wf_ghost()
        &&& Self::parameter_validity()

        // Each free list is well-formed
        &&& forall |i: int, j: int| BlockIndex::<FLLEN, SLLEN>::valid_block_index((i, j))
                ==> self.first_free[i][j].wf()

        // Book keeping with bitmaps
        &&& self.bitmap_wf()
        // `sl_bitmap[fl][sl]` is set iff `first_free[fl][sl].is_some()`
        &&& self.bitmap_sync()
    }

    pub const fn new() -> (r: Self)
        ensures r.wf()
    {
        Self {
            fl_bitmap: 0,
            sl_bitmap: [0; FLLEN],
            first_free: Self::initial_free_lists(),
            used_info: UsedInfo {
                ptrs: Ghost(Seq::empty()),
                perms: Tracked(Map::tracked_empty()),
            },
            all_blocks: Ghost(Seq::empty()),
            valid_range: Ghost(Set::empty()),
            root_provenances: Ghost(None),
            _phantom: PhantomData
        }
    }

    /// Due to `error: The verifier does not yet support the following Rust feature: array-fill expresion with non-copy type`
    #[verifier::external_body]
    const fn initial_free_lists() -> (r: [[DLL; SLLEN]; FLLEN])
        ensures forall|i: int, j: int| r[i][j]@.len() == 0 && r[i][j].wf()
    {
        [const { [const { DLL::empty() }; SLLEN] }; FLLEN]
    }

    //#[verifier::external_body] // debug


    //---------------------------------
    //    Memory block axiomization
    //---------------------------------
    //
    // insert_free_block_ptr -> alloc -> ... -> dealloc -> alloc -> ...
    //
    // after insert_free_block_ptr:
    //      ∃ (buf_size: nat) (buf_start: addr) (pointsto: PointsToRaw),
    //           pointsto.is_range(buf_start, buf_size)
    //
    //

    /// Max size of the memory pool
    /// In original implementation in rlsf, MAX_POOL_SIZE was partial to handle block size larger
    /// than `1 << (usize::BITS - 1)`. But we going to ignore this treatment for simplification.
    /// And also in the environment this allocator will be used (e.g. with 64bit/32bit width usize,
    /// managing 2^63(31) bytes of memmory with TLSF), such a situation unlikely to occur.
    /// TODO: justification needed!
    const fn max_pool_size() -> (r: usize)
        requires
            usize::BITS > Self::granularity_log2_spec() + FLLEN as u32
        ensures
            1 << (usize::BITS - 1) >= r >= GRANULARITY,
            r % GRANULARITY == 0
    {
        let shift = Self::granularity_log2() + FLLEN as u32;
        1 << shift
    }

    /// `insert_free_block_ptr` provides NonNull<[u8]> based interface, but Verus doesn't handle
    /// subtile properties like "dereferencing the length field of slice pointer doesn't dereference the
    /// entire slice pointer (thus safe)". This assumption used in `nonnull_slice_len` in rlsf.
    ///
    /// TODO: As an option we can wrap the address based interface with slice pointer based one
    ///       `insert_free_block_ptr` out of Verus world and wrap/axiomize it with external_body annotation. 
    ///       (the postcondition would meet the precondition of `insert_free_block_ptr_aligned`)
    // TODO: update ghost_free_list/all_block_headers in insert_free_block_ptr_aligned()
    //#[verifier::external_body] // for spec debug
    unsafe fn insert_free_block_ptr_aligned(
        &mut self,
        start: *mut u8,
        size: usize,
        Tracked(points_to_block): Tracked<PointsToRaw>
    ) -> (r: Option<usize>)
    requires
        // Given memory must have continuous range as specified by start/size.
        points_to_block.is_range(start as usize as int, size as int),
        // Given pointer must be aligned
        start as usize as int % GRANULARITY as int == 0,
        // Tlsf is well-formed
        old(self).wf()
    ensures
        self.wf(),
        self.root_provenances@ is Some

        // Newly added free list nodes have their addresses in the given range (start..start+size)
        // Tlsf is well-formed
    {
        None
//        let tracked mut new_header;
//        let tracked mut mem_remains;
//
//        let mut size_remains = size;
//        let mut cursor = start as usize;
//
//
//        // TODO: state loop invariant that ensures `valid_block_size(chunk_size - GRANULARITY)`
//        while size_remains >= GRANULARITY * 2 /* header size + minimal allocation unit */ {
//            let chunk_size = size_remains.min(Self::max_pool_size());
//
//            assert(chunk_size % GRANULARITY == 0);
//
//            proof {
//                let (h, m) =
//                    points_to_block.split(set_int_range(cursor as int, cursor as int + GRANULARITY as int));
//                mem_remains = m;
//                new_header = h.into_typed(cursor);
//            }
//
//            // The new free block
//            // Safety: `cursor` is not zero.
//            let mut block = cursor as *mut FreeBlockHdr;
//
//            // Initialize the new free block
//            // NOTE: header size calculated as GRANULARITY
//            assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(chunk_size - GRANULARITY));
//            let idx = Self::map_floor(chunk_size - GRANULARITY)?;
//
//            // Write the header
//            // NOTE: because Verus doesn't supports field update through raw pointer,
//            //       we have to write it at once with `ptr_mut_write`.
//            ptr_mut_write(block, Tracked(&mut new_header),
//                FreeBlockHdr {
//                    common: BlockHdr {
//                        size: chunk_size - GRANULARITY,
//                        prev_phys_block: None,
//                    },
//                    next_free: None,
//                    prev_free: None,
//                });
//
//            // Link to the list
//            self.free_list_push_front(idx, block, Tracked(&mut new_header));
//
//            // Update bitmaps
//            self.set_bit_for_index(idx);
//            //self.set_fl_bitmap(fl as u32);
//            //self.sl_bitmap[fl].set_bit(sl as u32);
//
//
//
//            // Cap the end with a sentinel block (a permanently-used block)
//            let mut sentinel_block = ptr_ref(block, Tracked(&new_header))
//                .common
//                .next_phys_block()
//                .cast::<UsedBlockHdr>();
//
//            let tracked (sentinel_perm, m) = mem_remains.split(
//                set_int_range(cursor + (chunk_size - GRANULARITY), cursor + chunk_size)); // TODO: need to be confirmed
//            mem_remains = m;
//
//            ptr_mut_write(sentinel_block, Tracked(&mut sentinel_perm.into_typed((cursor + (chunk_size - GRANULARITY)) as usize)),
//                UsedBlockHdr { 
//                    common: BlockHdr {
//                        size: GRANULARITY | SIZE_USED | SIZE_SENTINEL,
//                        prev_phys_block: Some(block.cast()),
//                    }
//                });
//
//            // `cursor` can reach `usize::MAX + 1`, but in such a case, this
//            // iteration must be the last one
//            assert(cursor.checked_add(chunk_size).is_some() || size_remains == chunk_size);
//            size_remains -= chunk_size;
//            cursor = cursor.wrapping_add(chunk_size);
//        }
//
//        Some(cursor.wrapping_sub(start as usize))
//
//            // TODO: update gs.root_provenances
    }



    unsafe fn link_free_block(&mut self, mut block: *mut FreeBlockHdr, size: usize,
        Tracked(perm_block): Tracked<PointsTo<FreeBlockHdr>>)
        requires
            old(self).wf(),
            BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int),
            block == perm_block.ptr(),
            perm_block.is_init()
        ensures
            self.wf(),
            ({
                let BlockIndex(fl, sl) = choose|idx: BlockIndex<FLLEN, SLLEN>|
                        idx.wf() && idx.block_size_range().contains(size as int);
                self.first_free[fl as int][sl as int].wf_node_ptr(block)
            })
            // TODO: ensure that free list properly updated
    {
        assert(BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int));
        if let Some(BlockIndex(fl, sl)) = Self::map_floor(size) {
            self.free_list_push_front(BlockIndex(fl, sl), block, Tracked(perm_block));
            self.set_bit_for_index(BlockIndex(fl, sl));
            proof {
                assert(BlockIndex::<FLLEN,SLLEN>(fl, sl).block_size_range().contains(size as int));
                BlockIndex::<FLLEN,SLLEN>::index_exists_for_valid_size(size);
                assume(self.first_free[fl as int][sl as int].wf_node_ptr(block));
            }
        } else {
            // unreachable provided `valid_block_size(size)`
            unreachable_unchecked()
        }
    }

    unsafe fn unlink_free_block(&mut self, mut block: *mut FreeBlockHdr, size: usize,
        Tracked(perm_block): Tracked<PointsTo<FreeBlockHdr>>)
        requires
            old(self).wf(),
            BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int),
            exists|idx: BlockIndex<FLLEN, SLLEN>|
                // ensure that free list properly updated
                idx matches BlockIndex(fl, sl)
                    && #[trigger] idx.block_size_range().contains(size as int)
                    && old(self).first_free[fl as int][sl as int].wf_node_ptr(block)
        ensures
            self.wf(),
            ({
                // ensure that free list properly updated
                let BlockIndex(fl, sl) = choose|idx: BlockIndex<FLLEN, SLLEN>|
                    idx.block_size_range().contains(size as int);
                !self.first_free[fl as int][sl as int].wf_node_ptr(block)
            })
    {
        //TODO: self.first_free.unlink() & set_bit_for_index
        assert(BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int));
        if let Some(idx) = Self::map_floor(size) {
            self.free_list_unlink(idx, block)
        } else {
            // FIXME: how to use this: require false
            unreachable_unchecked()
        }
    }

    /// Search for a non-empty free block list for allocation.
    //#[verifier::external_body] // debug
    #[inline(always)]
    fn search_suitable_free_block_list_for_allocation(
        &self,
        min_size: usize,
    ) -> (r: Option<BlockIndex<FLLEN,SLLEN>>)
        requires self.wf()
        ensures
            r matches Some(idx) ==> idx.wf() &&
                !self.first_free[idx.0 as int][idx.1 as int].is_empty() &&
                idx.block_size_range().start() <= min_size as int
        // None ==> invalid size requested or there no free entry
    {
        let BlockIndex(mut fl, mut sl) = Self::map_ceil(min_size)?; // NOTE: return None if invalid size requested

        // Search in range `(fl, sl..SLLEN)`
        sl = bit_scan_forward(self.sl_bitmap[fl], sl as u32) as usize;
        if sl < SLLEN {
            //debug_assert!(self.sl_bitmap[fl].get_bit(sl as u32));

            return Some(BlockIndex(fl, sl));
        }

        // Search in range `(fl + 1.., ..)`
        fl = bit_scan_forward(self.fl_bitmap, fl as u32 + 1) as usize;
        if fl < FLLEN {
            //debug_assert!(self.fl_bitmap.get_bit(fl as u32));

            sl = self.sl_bitmap[fl].trailing_zeros() as usize;
            assert(sl < SLLEN);
            //if sl >= SLLEN {
                //debug_assert!(false, "bitmap contradiction");
                //unreachable!()
                //unsafe { unreachable_unchecked() };
            //}

            //debug_assert!(self.sl_bitmap[fl].get_bit(sl as u32));
            Some(BlockIndex(fl, sl))
        } else {
            None
        }
    }

    pub closed spec fn is_root_provenance<T>(self, ptr: *mut T) -> bool {
        let ptr = ptr@.provenance;
        self.root_provenances@ matches Some(ptr)
    }


    //-------------------------------------------
    //    Allocation & Deallocation interface
    //-------------------------------------------


    // TODO: refactor use Layout as an argument (external type?)
    // TODO: refactor array access to unchecked operations e.g. arr.get_unchecked_mut(i)
    //#[verifier::external_body] // for spec debug
    pub fn allocate(&mut self, size: usize, align: usize /* layout: Layout */) ->
        (r: (Option<(*mut u8, Tracked<PointsToRaw>, Tracked<DeallocToken>)>))
        requires
            /* TODO: Allocation precondition
             * - already initialized 
             * */
            old(self).wf()
        ensures
            // TODO: state that if there suitable block is available, the allocation succeed
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
                &&& !points_to@.dom().is_empty()
                &&& self.wf_dealloc(Ghost(tok@))
                &&& ptr@.provenance == points_to@.provenance()
                //&&& ptr@.metadata == Metadata::Thin
                &&& points_to@.is_range(ptr as usize as int, size as int)
                &&& ptr.addr() % align == 0
                &&& self.is_root_provenance(ptr)
            }),
            r matches None ==> old(self) == self,

            self.wf()
    {
        unsafe {
            // The extra bytes consumed by the header and padding.
            //
            // After choosing a free block, we need to adjust the payload's location
            // to meet the alignment requirement. Every block is aligned to
            // `GRANULARITY` bytes. `size_of::<UsedBlockHdr>` is `GRANULARITY / 2`
            // bytes, so the address immediately following `UsedBlockHdr` is only
            // aligned to `GRANULARITY / 2` bytes. Consequently, we need to insert
            // a padding containing at most `max(align - GRANULARITY / 2, 0)` bytes.
            let max_overhead =
                align.saturating_sub(GRANULARITY / 2) + mem::size_of::<UsedBlockHdr>();

            //NOTE: alignment (`align`) is arbitrary power of 2.
            //      But following prevents requests have insainly big alignment to be completed.
            //      i.e. search fails because the requested size is too big

            // Search for a suitable free block
            let search_size = size.checked_add(max_overhead)?;
            let search_size = search_size.checked_add(GRANULARITY - 1)? & !(GRANULARITY - 1);
            let BlockIndex(fl, sl) = self.search_suitable_free_block_list_for_allocation(search_size)?;

            // Detattch & get a free block from the list
            let first_free = self.free_list_pop_front(BlockIndex(fl, sl));
            // Get a free block: `block`
            let (block, Tracked(perm_block_header)) = if let Some(first_free) = first_free {
                first_free
            } else {
                // Unreachable provided `search_suitable_free_block_list_for_allocation`'s
                // postcondition
                unreachable_unchecked()
            };
            let Tracked(block_is_exposed) = expose_provenance(block);
            let (mut next_phys_block, Tracked(mut next_phys_block_pt)) = self.next_phys_block_of_fb(block, Tracked(&perm_block_header));
            let size_and_flags = ptr_ref(block, Tracked(&perm_block_header)).common.size;
            // NOTE: free block header has no flags -- only indicates about size
            let size = size_and_flags /* size_and_flags & SIZE_SIZE_MASK */;
            assert(size == size_and_flags & SIZE_SIZE_MASK);

            assert(size >= search_size);

            if self.first_free[fl][sl].is_empty() {
                // The free list is now empty - update the bitmap
                self.clear_bit_for_index(BlockIndex(fl, sl));
            }

            // Get permission for region managed by the header at `block`
            let tracked mut perm_block_block = PointsToRaw::empty(Provenance::null());
            assert(perm_block_block.is_range(block.addr() + GRANULARITY, size as int));

            // Decide the starting address of the payload
            let unaligned_ptr = block.addr() + mem::size_of::<UsedBlockHdr>();
            let ptr: *mut u8 = with_exposed_provenance(
                unaligned_ptr.wrapping_add(align - 1) & !(align - 1),
                Tracked(block_is_exposed));
            assert(ptr.addr() != 0);

            if align < GRANULARITY {
                assert(unaligned_ptr == ptr.addr());
            } else {
                assert(unaligned_ptr != ptr.addr());
            }

            // Calculate the actual overhead and the final block size of the
            // used block being created here
            let overhead = ptr.addr() - block.addr();
            assert(overhead <= max_overhead);

            let new_size = overhead + size;
            let new_size = (new_size + GRANULARITY - 1) & !(GRANULARITY - 1);
            assert(new_size <= search_size);

            let tracked mut new_block_block_perm = PointsToRaw::empty(Provenance::null());
            if new_size == size {
                // The allocation completely fills this free block.
                // Updating `next_phys_block.prev_phys_block` is unnecessary in this
                // case because it's still supposed to point to `block`.
            } else {
                // The allocation partially fills this free block. Create a new
                // free block header at `block + new_size..block + size`
                // of length (`new_free_block_size`).
                let new_block_addr = block.addr() + new_size;
                let mut new_free_block: *mut FreeBlockHdr =
                    with_exposed_provenance(new_block_addr, Tracked(block_is_exposed));
                let new_free_block_size = size - new_size;

                // Split permission for the new block
                let tracked (new_block_perm, perm_bb) =
                    perm_block_block.split(set_int_range(new_block_addr as int, new_block_addr + new_free_block_size as int));
                proof {
                    perm_block_block = perm_bb;
                }
                let tracked (new_block_header_perm, new_block_block_perm) =
                    new_block_perm.split(set_int_range(new_block_addr as int, new_block_addr as int + size_of::<FreeBlockHdr>() as int));
                let tracked mut new_block_header_perm = new_block_header_perm.into_typed(new_block_addr);
                proof {
                    new_block_block_perm = new_block_block_perm;
                }

                // Update `next_phys_block.prev_phys_block` to point to this new
                // free block
                // Invariant: No two adjacent free blocks
                //debug_assert!((next_phys_block.as_ref().size & SIZE_USED) != 0);
                let old_next_phys_block_size = ptr_ref(next_phys_block, Tracked(&next_phys_block_pt)).common.size;
                ptr_mut_write(next_phys_block, Tracked(&mut next_phys_block_pt), UsedBlockHdr {
                    common: BlockHdr {
                        size: old_next_phys_block_size,
                        prev_phys_block: Some(new_free_block as *mut BlockHdr),
                    }
                });

                // Create the new free block header
                ptr_mut_write(new_free_block, Tracked(&mut new_block_header_perm),
                    FreeBlockHdr {
                        prev_free: None,
                        next_free: None,
                        common: BlockHdr {
                            size: new_free_block_size,
                            prev_phys_block: Some(block as *mut BlockHdr)
                        }
                    });

                self.link_free_block(new_free_block,
                    new_free_block_size, Tracked(new_block_header_perm));
            }

            // Turn `block` into a used memory block and initialize the used block
            // header. `prev_phys_block` is already set.
            let old_block_prev_block =
                ptr_ref(block, Tracked(&perm_block_header)).common.prev_phys_block;
            let mut block = block as *mut UsedBlockHdr;

            let tracked perm_block_header = fbh_pt_into_ubh(perm_block_header);
            ptr_mut_write(block, Tracked(&mut perm_block_header), UsedBlockHdr {
                common: BlockHdr {
                    size: new_size | SIZE_USED,
                    prev_phys_block: old_block_prev_block
                }
            });

            let mut pad: Option<Tracked<PointsTo<UsedBlockPad>>> = None;

            // Place a `UsedBlockPad` (used by `used_block_hdr_for_allocation`)
            if align >= GRANULARITY {
                let pad_ptr = UsedBlockPad::get_for_allocation(ptr);
                let tracked (pad_perm, perm_bb) = perm_block_block.split(set_int_range(pad_ptr.addr() as int, 1));
                proof {
                    perm_block_block = perm_bb;
                }
                let tracked pad_perm = pad_perm.into_typed::<UsedBlockPad>(pad_ptr.addr());
                ptr_mut_write(pad_ptr, Tracked(&mut pad_perm), UsedBlockPad {
                    block_hdr: block as *mut UsedBlockHdr
                });
                pad = Some(Tracked(pad_perm));
            }

            proof {
                // TODO: update ghost states
                // * adjast perm_block_block to fit ptr..+(search_size - overhead)
            }

            // TODO: perm_block_block must be continuous?
            //      there unnecessary permission to "padding gap" here
            Some((ptr, Tracked(perm_block_block),
                Tracked(DeallocToken {
                    ptr: Ghost(block as *mut UsedBlockHdr),
                    pad
                })
            ))
        }
    }

    pub fn deallocate(&mut self,
        ptr: *mut u8, align: usize,
        Tracked(token): Tracked<DeallocToken>, //NOTE: pattern matching to move out token
        Tracked(points_to): Tracked<PointsToRaw>, // permssion to previously allocated region
    )
    requires old(self).wf(), old(self).wf_dealloc(Ghost(token))
    ensures self.wf()
    {
        // Safety: `ptr` is a previously allocated memory block with the same
        //         alignment as `align`. This is upheld by the caller.
        let block = Self::used_block_hdr_for_allocation(ptr, align, Tracked(token.pad));
        let tracked ubh_perm = None.tracked_unwrap();
        self.deallocate_block(block, Tracked(ubh_perm));
    }


    #[inline]
    //#[verifier::external_body] // debug
    unsafe fn deallocate_block(&mut self, mut block: *mut UsedBlockHdr,
        Tracked(ubh_perm): Tracked<PointsTo<UsedBlockHdr>>) {
        let mut size = ptr_ref(block, Tracked(&ubh_perm)).common.size & !SIZE_USED;
        //assert((ptr_ref(block, Tracked(&ubh_perm)).common.size & SIZE_USED) != 0);

        //// This variable tracks whose `prev_phys_block` we should update.
        //let mut new_next_phys_block;

        //// Merge the created hole with the next block if the next block is a
        //// free block
        //// Safety: `block.common` should be fully up-to-date and valid
        //let next_phys_block = block.as_ref().next_phys_block();
        //let next_phys_block_size_and_flags = next_phys_block.as_ref().size;
        //if (next_phys_block_size_and_flags & SIZE_USED) == 0 {
            //let next_phys_block_size = next_phys_block_size_and_flags;
            //debug_assert_eq!(
                //next_phys_block_size_and_flags & SIZE_SIZE_MASK,
                //next_phys_block_size
            //);

            //// It's coalescable. Add its size to `size`. This will transfer
            //// any `SIZE_LAST_IN_POOL` flag `next_phys_block` may have at
            //// the same time.
            //size += next_phys_block_size;

            //// Safety: `next_phys_block` is a free block and therefore is not a
            //// sentinel block
            //new_next_phys_block = next_phys_block.as_ref().next_phys_block();

            //// Unlink `next_phys_block`.
            //self.unlink_free_block(next_phys_block.cast(), next_phys_block_size);
        //} else {
            //new_next_phys_block = next_phys_block;
        //}

        //// Merge with the previous block if it's a free block.
        //if let Some(prev_phys_block) = block.as_ref().prev_phys_block {
            //let prev_phys_block_size_and_flags = prev_phys_block.as_ref().size;

            //if (prev_phys_block_size_and_flags & SIZE_USED) == 0 {
                //let prev_phys_block_size = prev_phys_block_size_and_flags;
                //debug_assert_eq!(
                    //prev_phys_block_size_and_flags & SIZE_SIZE_MASK,
                    //prev_phys_block_size
                //);

                //// It's coalescable. Add its size to `size`.
                //size += prev_phys_block_size;

                //// Unlink `prev_phys_block`.
                //self.unlink_free_block(prev_phys_block.cast(), prev_phys_block_size);

                //// Move `block` to where `prev_phys_block` is located. By doing
                //// this, `block` will implicitly inherit `prev_phys_block.
                //// as_ref().prev_phys_block`.
                //block = prev_phys_block;
            //}
        //}

        //// Write the new free block's size and flags.
        //debug_assert!((size & SIZE_USED) == 0);
        //block.as_mut().size = size;

        //// Link this free block to the corresponding free list
        //let block = block.cast::<FreeBlockHdr>();
        //self.link_free_block(block, size);

        //// Link `new_next_phys_block.prev_phys_block` to `block`
        //debug_assert_eq!(new_next_phys_block, block.as_ref().common.next_phys_block());
        //new_next_phys_block.as_mut().prev_phys_block = Some(block.cast());
    }

    // TODO: update ghost_free_list/all_block_headers in deallocate()

    /// Validity of blocks being deallocated
    ///
    /// allocated region and headers,
    /// - Must have same provenance with PointsToRaw that we got when called insert_free_block_ptr*
    ///
    ///TODO: Check equlity with `PtrData { ptr: tok.ptr, provenance: /* root provenance */, Thin }`
    /// TODO: formalize assumptions on the header of blocks being deallocated
    ///
    /// Assumption about deallocation
    ///
    /// - Given pointer must be previously allocated one
    ///     - NOTE: In Verus world, it's assured because `deallocate` requires PointsToRaw 
    /// - Header of the previously allocated pointer which going to deallocated, must have same size/flags as when it allocated
    ///     (NOTE: header integrity is assumed)
    pub closed spec fn wf_dealloc(&self, tok: Ghost<DeallocToken>) -> bool {
        true
    }

    #[verifier::external_body]
    fn free_list_pop_front(&mut self, idx: BlockIndex<FLLEN, SLLEN>)
        -> (r: Option<(*mut FreeBlockHdr, Tracked<PointsTo<FreeBlockHdr>>)>)
    {
        self.first_free[idx.0][idx.1].pop_front()
    }

    #[verifier::external_body]
    fn free_list_push_front(&mut self, idx: BlockIndex<FLLEN, SLLEN>,
            node: *mut FreeBlockHdr,
            Tracked(perm): Tracked<PointsTo<FreeBlockHdr>>)
        requires old(self).wf(),
            node == perm.ptr(),
            perm.is_init()
        ensures self.wf(),
            ({
                let ls = self.first_free[idx.0 as int][idx.1 as int];
                let old_ls = old(self).first_free[idx.0 as int][idx.1 as int];
                ls@ == seq![ls.perms@[node].value().common].add(old_ls@)
                    && ls.wf_node_ptr(node)
            })
            // TODO: propagate push_front postcondition
    {
        self.first_free[idx.0][idx.1].push_front(node, Tracked(perm));
    }

    #[verifier::external_body]
    fn free_list_unlink(&mut self, idx: BlockIndex<FLLEN, SLLEN>,
        node: *mut FreeBlockHdr)
        requires old(self).wf(),
            old(self).first_free[idx.0 as int][idx.1 as int].wf_node_ptr(node)
        ensures self.wf()
            // TODO: propagate unlink postcondition
    {
        self.first_free[idx.0][idx.1].unlink(node);
    }


    //#[verifier::external_body] //debug
    #[inline]
    unsafe fn used_block_hdr_for_allocation(
        ptr: *mut u8,
        align: usize,
        tracked Tracked(pad_perm): Tracked<Option<Tracked<PointsTo<UsedBlockPad>>>>
    ) -> *mut UsedBlockHdr
        requires
            align >= GRANULARITY ==> pad_perm is Some
    {
        if align >= GRANULARITY {
            // Read the header pointer
            //(*UsedBlockPad::get_for_allocation(ptr)).block_hdr
            //TODO: wf_dealloc(.., token) -->
            //      token.pad.ptr() == get_for_allocation(PTR_BEEN_DEALLOCATED)
            //      or in precondition?
            let ptr =
                UsedBlockPad::get_for_allocation(ptr);
            let tracked Tracked(perm) = pad_perm.tracked_unwrap();
            ptr_ref(ptr, Tracked(&perm)).block_hdr
        } else {
            let is_exposed = expose_provenance(ptr);
            let ptr = ptr as usize - (GRANULARITY / 2);
            with_exposed_provenance(ptr, is_exposed)
        }
    }


    // only used for updating `next_phys_block.prev_phys_block`
    fn next_phys_block_of_fb(&mut self, fbh: *mut FreeBlockHdr, Tracked(pt): Tracked<&PointsTo<FreeBlockHdr>>)
            //NOTE: sentinel is UsedBlockHdr
          -> (r: (*mut UsedBlockHdr, Tracked<PointsTo<UsedBlockHdr>>))
        requires old(self).wf(),
        // NOTE: by the existance of sentinel block, we can conclude that every usual block we can
        //       pop from the free list, we have following
            //exists|i: int| 0 <= i < old(self).gs.all_ptrs@.len() - 1 && #[trigger] old(self).gs.all_ptrs@[i] matches HeaderPointer::Free(fbh)
        ensures //self.wf(),
            //self.gs.all_ptrs@.contains(ghost_tlsf::HeaderPointer::Used(r.0)),
            r.0 == r.1@.ptr(),
    {
        let size = ptr_ref(fbh, Tracked(pt)).common.size & SIZE_SIZE_MASK;
        let next_phys_block_addr = (fbh as *mut u8) as usize + size;
        let pv = expose_provenance(fbh);
        let ptr: *mut UsedBlockHdr = with_exposed_provenance(next_phys_block_addr, pv);
        let tracked uhdr_perm = None.tracked_unwrap();

        (ptr, Tracked(uhdr_perm))
    }

    //fn next_phys_block_of_ub(&mut self, ubh: *mut UsedBlockHdr, Tracked(pt): Tracked<&PointsTo<UsedBlockHdr>>)
          //-> (r: (Option<*mut FreeBlockHdr>, Tracked<PointsTo<UsedBlockHdr>>))
    //{
    //}


    spec fn plat64_basics() -> bool
    {
        &&& GRANULARITY == 32
        &&& 0 <= Self::sli_spec() <= 6
        &&& Self::granularity_log2_spec() == 5
    }

    spec fn plat32_basics() -> bool
    {
        &&& GRANULARITY == 16
        &&& 0 <= Self::sli_spec() <= 5
        &&& Self::granularity_log2_spec() == 4
    }

    proof fn plat_basics()
        requires Self::parameter_validity()
        ensures
            usize::BITS == 64 ==> Self::plat64_basics(),
            usize::BITS == 32 ==> Self::plat32_basics(),
            pow2(Self::sli_spec() as nat) == SLLEN

    {
        lemma_pow2_values();
        lemma_log2_values();
        Self::sli_pow2_is_sllen();
        assert(0 <= Self::sli_spec()) by {
            assert(0 < SLLEN);
            vstd::arithmetic::logarithm::lemma_log_is_ordered(2, 0, SLLEN as int);
        };
        if usize::BITS == 64 {
            vstd::arithmetic::logarithm::lemma_log_is_ordered(2, SLLEN as int, 64);
            assert(Self::plat64_basics());
        } else if usize::BITS == 32 {
            vstd::arithmetic::logarithm::lemma_log_is_ordered(2, SLLEN as int, 32);
            assert(Self::plat32_basics());
        }
    }

    spec fn free_header_ptrs(self) -> Set<*mut FreeBlockHdr> {
        arbitrary()
        //Seq::new(FLLEN as nat, |i: int| Seq::new(SLLEN as nat, |j: int| self.first_free[i][j]@).to_set()).to_set()
    }


    /// Get the next block, assuming it exists.
    ///
    /// # Safety
    ///
    /// `self` must have a next block (it must not be the sentinel block in a
    /// pool).
    ///
    /// e.g. splitting a large block into two (continuous) small blocks 
    #[inline(always)]
    #[verifier::external_body] // debug
    unsafe fn next_phys_block(&mut self, bhdr: &BlockHdr) -> (r: (*mut BlockHdr, Tracked<BlockPerm>))
        requires old(self).wf_all_blocks(), /* and bhdr is not sentinel */
        ensures r.0 == r.1@.bhdr_ptr()
    {
        let ptr = ((bhdr as *const _ as *mut u8).add(bhdr.size & SIZE_SIZE_MASK)).cast();
        let tracked mut perm: BlockPerm;

        proof {
            let i = choose|i: int| bhdr == self.all_blocks@[i].to_ptr() as *mut BlockHdr;
            let blk = self.all_blocks@[i];
            let next_block = self.phys_next_of(i).unwrap();
            affirm(!self.is_sentinel(blk));
            perm = match next_block {
                Block::Used(ptr) => {
                    let perm = self.used_info.perms@.tracked_remove(ptr);
                    BlockPerm::Used(Tracked(perm))
                }
                Block::Free(ptr, i, j) => {
                    let perm = self.first_free[i][j].perms@.tracked_remove(ptr);
                    BlockPerm::Free(Tracked(perm))
                }
            }
        }

        (ptr, Tracked(perm))
    }
}

impl !Copy for DeallocToken {}

// NOTE: Consider merging block in deallocate(), it's going to be impossible to 
//        peek usedness and merge if we give permission for hole header to the user
//        option: use header address as an ID
//TODO: add pointer to start of the allocated region & size of that block
//      * wf-ness:
//          * pointer
//              * the pointer is in the managed region 
//              * has same provenance with initial block
//              * aligned to GRANULARITY
//          * size
//              * valid size
//              * aligned to GRANULARITY
/// Deallocation token
/// 
/// * This leaved abstract & tracked
///     * `allocate` moves out DeallocToken to ensure absence of double free
tracked struct DeallocToken {
    /// Copy of header pointer of allocated region as an allocation identifier
    ghost ptr: Ghost<*mut UsedBlockHdr>,
    /// Padding if there exists
    /// invariant: pad.ptr() = pad_ptr = PTR_BEEN_DEALLOCATED - 1
    tracked pad: Option<Tracked<PointsTo<UsedBlockPad>>>
}

#[verifier::external_body]
const fn mem_replace<T>(dest: &mut T, src: T) -> (r: T)
    ensures
    r == *old(dest)
{
    core::mem::replace(dest, src)
}

proof fn fbh_pt_into_ubh(tracked mut fbh: PointsTo<FreeBlockHdr>) -> (tracked r: PointsTo<UsedBlockHdr>) {
    fbh.leak_contents();
    let tracked fbh_raw = fbh.into_raw();
    fbh_raw.into_typed(size_of::<UsedBlockHdr>())
}


#[macro_export]
macro_rules! nth_bit_macro {
    ($a:expr, $b:expr) => {{
        (0x1usize & ($a >> $b)) == 1
    }};
}

#[macro_export]
macro_rules! nth_bit {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(nth_bit_macro!($($a)*))
    }
}

} // verus!
