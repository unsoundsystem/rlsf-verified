//#![feature(const_mut_refs)]
//#![feature(const_replace)]
//#![feature(strict_provenance)]
#![allow(unused_imports)]
#![no_std]

mod bits;
mod block_index;
//mod rational_numbers;
mod half_open_range;
mod linked_list;
mod relation_utils;
//mod ghost_tlsf;
mod all_blocks;
mod bitmap;
mod block;
mod mapping;
mod parameters;

use vstd::prelude::*;

verus! {
use vstd::pervasive::*;
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
#[cfg(verus_keep_ghost)]
use vstd::raw_ptr::{ptr_from_data, PtrData};
use vstd::raw_ptr::{
    ptr_mut_read, ptr_mut_write, ptr_ref2, ptr_ref,
    PointsToRaw, PointsTo, Metadata, Provenance,
    expose_provenance, with_exposed_provenance,
    IsExposed
};
#[cfg(verus_keep_ghost)]
use vstd::set_lib::set_int_range;
use vstd::calc_macro::calc;
use core::marker::PhantomData;
use vstd::{seq::*, seq_lib::*, bytes::*};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::{logarithm::log, power2::pow2, power::pow};
use core::alloc::Layout;
use core::mem;
use crate::bits::*;
//#[cfg(verus_keep_ghost)]
//use crate::bits::bit_scan_forward;
use crate::block_index::BlockIndex;
//use crate::rational_numbers::{Rational, rational_number_facts, rational_number_properties};
use vstd::array::*;
use core::hint::unreachable_unchecked;
//use ghost_tlsf::{UsedInfo, Block, BlockPerm};
use crate::block::*;
use crate::parameters::*;
use crate::all_blocks::*;

#[cfg(target_pointer_width = "64")]
global size_of usize == 8;


#[verifier::reject_recursive_types(FLLEN)]
#[verifier::reject_recursive_types(SLLEN)]
pub struct Tlsf<'pool, const FLLEN: usize, const SLLEN: usize> {
    pub fl_bitmap: usize,
    /// `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
    pub sl_bitmap: [usize; FLLEN],
    pub first_free: [[Option<*mut BlockHdr>; SLLEN]; FLLEN],
    //FIXME: is it valid to have it? clarify which parts of memory is delegated to user.
    pub used_info: UsedInfo,
    pub _phantom: PhantomData<&'pool ()>,

    /// represents region managed by this allocator
    pub valid_range: Ghost<Set<int>>,

    /// ordered by address
    pub all_blocks: AllBlocks<FLLEN, SLLEN>,
    // FIXME: reflect acutual status of Tlsf field
    //      * option 1: move related filed to Tlsf
    //      * option 2: wf paramter taking Tlsf
    //      * option 3: ensure the condion in Tlsf method

    // provenance of initially added blocks
    // NOTE: Assuming that there is only single memory pool and once the pool registered, no more
    //       new region could be registered to extend.
    pub root_provenances: Tracked<Option<IsExposed>>,

    /// Auxiliary data used to verify segregated list
    pub shadow_freelist: Ghost<Map<BlockIndex<FLLEN, SLLEN>, Seq<*mut BlockHdr>>>
}
impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    /// well-formedness of Tlsf structure
    /// * freelist well-formedness
    ///   * TODO: blocks connected to freelist ordered by start address
    /// * bitmap is consistent with the freelist
    /// * TODO: blocks stored in the list have proper size as calculated from their index
    pub closed spec fn wf(self) -> bool {
        &&& self.all_blocks.wf()
        &&& self.all_freelist_wf()
        &&& Self::parameter_validity()

        // FIXME: restate it
        // Each free list is well-formed
        //&&& forall |i: int, j: int| BlockIndex::<FLLEN, SLLEN>::valid_block_index((i, j))
                //==> self.first_free[i][j].wf()

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
                pad_perms: Tracked(Map::tracked_empty())
            },
            all_blocks: AllBlocks::empty(),
            valid_range: Ghost(Set::empty()),
            root_provenances: Tracked(None),
            _phantom: PhantomData,
            shadow_freelist: Ghost(Map::empty())
        }
    }

    /// Due to `error: The verifier does not yet support the following Rust feature: array-fill expresion with non-copy type`
    #[verifier::external_body]
    const fn initial_free_lists() -> (r: [[Option<*mut BlockHdr>; SLLEN]; FLLEN])
        //ensures forall|i: int, j: int| r[i][j]@.len() == 0
    {
        [const { [None; SLLEN] }; FLLEN]
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
                // FIXME:
                // !self.first_free[idx.0 as int][idx.1 as int].is_empty() &&
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
        let pv = ptr@.provenance;
        self.root_provenances@ matches Some(ex) && ex.provenance() == pv
    }


    //-------------------------------------------
    //    Allocation & Deallocation interface
    //-------------------------------------------


    // TODO: refactor use Layout as an argument (external type?)
    // TODO: refactor array access to unchecked operations e.g. arr.get_unchecked_mut(i)
    #[verifier::external_body] // for spec debug
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

            // Search for a suitable free block
            let search_size = size.checked_add(max_overhead)?;
            let search_size = search_size.checked_add(GRANULARITY - 1)? & !(GRANULARITY - 1);
            let idx = self.search_suitable_free_block_list_for_allocation(search_size)?;
            let BlockIndex(fl, sl) = idx;

            let tracked mut old_head_perm: BlockPerm; // permission for first_free
            let tracked mut new_head_perm: BlockPerm; // permission for next_free

            // Get a free block: `block`
            //let first_free = self.first_free[fl][sl].unwrap();
            let block = self.first_free[fl][sl].unwrap();

            let mut next_phys_block = BlockHdr::next_phys_block(block, Tracked(old_head_perm));
            let tracked next_phys_block_perm: PointsTo<BlockHdr> = {
                let i = choose|i: int| self.all_blocks.ptrs@[i] == next_phys_block;
                let perm = self.all_blocks.perms.borrow_mut().tracked_remove(self.all_blocks.phys_next_of(i).unwrap());
                perm.points_to
            };
            let size_and_flags = ptr_ref(block, Tracked(&old_head_perm.points_to)).size;
            let size = size_and_flags /* size_and_flags & SIZE_SIZE_MASK */;
            //debug_assert_eq!(size, size_and_flags & SIZE_SIZE_MASK);

            //debug_assert!(size >= search_size);

            // Unlink the free block. We are not using `unlink_free_block` because
            // we already know `(fl, sl)` and that `block.prev_free` is `None`.
            {
                let block_freelink = get_freelink_ptr(block);
                let tracked block_freelink_perm = old_head_perm.free_link_perm.unwrap();
                Self::set_freelist(&mut self.first_free, idx, ptr_ref(block_freelink, Tracked(&block_freelink_perm)).next_free);
            }
            if self.first_free[fl][sl].is_some() {
                let next_free = self.first_free[fl][sl].unwrap();
                let next_free_link = get_freelink_ptr(next_free);
                ptr_mut_write(next_free_link,
                    Tracked(&mut new_head_perm.free_link_perm.unwrap()),
                    FreeLink {
                        next_free: ptr_ref(next_free_link, Tracked(&new_head_perm.free_link_perm.unwrap())).next_free,
                        prev_free: None,
                    },
                    );
            } else {
                // The free list is now empty - update the bitmap
                self.clear_bit_for_sl(idx);
            }

            //// Decide the starting address of the payload
            let unaligned_ptr =
                (block as *mut u8).wrapping_add(size_of::<UsedBlockHdr>());
            let ptr = round_up(unaligned_ptr, align);

            //if align < GRANULARITY {
                //assert(unaligned_ptr ==  ptr.as_ptr());
            //} else {
                //assert(unaligned_ptr != ptr.as_ptr());
            //}

            //// Calculate the actual overhead and the final block size of the
            //// used block being created here
            let overhead = ptr as usize - block as usize;
            assert(overhead <= max_overhead);

            let new_size = overhead + size;
            let new_size = (new_size + GRANULARITY - 1) & !(GRANULARITY - 1);
            //assert(new_size <= search_size);

            //let tracked mut 

            // Permission object for `ptr`
             let tracked mut new_block_perm = old_head_perm;
            if new_size == size {
                // The allocation completely fills this free block.
                // Updating `next_phys_block.prev_phys_block` is unnecessary in this
                // case because it's still supposed to point to `block`.
            } else {
                // The allocation partially fills this free block. Create a new
                // free block header at `block + new_size..block + size`
                // of length (`new_free_block_size`).
                let new_free_block: *mut BlockHdr = (block as usize + new_size) as *mut _;
                let new_free_block_size = size - new_size;

                let tracked (m1, m2) = old_head_perm.mem.split(set_int_range(block as int, (block as int) + new_size as int));
                old_head_perm.mem = m2;

                let tracked (new_block_header_perm, m3) =
                    m1.split(set_int_range(block as int, (block as int) + size_of::<BlockHdr>() as int));
                // NOTE: previously new_free_block_perm
                new_block_perm = BlockPerm {
                    points_to: new_block_header_perm.into_typed::<BlockHdr>(block as usize),
                    free_link_perm: None,
                    mem: m3,
                };


                // Update `next_phys_block.prev_phys_block` to point to this new
                // free block
                // Invariant: No two adjacent free blocks
                //debug_assert!((next_phys_block.as_ref().size & SIZE_USED) != 0);
                ptr_mut_write(next_phys_block, Tracked(&mut next_phys_block_perm),
                    BlockHdr {
                        size: ptr_ref(next_phys_block, Tracked(&next_phys_block_perm)).size,
                        prev_phys_block: Some(new_free_block)
                    });


                // Create the new free block header
                ptr_mut_write(new_free_block, Tracked(&mut new_block_perm.points_to),
                    BlockHdr {
                        size: new_free_block_size,
                        prev_phys_block: Some(block.cast()),
                    });
                // NOTE: This unwrap panics when invalid size is provided
                let new_block_idx = Self::map_floor(new_free_block_size).unwrap();
                self.link_free_block(new_block_idx, new_free_block, Tracked(new_block_perm));
            }

            //// Turn `block` into a used memory block and initialize the used block
            //// header. `prev_phys_block` is already set.
            //let mut block = block.cast::<UsedBlockHdr>();
            ptr_mut_write(block, Tracked(&mut old_head_perm.points_to),
                BlockHdr {
                    size: new_size | SIZE_USED,
                    prev_phys_block: ptr_ref(block, Tracked(&old_head_perm.points_to)).prev_phys_block
                });

            //// Place a `UsedBlockPad` (used by `used_block_hdr_for_allocation`)
            if align >= GRANULARITY {
                let tracked mut pad: PointsTo<UsedBlockPad> = self.used_info.pad_perms.borrow_mut().tracked_remove(ptr);
                ptr_mut_write(UsedBlockPad::get_for_allocation(ptr), Tracked(&mut pad),
                    UsedBlockPad { block_hdr: block as *mut UsedBlockHdr });
                proof {
                    self.used_info.pad_perms.borrow_mut().tracked_insert(ptr, pad);
                }
            }

            Some((ptr, Tracked(new_block_perm.mem), Tracked(DeallocToken)))
        }
    }

    /// used_info.pad_perms.contians_key(get_for_allocation(ptr)) can be assumed
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
        let block = unsafe { self.used_block_hdr_for_allocation(ptr, align) };
        let tracked ubh_perm = None.tracked_unwrap();
        unsafe { self.deallocate_block(block, Tracked(ubh_perm)) };
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


    //#[verifier::external_body] //debug
    #[inline]
    unsafe fn used_block_hdr_for_allocation(
        &mut self,
        ptr: *mut u8,
        align: usize,
    ) -> *mut UsedBlockHdr
    {
        if align >= GRANULARITY {
            // Read the header pointer
            //(*UsedBlockPad::get_for_allocation(ptr)).block_hdr
            //TODO: wf_dealloc(.., token) -->
            //      token.pad.ptr() == get_for_allocation(PTR_BEEN_DEALLOCATED)
            //      or in precondition?
            let tracked mut pad_perm: PointsTo<UsedBlockPad> = self.used_info.pad_perms.borrow_mut().tracked_remove(ptr);
            let ptr =
                UsedBlockPad::get_for_allocation(ptr);
            ptr_ref(ptr, Tracked(&pad_perm)).block_hdr
        } else {
            let is_exposed = expose_provenance(ptr);
            let ptr = ptr as usize - (GRANULARITY / 2);
            with_exposed_provenance(ptr, is_exposed)
        }
    }


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
    unsafe fn next_phys_block(&mut self, bhdr: *mut BlockHdr) -> (r: (*mut BlockHdr, BlockPerm))
        requires
            old(self).all_blocks.wf(),
            old(self).all_blocks.contains(bhdr),
            !old(self).all_blocks.is_sentinel_pointer(bhdr),
        ensures r.1.wf(), //r.0 == r.1.bhdr_ptr()

    {
        unimplemented!()
        //let ptr = ((bhdr as *mut u8).add((ptr_ref(block, Tracked(&perm_block_header)).size) & SIZE_SIZE_MASK)).cast::<BlockHdr>();
        //let tracked mut perm: BlockPerm;


        //proof {
            //let i = choose|i: int| bhdr == self.all_blocks@[i].to_ptr();
            //let blk = self.all_blocks@[i];
            //let next_block = self.phys_next_of(i).unwrap();
            ////affirm(!self.is_sentinel(blk));
            //perm = match next_block {
                //Block::Used(ptr) => {
                    //let perm = self.used_info.perms@.tracked_remove(ptr);
                    //BlockPerm::Used { block: next_block, perm: Tracked(perm) }
                //}
                //Block::Free(ptr, i, j) => {
                    //let perm = self.first_free[i][j].perms@.tracked_remove(ptr);
                    //BlockPerm::Free { block: next_block, perm: Tracked(perm) }
                //}
            //}
        //}


        ////let size = ptr_ref(fbh, Tracked(pt)).common.size & SIZE_SIZE_MASK;
        ////let next_phys_block_addr = (fbh as *mut u8) as usize + size;
        ////let pv = expose_provenance(fbh);
        ////let ptr: *mut UsedBlockHdr = with_exposed_provenance(next_phys_block_addr, pv);
        ////let tracked uhdr_perm = None.tracked_unwrap();


        //(ptr, perm)
    }
}

//impl !Copy for DeallocToken {}

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
tracked struct DeallocToken;
//{
    ///// Copy of header pointer of allocated region as an allocation identifier
    //ghost ptr: Ghost<*mut UsedBlockHdr>,
    ///// Padding if there exists
    ///// invariant: pad.ptr() = pad_ptr = PTR_BEEN_DEALLOCATED - 1
    //tracked pad: Option<Tracked<PointsTo<UsedBlockPad>>>
//}


#[inline]
pub unsafe fn round_up(ptr: *mut u8, align: usize) -> *mut u8
    requires is_power_of_two(align as int)
    ensures
{
    let prov = expose_provenance(ptr);
    with_exposed_provenance(
        (ptr as usize).wrapping_add(align - 1) & !(align as usize - 1),
        prov)

    //ptr.map_addr(|addr| addr.wrapping_add(align - 1) & !(align - 1))
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

// FIXME: following MUST be commented out while `cargo build`
pub assume_specification [usize::leading_zeros] (x: usize) -> (r: u32)
    ensures r == usize_leading_zeros(x)
    opens_invariants none
    no_unwind;

pub assume_specification [usize::trailing_zeros] (x: usize) -> (r: u32)
    ensures r == usize_trailing_zeros(x)
    opens_invariants none
    no_unwind;

pub assume_specification [usize::rotate_right] (x: usize, n: u32) -> (r: usize)
    // This primitive cast just work as usual exec code
    // NOTE: is it ok? primitive cast really just reinterpet bytes?
    //      ref. `unsigned_to_signed`
    ensures r == usize_rotate_right(x, n as i32)
    opens_invariants none
    no_unwind;

} // verus!
