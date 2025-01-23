#![feature(const_mut_refs)]
#![feature(const_replace)]

mod bits;
mod block_index;
mod rational_numbers;
mod relation_utils;
mod half_open_range;

use vstd::prelude::*;

verus! {
use vstd::raw_ptr::{ptr_mut_write, ptr_ref, PointsToRaw, PointsTo};
use vstd::set_lib::set_int_range;
use std::marker::PhantomData;
use vstd::{seq::*, seq_lib::*, bytes::*};
use vstd::arithmetic::{logarithm::log, power2::pow2};
use core::alloc::Layout;
use core::mem;
use crate::bits::{
    usize_trailing_zeros, is_power_of_two
};
use crate::block_index::BlockIndex;
use crate::rational_numbers::Rational;

// for codes being executed
macro_rules! get_bit {
    ($a:expr, $b:expr) => {{
        (0x1usize & ($a >> $b)) == 1
    }};
}

// for spec/proof codes
macro_rules! nth_bit {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bit!($($a)*))
    }
}

pub struct Tlsf<'pool, const FLLEN: usize, const SLLEN: usize> {
    fl_bitmap: usize,
    /// `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
    sl_bitmap: [usize; FLLEN],
    first_free: [[Option<*mut FreeBlockHdr>; SLLEN]; FLLEN],
    gs: Ghost<GhostTlsf>,
    _phantom: PhantomData<&'pool ()>,
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
const SIZE_SIZE_MASK: usize =  0; // !((1 << ex_usize_trailing_zeros(GRANULARITY)) - 1); // FIXME

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
    /// Get the next block, assuming it exists.
    ///
    /// # Safety
    ///
    /// `self` must have a next block (it must not be the sentinel block in a
    /// pool).
    /// TODO: must consider the cases that non-continuous chunks are added
    #[inline(always)]
    #[verifier::external] // debug
    unsafe fn next_phys_block(&self) -> *mut BlockHdr {
        ((self as *const _ as *mut u8).add(self.size & SIZE_SIZE_MASK)).cast()
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

#[repr(C)]
struct FreeBlockHdr {
    common: BlockHdr,
    next_free: Option<*mut FreeBlockHdr>,
    prev_free: Option<*mut FreeBlockHdr>,
}


//impl UsedBlockPad {
    //#[inline]
    //fn get_for_allocation(ptr: *mut u8) -> *mut Self {
        //ptr.cast::<Self>().wrapping_sub(1)
    //}
//}

/// A proof constract tracking information about Tlsf struct
struct GhostTlsf {
    /// Things we have to track
    /// * all `PointsTo`s related to registered blocks
    /// * things needed to track the list views 
    ///     * singly linked list by prev_phys_block chain 
    ///      NOTE: This contains allocated blocks
    ///     * doubly linked list by FreeBlockHdr fields
    ///
    /// Remark: ghost_free_list[fl][sl] contains size of blocks in
    ///     BlockIndex(fl, sl).block_size_range()
    tracked ghost_free_list: Seq<Seq<Option<PointsTo<FreeBlockHdr>>>>,

    //FIXME: the points to here overwraps with avobe ghost_free_list
    //TODO: We need a way to obtain permission from block to adjacent
    // List of all BlockHdrs ordered by their addresses.
    tracked all_block_headers: Seq<PointsTo<BlockHdr>>,
}

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    // workaround: verus doesn't support constants definitions in impl.
    //const SLI: u32 = SLLEN.trailing_zeros();
    const fn sli() -> (r: u32)
        ensures r == Self::sli_spec()
    { SLLEN.trailing_zeros() }

    spec fn sli_spec() -> int {
        log(2, SLLEN as int)
    }

    const fn granularity_log2() -> (r: u32)
        requires is_power_of_two(GRANULARITY as int)
        ensures r == Self::granularity_log2_spec()
    {
        GRANULARITY.trailing_zeros()
    }

    spec fn granularity_log2_spec() -> int {
        log(2, GRANULARITY as int)
    }

    /// well-formedness of Tlsf structure
    /// * freelist well-formedness
    ///   * TODO: blocks connected to freelist ordered by start address
    /// * bitmap is consistent with the freelist
    /// * TODO: blocks stored in the list have proper size as calculated from their index
    pub closed spec fn wf(&self) -> bool {
        &&& self.bitmap_wf()
        &&& is_power_of_two(SLLEN as int) && SLLEN <= usize::BITS
    }

    pub const fn new() -> Self {
        Self {
            fl_bitmap: 0,
            sl_bitmap: [0; FLLEN],
            first_free: [[None; SLLEN]; FLLEN],
            gs: Ghost(GhostTlsf {
                ghost_free_list: Seq::new(FLLEN as nat, |i: int| Seq::new(SLLEN as nat, |j: int| None)),
                all_block_headers: Seq::empty(),
            }),
            _phantom: PhantomData
        }
    }

    #[verifier::external_body]
    #[inline(always)]
    fn update_bitmap(&mut self, idx: BlockIndex<FLLEN, SLLEN>)
        requires idx.wf(),
        ensures ({ let BlockIndex(fl, sl) = idx;
                &&& self.fl_bitmap == (old(self).fl_bitmap | (1usize << fl as int))
                &&& self.sl_bitmap[fl as int] == (old(self).sl_bitmap[fl as int] | (1usize << sl as int))
                &&& self.wf() })
                // NOTE: this function should be used to fix the inconsistency bitween
                //       freelist & bitmaps (thus the postcondition)

    {
        let BlockIndex(fl, sl) = idx;
        self.fl_bitmap = self.fl_bitmap | (1usize << fl);
        self.sl_bitmap[fl] = self.sl_bitmap[fl] | (1usize << sl); // FIXME: Verus doesn't allow lhs
                                                                  // mutation
    }

    //-------------------------------------------------------
    //    Free list index calculation & bitmap properties
    //-------------------------------------------------------

    /// TODO: state and proof more detailed property about index calculation and relate with
    /// `map_ceil` / `map_floor`
    //#[verifier::external_body] // debug
    pub fn map_ceil(size: usize) -> (r: BlockIndex<FLLEN, SLLEN>)
        requires
            BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int),
        ensures
            r.wf(),
            forall|sz: int| r.block_size_range_set().contains(Rational::from_int(sz)) ==> sz >= size
            // TODO: ensure `r` is index of freelist that all of its elements larger or equal to
            //       the requested size
    {
        assert(GRANULARITY < usize::BITS);
        // subtracting `Self::granularity_log2()` because actual freelist starts from `2^Self::granularity_log2()`
        let mut fl = usize::BITS - Self::granularity_log2() - 1 - size.leading_zeros();
        assert(fl == log(2, size as int) - log(2, GRANULARITY as int)); // TODO

        // The shift amount can be negative, and rotation lets us handle both
        // cases without branching.
        // negative case can occur when all of following holds
        // - fl == 0
        //   - log2(size) == GRANULARITY_LOG2 i.e. size == GRANULARITY
        // - SLI > GRANULARITY_LOG2 i.e. SLLEN > GRANULARITY
        // 
        // FIXME: guessing the negative case is for treating this specific case
        // FIXME(if i wrong):  the negative case occurs only when
        //                     requested size is GRANULARITY (i.e. fl=0)
        //      - Supposing 64bit platform, SLI <= 6 and GRANULARITY_LOG2 = 5.
        //        thus when `SLI > fl + GRANULARITY_LOG2` holds, fl must be 0
        //      - Supposing 32bit platform, SLI <= 5 and GRANULARITY_LOG2 = 4.
        //        thus when `SLI > fl + GRANULARITY_LOG2` holds, fl must be 0
        //      - Generally SLI <= log2(sizeof(usize)*8) = log2(sizeof(usize)) + 3 and
        //        GRANULARITY_LOG2 = log2(sizeof(usize)*4) = log2(sizeof(usize)) + 2
        //        thus when `SLI > fl + GRANULARITY_LOG2`
        //        (i.e. `3 > fl + 2`) holds, fl must be 0
        //
        // (NOTE: this *is* unusual case! target usecase configured as SLLEN = 64)
        let mut sl = size.rotate_right((fl + Self::granularity_log2()).wrapping_sub(Self::sli()));

        // The most significant one of `size` should be now at `sl[SLI]`
        assert(((sl >> Self::sli_spec()) & 1) == 1);

        // Underflowed digits appear in `sl[SLI + 1..USIZE-BITS]`. They should
        // be rounded up
        // NOTE:
        // - `sl & (SLLEN - 1)` mask with second-level index set (sl[0..=SLI]
        // - because of rotating, if above underflowed, there bits present in sl[SLI+1..]
        //   so round up
        // NOTE: underflowed digits means reminder of dividing size by second-level block size
        //       thus they must be rounded up to return appropriate index for allocating from
        // TODO: how to formalize this?
        sl = (sl & (SLLEN - 1)) + bool_to_usize(sl >= (1 << (Self::sli() + 1)));

        // if sl[SLI] { fl += 1; sl = 0; }
        fl = fl + (sl >> Self::sli()) as u32;

        // FIXME: fl can be greater than FLLEN.
        //        in Verus this not a problem but for real use (interoperation with unverified code)
        //        validation must be made.
        //
        //        - opiton: in the original code, result was Option<(usize, usize)>, seems this was the right
        //                  way to insert validation. mapping function should be partial to accept
        //                  any size of request.

        BlockIndex(fl as usize, sl & (SLLEN - 1))
    }

    #[inline(always)]
    //#[verifier::external_body] // debug
    fn map_floor(size: usize) -> (r: BlockIndex<FLLEN, SLLEN>)
        requires BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int),
        ensures r.wf(),
            r.block_size_range_set().contains(Rational::from_int(size as int)),
        // ensuring `r` is index of freelist appropriate to store the block of size requested
    {
        assert(size >= GRANULARITY);
        assert(size % GRANULARITY == 0);
        let mut fl = usize::BITS - Self::granularity_log2() - 1 - size.leading_zeros();

        // The shift amount can be negative, and rotation lets us handle both
        // cases without branching. Underflowed digits can be simply masked out
        // in `map_floor`.
        let mut sl = size.rotate_right((fl + Self::granularity_log2()).wrapping_sub(Self::sli()));

        // The most significant one of `size` should be now at `sl[SLI]`
        assert(((sl >> Self::sli_spec()) & 1) == 1);

        // FIXME: fl can be greater than FLLEN.
        //        in Verus this not a problem but for real use (interoperation with unverified code)
        //        validation must be made.

       BlockIndex(fl as usize, sl & (SLLEN - 1))
    }

    spec fn bitmap_wf(&self) -> bool {
        // TODO: state that self.fl_bitmap[0..GRANULARITY_LOG2] is zero?
        // `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
        forall|idx: BlockIndex<FLLEN, SLLEN>|  idx.wf() ==>
            nth_bit!(self.sl_bitmap[idx.0 as int], idx.1 as usize)
                <==> self.first_free[idx.0 as int][idx.1 as int].is_some()
    }


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
    ) -> Option<usize>
    requires
        // Given memory must have continuous range as specified by start/size.
        points_to_block.is_range(start as usize as int, size as int),
        // Given pointer must be aligned
        start as usize as int % GRANULARITY as int == 0,
        // Tlsf is well-formed
        // TODO: Is it reasonable to assume the free list is empty as a precondition?
        //       As I read the use case, there wasn't code adding new region twice.
    ensures
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
//                new_header = h.into_typed(cursor as int);
//            }
//
//            // The new free block
//            // Safety: `cursor` is not zero.
//            let mut block = cursor as *mut FreeBlockHdr;
//
//            // Initialize the new free block
//            // NOTE: header size calculated as GRANULARITY
//            assert(Self::valid_block_size(chunk_size - GRANULARITY));
//            let BlockIndex(fl, sl) = Self::map_floor(chunk_size - GRANULARITY);
//            let first_free = &mut self.first_free[fl][sl];
//            let next_free = mem::replace(first_free, Some(block));
//
//            // Obtain permssion for writing to the first node in the appropriate
//            // freelist to insert `block`
//            let tracked next_free_perm = self.gs@.ghost_free_list[fl as int][sl as int];
//
//            // Write the header
//            // NOTE: because Verus doesn't supports field update through raw pointer,
//            //       we have to write it at once with `ptr_mut_write`.
//            ptr_mut_write(block, Tracked(&mut new_header),
//            FreeBlockHdr {
//                common: BlockHdr {
//                    size: chunk_size - GRANULARITY,
//                    prev_phys_block: None,
//                },
//                next_free: next_free,
//                prev_free: None,
//            });
//
//            if let Some(mut next_free) = next_free {
//                //FIXME: looking for some way to eliminate this read
//                if let Some(next_free_perm) = next_free_perm {
//                    let &FreeBlockHdr { common: common_, next_free: next_free_, prev_free: prev_free_ }
//                        = ptr_ref(next_free, Tracked(&next_free_perm));
//                    ptr_mut_write(next_free, Tracked(&mut next_free_perm),
//                        FreeBlockHdr {
//                            common: common_,
//                            next_free: next_free_,
//                            prev_free: Some(block)
//                        }
//                    );
//                } else { assert(false) }
//                //next_free.prev_free = Some(block);
//            }
//            // Update bitmaps
//            self.update_bitmap(fl, sl);
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
    }



    // TODO: remove this
    #[verifier::external_body] // for spec debug
    unsafe fn link_free_block(&mut self, mut block: *mut FreeBlockHdr, size: usize)
        requires
            old(self).wf(),
            BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int),
        ensures
            self.wf()
    {
        unimplemented!()
        // if let Some((fl, sl)) = Self::map_floor(size) {
        //     //TODO
//      //       let first_free = &mut self.first_free[fl][sl];
//      //       let next_free = mem::replace(first_free, Some(block));
//      //       block.as_mut().next_free = next_free;
//      //       block.as_mut().prev_free = None;
//      //       if let Some(mut next_free) = next_free {
//      //           next_free.as_mut().prev_free = Some(block);
//      //       }
//
//      //       self.fl_bitmap.set_bit(fl as u32);
//      //       self.sl_bitmap[fl].set_bit(sl as u32);
        // } else {
        //     // TODO: how do we handle this error?
        // }
    }

    /// Search for a non-empty free block list for allocation.
    #[verifier::external_body] // debug
    #[inline(always)]
    fn search_suitable_free_block_list_for_allocation(
        &self,
        min_size: usize,
    ) -> (r: Option<(usize, usize)>)
        requires self.wf()
        ensures
        // None ==> invalid size requested or there no free entry
        // Some(fl, sl) ==> first_free[fl][sl].is_some()
    {
        //let (mut fl, mut sl) = Self::map_ceil(min_size)?; // TODO: return None if invalid size requested

        //// Search in range `(fl, sl..SLLEN)`
        //sl = self.sl_bitmap[fl].bit_scan_forward(sl as u32) as usize;
        //if sl < SLLEN {
            //debug_assert!(self.sl_bitmap[fl].get_bit(sl as u32));

            //return Some((fl, sl));
        //}

        //// Search in range `(fl + 1.., ..)`
        //fl = self.fl_bitmap.bit_scan_forward(fl as u32 + 1) as usize;
        //if fl < FLLEN {
            //debug_assert!(self.fl_bitmap.get_bit(fl as u32));

            //sl = self.sl_bitmap[fl].trailing_zeros() as usize;
            //if sl >= SLLEN {
                //debug_assert!(false, "bitmap contradiction");
                //unreachable!()
                ////unsafe { unreachable_unchecked() };
            //}

            //debug_assert!(self.sl_bitmap[fl].get_bit(sl as u32));
            //Some((fl, sl))
        //} else {
            //None
        //}
    }


    //-------------------------------------------
    //    Allocation & Deallocation interface
    //-------------------------------------------


    #[verifier::external_body] // for spec debug
    pub fn allocate(&mut self, size: usize, align: usize /* layout: Layout */) ->
        (r: (Option<*mut u8>, Tracked<PointsToRaw>, Tracked<Option<DeallocToken>>))
        requires
            /* TODO */
            old(self).wf()
        ensures
            ({  let (m, points_to, token) = r;
                m matches Some(mem) ==>
                    !points_to@.dom().is_empty() &&
                    (token@ matches Some(tok) && tok.wf()) &&
                    points_to@.dom().len() >= size /* &&
                    // TODO: spec without existential
                    (exists|nbytes: int| points_to@.is_range(mem as usize as int, nbytes) && nbytes >= size) &&
                    points_to.provenance() == old(self).ghost_free_list@[i][j].provenance */
                    /* TODO
                     * - points_to has size as requested
                     * - mem's start address is same as points_to
                     * */ }),
            ({  let (m, points_to, token) = r;
                m == None::<*mut u8> ==> points_to@.dom().is_empty() && token@ == None::<DeallocToken> }),
            self.wf()
    { 
//        unsafe {
//            // The extra bytes consumed by the header and padding.
//            //
//            // After choosing a free block, we need to adjust the payload's location
//            // to meet the alignment requirement. Every block is aligned to
//            // `GRANULARITY` bytes. `size_of::<UsedBlockHdr>` is `GRANULARITY / 2`
//            // bytes, so the address immediately following `UsedBlockHdr` is only
//            // aligned to `GRANULARITY / 2` bytes. Consequently, we need to insert
//            // a padding containing at most `max(align - GRANULARITY / 2, 0)` bytes.
//            let max_overhead =
//                layout.align().saturating_sub(GRANULARITY / 2) + mem::size_of::<UsedBlockHdr>();
//
//            // Search for a suitable free block
//            let search_size = layout.size().checked_add(max_overhead)?;
//            let search_size = search_size.checked_add(GRANULARITY - 1)? & !(GRANULARITY - 1);
//            let (fl, sl) = self.search_suitable_free_block_list_for_allocation(search_size)?;
//
//            // Get a free block: `block`
//            let first_free = self.first_free.get_unchecked_mut(fl).get_unchecked_mut(sl);
//            let block = first_free.unwrap_or_else(|| {
//                debug_assert!(false, "bitmap outdated");
//                // Safety: It's unreachable
//                unreachable_unchecked()
//            });
//            let mut next_phys_block = block.as_ref().common.next_phys_block();
//            let size_and_flags = block.as_ref().common.size;
//            let size = size_and_flags /* size_and_flags & SIZE_SIZE_MASK */;
//            debug_assert_eq!(size, size_and_flags & SIZE_SIZE_MASK);
//
//            debug_assert!(size >= search_size);
//
//            // Unlink the free block. We are not using `unlink_free_block` because
//            // we already know `(fl, sl)` and that `block.prev_free` is `None`.
//            *first_free = block.as_ref().next_free;
//            if let Some(mut next_free) = *first_free {
//                next_free.as_mut().prev_free = None;
//            } else {
//                // The free list is now empty - update the bitmap
//                let sl_bitmap = self.sl_bitmap.get_unchecked_mut(fl);
//                sl_bitmap.clear_bit(sl as u32);
//                if *sl_bitmap == SLBitmap::ZERO {
//                    self.fl_bitmap.clear_bit(fl as u32);
//                }
//            }
//
//            // Decide the starting address of the payload
//            let unaligned_ptr = block.as_ptr() as *mut u8 as usize + mem::size_of::<UsedBlockHdr>();
//            let ptr = NonNull::new_unchecked(
//                (unaligned_ptr.wrapping_add(layout.align() - 1) & !(layout.align() - 1)) as *mut u8,
//            );
//
//            if layout.align() < GRANULARITY {
//                debug_assert_eq!(unaligned_ptr, ptr.as_ptr() as usize);
//            } else {
//                debug_assert_ne!(unaligned_ptr, ptr.as_ptr() as usize);
//            }
//
//            // Calculate the actual overhead and the final block size of the
//            // used block being created here
//            let overhead = ptr.as_ptr() as usize - block.as_ptr() as usize;
//            debug_assert!(overhead <= max_overhead);
//
//            let new_size = overhead + layout.size();
//            let new_size = (new_size + GRANULARITY - 1) & !(GRANULARITY - 1);
//            debug_assert!(new_size <= search_size);
//
//            if new_size == size {
//                // The allocation completely fills this free block.
//                // Updating `next_phys_block.prev_phys_block` is unnecessary in this
//                // case because it's still supposed to point to `block`.
//            } else {
//                // The allocation partially fills this free block. Create a new
//                // free block header at `block + new_size..block + size`
//                // of length (`new_free_block_size`).
//                let mut new_free_block: NonNull<FreeBlockHdr> =
//                    NonNull::new_unchecked(block.cast::<u8>().as_ptr().add(new_size)).cast();
//                let new_free_block_size = size - new_size;
//
//                // Update `next_phys_block.prev_phys_block` to point to this new
//                // free block
//                // Invariant: No two adjacent free blocks
//                debug_assert!((next_phys_block.as_ref().size & SIZE_USED) != 0);
//                next_phys_block.as_mut().prev_phys_block = Some(new_free_block.cast());
//
//                // Create the new free block header
//                new_free_block.as_mut().common = BlockHdr {
//                    size: new_free_block_size,
//                    prev_phys_block: Some(block.cast()),
//                };
//                self.link_free_block(new_free_block, new_free_block_size);
//            }
//
//            // Turn `block` into a used memory block and initialize the used block
//            // header. `prev_phys_block` is already set.
//            let mut block = block.cast::<UsedBlockHdr>();
//            block.as_mut().common.size = new_size | SIZE_USED;
//
//            // Place a `UsedBlockPad` (used by `used_block_hdr_for_allocation`)
//            if layout.align() >= GRANULARITY {
//                (*UsedBlockPad::get_for_allocation(ptr)).block_hdr = block;
//            }
//
//            Some(ptr)
//        }
//
        unimplemented!()
    }
    // TODO: update ghost_free_list in allocate()

    #[verifier::external_body] // for spec debug
    pub fn deallocate(&mut self, ptr: *mut u8, align: usize, Tracked(token): Tracked<DeallocToken>)
    requires old(self).wf(), token.wf()
    ensures self.wf()
    { unimplemented!() }

    // TODO: update ghost_free_list/all_block_headers in deallocate()

}

impl !Copy for DeallocToken {}

/// FIXME: Consider merging block in deallocate(), it's going to be impossible to 
///        peek usedness and merge if we give permission for hole header to the user
///        option: use header address as an ID
struct DeallocToken {
    header: PointsTo<UsedBlockHdr>
}

impl DeallocToken {
    /// Validity of blocks being deallocated
    /// allocated region and headers,
    /// - Must have same provenance with PointsToRaw that we got when called insert_free_block_ptr*
    /// - Must have same size/flags as allocated (NOTE: header integrity is assumed)
    ///
    /// TODO: formalize assumptions on the header of blocks being deallocated
    pub closed spec fn wf(&self) -> bool {
        true
    }
}

#[inline(always)]
#[verifier::external_body]
fn bool_to_usize(b: bool) -> (r: usize)
    ensures
        b ==> r == 1,
        !b ==> r == 0
{
    b as usize
}

#[verifier::external_body]
const fn mem_replace<T>(dest: &mut T, src: T) -> (r: T)
    ensures
    r == *old(dest)
{
    core::mem::replace(dest, src)
}

} // verus!
