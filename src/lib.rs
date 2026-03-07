// vim: foldmethod=marker
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
mod ordered_pointer_list;
pub mod parameters;
pub mod unverified_api;

#[cfg(feature = "std")]
extern crate std;

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
#[cfg(verus_keep_ghost)]
use vstd::std_specs::bits::u64_trailing_zeros;
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
use crate::ordered_pointer_list::*;
use crate::unverified_api::*;
use core::ptr::null;

#[cfg(feature = "std")]
use std::sync::OnceLock;

#[cfg(feature = "std")]
static FIRST_BLOCK: OnceLock<usize> = OnceLock::new();

#[cfg(feature = "std")]
static SENTINEL: OnceLock<usize> = OnceLock::new();

#[cfg(target_pointer_width = "64")]
global layout usize is size == 8;

#[cfg(target_pointer_width = "64")]
global layout BlockHdr is size == 16, align == 8;

#[cfg(target_pointer_width = "64")]
global layout FreeLink is size == 16, align == 8;

#[verifier::reject_recursive_types(FLLEN)]
#[verifier::reject_recursive_types(SLLEN)]
#[repr(C)]
pub struct Tlsf<'pool, const FLLEN: usize, const SLLEN: usize> {
    pub fl_bitmap: usize,
    /// `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
    pub sl_bitmap: [usize; FLLEN],
    pub first_free: [[*mut BlockHdr; SLLEN]; FLLEN],
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
    pub shadow_freelist: Ghost<ShadowFreelist<FLLEN, SLLEN>>
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
        &&& self.size_class_condition()
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

    proof fn lemma_usize_add_le_from_int(x: usize, y: usize)
        requires (x as int) <= (usize::MAX - y) as int
        ensures x + y <= usize::MAX
    {
        assert(x <= usize::MAX - y) by (nonlinear_arith);
        assert(x + y <= usize::MAX) by (bit_vector);
    }

    proof fn lemma_checked_add_eq(x: usize, y: usize, res: usize)
        requires x.checked_add(y) == Some(res)
        ensures res == x + y
    {
        assert(x + y <= usize::MAX) by (nonlinear_arith);
        assert(res == (x + y) as usize) by (bit_vector);
        assert(res == x + y) by (bit_vector);
    }

    proof fn lemma_usize_add_le_mono(a: usize, b: usize, c: usize)
        requires
            a <= b,
            b + c <= usize::MAX,
        ensures
            a + c <= b + c
    {
        assert(a as int <= b as int) by (nonlinear_arith);
        assert(a as int + c as int <= b as int + c as int) by (nonlinear_arith);
        assert((a + c) as int <= (b + c) as int) by (nonlinear_arith);
        assert(a + c <= b + c) by (bit_vector);
    }

    proof fn lemma_usize_le_from_int(x: usize, y: usize)
        requires (x as int) <= (y as int)
        ensures x <= y
    {
        assert(x <= y) by (nonlinear_arith);
    }

    proof fn lemma_int_le_implies_usize_le(x: int, y: usize)
        requires 0 <= x, x <= y as int
        ensures (x as usize) <= y
    {
        assert((x as usize) <= y) by (nonlinear_arith);
    }

    proof fn lemma_usize_nonneg(u: usize)
        ensures 0 <= u as int
    {
        assert(0 <= u as int) by (bit_vector);
    }

    proof fn lemma_mark_used_preserves_size_bits(sz: usize)
        requires
            sz as int % GRANULARITY as int == 0,
            Self::parameter_validity(),
        ensures
            (sz & SIZE_SIZE_MASK) == sz,
            ((sz | SIZE_USED) & SIZE_SIZE_MASK) == sz,
    {
        assert(usize::BITS == 64) by (compute);
        assert(GRANULARITY == 32);
        assert(sz as int % 32 == 0);
        assert(SIZE_USED == 1);
        reveal(usize_trailing_zeros);
        reveal(u64_trailing_zeros);
        assert(SPEC_SIZE_SIZE_MASK == !31usize) by (compute);
        assert((sz & !31usize) == sz) by (bit_vector)
            requires sz as int % 32 == 0;
        assert(((sz | 1usize) & !31usize) == sz) by (bit_vector)
            requires sz as int % 32 == 0;
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
            shadow_freelist: Ghost(ShadowFreelist {
                m: Map::empty(),
                pi: Map::empty(),
            })
        }
    }

    /// Due to `error: The verifier does not yet support the following Rust feature: array-fill expresion with non-copy type`
    #[verifier::external_body]
    const fn initial_free_lists() -> (r: [[*mut BlockHdr; SLLEN]; FLLEN])
        ensures forall|i: int, j: int| r[i][j]@.addr == 0
    {
        [const { [null_bhdr(); SLLEN] }; FLLEN]
    }

    spec fn is_ii(self) -> bool {
        is_identity_injection::<FLLEN, SLLEN>(
            self.shadow_freelist@, self.all_blocks.ptrs@
        )
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

    #[cfg(feature = "std")]
    #[verifier::external_body]
    pub fn print_stat(&self) {
        use std::println;
        println!("----- stats start -----");
        println!("fl_bitmap: {:b}", self.fl_bitmap);
        println!("sl_bitmap: {:x?}", self.sl_bitmap);
        println!("== segregated free lists ==");
        for i in 0..FLLEN {
            for j in 0..SLLEN {
                if self.first_free[i][j] != null_bhdr() {
                    let mut first_free = self.first_free[i][j];
                    println!("({i}, {j}) =>");
                    while first_free != null_bhdr() {
                        let mut link = get_freelink_ptr(first_free);
                        println!("\tsize: {}, prev_phys_block: {:?}, next: {:?}, prev: {:?}",
                            unsafe { (*first_free).size },
                            unsafe { (*first_free).prev_phys_block },
                            unsafe { (*link).next_free },
                            unsafe { (*link).prev_free },
                        );
                        first_free = unsafe { (*link).next_free };
                    }
                }
            }
        }
        println!("== all blocks ==");
        let mut block = *FIRST_BLOCK.get_or_init(|| unreachable!()) as *mut BlockHdr;
        unsafe {
            println!("first block: {:?}", block.as_ref());
            while block != null_bhdr() {
                    println!("addr: {:x?}, block: {:?}, sentinel: {}",
                        block,
                        block.as_ref(),
                        block.as_ref().unwrap().size & SIZE_SENTINEL != 0);
                    if block.as_ref().unwrap().size & SIZE_SENTINEL != 0 {
                        break;
                    }
                    block = BlockHdr::next_phys_block(block, Tracked::assume_new());
            }
        }
        println!("-----  stats end  -----");
    }

    #[verifier::external_body]
    pub unsafe fn insert_free_block_ptr_aligned_test(
        &mut self,
        start: *mut u8,
        size: usize,
    ) -> (r: Option<usize>) {
        self.insert_free_block_ptr_aligned(start, size, Tracked::assume_new())
    }

    #[verifier::external_body]
    pub unsafe fn deallocate_ext(
        &mut self,
        ptr: *mut u8,
        align: usize
    ) {
        self.deallocate(ptr, align, Tracked::assume_new(), Tracked::assume_new())
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
    pub unsafe fn insert_free_block_ptr_aligned(
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
        //self.root_provenances@ is Some

        // Newly added free list nodes have their addresses in the given range (start..start+size)
        // Tlsf is well-formed
    {
        let tracked mut mem_remains = points_to_block;

        let mut size_remains = size;
        let mut cursor = start as usize;

        #[cfg(feature = "std")]
        let mut sentinel_tmp = null_bhdr();

        // TODO: state loop invariant that ensures `valid_block_size(chunk_size - GRANULARITY)`
        while size_remains >= GRANULARITY * 2 /* header size + minimal allocation unit */
                decreases size_remains {
            let chunk_size = size_remains.min(Self::max_pool_size());

            assert(chunk_size % GRANULARITY == 0);

            let tracked mut new_header: PointsTo<BlockHdr>;
            let tracked mut new_header_frelink: PointsTo<FreeLink>;
            proof {
                let tracked (h1, m) =
                    mem_remains.split(
                        set_int_range(cursor as int, cursor as int
                            + size_of::<BlockHdr>() as int));
                let tracked (h2, m) =
                    m.split(
                        set_int_range(cursor as int + size_of::<BlockHdr>(),
                            cursor as int + size_of::<BlockHdr>() + size_of::<FreeLink>()));
                mem_remains = m;
                new_header = h1.into_typed(cursor);
                new_header_frelink = h2.into_typed(cursor);
            }

            // The new free block
            // Safety: `cursor` is not zero.
            let prov = expose_provenance(start);
            let mut block = with_exposed_provenance(cursor, prov);

            //#[cfg(feature = "std")]
            //{
                //use std::println;
                //FIRST_BLOCK.get_or_init(|| block as usize);
                //println!("first physical block is {:?}", block);
            //}

            // Initialize the new free block
            // NOTE: header size calculated as GRANULARITY
            assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(chunk_size - GRANULARITY));
            let idx = Self::map_floor(chunk_size - GRANULARITY)?;

            // Write the header
            // NOTE: because Verus doesn't supports field update through raw pointer,
            //       we have to write it at once with `ptr_mut_write`.
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
                mem: PointsToRaw::empty(Provenance::null())
            };
            let mut sentinel_block = BlockHdr::next_phys_block(block, Tracked(&new_block_perm));

            #[cfg(feature = "std")]
            {
                sentinel_tmp = sentinel_block;
            }

            // Link to the list
            {
                let tracked new_block_freelink_perm = new_block_perm.free_link_perm.tracked_unwrap();
                self.link_free_block(idx, block);
            }

            //self.set_fl_bitmap(fl as u32);
            //self.sl_bitmap[fl].set_bit(sl as u32);

            // Cap the end with a sentinel block (a permanently-used block)
            let tracked (sentinel_perm, m) = mem_remains.split(
                set_int_range(cursor + (chunk_size - GRANULARITY), cursor + chunk_size)); // TODO: need to be confirmed
            proof {
                mem_remains = m;
            }

            let tracked mut sentinel_perm =
                sentinel_perm.into_typed((cursor + (chunk_size - GRANULARITY)) as usize);
            ptr_mut_write(sentinel_block,
                Tracked(&mut sentinel_perm),
                BlockHdr {
                    size: GRANULARITY | SIZE_USED | SIZE_SENTINEL,
                    prev_phys_block: block,
                });

            proof {
                let i = choose|i: int| self.all_blocks.ptrs@[i] == block;
                assert(self.all_blocks.phys_next_of(i) matches Some(sentinel_block));
            }

            // `cursor` can reach `usize::MAX + 1`, but in such a case, this
            // iteration must be the last one
            assert(cursor.checked_add(chunk_size).is_some() || size_remains == chunk_size);
            size_remains -= chunk_size;
            cursor = cursor.wrapping_add(chunk_size);
        }
        //#[cfg(feature = "std")]
        //{
            //use std::println;
            //SENTINEL.get_or_init(|| sentinel_tmp.clone() as usize);
            //println!("sentinel block is {:?}", sentinel_tmp);
        //}

        Some(cursor.wrapping_sub(start as usize))

            // TODO: update gs.root_provenances
    }


    /// Search for a non-empty free block list for allocation.
    //#[verifier::external_body] // debug
    #[inline(always)]
    fn search_suitable_free_block_list_for_allocation(
        &self,
        min_size: usize,
    ) -> (r: Option<BlockIndex<FLLEN,SLLEN>>)
        requires self.wf(),
            min_size >= GRANULARITY,
            min_size % GRANULARITY == 0,
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
        let idx = Self::map_ceil(min_size)?; // NOTE: return None if invalid size requested
        let BlockIndex(mut fl, mut sl) = idx;


        //#[cfg(feature = "std")]
        //{
            //use std::println;
            //println!("hah? hah? {:?} {:b} {:?}", idx, self.fl_bitmap, self.sl_bitmap);
            //self.print_stat()
        //}
        assert(min_size <= idx.block_size_range().start());

        // Search in range `(fl, sl..SLLEN)`
        sl = bit_scan_forward(self.sl_bitmap[fl], sl as u32) as usize;
        assert(idx.1 < sl) by { admit(); };
        if sl < SLLEN {
            //debug_assert!(self.sl_bitmap[fl].get_bit(sl as u32));
            let new_idx = BlockIndex::<FLLEN, SLLEN>(fl, sl);
            assert(idx.block_index_lt(new_idx)) by { admit(); };
            assert(idx.block_size_range().start() < new_idx.block_size_range().start()) by { admit(); };

            assert(min_size <= idx.block_size_range().start());
            return Some(BlockIndex(fl, sl));
        }
        // Search in range `(fl + 1.., ..)`
        fl = bit_scan_forward(self.fl_bitmap, fl as u32 + 1) as usize;
        assert(idx.0 < fl) by { admit(); };
        if fl < FLLEN {
            //debug_assert!(self.fl_bitmap.get_bit(fl as u32));

            sl = self.sl_bitmap[fl].trailing_zeros() as usize;
            assert(sl < SLLEN) by { admit(); };
            //#[cfg(feature = "std")]
            //{
                //use std::println;
                //println!("hah? hah? {:b} {:b}", self.fl_bitmap, self.sl_bitmap[fl]);
                ////if SLLEN <= sl {
                    ////self.print_stat()
                ////}
            //}
            //if sl >= SLLEN {
                //debug_assert!(false, "bitmap contradiction");
                //unreachable!()
                //unsafe { unreachable_unchecked() };
            //}

            let new_idx = BlockIndex::<FLLEN, SLLEN>(fl, sl);
            assert(idx.block_index_lt(new_idx)) by { admit(); };
            assert(idx.block_size_range().start() < new_idx.block_size_range().start()) by { admit(); };
            //debug_assert!(self.sl_bitmap[fl].get_bit(sl as u32));
            assert(min_size <= idx.block_size_range().start());
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
    //#[verifier::external_body] // for spec debug
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
                &&& !points_to@.dom().is_empty()
                &&& self.wf_dealloc(Ghost(tok@))
                &&& ptr@.provenance == points_to@.provenance()
                //&&& ptr@.metadata == Metadata::Thin
                &&& points_to@.is_range(ptr as usize as int, size as int)
                &&& ptr.addr() % align == 0
                &&& self.is_root_provenance(ptr)
            }),
            // TODO: state that if allocation failes, there is no bitmap present for it
            r matches None ==> *old(self) == *self,
            self.wf(),
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
                align.saturating_sub(GRANULARITY / 2) + mem::size_of::<UsedBlockHdr>();
            // Search for a suitable free block
            let size_overhead = size.checked_add(max_overhead)?;
            proof {
                assert(size_overhead > 0);
            }
            let search_size = size_overhead.checked_add(GRANULARITY - 1)? & !(GRANULARITY - 1);
            proof {
                if size_overhead.checked_add((GRANULARITY - 1) as usize).is_some() {
                    assert(0 <= size_overhead + (GRANULARITY - 1) <= usize::MAX);
                    granularity_is_power_of_two();
                    lemma_round_up_pow2(size_overhead, GRANULARITY);
                    assert((((size_overhead + (GRANULARITY - 1)) as usize) & !((GRANULARITY - 1) as usize)) % GRANULARITY == 0);
                    assert(search_size % GRANULARITY == 0);
                    assert(search_size >= GRANULARITY);
                }
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
            }
            let ghost selected_block_size = self.all_blocks.perms@[block].points_to.value().size;
            assert(block@.addr != 0);
            let block_prov = expose_provenance(block);

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
                assert(search_size as int <= block_size as int);
                assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size((block_size & SIZE_SIZE_MASK) as int));
            }



            //debug_assert!(size >= search_size);

            // Unlink the free block. We are not using `unlink_free_block` because
            // we already know `(fl, sl)` and that `block.prev_free` is `None`.
            let block_freelink = get_freelink_ptr(block);
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
                assert(old(self).all_blocks.ptrs@.no_duplicates());
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
                        assert(next_free_candidate@.addr != 0);
                        assert(self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free
                            == next_next_free_candidate);
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
                // TODO
                admit();
                assert(block as int + 2*GRANULARITY <= usize::MAX) by { admit(); };
                // ptr = round_up(block + G / 2, align)
                //assert(unaligned_ptr - ptr < align);
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
                let size = ptr_ref(next_phys_block, Tracked(&next_phys_block_perm.points_to)).size;
                ptr_mut_write(next_phys_block, Tracked(&mut next_phys_block_perm.points_to),
                    BlockHdr {
                        size,
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
                        assert(old_ptrs.no_duplicates());
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
                                assert(old(self).wf_free_node(idx, 0));
                                assert(Some(next_free_candidate) == Self::free_next_of(old(self).shadow_freelist@.m[idx], 0));
                                assert(old(self).shadow_freelist@.m[idx][0] == block);
                                assert(old(self).shadow_freelist@.m[idx].len() > 1);
                                assert(Self::free_next_of(old(self).shadow_freelist@.m[idx], 0)
                                    == Some(old(self).shadow_freelist@.m[idx][1]));
                                assert(next_free_candidate == old(self).shadow_freelist@.m[idx][1]);
                                old(self).lemma_shadow_list_no_duplicates();
                                assert(old(self).shadow_freelist@.m[idx].no_duplicates());
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
                                    assert(old(self).wf_free_node(idx, 1));
                                    assert(old(self).all_blocks.contains(next_free_candidate));
                                    assert(old_ptrs.contains(next_free_candidate));
                                    let ghost ci = old(self).all_blocks.get_ptr_internal_index(next_free_candidate);
                                    assert(0 <= ci < old_ptrs.len());
                                    assert(old_ptrs[ci] == next_free_candidate);
                                    assert(old_ptrs[block_id] == block);
                                    old(self).all_blocks.lemma_wf_nodup();
                                    assert(old_ptrs.no_duplicates());
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
                            assert(perms_after_insert_block[next_free_candidate]
                                == perms_after_remove_next_phys[next_free_candidate]);
                            assert(perms_after_insert_next_phys[next_free_candidate]
                                == perms_after_insert_block[next_free_candidate]);
                            assert(self.all_blocks.perms@[next_free_candidate]
                                == perms_after_insert_next_phys[next_free_candidate]);
                            assert(perms_after_remove_next_phys[next_free_candidate]
                                == perms_before_split_update[next_free_candidate]);
                            assert(perms_before_split_update[next_free_candidate].free_link_perm.unwrap().value().next_free
                                == next_next_free_candidate);
                            assert(self.all_blocks.perms@[next_free_candidate].free_link_perm.unwrap().value().next_free
                                == next_next_free_candidate);
                        }
                    }

                    //assert(self.all_blocks.wf_node(next_phys_block_ind));
                    //assert(self.all_blocks.wf_node(next_phys_block_ind - 1));
                    assert(self.all_blocks.wf()) by {
                        // {{{
                        let ghost old_ptrs = old(self).all_blocks.ptrs@;
                        lemma_add_ghost_pointer_ensures(old(self).all_blocks.ptrs@, new_free_block);
                        old(self).all_blocks.lemma_wf_nodup();
                        assert(old_ptrs.no_duplicates());
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
                            assert(old_ptrs.no_duplicates());
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
                                assert(i == next_phys_block_ind + 1);
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
                                                    assert(i + 1 <= block_id);
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
                    assert(self.all_freelist_wf()) by {
                        assert(self.wf_shadow());
                        assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf()
                            implies self.freelist_wf(bi)
                        by {
                            // {{{
                            let ghost sfl_after_remove =
                                old(self).shadow_freelist@.ii_remove_for_index(old(self).all_blocks, idx, 0);
                            old(self).wf_index_in_freelist(bi);
                            assert(self.shadow_freelist@.m[bi] == sfl_after_remove.m[bi]);
                            if bi == idx {
                                assert(sfl_after_remove.m[bi] == old(self).shadow_freelist@.m[bi].remove(0));
                                assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi].remove(0));
                                assert forall|n: int| 0 <= n < self.shadow_freelist@.m[bi].len()
                                    implies self.wf_free_node(bi, n)
                                by {
                                    if n == 0 {
                                        assert(self.shadow_freelist@.m[bi].len() > 0);
                                        assert(old(self).shadow_freelist@.m[bi].len() > 1);
                                        assert(self.shadow_freelist@.m[bi][0] == old(self).shadow_freelist@.m[bi][1]);
                                        assert(old(self).wf_free_node(bi, 1));
                                        let node = self.shadow_freelist@.m[bi][0];
                                        assert(self.all_blocks.contains(node)) by {
                                            assert(self.is_ii());
                                            assert(0 <= self.shadow_freelist@.pi[(bi, 0)] < self.all_blocks.ptrs@.len());
                                            assert(self.shadow_freelist@.m[bi][0]
                                                == self.all_blocks.ptrs@[self.shadow_freelist@.pi[(bi, 0)]]);
                                            assert(self.all_blocks.ptrs@.contains(node));
                                        };
                                        assert(self.all_blocks.value_at(node).is_free()) by {
                                            assert(node == next_free_candidate);
                                            assert(self.all_blocks.perms@[next_free_candidate].points_to.value().is_free());
                                        };
                                        assert(self.all_blocks.perms@[node].free_link_perm.unwrap().value().prev_free@.addr == 0);
                                        assert(self.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free@.addr != 0
                                                ==> Some(self.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free)
                                                    == Self::free_next_of(self.shadow_freelist@.m[bi], 0)) by {
                                            assert(old(self).wf_free_node(bi, 1));
                                            assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi].remove(0));
                                            assert(Self::free_next_of(self.shadow_freelist@.m[bi], 0)
                                                == Self::free_next_of(old(self).shadow_freelist@.m[bi], 1));
                                            assert(self.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free@.addr != 0
                                                ==> Some(self.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free)
                                                    == Self::free_next_of(old(self).shadow_freelist@.m[bi], 1));
                                        };
                                        assert(self.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free@.addr == 0
                                                ==> Self::free_next_of(self.shadow_freelist@.m[bi], 0) is None) by {
                                            assert(old(self).wf_free_node(bi, 1));
                                            assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi].remove(0));
                                            assert(Self::free_next_of(self.shadow_freelist@.m[bi], 0)
                                                == Self::free_next_of(old(self).shadow_freelist@.m[bi], 1));
                                            assert(self.all_blocks.perms@[node].free_link_perm.unwrap().value().next_free@.addr == 0
                                                ==> Self::free_next_of(old(self).shadow_freelist@.m[bi], 1) is None);
                                        };
                                        assert(Self::free_prev_of(self.shadow_freelist@.m[bi], 0) is None);
                                    } else {
                                        assert(old(self).wf_free_node(bi, n + 1));
                                        let node = self.shadow_freelist@.m[bi][n];
                                        old(self).lemma_shadow_list_no_duplicates();
                                        old(self).wf_index_in_freelist(idx);
                                        old(self).freelist_nonempty(idx);
                                        assert(old(self).shadow_freelist@.m[idx].first() == block);
                                        assert(old(self).shadow_freelist@.m[idx][0] == block);
                                        assert((idx, 0int) != (idx, n + 1));
                                        assert(node != block);
                                        if next_free_candidate@.addr != 0 {
                                            assert(old(self).shadow_freelist@.m[idx][1] == next_free_candidate) by {
                                                assert(old(self).wf_free_node(idx, 0));
                                                assert(old(self).all_blocks.perms@[block].free_link_perm.unwrap().value().next_free
                                                    == next_free_candidate);
                                                assert(old(self).all_blocks.perms@[block].free_link_perm.unwrap().value().next_free@.addr != 0);
                                                assert(Some(next_free_candidate) == Self::free_next_of(old(self).shadow_freelist@.m[idx], 0));
                                                assert(Self::free_next_of(old(self).shadow_freelist@.m[idx], 0).unwrap()
                                                    == old(self).shadow_freelist@.m[idx][1]);
                                            };
                                            assert((idx, 1int) != (idx, n + 1));
                                            assert(node != next_free_candidate);
                                        }
                                        assert(node != next_phys_block) by {
                                            if node == next_phys_block {
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
                                            if node == new_free_block {
                                                assert(old(self).all_blocks.ptrs@.contains(node)) by {
                                                    assert(old(self).is_ii());
                                                    assert(0 <= old(self).shadow_freelist@.pi[(bi, n + 1)] < old(self).all_blocks.ptrs@.len());
                                                    assert(old(self).shadow_freelist@.m[bi][n + 1]
                                                        == old(self).all_blocks.ptrs@[old(self).shadow_freelist@.pi[(bi, n + 1)]]);
                                                };
                                                let i = choose|i: int| 0 <= i < old(self).all_blocks.ptrs@.len()
                                                    && old(self).all_blocks.ptrs@[i] == new_free_block;
                                                assert(ghost_pointer_ordered(old(self).all_blocks.ptrs@));
                                                assert(0 <= block_id + 1 < old(self).all_blocks.ptrs@.len());
                                                if i <= block_id {
                                                    lemma_ghost_pointer_ordered_index(old(self).all_blocks.ptrs@, i, block_id);
                                                    assert((old(self).all_blocks.ptrs@[i] as usize as int)
                                                        <= (old(self).all_blocks.ptrs@[block_id] as usize as int));
                                                    assert(old(self).all_blocks.ptrs@[block_id] == block);
                                                    assert((block as usize as int) < (new_free_block as usize as int));
                                                } else {
                                                    assert(block_id + 1 <= i);
                                                    lemma_ghost_pointer_ordered_index(old(self).all_blocks.ptrs@, block_id + 1, i);
                                                    assert((old(self).all_blocks.ptrs@[block_id + 1] as usize as int)
                                                        <= (old(self).all_blocks.ptrs@[i] as usize as int));
                                                    assert(old(self).all_blocks.ptrs@[block_id + 1] == next_phys_block);
                                                    assert((new_free_block as usize as int) < (next_phys_block as usize as int));
                                                }
                                                assert(old(self).all_blocks.ptrs@[i] == new_free_block);
                                                assert(false);
                                            }
                                        };
                                        assert(old(self).all_blocks.contains(node));
                                        old(self).all_blocks.lemma_contains(node);
                                        assert(self.all_blocks.contains(node)) by {
                                            assert(self.is_ii());
                                            assert(0 <= self.shadow_freelist@.pi[(bi, n)] < self.all_blocks.ptrs@.len());
                                            assert(self.shadow_freelist@.m[bi][n]
                                                == self.all_blocks.ptrs@[self.shadow_freelist@.pi[(bi, n)]]);
                                            assert(self.all_blocks.ptrs@.contains(node));
                                        };
                                        self.all_blocks.lemma_contains(node);
                                        assert(self.all_blocks.perms@[node] == old(self).all_blocks.perms@[node]);
                                        old(self).lemma_wf_free_node_preserve_remove_head(*self, bi, n);
                                    }
                                };
                                assert(self.shadow_freelist@.m[bi].len() == 0 ==> self.first_free[bi.0 as int][bi.1 as int]@.addr == 0) by {
                                    if self.shadow_freelist@.m[bi].len() == 0 {
                                        assert(self.first_free[idx.0 as int][idx.1 as int] == next_free_candidate);
                                        assert(self.first_free[bi.0 as int][bi.1 as int]
                                            == self.first_free[idx.0 as int][idx.1 as int]);
                                        if next_free_candidate@.addr != 0 {
                                            assert(old(self).wf_free_node(idx, 0));
                                            assert(old(self).all_blocks.perms@[block].free_link_perm.unwrap().value().next_free
                                                == next_free_candidate);
                                            assert(old(self).all_blocks.perms@[block].free_link_perm.unwrap().value().next_free@.addr != 0);
                                            assert(Some(next_free_candidate) == Self::free_next_of(old(self).shadow_freelist@.m[idx], 0));
                                            assert(Self::free_next_of(old(self).shadow_freelist@.m[idx], 0) is Some);
                                            assert(old(self).shadow_freelist@.m[idx].len() > 1);
                                            assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi].remove(0));
                                            assert(self.shadow_freelist@.m[bi].len() == old(self).shadow_freelist@.m[bi].len() - 1);
                                            assert(self.shadow_freelist@.m[bi].len() > 0);
                                            assert(false);
                                        }
                                    }
                                };
                                assert(self.freelist_wf(bi));
                            } else {
                                assert(sfl_after_remove.m[bi] == old(self).shadow_freelist@.m[bi]);
                                assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]);
                                assert forall|n: int| 0 <= n < self.shadow_freelist@.m[bi].len()
                                    implies self.wf_free_node(bi, n)
                                by {
                                    assert(old(self).wf_free_node(bi, n));
                                    let node = self.shadow_freelist@.m[bi][n];
                                    assert(old(self).shadow_freelist@.m[bi].contains(node));
                                    old(self).wf_index_in_freelist(idx);
                                    assert(old(self).shadow_freelist@.m[idx].contains(block)) by {
                                        old(self).freelist_nonempty(idx);
                                        assert(old(self).shadow_freelist@.m[idx].first()
                                            == old(self).first_free[idx.0 as int][idx.1 as int]);
                                    };
                                    old(self).lemma_shadow_list_contains_unique(idx, block);
                                    assert(!old(self).shadow_freelist@.m[bi].contains(block));
                                    assert(node != block);
                                    assert(node != next_phys_block) by {
                                        if node == next_phys_block {
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
                                        if node == new_free_block {
                                            assert(old(self).all_blocks.ptrs@.contains(node)) by {
                                                assert(old(self).is_ii());
                                                assert(0 <= old(self).shadow_freelist@.pi[(bi, n)] < old(self).all_blocks.ptrs@.len());
                                                assert(old(self).shadow_freelist@.m[bi][n]
                                                    == old(self).all_blocks.ptrs@[old(self).shadow_freelist@.pi[(bi, n)]]);
                                            };
                                            let i = choose|i: int| 0 <= i < old(self).all_blocks.ptrs@.len()
                                                && old(self).all_blocks.ptrs@[i] == new_free_block;
                                            assert(ghost_pointer_ordered(old(self).all_blocks.ptrs@));
                                            assert(0 <= block_id + 1 < old(self).all_blocks.ptrs@.len());
                                            if i <= block_id {
                                                lemma_ghost_pointer_ordered_index(old(self).all_blocks.ptrs@, i, block_id);
                                                assert((old(self).all_blocks.ptrs@[i] as usize as int)
                                                    <= (old(self).all_blocks.ptrs@[block_id] as usize as int));
                                                assert(old(self).all_blocks.ptrs@[block_id] == block);
                                                assert((block as usize as int) < (new_free_block as usize as int));
                                            } else {
                                                assert(block_id + 1 <= i);
                                                lemma_ghost_pointer_ordered_index(old(self).all_blocks.ptrs@, block_id + 1, i);
                                                assert((old(self).all_blocks.ptrs@[block_id + 1] as usize as int)
                                                    <= (old(self).all_blocks.ptrs@[i] as usize as int));
                                                assert(old(self).all_blocks.ptrs@[block_id + 1] == next_phys_block);
                                                assert((new_free_block as usize as int) < (next_phys_block as usize as int));
                                            }
                                            assert(old(self).all_blocks.ptrs@[i] == new_free_block);
                                            assert(false);
                                        }
                                    };
                                    assert(self.all_blocks.perms@[node] == old(self).all_blocks.perms@[node]);
                                    old(self).lemma_wf_free_node_preserve_if_not_touched(*self, bi, n);
                                };
                                assert(self.freelist_wf(bi));
                            }
                            // }}}
                        };
                    };
                    assert(self.bitmap_wf());
                    assert(self.bitmap_sync()) by {
                        // {{{
                        let ghost sfl_after_remove =
                            old(self).shadow_freelist@.ii_remove_for_index(old(self).all_blocks, idx, 0);
                        Self::lemma_ii_remove_for_index_ensures(old(self).shadow_freelist@, old(self).all_blocks, idx, 0);
                        assert forall|bi: BlockIndex<FLLEN, SLLEN>| bi.wf() implies
                            (nth_bit!(self.sl_bitmap[bi.0 as int], bi.1 as usize)
                                <==> self.shadow_freelist@.m[bi].len() > 0)
                        by {
                            assert(self.shadow_freelist@.m[bi] == sfl_after_remove.m[bi]);
                            if bi == idx {
                                if next_free_candidate@.addr == 0 {
                                    assert(!nth_bit!(self.sl_bitmap[idx.0 as int], idx.1 as usize));
                                    assert(self.freelist_wf(idx));
                                    assert(self.first_free[idx.0 as int][idx.1 as int] == next_free_candidate);
                                    assert(self.first_free[idx.0 as int][idx.1 as int]@.addr == 0);
                                    assert(self.shadow_freelist@.m[idx].len() == 0);
                                } else {
                                    assert(self.sl_bitmap[idx.0 as int] == old(self).sl_bitmap[idx.0 as int]);
                                    assert(old(self).bitmap_sync());
                                    assert(old(self).shadow_freelist@.m[idx].len() > 0);
                                    assert(nth_bit!(old(self).sl_bitmap[idx.0 as int], idx.1 as usize));
                                    assert(nth_bit!(self.sl_bitmap[idx.0 as int], idx.1 as usize));
                                    assert(self.freelist_wf(idx));
                                    assert(self.first_free[idx.0 as int][idx.1 as int] == next_free_candidate);
                                    assert(self.first_free[idx.0 as int][idx.1 as int]@.addr != 0);
                                    assert(self.shadow_freelist@.m[idx].len() > 0);
                                }
                            } else {
                                assert(self.shadow_freelist@.m[bi] == old(self).shadow_freelist@.m[bi]);
                                assert(old(self).bitmap_sync());
                                assert(nth_bit!(old(self).sl_bitmap[bi.0 as int], bi.1 as usize)
                                    <==> old(self).shadow_freelist@.m[bi].len() > 0);
                                assert(nth_bit!(self.sl_bitmap[bi.0 as int], bi.1 as usize)
                                    == nth_bit!(old(self).sl_bitmap[bi.0 as int], bi.1 as usize));
                            }
                        };
                        // }}}
                    };
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
                                    assert((old_ptrs[i] as usize as int) <= (old_ptrs[block_id] as usize as int));
                                    assert(old_ptrs[block_id] == block);
                                    assert((block as usize as int) < (new_free_block as usize as int));
                                } else {
                                    assert(block_id + 1 <= i);
                                    lemma_ghost_pointer_ordered_index(old_ptrs, block_id + 1, i);
                                    assert((old_ptrs[block_id + 1] as usize as int) <= (old_ptrs[i] as usize as int));
                                    assert(old_ptrs[block_id + 1] == next_phys_block);
                                    assert((new_free_block as usize as int) < (next_phys_block as usize as int));
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

                    proof {
                        assert(new_free_block_size == self.all_blocks.perms@[new_free_block].points_to.value().size);
                        assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(new_free_block_size as int));
                    }

                    let new_block_idx = Self::map_floor(new_free_block_size).unwrap();
                    self.link_free_block(new_block_idx, new_free_block);

                    proof { admit(); } //--------------------------------------------------------------------------------------------------------
                    assert(self.all_blocks.wf_node(self.all_blocks.get_ptr_internal_index(new_free_block)));
                    proof {
                        new_block_perm = self.all_blocks.perms.borrow_mut().tracked_remove(block);
                    }
                }
            }
            proof { admit(); } //---------------------------------------------------------------------------------------------------------------

            //// Place a `UsedBlockPad` (used by `used_block_hdr_for_allocation`)
            if align >= GRANULARITY {
                let tracked mut pad: PointsTo<UsedBlockPad> = self.used_info.pad_perms.borrow_mut().tracked_remove(ptr);
                ptr_mut_write(UsedBlockPad::get_for_allocation(ptr), Tracked(&mut pad),
                    UsedBlockPad { block_hdr: block as *mut UsedBlockHdr });
                proof {
                    self.used_info.pad_perms.borrow_mut().tracked_insert(ptr, pad);
                }
            }

            //self.print_stat();
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
    unsafe fn deallocate_block(&mut self, mut block: *mut BlockHdr,
        Tracked(block_perm): Tracked<BlockPerm>) {
        let tracked mut block_perm = block_perm;
        let mut size = ptr_ref(block, Tracked(&block_perm.points_to)).size & !SIZE_USED;
        //debug_assert!((block.as_ref().size & SIZE_USED) != 0);

        // This variable tracks whose `prev_phys_block` we should update.
        let mut new_next_phys_block;
        let tracked mut new_next_phys_block_perm: BlockPerm;

        // Merge the created hole with the next block if the next block is a
        // free block
        // Safety: `block.common` should be fully up-to-date and valid
        let mut next_phys_block = BlockHdr::next_phys_block(block, Tracked(&block_perm));
        let tracked next_phys_block_perm: BlockPerm = {
            let i = choose|i: int| self.all_blocks.ptrs@[i] == block;
            self.all_blocks.perms.borrow_mut()
                .tracked_remove(self.all_blocks.phys_next_of(i).unwrap())
        };
        let next_phys_block_size_and_flags =
            ptr_ref(next_phys_block,
                    Tracked(&next_phys_block_perm.points_to)).size;
        if (next_phys_block_size_and_flags & SIZE_USED) == 0 {
            let next_phys_block_size = next_phys_block_size_and_flags;
            //debug_assert_eq!(
                //next_phys_block_size_and_flags & SIZE_SIZE_MASK,
                //next_phys_block_size
            //);

            // It's coalescable. Add its size to `size`.
            size += next_phys_block_size;

            // Safety: `next_phys_block` is a free block and therefore is not a
            // sentinel block
            new_next_phys_block = BlockHdr::next_phys_block(next_phys_block, Tracked(&next_phys_block_perm));
            proof {
                new_next_phys_block_perm = {
                    let ghost i: int = choose|i: int| self.all_blocks.ptrs@[i] == next_phys_block;
                    self.all_blocks.perms.borrow_mut()
                        .tracked_remove(self.all_blocks.phys_next_of(i).unwrap())
                };
            }

            // Unlink `next_phys_block`.
            let idx = Self::map_floor(next_phys_block_size).unwrap();
            self.unlink_free_block(next_phys_block, idx);
        } else {
            new_next_phys_block = next_phys_block;
            proof {
                new_next_phys_block_perm = next_phys_block_perm;
            }
        }

        // Merge with the previous block if it's a free block.
        if ptr_ref(block, Tracked(&block_perm.points_to)).prev_phys_block.addr() != 0 {
            let prev_phys_block = ptr_ref(block, Tracked(&block_perm.points_to)).prev_phys_block;
            let tracked prev_phys_block_perm = {
                let i = choose|i: int| self.all_blocks.ptrs@[i] == prev_phys_block;
                self.all_blocks.perms.borrow_mut()
                    .tracked_remove(self.all_blocks.phys_prev_of(i).unwrap())
            };
            let prev_phys_block_size_and_flags = ptr_ref(prev_phys_block, Tracked(&prev_phys_block_perm.points_to)).size;

            if (prev_phys_block_size_and_flags & SIZE_USED) == 0 {
                let prev_phys_block_size = prev_phys_block_size_and_flags;
                //debug_assert_eq!(
                    //prev_phys_block_size_and_flags & SIZE_SIZE_MASK,
                    //prev_phys_block_size
                //);

                // It's coalescable. Add its size to `size`.
                size += prev_phys_block_size;

                // Unlink `prev_phys_block`.
                let idx = Self::map_floor(prev_phys_block_size).unwrap();
                self.unlink_free_block(prev_phys_block, idx);

                // Move `block` to where `prev_phys_block` is located. By doing
                // this, `block` will implicitly inherit `prev_phys_block.
                // as_ref().prev_phys_block`.
                block = prev_phys_block;
            }
        }

        // Write the new free block's size and flags.
        //debug_assert!((size & SIZE_USED) == 0);
        let prev_phys_block = ptr_ref(block, Tracked(&block_perm.points_to)).prev_phys_block;
        ptr_mut_write(block, Tracked(&mut block_perm.points_to), BlockHdr {
            size,
            prev_phys_block,
        });

        // Link this free block to the corresponding free list
        let new_block_idx = Self::map_floor(size).unwrap();
        {
            let tracked freelink_perm = block_perm.free_link_perm.tracked_unwrap();

            self.link_free_block(new_block_idx, block);
        }

        // Link `new_next_phys_block.prev_phys_block` to `block`
        //debug_assert_eq!(
            //new_next_phys_block,
            //BlockHdr::next_phys_block(nn_field!(block, common))
        //);
        let new_next_phys_block_size = ptr_ref(new_next_phys_block,
                          Tracked(&new_next_phys_block_perm.points_to)).size;
        ptr_mut_write(new_next_phys_block,
            Tracked(&mut new_next_phys_block_perm.points_to),
            BlockHdr {
                size: new_next_phys_block_size,
                prev_phys_block: block
        });
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

    spec fn size_class_condition(self) -> bool {
        forall|idx: BlockIndex<FLLEN, SLLEN>, i: int|
            self.shadow_freelist@.m.contains_key(idx)
                && 0 <= i < self.shadow_freelist@.m[idx].len() ==>
                    idx.block_size_range().contains(
                        self.all_blocks.perms@[
                            self.shadow_freelist@.m[idx][i]
                        ].points_to.value().size as int)
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
pub tracked struct DeallocToken;
//{
    ///// Copy of header pointer of allocated region as an allocation identifier
    //ghost ptr: Ghost<*mut UsedBlockHdr>,
    ///// Padding if there exists
    ///// invariant: pad.ptr() = pad_ptr = PTR_BEEN_DEALLOCATED - 1
    //tracked pad: Option<Tracked<PointsTo<UsedBlockPad>>>
//}


#[inline]
pub unsafe fn round_up(ptr: *mut u8, align: usize) -> (r: *mut u8)
    requires is_power_of_two(align as int)
    ensures
        (ptr as int) <= (r as int) < (ptr as int) + align as int ,
        ptr as usize % align == 0,
        r@.provenance == ptr@.provenance,
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

//// FIXME: following MUST be commented out while `cargo build`
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
