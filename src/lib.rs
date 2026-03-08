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
mod allocate;
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

#[cfg(target_pointer_width = "64")]
global layout UsedBlockPad is size == 8, align == 8;

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

    proof fn lemma_join_adjacent_ranges_is_range(
        tracked left: PointsToRaw,
        tracked right: PointsToRaw,
        start: int,
        mid: int,
        end: int,
    ) -> (tracked joined: PointsToRaw)
        requires
            left.provenance() == right.provenance(),
            left.is_range(start, mid - start),
            right.is_range(mid, end - mid),
            start <= mid <= end,
        ensures
            joined.provenance() == left.provenance(),
            joined.is_range(start, end - start),
    {
        let tracked joined0 = left.join(right);
        assert(joined0.is_range(start, end - start)) by {
            assert forall |a:int| #[trigger] joined0.dom().contains(a)
                <==> set_int_range(start, end).contains(a)
            by {
                if joined0.dom().contains(a) {
                    assert(left.dom().contains(a) || right.dom().contains(a));
                    if left.dom().contains(a) {
                        assert(set_int_range(start, mid).contains(a));
                        assert(start <= a < mid);
                        assert(set_int_range(start, end).contains(a));
                    } else {
                        assert(right.dom().contains(a));
                        assert(set_int_range(mid, end).contains(a));
                        assert(mid <= a < end);
                        assert(start <= mid);
                        assert(set_int_range(start, end).contains(a));
                    }
                } else if set_int_range(start, end).contains(a) {
                    assert(start <= a < end);
                    if a < mid {
                        assert(set_int_range(start, mid).contains(a));
                        assert(left.dom().contains(a));
                    } else {
                        assert(mid <= a < end);
                        assert(set_int_range(mid, end).contains(a));
                        assert(right.dom().contains(a));
                    }
                    assert(left.dom().contains(a) || right.dom().contains(a));
                    assert(joined0.dom().contains(a));
                }
            };
            assert(joined0.dom() =~= set_int_range(start, end));
        };
        joined0
    }

    proof fn lemma_range_subset_of_mem_dom(
        mem: PointsToRaw,
        mem_start: int,
        mem_end: int,
        lo: int,
        hi: int,
    )
        requires
            mem.is_range(mem_start, mem_end - mem_start),
            mem_start <= lo,
            hi <= mem_end,
        ensures
            set_int_range(lo, hi).subset_of(mem.dom()),
    {
        assert(mem.dom() == set_int_range(mem_start, mem_end));
        assert forall |a:int|
            #[trigger] set_int_range(lo, hi).contains(a)
            implies mem.dom().contains(a)
        by {
            assert(lo <= a < hi) by {
                assert(set_int_range(lo, hi).contains(a));
            };
            assert(mem_start <= a < mem_end) by {
                assert(mem_start <= lo <= a);
                assert(a < hi <= mem_end);
            };
            assert(set_int_range(mem_start, mem_end).contains(a));
        };
    }

    proof fn lemma_perm_size_preserved_for_untouched_node(
        old_perms: Map<*mut BlockHdr, BlockPerm>,
        new_perms: Map<*mut BlockHdr, BlockPerm>,
        touched: *mut BlockHdr,
        node: *mut BlockHdr,
    )
        requires
            old_perms.contains_key(touched),
            old_perms.contains_key(node),
            node != touched,
            new_perms == old_perms.remove(touched).insert(touched, old_perms[touched]),
        ensures
            new_perms[node].points_to.value().size == old_perms[node].points_to.value().size,
    {
        assert(new_perms[node] == old_perms[node]);
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
                pad_perms: Tracked(Map::tracked_empty()),
                overhead_perms: Tracked(Map::tracked_empty()),
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
        r as usize % align == 0,
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
