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
//mod ghost_tlsf;
mod all_blocks;
mod allocate;
mod bitmap;
mod block;
mod deallocate;
mod mapping;
mod ordered_pointer_list;
pub mod parameters;
mod search_block;
pub mod unverified_api;
mod utils;

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
use vstd::std_specs::bits::{axiom_u64_trailing_zeros, u64_trailing_zeros};
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
    pub shadow_freelist: Ghost<ShadowFreelist<FLLEN, SLLEN>>,

    /// Maps user pointers (returned by allocate) to block header pointers
    pub user_block_map: Ghost<Map<*mut u8, *mut BlockHdr>>,
}

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    /// well-formedness of Tlsf structure
    /// * freelist well-formedness
    ///   * TODO: blocks connected to freelist ordered by start address
    /// * bitmap is consistent with the freelist
    /// * TODO: blocks stored in the list have proper size as calculated from their index
    pub closed spec fn wf(self) -> bool {
        &&& self.all_blocks.wf()
        // all_freelist_wf() now includes free_blocks_in_freelist() via all_freelist_wf_weak(Set::empty())
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

    /// Bridge lemma: decomposes closed wf() into its open components.
    /// Needed by deallocate module which cannot see wf() body.
    pub(crate) proof fn lemma_wf_components(&self)
        requires self.wf()
        ensures
            self.all_blocks.wf(),
            self.all_freelist_wf(),
            self.size_class_condition(),
            Self::parameter_validity(),
            self.bitmap_wf(),
            self.bitmap_sync(),
            self.all_blocks.pool_size_bounded(),
    {}

    /// Frame lemma: wf() is preserved when only user_block_map changes.
    pub(crate) proof fn lemma_wf_preserved_after_user_block_map_update(
        old_self: &Self, new_self: &Self,
    )
        requires
            old_self.wf(),
            new_self.all_blocks == old_self.all_blocks,
            new_self.fl_bitmap == old_self.fl_bitmap,
            new_self.sl_bitmap == old_self.sl_bitmap,
            new_self.first_free == old_self.first_free,
            new_self.shadow_freelist == old_self.shadow_freelist,
            new_self.root_provenances == old_self.root_provenances,
            new_self.valid_range == old_self.valid_range,
        ensures
            new_self.wf(),
    {}

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
            all_blocks: AllBlocks::empty(),
            valid_range: Ghost(Set::empty()),
            root_provenances: Tracked(None),
            _phantom: PhantomData,
            shadow_freelist: Ghost(ShadowFreelist {
                m: Map::empty(),
                pi: Map::empty(),
            }),
            user_block_map: Ghost(Map::empty()),
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
    pub open spec fn max_pool_size_spec() -> usize {
        (pow2(FLLEN as nat) * GRANULARITY) as usize
    }

    #[verifier::when_used_as_spec(max_pool_size_spec)]
    #[verifier::external_body]
    const fn max_pool_size() -> (r: usize)
        requires
            Self::parameter_validity()
        ensures
            r == Self::max_pool_size_spec(),
            1 << (usize::BITS - 1) >= r >= GRANULARITY * 2,
            r % GRANULARITY == 0,
    {
        let shift = Self::granularity_log2() + FLLEN as u32;
        1 << shift
    }

    /// Lemma: max_pool_size_spec() fits in usize and equals pow2(FLLEN) * GRANULARITY
    pub proof fn lemma_max_pool_size_spec_value()
        requires Self::parameter_validity()
        ensures
            Self::max_pool_size_spec() == (pow2(FLLEN as nat) * GRANULARITY) as usize,
            pow2(FLLEN as nat) * GRANULARITY <= usize::MAX,
            Self::max_pool_size_spec() as int == pow2(FLLEN as nat) * GRANULARITY,
    {
        Self::granularity_basics();
        let g = Self::granularity_log2_spec();
        let fl = FLLEN as nat;
        crate::bits::lemma_pow2_values();
        vstd::arithmetic::power2::lemma_pow2_adds(g as nat, fl);
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(
            (g + FLLEN) as nat, 64nat);
        vstd::arithmetic::power2::lemma_pow2_unfold(64nat);
        assert(pow2(64nat) == 18446744073709551616nat);
        assert(pow2((g + fl) as nat) <= usize::MAX as nat);
        assert(pow2(g as nat) == GRANULARITY as nat);
        assert(pow2(FLLEN as nat) * GRANULARITY <= usize::MAX);
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
        points_to_block.provenance() == start@.provenance,
        // Given pointer must be aligned and non-null
        start as usize as int % GRANULARITY as int == 0,
        start as usize != 0,
        // Size must be GRANULARITY-aligned
        size as int % GRANULARITY as int == 0,
        // Tlsf is well-formed
        old(self).wf(),
        // For now: limit to initially-empty allocator and single-chunk insertion
        // TODO: generalize to support multiple pool regions
        old(self).all_blocks.ptrs@.len() == 0,
        size as int <= Self::max_pool_size_spec() as int,
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

        // Phase 4: pre-loop proof
        proof {
            self.lemma_wf_components();
        }

        // Ghost flag to track first iteration (loop runs exactly once due to size <= max_pool_size)
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
                // Loop runs exactly once: either first_iter (haven't run) or done (size_remains == 0)
                first_iter || size_remains == 0,
                // On first iteration: size_remains == size and allocator is empty
                first_iter ==> size_remains == size,
                first_iter ==> self.all_blocks.ptrs@.len() == 0,
                // The following invariants may fail if cursor wrapped to 0 on last iteration
                // (when size_remains == 0), so guard them
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
                // size_remains >= 2*GRAN > 0 (loop condition), so size_remains != 0
                // From invariant: first_iter || size_remains == 0, so first_iter must be true
                assert(first_iter);
                // Therefore: size_remains == size and all_blocks.ptrs@.len() == 0
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
            // chunk_size == size_remains because size_remains <= size <= max_pool_size
            assert(chunk_size == size_remains);

            assert(chunk_size % GRANULARITY == 0);

            // Prove valid_block_size(chunk_size - GRANULARITY)
            // valid_block_size requires: GRANULARITY <= size < pow2(FLLEN) * GRANULARITY && size % GRANULARITY == 0
            proof {
                Self::lemma_max_pool_size_spec_value();
                Self::lemma_parameter_validity_implies_block_index_parameter_validity();
                let gran_int: int = GRANULARITY as int;
                let chunk_int: int = chunk_size as int;
                let mps_int: int = Self::max_pool_size_spec() as int;
                // max_pool_size_spec() as int == pow2(FLLEN) * GRANULARITY [from lemma]
                // chunk_size <= max_ps == max_pool_size_spec() [from if/else + when_used_as_spec]
                assert(chunk_int <= mps_int);
                assert(chunk_int - gran_int >= gran_int);
                assert((chunk_int - gran_int) % gran_int == 0) by {
                    assert(chunk_int % gran_int == 0);
                    assert(gran_int % gran_int == 0);
                };
                assert(chunk_int - gran_int < pow2(FLLEN as nat) * gran_int);
            }

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
                new_header_frelink = h2.into_typed(
                    (cursor + mem::size_of::<BlockHdr>()) as usize);
            }

            // The new free block
            let prov = expose_provenance(start);
            let mut block = with_exposed_provenance(cursor, prov);

            // Initialize the new free block
            let ghost free_block_size: usize = (chunk_size - GRANULARITY) as usize;

            assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(chunk_size - GRANULARITY));

            // Write the header
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

            // Cap the end with a sentinel block (a permanently-used block)
            // Split exactly size_of::<BlockHdr>() bytes for the sentinel header
            let ghost sentinel_addr: int = cursor as int + (chunk_size - GRANULARITY) as int;
            let tracked (sentinel_perm, m) = mem_remains.split(
                set_int_range(sentinel_addr, sentinel_addr + size_of::<BlockHdr>() as int));
            proof {
                mem_remains = m;
            }

            proof {
                // Prove alignment: sentinel_addr % align_of::<BlockHdr>() == 0
                assert(sentinel_addr % (GRANULARITY as int) == 0);
                assert(sentinel_addr % (align_of::<BlockHdr>() as int) == 0) by {
                    assert(GRANULARITY == 32) by (compute);
                    assert(align_of::<BlockHdr>() as int == 8) by (compute);
                    // GRANULARITY-aligned implies 8-aligned: 32 | x implies 8 | x
                    assert(sentinel_addr % 8 == 0) by (nonlinear_arith)
                        requires sentinel_addr % 32 == 0;
                };

                // Prove sentinel_block@.addr == sentinel_addr
                // next_phys_block gives addr = block@.addr + ((size & SIZE_SIZE_MASK) as int)
                // block@.addr = cursor, size = chunk_size - GRANULARITY
                // For valid block sizes (multiples of GRANULARITY >= 32),
                // (size & SIZE_SIZE_MASK) == size since lower 5 bits are already 0
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

            let tracked mut sentinel_perm =
                sentinel_perm.into_typed((cursor + (chunk_size - GRANULARITY)) as usize);

            proof {
                // ptr_mut_write requires old(perm).ptr() == ptr
                // sentinel_perm.ptr() is set by into_typed to point at sentinel_addr
                // sentinel_block@.addr == sentinel_addr (proved above)
                assert(sentinel_perm.ptr() == sentinel_block);
            }

            ptr_mut_write(sentinel_block,
                Tracked(&mut sentinel_perm),
                BlockHdr {
                    size: SIZE_USED | SIZE_SENTINEL,
                    prev_phys_block: block,
                });

            // Split free block body memory from mem_remains for new_block_perm.mem
            let tracked mut sentinel_overhead: PointsToRaw;
            proof {
                let tracked (free_body_mem, m) = mem_remains.split(
                    set_int_range(
                        cursor as int + size_of::<BlockHdr>() as int + size_of::<FreeLink>() as int,
                        cursor as int + (chunk_size - GRANULARITY) as int));
                // Split sentinel overhead (remaining bytes after sentinel header)
                let tracked (overhead, m) = m.split(
                    set_int_range(
                        sentinel_addr + size_of::<BlockHdr>() as int,
                        cursor as int + chunk_size as int));
                mem_remains = m;
                new_block_perm.mem = free_body_mem;
                sentinel_overhead = overhead;
            }

            // Phase 3: ghost/tracked — update all_blocks with both blocks
            proof {
                let ghost old_ptrs = self.all_blocks.ptrs@;
                let ghost old_sfl = self.shadow_freelist@;

                // Before modifying all_blocks, extract first_free null facts.
                // From wf() → all_freelist_wf() → freelist_wf(idx) for all wf idx.
                // Since old_ptrs.len() == 0, sfl.m[idx].len() == 0 (proved via is_identity_injection).
                // freelist_wf with empty sfl → ptr_is_null(first_free[idx]).
                // Note: is_identity_injection derivation needs old_ptrs.len() == 0,
                // and we have first_iter ==> ptrs@.len() == 0 ==> old_ptrs.len() == 0.
                // We can derive sfl.m[idx].len() == 0 here (before modification):
                assert forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf()
                    implies old_sfl.m[idx].len() == 0
                by {
                    if old_sfl.m[idx].len() > 0 {
                        assert(old_sfl.pi.contains_key((idx, 0int)));
                        assert(0 <= old_sfl.pi[(idx, 0int)] < old_ptrs.len());
                    }
                };
                // Extract first_free null facts before modification
                assert forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf()
                    implies AllBlocks::<FLLEN, SLLEN>::ptr_is_null(
                        self.first_free[idx.0 as int][idx.1 as int])
                by {
                    self.wf_index_in_freelist(idx);
                    self.lemma_extract_first_free_null(idx);
                };

                // Capture bitmap field values before all_blocks modification
                // so we can assert they're unchanged afterwards.
                let ghost saved_fl_bitmap = self.fl_bitmap;
                let ghost saved_sl_bitmap = self.sl_bitmap;

                // Build sentinel BlockPerm
                let tracked sentinel_block_perm = BlockPerm {
                    points_to: sentinel_perm,
                    free_link_perm: None,
                    mem: PointsToRaw::empty(sentinel_block@.provenance),
                    overhead_mem: sentinel_overhead,
                    pad_perm: None,
                };

                // Add free block to ptrs@
                lemma_add_ghost_pointer_ensures(old_ptrs, block);
                let ghost ptrs_after_free = add_ghost_pointer(old_ptrs, block);

                // Add sentinel to ptrs@ (sentinel addr > block addr)
                lemma_add_ghost_pointer_ensures(ptrs_after_free, sentinel_block);
                let ghost ptrs_after_both = add_ghost_pointer(ptrs_after_free, sentinel_block);

                // Update ptrs@
                self.all_blocks.ptrs@ = ptrs_after_both;

                // For now, use the fact that on first call all_blocks is empty
                // and shadow_freelist is trivially maintained
                // TODO: generalize for non-empty initial state

                // Insert perms
                self.all_blocks.perms.borrow_mut().tracked_insert(block, new_block_perm);
                self.all_blocks.perms.borrow_mut().tracked_insert(sentinel_block, sentinel_block_perm);

                // Prove free block is_free()
                assert(new_block_perm.points_to.value().is_free()) by {
                    assert(new_block_perm.points_to.value().size == free_block_size);
                    Self::lemma_mark_used_preserves_size_bits(free_block_size);
                    assert((free_block_size & SIZE_USED) == 0usize) by (bit_vector)
                        requires free_block_size as int % 2 == 0, SIZE_USED == 1usize;
                };

                // Prove new_block_perm.wf()
                assert(new_block_perm.wf()) by {
                    assert(new_block_perm.points_to.is_init());
                    Self::lemma_mark_used_preserves_size_bits(free_block_size);
                    assert((new_block_perm.points_to.value().size & SIZE_SIZE_MASK)
                        == new_block_perm.points_to.value().size);
                };

                // Prove sentinel_block_perm.wf()
                assert(sentinel_block_perm.wf()) by {
                    assert(sentinel_block_perm.points_to.is_init());
                    // sentinel is not free (SIZE_USED bit set)
                    assert(!sentinel_block_perm.points_to.value().is_free()) by {
                        assert(sentinel_block_perm.points_to.value().size == SIZE_USED | SIZE_SENTINEL);
                        assert(((SIZE_USED | SIZE_SENTINEL) & SIZE_USED) != 0usize) by (bit_vector)
                            requires SIZE_USED == 1usize, SIZE_SENTINEL == 2usize;
                    };
                };

                // Prove sentinel is_sentinel()
                assert(sentinel_block_perm.points_to.value().is_sentinel()) by {
                    assert(sentinel_block_perm.points_to.value().size == SIZE_USED | SIZE_SENTINEL);
                    assert(((SIZE_USED | SIZE_SENTINEL) & SIZE_SENTINEL) != 0usize) by (bit_vector)
                        requires SIZE_USED == 1usize, SIZE_SENTINEL == 2usize;
                };

                // Prove sentinel (size & SIZE_SIZE_MASK) == 0
                assert(((SIZE_USED | SIZE_SENTINEL) & SIZE_SIZE_MASK) == 0usize) by {
                    reveal(usize_trailing_zeros);
                    reveal(u64_trailing_zeros);
                    assert(SPEC_SIZE_SIZE_MASK == !31usize) by (compute);
                    assert(SIZE_USED == 1usize) by (compute);
                    assert(SIZE_SENTINEL == 2usize) by (compute);
                    assert(((1usize | 2usize) & !31usize) == 0usize) by (bit_vector);
                };

                // Prove wf_node_ptr for block
                AllBlocks::<FLLEN, SLLEN>::lemma_wf_node_ptr_from_facts(block);

                // Prove wf_node_ptr for sentinel
                AllBlocks::<FLLEN, SLLEN>::lemma_wf_node_ptr_from_facts(sentinel_block);

                // Prove phys_next_matches for block → sentinel
                AllBlocks::<FLLEN, SLLEN>::lemma_phys_next_matches_intro(
                    sentinel_block, block, self.all_blocks.value_at(block).size);

                // --- Prove all_blocks.wf() ---
                // We need: all_nodes_wf, ghost_pointer_ordered, pool_size_bounded

                // ghost_pointer_ordered: from lemma_add_ghost_pointer_ensures (applied twice)
                assert(ghost_pointer_ordered(self.all_blocks.ptrs@));

                // pool_size_bounded: for the new ptrs@ list
                // The span from first to last ptr < pow2(FLLEN) * GRANULARITY = max_pool_size
                // sentinel_block - block = chunk_size - GRANULARITY < max_pool_size
                // (chunk_size <= max_pool_size, so chunk_size - GRANULARITY < max_pool_size)
                // For the combined list with old blocks, need to show total span is bounded.
                // For now, handle the empty-initial-state case where ptrs@ = [block, sentinel]
                // pool_size_bounded: for the new ptrs@ list
                // sentinel - block = chunk_size - GRAN < max_pool_size = pow2(FLLEN) * GRAN
                // TODO: prove pool_size_bounded for non-empty initial state
                // For empty initial state: ptrs@ = [block, sentinel], span = chunk_size - GRAN < max_pool_size

                // all_nodes_wf: prove wf_node for each index
                // For new blocks (block and sentinel), construct wf_node
                // For old blocks, show wf_node is preserved

                // --- For empty initial state: ptrs@ = [block, sentinel] ---
                // From first_iter ==> ptrs@.len() == 0 (proved above)
                assert(old_ptrs.len() == 0);
                assert(old_ptrs =~= Seq::<*mut BlockHdr>::empty());

                // Use lemmas to determine concrete sequence
                lemma_add_ghost_pointer_empty(block);
                // Now: add_ghost_pointer(Seq::empty(), block) has len 1 and [0] == block
                // Since old_ptrs =~= Seq::empty(), ptrs_after_free == add_ghost_pointer(old_ptrs, block)
                //   == add_ghost_pointer(Seq::empty(), block)
                assert(ptrs_after_free.len() == 1);
                assert(ptrs_after_free[0] == block);

                // sentinel addr > block addr
                assert(sentinel_block as usize as int > block as usize as int) by {
                    assert(sentinel_block@.addr == sentinel_addr);
                    assert(block@.addr == cursor as int);
                    assert(sentinel_addr > cursor as int);
                };
                // ptrs_after_free =~= seq![block]
                assert(ptrs_after_free =~= seq![block]);
                lemma_add_ghost_pointer_append_to_singleton(block, sentinel_block);
                assert(ptrs_after_both.len() == 2);
                assert(ptrs_after_both[0] == block);
                assert(ptrs_after_both[1] == sentinel_block);
                assert(self.all_blocks.ptrs@.len() == 2);
                assert(self.all_blocks.ptrs@[0] == block);
                assert(self.all_blocks.ptrs@[1] == sentinel_block);

                // Find indices of block and sentinel in ptrs@
                let ghost block_idx = self.all_blocks.get_ptr_internal_index(block);
                let ghost sentinel_idx = self.all_blocks.get_ptr_internal_index(sentinel_block);
                // Since ptrs@ == [block, sentinel] with no duplicates
                assert(block_idx == 0);
                assert(sentinel_idx == 1);

                // phys_prev_of/phys_next_of facts
                assert(self.all_blocks.phys_prev_of(0) is None);
                assert(self.all_blocks.phys_next_of(0) == Some(sentinel_block));
                assert(self.all_blocks.phys_prev_of(1) == Some(block));
                assert(self.all_blocks.phys_next_of(1) is None);

                // --- wf_node for free block (block_idx == 0) ---
                // Preconditions for lemma_construct_wf_node_glue:
                // 1. prev_phys_block@.addr == 0 ==> phys_prev_of(0) is None ✓ (by defn)
                // 2. !is_sentinel(): the free block has size chunk_size - GRANULARITY >= GRANULARITY
                //    which is a valid block size. Sentinel has (size & SIZE_SIZE_MASK) == 0.
                // 3. valid_block_size((size & SIZE_SIZE_MASK) as int) — already proved
                // 4. size + ptr < usize::MAX — cursor + chunk_size - GRANULARITY < usize::MAX
                //    (from cursor + size_remains = start + size, and chunk_size <= size_remains)
                assert(((chunk_size - GRANULARITY) as int) + (cursor as int) < usize::MAX as int) by {
                    // cursor + chunk_size - GRANULARITY <= cursor + size_remains - GRANULARITY
                    // = start + size - GRANULARITY < start + size <= usize::MAX + 1
                    // So cursor + chunk_size - GRANULARITY <= usize::MAX
                    // Actually we need strict < usize::MAX. Since chunk_size >= 2*GRAN,
                    // cursor + chunk_size - GRAN = cursor + chunk_size - GRAN
                    // < cursor + size_remains = start + size <= usize::MAX + 1
                    // Wait: we need (free_block_size as int) + (cursor as int) < usize::MAX
                    // free_block_size = chunk_size - GRANULARITY
                    // cursor + (chunk_size - GRANULARITY) = cursor + chunk_size - GRANULARITY
                    // <= cursor + size_remains - GRANULARITY = start + size - GRANULARITY
                    // start + size <= usize::MAX + 1 (from is_range),
                    // so cursor + chunk_size - GRANULARITY <= usize::MAX + 1 - GRANULARITY
                    // = usize::MAX - GRANULARITY + 1 < usize::MAX (since GRANULARITY >= 1)
                };
                // 5. phys_next_of(0) is Some ✓ (block_idx == 0 != ptrs@.len()-1 == 1)
                // 6. is_free() ==> free_link_perm is Some ✓
                // Prove !is_sentinel(): free block's size has no SIZE_SENTINEL bit
                assert(!self.all_blocks.value_at(block).is_sentinel()) by {
                    assert(self.all_blocks.value_at(block).size == free_block_size);
                    assert(free_block_size % GRANULARITY == 0);
                    assert(free_block_size >= GRANULARITY);
                    // SIZE_SENTINEL == 2, GRANULARITY >= 32, so a GRANULARITY-aligned size
                    // doesn't have bit 1 set
                    assert(((free_block_size) & SIZE_SENTINEL) == 0usize) by (bit_vector)
                        requires free_block_size % 32 == 0, free_block_size >= 32,
                            SIZE_SENTINEL == 2usize;
                };
                self.all_blocks.lemma_construct_wf_node_glue(block_idx);

                // Preconditions for lemma_construct_wf_node_structural:
                // 1. phys_next_of(0) == Some(sentinel_block) ==> phys_next_matches(sentinel_block, block, size)
                // 2. is_free() ==> phys_next_of matches Some && !value_at(next_ptr).is_free()
                //    (sentinel is not free)
                self.all_blocks.lemma_construct_wf_node_structural(block_idx);

                // --- wf_node for sentinel (sentinel_idx == 1) ---
                // Preconditions for lemma_construct_wf_node_glue:
                // 1. prev_phys_block@.addr != 0 (prev_phys_block == block, block addr != 0)
                //    ==> phys_prev_of(1) == Some(block) ✓ && block == prev_phys_block ✓
                assert(self.all_blocks.value_at(sentinel_block).prev_phys_block == block);
                assert(block@.addr != 0);
                // 2. is_sentinel() ==> sentinel_idx == ptrs@.len()-1 ✓ (1 == 2-1)
                // 3. is_sentinel() ==> (size & SIZE_SIZE_MASK) == 0 ✓
                self.all_blocks.lemma_construct_wf_node_glue(sentinel_idx);

                // Preconditions for lemma_construct_wf_node_structural:
                // phys_next_of(1) is None, so the implication is vacuously true
                // !is_free(), so the free condition is vacuously true
                self.all_blocks.lemma_construct_wf_node_structural(sentinel_idx);

                // --- wf_node for block ---
                assert(self.all_blocks.wf_node(block_idx));
                assert(self.all_blocks.wf_node(sentinel_idx));

                // For old blocks: ptrs@ == [block, sentinel], no old blocks
                // The forall is vacuously true
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

                // pool_size_bounded: ptrs@ == [block, sentinel]
                // span = sentinel - block = chunk_size - GRANULARITY
                // chunk_size <= max_pool_size = pow2(FLLEN) * GRANULARITY
                // so span = chunk_size - GRANULARITY < pow2(FLLEN) * GRANULARITY
                assert(self.all_blocks.ptrs@.last() == sentinel_block);
                assert(self.all_blocks.ptrs@[0] == block);
                assert((sentinel_block as usize as int) - (block as usize as int)
                    == (chunk_size - GRANULARITY) as int);
                Self::lemma_max_pool_size_spec_value();
                let ghost mps = Self::max_pool_size_spec();
                assert((chunk_size - GRANULARITY) < mps);
                self.all_blocks.lemma_pool_size_bounded_from_span();

                // Reconstruct all_blocks.wf()
                self.all_blocks.lemma_wf_from_nodes();

                // --- Establish link_free_block preconditions ---
                // all_blocks.wf() ✓ (just proved)
                // all_blocks.contains(block) ✓ (from add_ghost_pointer)
                assert(self.all_blocks.contains(block));

                // all_freelist_wf_weak(set![block])
                // This requires: wf_shadow, freelist_wf for all indices,
                // free_blocks_in_freelist_except(set![block])

                // sfl.m[idx].len() == 0 for all wf idx (proved earlier, before modification)
                // shadow_freelist hasn't changed, so still holds.

                // Prove !shadow_freelist.contains(block) (all freelist entries are empty)
                assert(!self.shadow_freelist@.contains(block)) by {
                    // sfl.contains(block) = exists|i: BlockIndex| i.wf() && sfl.m[i].contains(block)
                    // But sfl.m[i].len() == 0 for all wf i, so sfl.m[i] is empty
                    if self.shadow_freelist@.contains(block) {
                        let i: BlockIndex<FLLEN, SLLEN> = choose|i: BlockIndex<FLLEN, SLLEN>|
                            i.wf() && self.shadow_freelist@.m[i].contains(block);
                        assert(self.shadow_freelist@.m[i].len() == 0);
                    }
                };

                // self.all_blocks.perms@[block].points_to.value().is_free() ✓
                assert(self.all_blocks.perms@[block].points_to.value().is_free());

                // self.all_blocks.perms@[block].points_to.value().size == chunk_size - GRANULARITY
                assert(self.all_blocks.perms@[block].points_to.value().size == free_block_size);

                // --- Prove all_freelist_wf_weak(set![block]) ---
                // 1. wf_shadow(): shadow_freelist unchanged, need is_identity_injection with new ptrs@
                // Since sfl.m[idx].len() == 0 for all wf idx (proved above),
                // is_identity_injection conditions hold vacuously for the third clause.
                // shadow_freelist_has_all_wf_index and shadow_ptrs_nonnull are unchanged.
                // Reveal shadow_ptrs_nonnull so the solver can see it only depends on shadow_freelist
                reveal(Tlsf::shadow_ptrs_nonnull);
                assert(self.shadow_ptrs_nonnull());
                assert(is_identity_injection(self.shadow_freelist@, self.all_blocks.ptrs@)) by {
                    // pi.is_injective(): unchanged
                    // totality: pi.contains_key((idx,m)) <==> ... : sfl unchanged
                    // value constraint: vacuously true since sfl.m[idx].len() == 0
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
                        // sfl.m[idx].len() == 0 for all wf idx, so antecedent is false
                        assert(self.shadow_freelist@.m[idx].len() == 0);
                    };
                };
                assert(self.wf_shadow());

                // 2. freelist_wf(idx) for all wf idx:
                // sfl.m[idx].len() == 0 (proved above), first_free[idx] is null (extracted before modification)
                // Use lemma_freelist_wf_from_empty to reconstruct freelist_wf from these facts
                assert forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf()
                    implies self.freelist_wf(idx)
                by {
                    self.lemma_freelist_wf_from_empty(idx);
                };

                // 3. free_blocks_in_freelist_except(set![block]):
                // For ptrs@ = [block, sentinel], block is excluded, sentinel is not free.
                assert forall|i: int| 0 <= i < self.all_blocks.ptrs@.len()
                    && self.all_blocks.value_at(self.all_blocks.ptrs@[i]).is_free()
                    && !set![block].contains(self.all_blocks.ptrs@[i])
                    implies self.shadow_freelist@.contains(self.all_blocks.ptrs@[i])
                by {
                    // ptrs@ == [block, sentinel]
                    if i == 0 {
                        // ptrs@[0] == block, which is in the exception set
                        assert(set![block].contains(self.all_blocks.ptrs@[0]));
                    } else {
                        // ptrs@[1] == sentinel_block, which is not free
                        assert(i == 1);
                        assert(!self.all_blocks.value_at(sentinel_block).is_free());
                    }
                };
                self.lemma_free_blocks_in_freelist_except_intro(set![block]);

                // Now prove all_freelist_wf_weak(set![block])
                assert(self.all_freelist_wf_weak(set![block]));

                // Assert bitmap fields are unchanged (only all_blocks was modified)
                assert(self.fl_bitmap == saved_fl_bitmap);
                assert(self.sl_bitmap == saved_sl_bitmap);
                // bitmap_wf(): reconstructed from field equality
                assert(self.bitmap_wf());
                // bitmap_sync(): depends on sl_bitmap (unchanged) and shadow_freelist (unchanged)
                assert(self.bitmap_sync());
                // size_class_condition(): opaque, vacuously true since sfl.m[idx].len() == 0
                reveal(Tlsf::size_class_condition);
                assert(self.size_class_condition());
            }

            // Link to the list
            self.link_free_block(chunk_size - GRANULARITY, block);

            // chunk_size == size_remains (proved above), so this is the last iteration
            assert(size_remains == chunk_size);
            size_remains -= chunk_size;
            cursor = cursor.wrapping_add(chunk_size);

            // Re-establish loop invariants for new size_remains
            proof {
                // chunk_size == size_remains (proved earlier), so size_remains is now 0
                first_iter = false;
                if size_remains > 0 {
                    // chunk_size < old size_remains, so cursor + chunk_size didn't overflow
                    // wrapping_add == regular add
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


    pub closed spec fn is_root_provenance<T>(self, ptr: *mut T) -> bool {
        let pv = ptr@.provenance;
        self.root_provenances@ matches Some(ex) && ex.provenance() == pv
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

}

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
pub tracked struct DeallocToken {
    pub ghost ptr: *mut u8,
    pub ghost user_size: int,
    pub ghost align: usize,
}


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
