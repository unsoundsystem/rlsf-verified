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
        // reveal(u64_trailing_zeros); // closed in newer vstd
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
                mem: PointsToRaw::empty(Provenance::null()),
                overhead_mem: PointsToRaw::empty(Provenance::null()),
                pad_perm: None,
            };
            let mut sentinel_block = BlockHdr::next_phys_block(block, Tracked(&new_block_perm));

            #[cfg(feature = "std")]
            {
                sentinel_tmp = sentinel_block;
            }

            // Link to the list
            {
                let tracked new_block_freelink_perm = new_block_perm.free_link_perm.tracked_unwrap();
                self.link_free_block(chunk_size - GRANULARITY, block);
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
