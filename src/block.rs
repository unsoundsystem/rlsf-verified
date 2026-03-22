use crate::parameters::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::bits::u64_trailing_zeros;
#[cfg(verus_keep_ghost)]
use crate::bits::usize_trailing_zeros;
use vstd::prelude::*;
use vstd::raw_ptr::*;
#[cfg(verus_keep_ghost)]
use vstd::relations::injective;

verus! {
    #[repr(C)]
    #[derive(Debug)]
    pub struct BlockHdr {
        pub(crate) size: usize,
        pub(crate) prev_phys_block: *mut BlockHdr,
    }

    impl BlockHdr {
        pub(crate) open spec fn is_sentinel(self) -> bool {
            self.size & SIZE_SENTINEL != 0
        }
        pub(crate) open spec fn is_free(self) -> bool {
            self.size & SIZE_USED == 0
        }

        pub(crate) fn next_phys_block(block: *mut Self, Tracked(perm): Tracked<&BlockPerm>) -> (r: *mut Self)
            requires
                perm.points_to.is_init(),
                perm.points_to.ptr() == block,
                !perm.points_to.value().is_sentinel(),
                (block as usize as int) + (perm.points_to.value().size as int) < usize::MAX as int,
            ensures
                r@.provenance == block@.provenance,
                r@.addr == block@.addr + ((perm.points_to.value().size & SIZE_SIZE_MASK) as int),
        {
            let size = ptr_ref(block, Tracked(&perm.points_to)).size;

            //debug_assert!((size & SIZE_SENTINEL) == 0, "`self` must not be a sentinel");
            #[cfg(feature = "std")]
            {
                assert!((size & SIZE_SENTINEL) == 0, "`self` must not be a sentinel");
            }

            proof {
                reveal(usize_trailing_zeros);
                reveal(u64_trailing_zeros);
                assert(SPEC_SIZE_SIZE_MASK == !31usize) by (compute);
                assert(size == perm.points_to.value().size);
            }

            // Compute masked size with overflow-safe bit masking
            // SIZE_SIZE_MASK clears the low 5 bits
            let mask: usize = !31usize;
            let masked_size = size & mask;
            proof {
                assert(masked_size <= size) by (bit_vector)
                    requires masked_size == size & mask, mask == !31usize;
                assert((block as usize) as int + (masked_size as int)
                    <= (block as usize) as int + (size as int));
            }

            // Safety: Since `self.size & SIZE_SENTINEL` is not lying, the
            //         next block should exist at a non-null location.
            let prov = expose_provenance(block);
            let r = with_exposed_provenance((block as usize) + masked_size, prov);
            r
        }
    }

    #[repr(C)]
    pub(crate) struct FreeLink {
        pub(crate) next_free: *mut BlockHdr,
        pub(crate) prev_free: *mut BlockHdr,
    }

    pub struct BlockPerm {
        pub(crate) points_to: PointsTo<BlockHdr>,
        pub(crate) free_link_perm: Option<PointsTo<FreeLink>>,
        pub(crate) mem: PointsToRaw,
        pub(crate) overhead_mem: PointsToRaw,
        pub(crate) pad_perm: Option<PointsTo<UsedBlockPad>>,
    }

    impl BlockPerm {
        pub(crate) open spec fn wf(self) -> bool {
            &&& self.points_to.is_init()
            &&& self.mem.provenance() == self.points_to.ptr()@.provenance
            &&& self.points_to.value().is_free() ==> {
                    let size = self.points_to.value().size;
                    &&& self.free_link_perm matches Some(pt) &&
                            get_freelink_ptr_spec(self.points_to.ptr()) == pt.ptr()
                                && pt.is_init()
                    // NOTE: SIZE_USED and SIZE_SENTINEL is not present
                    &&& size == size & SIZE_SIZE_MASK
                    &&& self.mem.is_range(
                        self.points_to.ptr() as int + size_of::<BlockHdr>() as int + size_of::<FreeLink>() as int,
                        size as int - size_of::<BlockHdr>() as int - size_of::<FreeLink>() as int)
                    &&& self.overhead_mem.dom().is_empty()
                    &&& self.pad_perm is None
                }
        }
    }

    pub(crate) type UsedBlockHdr = BlockHdr;

    #[repr(C)]
    pub struct UsedBlockPad {
        pub(crate) block_hdr: *mut UsedBlockHdr,
    }

    impl UsedBlockPad {
        //#[verifier::external_body] // debug
        #[inline]
        pub(crate) fn get_for_allocation(ptr: *mut u8) -> (r: *mut Self)
            ensures
                r@.provenance == ptr@.provenance,
                r@.addr == ((ptr as usize).wrapping_sub(core::mem::size_of::<Self>()) as int),
                ptr@.addr >= core::mem::size_of::<Self>() as int
                    ==> r@.addr == ptr@.addr - core::mem::size_of::<Self>() as int,
        {
            let Tracked(is_exposed) = expose_provenance(ptr);
            let ptr = with_exposed_provenance(
                (ptr as usize).wrapping_sub(core::mem::size_of::<Self>()),
                Tracked(is_exposed));
            ptr
        }
    }

    pub closed spec fn get_freelink_ptr_spec(ptr: *mut BlockHdr) -> *mut FreeLink {
        ptr_from_data(PtrData::<FreeLink> {
            provenance: ptr@.provenance,
            addr: (ptr as usize + size_of::<BlockHdr>()) as usize,
            metadata: ()
        }) as *mut _
    }

    pub fn get_freelink_ptr(ptr: *mut BlockHdr) -> (r: *mut FreeLink)
        requires
            (ptr as usize as int) + (size_of::<BlockHdr>() as int) <= usize::MAX as int,
        ensures
            r == get_freelink_ptr_spec(ptr),
            r@.provenance == ptr@.provenance,
            r as usize == ptr as usize + size_of::<BlockHdr>(),
    {
        let prov = expose_provenance(ptr);
        with_exposed_provenance(ptr as usize + size_of::<BlockHdr>(), prov)
    }

    pub(crate) const fn null_bhdr() -> (r: *mut BlockHdr)
        ensures r@.addr == 0
    {
        core::ptr::null::<BlockHdr>() as *mut _
    }


}
