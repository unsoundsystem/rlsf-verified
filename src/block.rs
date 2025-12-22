#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd::raw_ptr::*;
#[cfg(verus_keep_ghost)]
use vstd::relations::injective;
use crate::parameters::*;


verus! {
    #[repr(C)]
    pub(crate) struct BlockHdr {
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
        pub(crate) size: usize,
        pub(crate) prev_phys_block: Option<*mut BlockHdr>,
    }

    impl BlockHdr {
        pub(crate) closed spec fn is_sentinel(self) -> bool {
            self.size & SIZE_SENTINEL != 0
        }
        pub(crate) closed spec fn is_free(self) -> bool {
            self.size & SIZE_USED == 0
        }
    }

    #[repr(C)]
    pub(crate) struct FreeLink {
        pub(crate) next_free: Option<*mut BlockHdr>,
        pub(crate) prev_free: Option<*mut BlockHdr>,
    }

    pub(crate) struct BlockPerm {
        pub(crate) points_to: PointsTo<BlockHdr>,
        pub(crate) free_link_perm: Option<PointsTo<FreeLink>>,
    }

    impl BlockPerm {
        pub(crate) closed spec fn wf(self) -> bool {
            &&& self.points_to.value().size & SIZE_USED == 0
                ==> self.free_link_perm is Some
            &&& self.points_to.is_init()
            &&& self.free_link_perm matches Some(pt) &&
                get_freelink_ptr_spec(self.points_to.ptr()) == pt.ptr()
                    && pt.is_init()
        }
    }

    #[repr(C)]
    pub(crate) struct UsedBlockHdr {
        pub(crate) common: BlockHdr,
    }

    #[repr(C)]
    pub(crate) struct UsedBlockPad {
        pub(crate) block_hdr: *mut UsedBlockHdr,
    }

    impl UsedBlockPad {
        //#[verifier::external_body] // debug
        #[inline]
        pub(crate) fn get_for_allocation(ptr: *mut u8) -> (r: *mut Self) {
            let Tracked(is_exposed) = expose_provenance(ptr);
            // FIXME: this subtraction was wrapping_sub
            let ptr = with_exposed_provenance(
                ptr as usize - size_of::<BlockHdr>() - size_of::<FreeLink>(),
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
        ensures r == get_freelink_ptr_spec(ptr)
    {
        let prov = expose_provenance(ptr);
        with_exposed_provenance(ptr as usize + size_of::<BlockHdr>(), prov)
    }

}
