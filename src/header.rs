use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::relations::injective;

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
        size: usize,
        prev_phys_block: Option<*mut BlockHdr>,
    }

    impl BlockHdr {
        spec fn is_sentinel(self) -> bool {
            self.size & MASK_SENTINEL != 0
        }
        spec fn is_free(self) -> bool {
            self.size & MASK_USED == 0
        }
    }

    pub(crate) struct FreeLink {
        next_free: Option<*mut BlockHdr>,
        prev_free: Option<*mut BlockHdr>,
    }

    pub(crate) struct BlockPerm {
        points_to: PointsTo<BlockHdr>,
        free_link_perm: Option<PointsTo<FreeLink>>,
    }

    impl BlockPerm {
        spec fn wf(self) -> bool {
            &&& self.points_to.value().size & MASK_USED == 0
                ==> self.free_link_perm is Some
            &&& self.points_to.is_init()
            &&& self.free_link_perm matches Some(pt) &&
                get_freelink_ptr_spec(self.points_to.ptr()) == pt.ptr()
                    && pt.is_init()
        }
    }

    #[repr(C)]
    pub(crate) struct UsedBlockHdr {
        common: BlockHdr,
    }

    #[repr(C)]
    pub(crate) struct UsedBlockPad {
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
    pub(crate) struct FreeBlockHdr {
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
}
