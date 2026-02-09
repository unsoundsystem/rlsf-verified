use crate::parameters::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd::raw_ptr::*;
#[cfg(verus_keep_ghost)]
use vstd::relations::injective;

verus! {
    #[repr(C)]
    #[derive(Debug)]
    pub(crate) struct BlockHdr {
        pub(crate) size: usize,
        pub(crate) prev_phys_block: *mut BlockHdr,
    }

    impl BlockHdr {
        pub(crate) closed spec fn is_sentinel(self) -> bool {
            self.size & SIZE_SENTINEL != 0
        }
        pub(crate) closed spec fn is_free(self) -> bool {
            self.size & SIZE_USED == 0
        }

        pub(crate) fn next_phys_block(block: *mut Self, Tracked(perm): Tracked<&BlockPerm>) -> *mut Self {
            let size = ptr_ref(block, Tracked(&perm.points_to)).size;

            //debug_assert!((size & SIZE_SENTINEL) == 0, "`self` must not be a sentinel");

            // Safety: Since `self.size & SIZE_SENTINEL` is not lying, the
            //         next block should exist at a non-null location.
            let prov = expose_provenance(block);
            with_exposed_provenance((block as usize) + (size & SIZE_SIZE_MASK), prov)
        }
    }

    #[repr(C)]
    pub(crate) struct FreeLink {
        pub(crate) next_free: *mut BlockHdr,
        pub(crate) prev_free: *mut BlockHdr,
    }

    pub(crate) struct BlockPerm {
        pub(crate) points_to: PointsTo<BlockHdr>,
        pub(crate) free_link_perm: Option<PointsTo<FreeLink>>,
        pub(crate) mem: PointsToRaw,
    }

    impl BlockPerm {
        pub(crate) open spec fn wf(self) -> bool {
            &&& self.points_to.is_init()
            &&& self.points_to.value().is_free()
                ==> self.free_link_perm is Some
            &&& self.free_link_perm matches Some(pt) &&
                get_freelink_ptr_spec(self.points_to.ptr()) == pt.ptr()
                    && pt.is_init()
        }
    }

    pub(crate) struct UsedInfo {
        pub ptrs: Ghost<Seq<*mut BlockHdr>>,
        // map from block start (i.e. allocated pointer) to the padding
        pub pad_perms: Tracked<Map<*mut u8, PointsTo<UsedBlockPad>>>,
    }

    impl UsedInfo {
        pub closed spec fn wf(self) -> bool {
            &&& ghost_pointer_ordered(self.ptrs@)
            // FIXME: replace with II
            //&&& forall|ptr: *mut UsedBlockHdr|
                    //self.perms@.contains_key(ptr) <==> self.ptrs@.contains(ptr)
            //&&& forall|p: *mut UsedBlockHdr|
                    //self.ptrs@.contains(p) ==> self.perms@[p].ptr() == p
        }

        pub closed spec fn contains(self, ptr: *mut BlockHdr) -> bool
            recommends self.wf()
        {
            &&& self.wf()
            &&& self.ptrs@.contains(ptr)
        }

        //FIXME: should be a macro
        //pub fn add(&mut self, ptr: *mut UsedBlockHdr, Tracked(perm): Tracked<PointsTo<UsedBlockHdr>>) {
            //proof {
                //self.ptrs@ = self.ptrs@.push(ptr)
                    //.sort_by(pointer_le::<UsedBlockHdr>());
                //self.perms@.tracked_insert(ptr, perm);
            //}
        //}
    }


    pub(crate) type UsedBlockHdr = BlockHdr;

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

    pub(crate) open spec fn pointer_leq<T>() -> spec_fn(*mut T, *mut T) -> bool {
        |x: *mut T, y: *mut T| {
            let xi = x as usize as int;
            let yi = y as usize as int;
            xi <= yi
        }
    }

    pub(crate) open spec fn ghost_pointer_ordered(ls: Seq<*mut BlockHdr>) -> bool {
        forall|i: int, j: int|
            0 <= i < ls.len() && 0 <= j < ls.len() && i < j ==>
                (ls[i] as usize as int) <= (ls[j] as usize as int)
    }

    pub(crate) const fn null_bhdr() -> (r: *mut BlockHdr)
        ensures r@.addr == 0
    {
        core::ptr::null::<BlockHdr>() as *mut _
    }


}
