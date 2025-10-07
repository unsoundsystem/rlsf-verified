use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

    const MASK_USED: usize = 2;
    const MASK_SENTINEL: usize = 1;
    pub struct Tlsf<const FLLEN: usize, const SLLEN: usize> {
        pub first_free: [[Option<*mut BlockHdr>; SLLEN]; FLLEN],
        pub all_blocks: AllBlocks,
    }

    /// Tracks global structure of the header linkage and memory states
    struct AllBlocks {
        pub ptrs: Ghost<Seq<*mut BlockHdr>>,
        pub perms: Tracked<Map<*mut BlockHdr, BlockPerm>>,
    }

    impl AllBlocks {
        spec fn value_at(self, ptr: *mut BlockHdr) -> BlockHdr {
            self.perms@[ptr].points_to.value()
        }

        spec fn contains(self, ptr: *mut BlockHdr) -> bool {
            self.ptrs@.contains(ptr)
        }

        spec fn wf_node(self, i: int) -> bool
            recommends 0 <= i < self.ptrs@.len()
        {
            let ptr = self.ptrs@[i];
            // 
            &&& self.ptrs@[i] == self.perms@[ptr].points_to.ptr()
            &&& self.perms@[ptr].points_to.is_init()
            // prev_phys_block invariant
            &&& self.value_at(ptr).prev_phys_block is None ==> i == 0
            &&& self.value_at(ptr).prev_phys_block matches Some(prev_ptr) ==>
                    self.ptrs@[i - 1] == prev_ptr && i > 0
            // next block invariant
            &&& if i < self.ptrs@.len() - 1 {
                let next_ptr = ptr_from_data(PtrData::<BlockHdr> {
                    provenance: ptr@.provenance,
                    addr: (ptr as usize + self.value_at(ptr).size) as usize,
                    metadata: ()
                }) as *mut BlockHdr;
                &&& self.contains(next_ptr)
                &&& self.ptrs@[i + 1] == next_ptr
            } else {
                true
            }
            // sentinel
            &&& self.value_at(ptr).is_sentinel() ==> i == self.ptrs@.len() - 1
            // free block invariant
            &&& if self.value_at(ptr).is_free() {
                // Free list linkage header exists
                self.perms@[ptr].free_link_perm matches Some(p)
                        && p.ptr() == Self::get_freelink_ptr(ptr)
            } else {
                // used
                true
            }
        }

        spec fn wf(self) -> bool {
            &&& forall|i: int| 0 <= i < self.ptrs@.len() ==> self.wf_node(i)
            // TLSF block invariant: No adjacent free blocks
            &&& forall|i: int| 0 <= i < self.ptrs@.len() - 1
                    ==> #[trigger] self.value_at(self.ptrs@[i]).is_free()
                    ==> !self.value_at(self.ptrs@[i + 1]).is_free()
        }


        spec fn free_list_pred(self, freelist: Seq<*mut BlockHdr>, first: *mut BlockHdr) -> bool
            recommends self.wf()
        {
            forall|i: int| 0 <= i < freelist.len() ==> {
                let node = self.value_at(freelist[i]);
                spec_affirm(node.is_free());
                let node_link_ptr = Self::get_freelink_ptr(freelist[i]);
                let node_link = #[trigger] self.perms@[freelist[i]].free_link_perm.unwrap().value();
                &&& node_link.next_free matches Some(next_ptr) ==> next_ptr == freelist[i + 1]
                &&& node_link.next_free is None ==> i == freelist.len() - 1
                &&& node_link.next_free matches Some(next_ptr) ==> next_ptr == freelist[i - 1]
                &&& node_link.prev_free is None ==> i == 0
            }
        }

        spec fn get_freelink_ptr(ptr: *mut BlockHdr) -> *mut FreeLink {
            ptr_from_data(PtrData::<FreeLink> {
                provenance: ptr@.provenance,
                addr: (ptr as usize + size_of::<BlockHdr>()) as usize,
                metadata: ()
            }) as *mut _
        }

        // free_list_pred(ab, seq![1, 2, 3], ptr)
        // <==> ab.value_at(ptr) == 1
        //      && free_list_pred(ab, seq![2, 3],
        //              ab.perms@[ptr].free_link_perm.unwrap().value().next_free)
        //


    }

    //impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    //}

    struct BlockHdr {
        size: usize,
        prev_phys_block: Option<*mut BlockHdr>
    }

    impl BlockHdr {
        spec fn is_sentinel(self) -> bool {
            self.size & MASK_SENTINEL != 0
        }
        spec fn is_free(self) -> bool {
            self.size & MASK_USED == 0
        }
    }

    struct FreeLink {
        next_free: Option<*mut BlockHdr>,
        prev_free: Option<*mut BlockHdr>,
    }

    struct BlockPerm {
        points_to: PointsTo<BlockHdr>,
        free_link_perm: Option<PointsTo<FreeLink>>,
    }

    impl BlockPerm {
        spec fn wf(self) -> bool {
            self.points_to.value().size & MASK_USED == 0
                ==> self.free_link_perm is Some
        }
    }


}
