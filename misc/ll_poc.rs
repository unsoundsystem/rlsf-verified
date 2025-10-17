use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

    const MASK_USED: usize = 2;
    const MASK_SENTINEL: usize = 1;
    const MASK_SIZE: usize = 0b11;

    pub struct Tlsf<const FLLEN: usize, const SLLEN: usize> {
        pub first_free: [[Option<*mut BlockHdr>; SLLEN]; FLLEN],
        pub root_provenance: Tracked<Option<IsExposed>>,
        pub all_blocks: AllBlocks,
    }

    /// Tracks global structure of the header linkage and memory states
    struct AllBlocks {
        pub ptrs: Ghost<Seq<*mut BlockHdr>>,
        pub perms: Tracked<Map<*mut BlockHdr, BlockPerm>>,
    }

    impl AllBlocks {
        spec fn value_at(self, ptr: *mut BlockHdr) -> BlockHdr
            recommends self.contains(ptr)
        {
            self.perms@[ptr].points_to.value()
        }

        spec fn contains(self, ptr: *mut BlockHdr) -> bool {
            self.ptrs@.contains(ptr)
        }

        spec fn wf_node(self, i: int) -> bool
            recommends 0 <= i < self.ptrs@.len()
        {
            let ptr = self.ptrs@[i];
            // --- Well-formedness for tracked/ghost states
            &&& self.ptrs@[i] == self.perms@[ptr].points_to.ptr()
            &&& self.perms@[ptr].points_to.is_init()

            // --- Glue invariants between physical state & tracked/ghost state
            // prev_phys_block invariant
            &&& self.value_at(ptr).prev_phys_block is None ==> self.phys_prev_of(i) is None
            &&& self.value_at(ptr).prev_phys_block matches Some(prev_ptr) ==>
                    self.phys_prev_of(i) == Some(prev_ptr)
            // if sentinel flag is present then it's last element in ptrs
            &&& self.value_at(ptr).is_sentinel() ==> i == self.ptrs@.len() - 1
            // if used flag is not present then it connected to freelist
            &&& if self.value_at(ptr).is_free() {
                self.perms@[ptr].free_link_perm matches Some(p)
                        && p.ptr() == Self::get_freelink_ptr(ptr)
                } else { true }

            // --- Invariants on tracked/ghost states
            // next block invariant
            &&& self.phys_next_of(i) matches Some(next_ptr) ==>
                ({
                    &&& next_ptr == ptr_from_data(
                        PtrData::<BlockHdr> {
                            provenance: ptr@.provenance,
                            addr: (ptr as usize + self.value_at(ptr).size) as usize,
                            metadata: ()
                        }) as *mut BlockHdr
                    &&& self.contains(next_ptr)
                    &&& self.ptrs@[i + 1] == next_ptr
                })
            &&& if self.value_at(ptr).is_free() {
                    self.phys_next_of(i) matches Some(next_ptr)
                        && !self.value_at(next_ptr).is_free()
                } else { true }
        }

        spec fn phys_next_of(self, i: int) -> Option<*mut BlockHdr> {
            if self.ptrs@.len() - 1 == i {
                None
            } else {
                Some(self.ptrs@[i + 1])
            }
        }

        spec fn phys_prev_of(self, i: int) -> Option<*mut BlockHdr> {
            if i == 0 {
                None
            } else {
                Some(self.ptrs@[i - 1])
            }
        }

        spec fn is_sentinel_pointer(self, ptr: *mut BlockHdr) -> bool
            recommends self.wf(), self.contains(ptr)
        {
            self.value_at(ptr).is_sentinel()
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
                &&& node_link.next_free matches Some(next_ptr)
                    ==> self.phys_next_of(i) == Some(next_ptr)
                &&& node_link.next_free is None ==> self.phys_next_of(i) is None
                &&& node_link.prev_free matches Some(prev_ptr) ==> prev_ptr == freelist[i - 1]
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

    impl<const FLLEN: usize, const SLLEN: usize> Tlsf<FLLEN, SLLEN> {
        fn next_phys_block(&mut self, cur: *mut BlockHdr) -> (r: (*mut BlockHdr, Tracked<BlockPerm>))
            requires
                old(self).all_blocks.wf(),
                old(self).all_blocks.contains(cur),
                !old(self).all_blocks.is_sentinel_pointer(cur)
            ensures
                self.all_blocks.wf(),
                r.0 == r.1@.points_to.ptr(),
                ({
                    let (res_next, res_pt) = r;
                    let cur_pos = choose|i: int| self.all_blocks.ptrs@[i] == cur;
                    self.all_blocks.phys_next_of(cur_pos) matches Some(r)
                })
        {
            let tracked mut perm = self.all_blocks.perms.borrow_mut().tracked_remove(cur);
            let size = ptr_ref(cur, Tracked(&mut perm.points_to)).size & MASK_SIZE;
            let next_phys_block_addr = (cur as *mut u8) as usize + size;
            let Tracked(pv) = self.root_provenance;
            let tracked pv = pv.tracked_unwrap();
            let ptr: *mut BlockHdr =
                with_exposed_provenance(next_phys_block_addr, Tracked(pv));
            (ptr, Tracked(perm))
        }
    }

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
