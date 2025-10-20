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
        pub shadow_freelist: [[Seq<*mut BlockHdr>; SLLEN]; FLLEN]
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
                        && p.ptr() == get_freelink_ptr_spec(ptr)
                } else { true }

            // --- Invariants on tracked/ghost states
            // next block invariant
            &&& self.phys_next_of(i) matches Some(next_ptr) ==>
                    next_ptr == ptr_from_data(
                        PtrData::<BlockHdr> {
                            provenance: ptr@.provenance,
                            addr: (ptr as usize + self.value_at(ptr).size) as usize,
                            metadata: ()
                        }) as *mut BlockHdr
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


        // free_list_pred(ab, seq![1, 2, 3], ptr)
        // <==> ab.value_at(ptr) == 1
        //      && free_list_pred(ab, seq![2, 3],
        //              ab.perms@[ptr].free_link_perm.unwrap().value().next_free)
        //

    }

    impl<const FLLEN: usize, const SLLEN: usize> Tlsf<FLLEN, SLLEN> {
        fn link_free_block(&mut self, i: usize, j: usize, node: *mut BlockHdr, Tracked(perm): Tracked<BlockPerm>)
            requires
                0 <= i < FLLEN, 0 <= j < SLLEN,
                old(self).all_blocks.wf(),
                old(self).freelist_wf(),
                node == perm.points_to.ptr(),
                perm.wf(),
                perm.free_link_perm is Some,
                old(self).tlsf_free_list_pred(
                    i as int,
                    j as int,
                    old(self).shadow_freelist[i as int][j as int])
            ensures
                self.freelist_wf(),
                self.tlsf_free_list_pred(
                    i as int,
                    j as int,
                    seq![node].add(self.shadow_freelist[i as int][j as int]))
        {
            let tracked BlockPerm {
                points_to: node_pt,
                free_link_perm: node_fl_pt
            } = perm;
            let tracked node_fl_pt = node_fl_pt.tracked_unwrap();
            if let Some(first_free) = self.first_free[i][j] {
                // unimplemented
                let tracked first_free_perm = self.all_blocks.perms.borrow_mut().tracked_remove(first_free);
                let tracked first_free_fl_pt = first_free_perm.free_link_perm.tracked_unwrap();
            } else {
                self.set_freelist(i, j, Some(node));
                ptr_mut_write(get_freelink_ptr(node), Tracked(&mut node_fl_pt), FreeLink {
                    next_free: None,
                    prev_free: None
                });
            }
        }

        spec fn freelist_wf(self) -> bool {
            forall|i: int, j: int|
                0 <= i < FLLEN && 0 <= j < SLLEN
                    ==> self.free_list_pred(self.shadow_freelist[i][j], self.first_free[i][j])
        }

        spec fn tlsf_free_list_pred(self, i: int, j: int, ls: Seq<*mut BlockHdr>) -> bool {
            self.free_list_pred(ls, self.first_free[i][j])
        }

        spec fn free_list_pred(self, freelist: Seq<*mut BlockHdr>, first: Option<*mut BlockHdr>) -> bool
            recommends self.all_blocks.wf()
        {
            if first.is_none() {
                freelist.len() == 0
            } else {
                forall|i: int| 0 <= i < freelist.len() ==> {
                    let node = self.all_blocks.value_at(freelist[i]);
                    spec_affirm(node.is_free());
                    let node_link_ptr = get_freelink_ptr_spec(freelist[i]);
                    let node_link = #[trigger] self.all_blocks.perms@[freelist[i]].free_link_perm.unwrap().value();
                    &&& node_link.next_free matches Some(next_ptr)
                        ==> self.all_blocks.phys_next_of(i) == Some(next_ptr)
                    &&& node_link.next_free is None ==> self.all_blocks.phys_next_of(i) is None
                    &&& node_link.prev_free matches Some(prev_ptr) ==> prev_ptr == freelist[i - 1]
                    &&& node_link.prev_free is None ==> i == 0
                }
            }
        }

        #[verifier::external_body]
        fn set_freelist(&mut self, i: usize, j: usize, e: Option<*mut BlockHdr>)
            requires 0 <= i < FLLEN, 0 <= j < SLLEN
            ensures
                self.first_free[i as int][j as int] == e
        {
            self.first_free[i][j] = e;
        }
    }

    spec fn get_freelink_ptr_spec(ptr: *mut BlockHdr) -> *mut FreeLink {
        ptr_from_data(PtrData::<FreeLink> {
            provenance: ptr@.provenance,
            addr: (ptr as usize + size_of::<BlockHdr>()) as usize,
            metadata: ()
        }) as *mut _
    }

    fn get_freelink_ptr(ptr: *mut BlockHdr) -> *mut FreeLink {
        let prov = expose_provenance(ptr);
        with_exposed_provenance(ptr as usize + size_of::<BlockHdr>(), prov)
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


pub assume_specification<T> [core::mem::replace::<T>] (dest: &mut T, src: T) -> (res: T)
    ensures
        *dest == src,
        res == *old(dest)
    opens_invariants none
    no_unwind;
}
