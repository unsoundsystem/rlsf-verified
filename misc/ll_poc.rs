use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

    const MASK_USED: usize = 2;
    const MASK_SENTINEL: usize = 1;
    pub struct Tlsf<const FLLEN: usize, const SLLEN: usize> {
        pub first_free: [[Option<*mut BlockHdr>; SLLEN]; FLLEN],
        pub all_blocks: AllBlocks,
        pub shadow_free_list: [[Ghost<Seq<*mut BlockHdr>>; SLLEN]; FLLEN],
        pub root_provenance: Tracked<Option<IsExposed>>
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


        spec fn free_list_pred(self, freelist: Seq<*mut BlockHdr>, first: Option<*mut BlockHdr>) -> bool
            recommends self.wf()
        {
            if freelist.len() == 0 {
                first is None
            } else {
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

        //spec fn wf_free_list(self, f: int, s: int) -> bool {
            //self.free_list_pred(self.first_free[f][s])
        //}
    }

    impl<const FLLEN: usize, const SLLEN: usize> Tlsf<FLLEN, SLLEN> {
        fn push_node(&mut self,
            idx: (usize, usize),
            node: *mut BlockHdr,
            Tracked(node_pt): Tracked<PointsTo<BlockHdr>>,
            Tracked(node_fl_pt): Tracked<PointsTo<FreeLink>>)
            requires
                node == node_pt.ptr(),
                node_pt.is_init(),
                node_pt.value().is_free(),
                BlockHdr::fl_ptr_spec(node, old(self).root_provenance@.unwrap().provenance()) == node_fl_pt.ptr(),
                old(self).all_blocks.free_list_pred(
                    old(self).shadow_free_list[idx.0 as int][idx.1 as int]@,
                    old(self).first_free[idx.0 as int][idx.1 as int])
            ensures
                self.all_blocks.free_list_pred(
                    seq![node].add(old(self).shadow_free_list[idx.0 as int][idx.1 as int]@),
                    self.first_free[idx.0 as int][idx.1 as int])
        {
            let (f, s) = idx;
            let tracked mut node_pt = node_pt;
            let tracked mut node_fl_pt = node_fl_pt;
            let root_provenance = {
                let Tracked(prov) = self.root_provenance;
                Tracked(prov.tracked_unwrap())
            };

            if self.first_free[f][s].is_some() {
                let first_node = self.first_free[f][s].unwrap();
                let tracked BlockPerm { points_to: first_pt, free_link_perm: first_fl_pt }
                    = self.all_blocks.perms.borrow_mut().tracked_remove(first_node);
                // because first_node is free block
                let tracked first_fl_pt = first_fl_pt.tracked_unwrap();

                // update first pointer
                self.set_freelist(f, s, Some(node));

                // update link
                let link = BlockHdr::fl_ptr(first_node, root_provenance);
                let link_payload = ptr_mut_read(link, Tracked(&mut first_fl_pt));
                ptr_mut_write(link, Tracked(&mut first_fl_pt), FreeLink {
                    next_free: link_payload.next_free,
                    prev_free: Some(node)
                });

                // update new node's link
                let link = BlockHdr::fl_ptr(node, root_provenance);
                ptr_mut_write(link, Tracked(&mut node_fl_pt), FreeLink {
                    next_free: Some(first_node),
                    prev_free: None
                });

                proof {
                    self.all_blocks.perms.borrow_mut().tracked_insert(node,
                        BlockPerm {
                            points_to: node_pt,
                            free_link_perm: Some(node_fl_pt)
                        });
                    self.all_blocks.perms.borrow_mut().tracked_insert(first_node,
                        BlockPerm {
                            points_to: first_pt,
                            free_link_perm: Some(first_fl_pt)
                        });
                }
            } else {
                // list is empty
                self.set_freelist(f, s, Some(node));

                // update new node's link
                let link = BlockHdr::fl_ptr(node, root_provenance);
                ptr_mut_write(link, Tracked(&mut node_fl_pt), FreeLink {
                    next_free: None,
                    prev_free: None
                });

            }
        }

        #[inline(always)]
        #[verifier::external_body]
        fn set_freelist(&mut self, i: usize, j: usize, v: Option<*mut BlockHdr>)
            requires
                0 <= i < FLLEN,
                0 <= j < SLLEN
            ensures
                self.first_free[i as int][j as int] == v
        {
            self.first_free[i][j] = v;
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


        fn fl_ptr(ptr: *mut BlockHdr, prov: Tracked<IsExposed>) -> *mut FreeLink {
            with_exposed_provenance(ptr as usize + size_of::<BlockHdr>(), prov)
        }

        spec fn fl_ptr_spec(ptr: *mut BlockHdr, prov: Provenance) -> *mut FreeLink {
            ptr_from_data(PtrData::<FreeLink> {
                addr: (ptr@.addr + size_of::<BlockHdr>()) as usize,
                provenance: ptr@.provenance,
                metadata: ()
            }) as *mut _
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
