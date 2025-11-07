use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

    const MASK_USED: usize = 2;
    const MASK_SENTINEL: usize = 1;
    const MASK_SIZE: usize = 0b11;

    #[verifier::ext_equal]
    pub struct BlockIndex<const FLLEN: usize, const SLLEN: usize>(pub usize, pub usize);

    impl<const FLLEN: usize, const SLLEN: usize> BlockIndex<FLLEN, SLLEN> {
        pub open spec fn valid_block_index(idx: (int, int)) -> bool {
            let (fl, sl) = idx;
            &&& 0 <= fl < FLLEN as int
            &&& 0 <= sl < SLLEN as int
        }

        pub open spec fn view(self) -> (int, int) {
            (self.0 as int, self.1 as int)
        }


        pub open spec fn wf(self) -> bool {
            Self::valid_block_index(self@)
        }
    }

    #[verifier::reject_recursive_types(FLLEN)]
    #[verifier::reject_recursive_types(SLLEN)]
    pub struct Tlsf<const FLLEN: usize, const SLLEN: usize> {
        pub first_free: [[Option<*mut BlockHdr>; SLLEN]; FLLEN],
        pub root_provenance: Tracked<Option<IsExposed>>,
        pub all_blocks: AllBlocks,
        pub shadow_freelist: Ghost<Map<BlockIndex<FLLEN, SLLEN>, Seq<*mut BlockHdr>>>
    }

    /// Tracks global structure of the header linkage and memory states
    struct AllBlocks {
        /// Pointers for all blocks, ordered by address.
        pub ptrs: Ghost<Seq<*mut BlockHdr>>,
        /// Tracked permissions for all blocks, indexed by pointer.
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

        /// States that each block at `self.ptr[i]` is well-formed i.e.
        ///
        /// * Block is properly connected to the global list
        ///     * Ghost state `self.ptrs` properly reflecting physical state;
        ///       for each p: `self.ptrs[i]`,
        ///         * self.perms[p] is defined, `Init` and pointer matches p
        ///         * `self.ptrs` reflects the order of linked list;
        ///           let pr = self.perms[i],
        ///              * 0 < i <= self.ptrs.len():
        ///                  pr.value().prev_phys_block is Some(p') ==> p' == self.ptr[i-1]
        ///              * i == 0: pr.value().prev_phys_block is None
        spec fn wf_node(self, i: int) -> bool
            recommends 0 <= i < self.ptrs@.len()
        {
            let ptr = self.ptrs@[i];
            // --- Well-formedness for tracked/ghost states
            &&& self.perms@.contains_key(ptr)
            &&& ptr == self.perms@[ptr].points_to.ptr()
            &&& self.perms@[ptr].wf()

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

            // TODO: Move following to self.wf() ?
            // --- Invariants on tracked/ghost states
            // Next block address
            &&& self.phys_next_of(i) matches Some(next_ptr) ==>
                    next_ptr as usize == (ptr as usize + self.value_at(ptr).size) as usize
            // No adjacent free blocks
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

        /// Well-formedness for the global list structure.
        spec fn wf(self) -> bool {
            // Each block at ptrs[i] is well-formed.
            &&& forall|i: int| 0 <= i < self.ptrs@.len() ==> self.wf_node(i)
        }


        // free_list_pred(ab, seq![1, 2, 3], ptr)
        // <==> ab.value_at(ptr) == 1
        //      && free_list_pred(ab, seq![2, 3],
        //              ab.perms@[ptr].free_link_perm.unwrap().value().next_free)
        //


        proof fn lemma_contains(self, x: *mut BlockHdr)
            requires self.wf(), self.contains(x)
            ensures self.perms@.contains_key(x)
        {
            let i = self.get_ptr_internal_index(x);
            assert(self.wf_node(i));
        }

        spec fn get_ptr_internal_index(self, x: *mut BlockHdr) -> int
            recommends exists|i: int| self.ptrs@[i] == x && 0 <= i < self.ptrs@.len()
        {
            choose|i: int| self.ptrs@[i] == x && 0 <= i < self.ptrs@.len()
        }

        proof fn lemma_node_is_wf(self, x: *mut BlockHdr)
            requires self.contains(x)
            ensures self.wf_node(self.get_ptr_internal_index(x))
        {}
    }

    impl<const FLLEN: usize, const SLLEN: usize> Tlsf<FLLEN, SLLEN> {
        proof fn freelist_empty(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.all_freelist_wf(),
                self.shadow_freelist@[idx].len() == 0
            ensures
                self.first_free[idx.0 as int][idx.1 as int].is_none()
        {
        }

        proof fn freelist_nonempty(self, idx: BlockIndex<FLLEN, SLLEN>)
            requires
                idx.wf(),
                self.all_freelist_wf(),
                self.all_blocks.wf(),
                self.shadow_freelist@[idx].len() > 0
            ensures
                self.first_free[idx.0 as int][idx.1 as int] matches Some(first_free) &&
                    self.all_blocks.contains(first_free)
        {
            let first = self.shadow_freelist@[idx].first();
            assert(self.free_list_pred(self.shadow_freelist@[idx], self.first_free[idx.0 as int][idx.1 as int]));
            assert(self.shadow_freelist@[idx].len() != 0);
            assert(self.first_free[idx.0 as int][idx.1 as int] matches Some(first) && self.shadow_freelist@[idx].first() == first);
            assert(self.shadow_freelist@[idx].all(|e| self.all_blocks.contains(e)));
            assert(self.shadow_freelist@[idx].contains(self.shadow_freelist@[idx].first()));
            assert(self.all_blocks.contains(self.shadow_freelist@[idx].first()));
        }

        fn link_free_block(&mut self, idx: BlockIndex<FLLEN, SLLEN>, node: *mut BlockHdr, Tracked(perm): Tracked<BlockPerm>)
            requires
                idx.wf(),
                old(self).wf_shadow(),
                old(self).all_blocks.wf(),
                old(self).all_freelist_wf(),
                node == perm.points_to.ptr(),
                perm.wf(),
                perm.free_link_perm is Some,
                old(self).tlsf_free_list_pred(
                    idx,
                    old(self).shadow_freelist@[idx])
            ensures
                self.wf_shadow(),
                self.all_freelist_wf(),
                self.tlsf_free_list_pred(
                    idx,
                    seq![node].add(old(self).shadow_freelist@[idx]))
        {
            let tracked BlockPerm {
                points_to: node_pt,
                free_link_perm: node_fl_pt
            } = perm;
            let tracked node_fl_pt = node_fl_pt.tracked_unwrap();
            if let Some(first_free) = self.first_free[idx.0][idx.1] {
                assert(self.shadow_freelist@[idx].len() != 0);
                assert(self.shadow_freelist@[idx].first() == first_free);
                assert(self.shadow_freelist@[idx].contains(first_free));
                assert(self.freelist_wf(idx));
                assert(self.all_freelist_wf());
                assert(self.all_blocks.wf());
                assert(self.all_blocks.contains(first_free));
                proof {
                    self.all_blocks.lemma_contains(first_free);
                    self.all_blocks.lemma_node_is_wf(first_free);
                }
                assert(self.all_blocks.perms@.contains_key(first_free));
                assert(self.all_blocks.wf());
                let tracked first_free_perm = self.all_blocks.perms.borrow_mut().tracked_remove(first_free);
                assert(first_free_perm.wf()) by {
                    self.all_blocks.lemma_node_is_wf(first_free);
                };
                let tracked first_free_fl_pt = first_free_perm.free_link_perm.tracked_unwrap();

                // update first pointer
                Self::set_freelist(&mut self.first_free, idx, Some(node));
                    assert(old(self).shadow_freelist@[idx] == self.shadow_freelist@[idx]);

                // update link
                let link = get_freelink_ptr(first_free);
                assert(first_free == first_free_perm.points_to.ptr());
                assert(get_freelink_ptr_spec(first_free) == get_freelink_ptr_spec(first_free_perm.points_to.ptr()));
                assert(get_freelink_ptr_spec(first_free) == first_free_fl_pt.ptr());
                let link_payload = ptr_mut_read(link, Tracked(&mut first_free_fl_pt));
                ptr_mut_write(link, Tracked(&mut first_free_fl_pt), FreeLink {
                    next_free: link_payload.next_free,
                    prev_free: Some(node)
                });

                // update new node's link
                let link = get_freelink_ptr(node);
                ptr_mut_write(link, Tracked(&mut node_fl_pt), FreeLink {
                    next_free: Some(first_free),
                    prev_free: None
                });

                proof {
                    self.all_blocks.perms.borrow_mut().tracked_insert(node,
                        BlockPerm {
                            points_to: node_pt,
                            free_link_perm: Some(node_fl_pt)
                        });
                    self.all_blocks.perms.borrow_mut().tracked_insert(first_free,
                        BlockPerm {
                            points_to: first_free_perm.points_to,
                            free_link_perm: Some(first_free_fl_pt)
                        });
                    assert(old(self).shadow_freelist@.contains_key(idx));
                    self.shadow_freelist@ = self.shadow_freelist@.insert(idx, seq![node].add(self.shadow_freelist@[idx]));

                    assert(self.shadow_freelist@[idx] == seq![node].add(old(self).shadow_freelist@[idx]));

                    self.shadow_freelist@.lemma_insert_invariant_contains(
                        old(self).shadow_freelist@[idx],
                        idx,
                        seq![node].add(old(self).shadow_freelist@[idx]));

                    assert(idx.wf() <==> self.shadow_freelist@.contains_key(idx));
                    assert(forall|i: BlockIndex<FLLEN, SLLEN>| i != idx ==> self.shadow_freelist@[i] == old(self).shadow_freelist@[i]);
                    assert(forall|i: BlockIndex<FLLEN, SLLEN>| i != idx ==>
                        self.shadow_freelist@[i] == old(self).shadow_freelist@[i]);
                    assume(self.all_blocks.wf());
                    assert(self.all_freelist_wf()) by {
                        assert forall|i: BlockIndex<FLLEN, SLLEN>| i.wf()
                            implies self.freelist_wf(i) by {
                                if i == idx {
            //&&& self.free_list_pred(self.shadow_freelist[i][j], self.first_free[i][j])
            //&&& forall|k: int| 0 <= k < self.shadow_freelist[i][j].len() ==>
                    //self.all_blocks.contains(self.shadow_freelist[i][j][k])
                                    //assume(self.freelist_wf(idx));
                                    //assert(self.freelist_wf(i));
                                    admit();
                                } else {
                                    assert(i != idx);
                                    assert(old(self).shadow_freelist@[i] =~= self.shadow_freelist@[i]);
                                    assert(old(self).freelist_wf(i));
                                    //assert(self.free_list_pred(self.shadow_freelist@[idx], self.first_free[idx.0 as int][idx.1 as int]));
                                    //assert(old(self).freelist_wf(i))
                                }
                            };
                    };
                }
            } else {
                assert(self.shadow_freelist@[idx].len() == 0);
                Self::set_freelist(&mut self.first_free, idx, Some(node));
                ptr_mut_write(get_freelink_ptr(node), Tracked(&mut node_fl_pt), FreeLink {
                    next_free: None,
                    prev_free: None
                });
                proof {
                    admit()
                }
            }
        }

        spec fn freelist_wf(self, idx: BlockIndex<FLLEN, SLLEN>) -> bool {
            &&& self.free_list_pred(self.shadow_freelist@[idx], self.first_free[idx.0 as int][idx.1 as int])
            &&& forall|k: int| 0 <= k < self.shadow_freelist@[idx].len() ==>
                    self.all_blocks.contains(self.shadow_freelist@[idx][k])
        }

        spec fn all_freelist_wf(self) -> bool {
            forall|idx: BlockIndex<FLLEN, SLLEN>|
                idx.wf() ==> self.freelist_wf(idx)
        }

        spec fn tlsf_free_list_pred(self, idx: BlockIndex<FLLEN, SLLEN>, ls: Seq<*mut BlockHdr>) -> bool {
            self.free_list_pred(ls, self.first_free[idx.0 as int][idx.1 as int])
        }

        spec fn free_list_pred(self, freelist: Seq<*mut BlockHdr>, first: Option<*mut BlockHdr>) -> bool
            recommends self.all_blocks.wf()
        {
            if freelist.len() == 0 {
                first.is_none()
            } else {
                &&& first matches Some(p) && freelist.first() == p
                &&& forall|i: int| 0 <= i < freelist.len() ==> {
                    let node_link_ptr = get_freelink_ptr_spec(freelist[i]);
                    let node_link = #[trigger] self.all_blocks.perms@[freelist[i]].free_link_perm.unwrap().value();
                    &&& self.all_blocks.contains(freelist[i])
                    &&& self.all_blocks.value_at(freelist[i]).is_free()
                    &&& node_link.next_free matches Some(next_ptr)
                            ==> self.all_blocks.phys_next_of(i) == Some(next_ptr)
                    &&& node_link.next_free is None ==> self.all_blocks.phys_next_of(i) is None
                    &&& node_link.prev_free matches Some(prev_ptr)
                            ==> self.all_blocks.phys_prev_of(i) == Some(prev_ptr)
                    &&& node_link.prev_free is None ==> self.all_blocks.phys_prev_of(i) is None
                }
            }
        }

        #[verifier::external_body]
        fn set_freelist(
            freelist: &mut [[Option<*mut BlockHdr>; SLLEN]; FLLEN],
            idx: BlockIndex<FLLEN, SLLEN>, e: Option<*mut BlockHdr>)
            requires idx.wf()
            ensures
                freelist[idx.0 as int][idx.1 as int] == e,
                forall|i: BlockIndex<FLLEN, SLLEN>|
                    i != idx && i.wf() ==>
                        old(freelist)[i.0 as int][i.1 as int]
                            == freelist[i.0 as int][i.1 as int],
        {
            freelist[idx.0][idx.1] = e;
        }

        //#[verifier::type_invariant]
        spec fn wf_shadow(self) -> bool {
            forall|idx: BlockIndex<FLLEN, SLLEN>|
                self.shadow_freelist@.contains_key(idx) <==> idx.wf()
        }
    }

    spec fn get_freelink_ptr_spec(ptr: *mut BlockHdr) -> *mut FreeLink {
        ptr_from_data(PtrData::<FreeLink> {
            provenance: ptr@.provenance,
            addr: (ptr as usize + size_of::<BlockHdr>()) as usize,
            metadata: ()
        }) as *mut _
    }

    fn get_freelink_ptr(ptr: *mut BlockHdr) -> (r: *mut FreeLink)
        ensures r == get_freelink_ptr_spec(ptr)
    {
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
            &&& self.points_to.value().size & MASK_USED == 0
                ==> self.free_link_perm is Some
            &&& self.points_to.is_init()
            &&& self.free_link_perm matches Some(pt) &&
                get_freelink_ptr_spec(self.points_to.ptr()) == pt.ptr()
                    && pt.is_init()
        }
    }


pub assume_specification<T> [core::mem::replace::<T>] (dest: &mut T, src: T) -> (res: T)
    ensures
        *dest == src,
        res == *old(dest)
    opens_invariants none
    no_unwind;
}
