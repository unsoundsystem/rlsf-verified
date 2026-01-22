use crate::block::*;
use crate::block_index::BlockIndex;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd::raw_ptr::*;
#[cfg(verus_keep_ghost)]
use vstd::relations::injective;

verus! {

    /// Tracks global structure of the header linkage and memory states
    pub(crate) struct AllBlocks<const FLLEN: usize, const SLLEN: usize> {
        /// Pointers for all blocks, ordered by address.
        pub ptrs: Ghost<Seq<*mut BlockHdr>>,
        /// Tracked permissions for all blocks, indexed by pointer.
        pub perms: Tracked<Map<*mut BlockHdr, BlockPerm>>,
    }

    impl<const FLLEN: usize, const SLLEN: usize> AllBlocks<FLLEN, SLLEN> {
        pub(crate) closed spec fn value_at(self, ptr: *mut BlockHdr) -> BlockHdr
            recommends
            self.contains(ptr),
            self.perms@[ptr].points_to.is_init()
        {
            self.perms@[ptr].points_to.value()
        }

        pub(crate) closed spec fn contains(self, ptr: *mut BlockHdr) -> bool {
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
        pub(crate) closed spec fn wf_node(self, i: int) -> bool
            recommends 0 <= i < self.ptrs@.len()
        {
            let ptr = self.ptrs@[i];
            // --- Well-formedness for tracked/ghost states
            &&& ptr@.addr != 0
            &&& self.perms@.contains_key(ptr)
                &&& ptr == self.perms@[ptr].points_to.ptr()
                &&& self.perms@[ptr].wf()

                // --- Glue invariants between physical state & tracked/ghost state
                // prev_phys_block invariant
                &&& {
                    ||| self.value_at(ptr).prev_phys_block@.addr != 0 && self.phys_prev_of(i) is None
                    ||| self.value_at(ptr).prev_phys_block == self.phys_prev_of(i).unwrap()
                }
            // if sentinel flag is present then ...
            &&& if self.value_at(ptr).is_sentinel() {
                // it's last element in ptrs
                &&& i == self.ptrs@.len() - 1
                // sentinel block has size of 0
                &&& self.value_at(ptr).size == 0
            } else {
                // there no zero-sized block except sentinel block
                &&& BlockIndex::<FLLEN, SLLEN>::valid_block_size(self.value_at(ptr).size as int)
                &&& (self.value_at(ptr).size as int) + (ptr as int) < usize::MAX
            }
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

        pub(crate) closed spec fn phys_next_of(self, i: int) -> Option<*mut BlockHdr> {
            if self.ptrs@.len() - 1 == i {
                None
            } else {
                Some(self.ptrs@[i + 1])
            }
        }

        pub(crate) proof fn lemma_wf_nodup(self)
            requires self.wf()
            ensures self.ptrs@.no_duplicates()
        {
            assert forall|i: int| 0 <= i < self.ptrs@.len() - 1
                implies (#[trigger] self.ptrs@[i] as int) < self.ptrs@[i + 1] as int
                by {
                    assert(self.wf_node(i));
                }
        }

        pub(crate) closed spec fn phys_prev_of(self, i: int) -> Option<*mut BlockHdr> {
            if i == 0 {
                None
            } else {
                Some(self.ptrs@[i - 1])
            }
        }

        pub(crate) closed spec fn is_sentinel_pointer(self, ptr: *mut BlockHdr) -> bool
            recommends self.wf(), self.contains(ptr)
        {
            self.value_at(ptr).is_sentinel()
        }

        /// Well-formedness for the global list structure.
        pub(crate) closed spec fn wf(self) -> bool {
            // Each block at ptrs[i] is well-formed.
            &&& forall|i: int| 0 <= i < self.ptrs@.len() ==> self.wf_node(i)
            &&& ghost_pointer_ordered(self.ptrs@)
        }


        // free_list_pred(ab, seq![1, 2, 3], ptr)
        // <==> ab.value_at(ptr) == 1
        //      && free_list_pred(ab, seq![2, 3],
        //              ab.perms@[ptr].free_link_perm.unwrap().value().next_free)
        //


        pub(crate) proof fn lemma_contains(self, x: *mut BlockHdr)
            requires self.wf(), self.contains(x)
            ensures self.perms@.contains_key(x)
        {
            let i = self.get_ptr_internal_index(x);
            assert(self.wf_node(i));
        }

        pub(crate) closed spec fn get_ptr_internal_index(self, x: *mut BlockHdr) -> int
            recommends exists|i: int| self.ptrs@[i] == x && 0 <= i < self.ptrs@.len()
        {
            choose|i: int| self.ptrs@[i] == x && 0 <= i < self.ptrs@.len()
        }

        pub(crate) proof fn lemma_node_is_wf(self, x: *mut BlockHdr)
            requires self.contains(x)
            ensures self.wf_node(self.get_ptr_internal_index(x))
        {}


        pub const fn empty() -> Self {
            Self {
                ptrs: Ghost(Seq::empty()),
                perms: Tracked(Map::tracked_empty()),
            }
        }

    }

    #[cfg(verus_keep_ghost)]
    pub(crate) type Pi<const FLLEN: usize, const SLLEN: usize> = spec_fn((BlockIndex<FLLEN, SLLEN>, int)) -> int;
    pub(crate) type ShadowFreelist<const FLLEN: usize, const SLLEN: usize>
        = Map<BlockIndex<FLLEN, SLLEN>, Seq<*mut BlockHdr>>;

    pub(crate) proof fn lemma_ghost_pointer_first_is_least(ls: Seq<*mut BlockHdr>)
        requires ghost_pointer_ordered(ls), ls.len() > 0
        ensures ls.all(|e: *mut BlockHdr| (ls.first() as usize as int) <= e as usize as int)
    {
    }

    pub(crate) proof fn lemma_ghost_pointer_add_least(ls: Seq<*mut BlockHdr>, p: *mut BlockHdr)
        requires ghost_pointer_ordered(ls),
            (p as usize as int) <= ls.first() as usize as int
        ensures ghost_pointer_ordered(seq![p].add(ls)),
    {
        if ls.len() > 0 {
            lemma_ghost_pointer_first_is_least(ls);
        }
    }

    pub(crate) open spec fn add_ghost_pointer(ls: Seq<*mut BlockHdr>, p: *mut BlockHdr) -> Seq<*mut BlockHdr>
        recommends ghost_pointer_ordered(ls)
        decreases ls.len()
    {
        if ls.len() == 0 {
            seq![p]
        } else {
            if (p as usize as int) <= ls.first() as usize as int {
                seq![p].add(ls)
            } else {
                seq![ls.first()].add(add_ghost_pointer(ls.drop_first(), p))
            }
        }
    }


    pub(crate) proof fn lemma_add_ghost_pointer_ensures(ls: Seq<*mut BlockHdr>, p: *mut BlockHdr)
        requires ghost_pointer_ordered(ls)
        ensures
            ghost_pointer_ordered(add_ghost_pointer(ls, p)),
            add_ghost_pointer(ls, p).contains(p),
            forall|e: *mut BlockHdr| ls.contains(e) ==> add_ghost_pointer(ls, p).contains(e),
        decreases ls.len()
    {
        if ls.len() > 0 {
            lemma_add_ghost_pointer_ensures(ls.drop_first(), p);
            assert(ls.drop_first().len() < ls.len());
            assert(ghost_pointer_ordered(add_ghost_pointer(ls.drop_first(), p)));
            if (p as usize as int) <= ls.first() as usize as int {
                assert(ghost_pointer_ordered(seq![p, ls.first()].add(ls.drop_first())));
                assert(add_ghost_pointer(ls, p) == seq![p, ls.first()].add(ls.drop_first()));
                assert(seq![p, ls.first()].add(ls.drop_first())[0] == p);
                assert forall|e: *mut BlockHdr| ls.contains(e)
                    implies add_ghost_pointer(ls, p).contains(e)
                by {
                    let i = choose|i: int| ls[i] == e;
                    assert(seq![p, ls.first()].add(ls.drop_first()) == seq![p].add(ls));
                    lemma_list_add_contains(ls, seq![p], e);
                }
            } else {
                assert((p as usize as int) > ls.first() as usize as int);
                assert(add_ghost_pointer(ls.drop_first(), p).contains(p));
                assert(add_ghost_pointer(ls, p) == seq![ls.first()].add(add_ghost_pointer(ls.drop_first(), p)));
                lemma_list_add_contains(add_ghost_pointer(ls.drop_first(), p), seq![ls.first()], p);
                lemma_ghost_pointer_add_least(add_ghost_pointer(ls.drop_first(), p), ls.first());


                assert(forall|e: *mut BlockHdr| ls.drop_first().contains(e)
                    ==> add_ghost_pointer(ls.drop_first(), p).contains(e));
                assert forall|e: *mut BlockHdr| ls.contains(e)
                    implies add_ghost_pointer(ls, p).contains(e)
                by {
                    let i = choose|i: int| 0 <= i < ls.len() && ls[i] == e;
                    if i > 0 {
                        lemma_drop_first_elements(ls);
                        lemma_list_add_contains(add_ghost_pointer(ls.drop_first(), p),
                            seq![ls.first()], e);
                    }
                }
            }
        } else {
            assert(add_ghost_pointer(ls, p)[0] == p);
        }
    }


    pub(crate) proof fn lemma_drop_first_elements<T>(x: Seq<T>)
        requires x.len() > 0
        ensures forall|i: int| 0 < i < x.len() ==> x.drop_first().contains(x[i])
    {
        assert forall|i: int| 0 < i < x.len()
            implies x.drop_first().contains(x[i]) by {
                if x.len() == 1 {
                    assert(false);
                } else {
                    assert(x.drop_first()[i - 1] == x[i]);
                }
            }
    }

    pub(crate) proof fn lemma_list_add_contains<T>(x: Seq<T>, y: Seq<T>, e: T)
        requires x.contains(e)
        ensures  y.add(x).contains(e)
    {
        assert(forall|i: int| 0 <= i < x.len() ==>
            y.add(x)[i + y.len()] == x[i]);
    }


    pub(crate) closed spec fn is_identity_injection<const FLLEN: usize, const SLLEN: usize>(
        shadow_freelist: ShadowFreelist<FLLEN, SLLEN>,
        all_block_ptrs: Seq<*mut BlockHdr>,
        pi: Pi<FLLEN, SLLEN>) -> bool
        recommends
            all_block_ptrs.no_duplicates(),
            shadow_freelist_has_all_wf_index(shadow_freelist)
    {
        &&& injective(pi)
        &&& forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
            idx.wf() && 0 <= m < shadow_freelist[idx].len() ==> {
                &&& 0 <= pi((idx, m)) < all_block_ptrs.len()
                &&& shadow_freelist[idx][m] == all_block_ptrs[pi((idx, m))]
            }
    }

    pub(crate) closed spec fn shadow_freelist_has_all_wf_index<const FLLEN: usize, const SLLEN: usize>(sfl: ShadowFreelist<FLLEN, SLLEN>) -> bool {
        forall|idx: BlockIndex<FLLEN, SLLEN>|
            sfl.contains_key(idx) <==> idx.wf()
    }

}
