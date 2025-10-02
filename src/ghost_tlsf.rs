use vstd::prelude::*;
use vstd::raw_ptr::{ptr_mut_write, ptr_ref2, ptr_ref, PointsToRaw, PointsTo, Metadata, Provenance};
use crate::{FreeBlockHdr, UsedBlockHdr, Tlsf, SIZE_SIZE_MASK, SIZE_SENTINEL, BlockHdr};
use crate::block_index::BlockIndex;
use vstd::set_lib::set_int_range;
use core::hint::unreachable_unchecked;
use vstd::relations::sorted_by;

verus! {

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    //FIXME: error: external_type_specification: Const params not yet supported
    /// Invariant for the structure tracks global header information
    /// 
    /// We must ensure following holds for all operations allocator provides
    /// * block invariants
    ///   1. blocks precisely covers whole memory pool
    ///   2. no successive free blocks
    ///   3. blocks must not be overwrapped
    /// * To ensure the invariant hold for every block, 
    ///   we must track all the pointers of registered blocks
    /// * all blocks constitues a singly-linked list
    pub closed spec fn wf_ghost(self) -> bool {
        // all elements of all_blocks has a corresponding element in first_free/used_info
        &&& self.all_blocks@.all(|blk: Block| self.wf_block(blk))
        // elements of all_blocks are ordered by their address
        &&& forall|i: int, j: int| i < j
                ==> (self.all_blocks@[i].to_ptr() as int) < (self.all_blocks@[j].to_ptr() as int)
        // at least one provenance exist for memory pool
        &&& self.root_provenances@ is Some
        // No adjecent free blocks
        &&& forall|i: int|
                0 <= i < self.all_blocks@.len() - 1
                    ==> #[trigger] self.all_blocks@[i] is Free
                        ==> self.all_blocks@[i + 1] is Used
        // TODO: must be connected by prev_phys_block
    }

    pub closed spec fn phys_next_of(self, i: int) -> Option<Block>
    {
        if i + 1 == self.all_blocks@.len() {
            None
        } else {
            Some(self.all_blocks@[i + 1])
        }
    }
    pub closed spec fn phys_prev_of(self, i: int) -> Option<Block> {
        if i - 1 == 0 {
            None
        } else {
            Some(self.all_blocks@[i - 1])
        }
    }

    pub closed spec fn wf_block(self, blk: Block) -> bool {
        &&& self.all_blocks@.contains(blk)
        &&& blk matches Block::Used(ptr)
                ==> self.used_info.perms@.contains_key(ptr)
        &&& blk matches Block::Free(ptr, i, j)
                ==> BlockIndex::<FLLEN, SLLEN>::valid_block_index((i, j))
                        && self.first_free[i][j].perms@.contains_key(ptr)
        // next_phys_block/prev_phys_block invariants
        // if blk isn't a sentinel then there is block next to it
        &&& self.phys_next_of(self.all_blocks.index_of(blk)) is None
                ==> self.is_sentinel(blk)
        // if blk isn't first one in the pool, prev_phys_block is Some
        &&& self.block_common(blk).prev_phys_block is Some == blk ==> self.all_blocks.first()
    }

    pub closed spec fn is_sentinel(self, blk: Block) -> bool {
        self.block_common().size & SIZE_SENTINEL == 0
    }

    pub closed spec fn block_common(self, blk: block) -> BlockHdr {
        match blk {
            Used(ptr) =>
                self.used_info.perms@[ptr].common
            Free(ptr, i, j) =>
                self.first_free[i][j].perms@[ptr].common
        }
    }
}

pub(crate) struct UsedInfo {
    pub ptrs: Ghost<Seq<*mut UsedBlockHdr>>,
    pub perms: Tracked<Map<*mut UsedBlockHdr, PointsTo<UsedBlockHdr>>>,
}

impl UsedInfo {
    pub closed spec fn wf(self) -> bool {
        &&& sorted_by(self.ptrs@, pointer_le::<UsedBlockHdr>())
        &&& forall|ptr: *mut UsedBlockHdr|
                self.perms@.contains_key(ptr) <==> self.ptrs@.contains(ptr)
        &&& self.ptrs@.no_duplicates()
    }

    pub closed spec fn contains_block(self, ptr: *mut UsedBlockHdr) -> bool
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

spec fn pointer_le<T>() -> spec_fn(*mut T, *mut T) -> bool {
    |x: *mut T, y: *mut T| {
        let xi = x as usize as int;
        let yi = y as usize as int;
        xi < yi
    }
}

pub enum Block {
    Used(*mut UsedBlockHdr),
    Free(*mut FreeBlockHdr, int, int)
}

impl Block {
    spec fn to_ptr(self) -> *mut u8 {
        match self {
            Block::Used(ptr) => ptr as *mut u8,
            Block::Free(ptr, _, _) => ptr as *mut u8,
        }
    }
    // FIXME: should be macro
    //proof fn get_prev_phys_block<const FLLEN: usize, const SLLEN: usize>(self, tlsf: Tlsf<FLLEN, SLLEN>) -> Option<*mut BlockHdr>
        //requires
            //self matches Self::Used(uhdr) ==> tlsf.used_info.perms.contains_key(uhdr),
            //self matches Self::Free(fhdr, i, j) ==> tlsf.first_free[i][j].wf_node_ptr(fhdr)
    //{
        //match self {
            //Self::Used(uhdr) =>
                //tlsf.used_info.perms.tracked_borrow(uhdr).value().common.prev_phys_block,
            //Self::Free(fhdr, i, j) =>
                //tlsf.first_free[i][j].perms@.tracked_borrow(fhdr).value().common.prev_phys_block
        //}
    //}
}

}

