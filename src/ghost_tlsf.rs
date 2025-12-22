use vstd::prelude::*;
use vstd::raw_ptr::{ptr_mut_write, ptr_ref2, ptr_ref, PointsToRaw, PointsTo, Metadata, Provenance};
use crate::{Tlsf, SIZE_SIZE_MASK, SIZE_SENTINEL};
use crate::block::*;
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
        &&& self.wf_all_blocks()
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

    /// Ensures `Block` abstraction is kept in sync with the actual memory state for index `i`.
    pub closed spec fn wf_block(self, i: int) -> bool
        recommends 0 <= i < self.all_blocks@.len()
    {
        let blk = self.all_blocks@[i];
        // The actual memory invariant (PointsTo) for the block is accessible using Block.
        &&& blk matches Block::Used(ptr)
                ==> self.used_info.perms@.contains_key(ptr)
        &&& blk matches Block::Free(ptr, i, j)
                ==> BlockIndex::<FLLEN, SLLEN>::valid_block_index((i, j))
                        && self.first_free[i][j].perms@.contains_key(ptr)
        // next_phys_block/prev_phys_block invariants
        // if BlockHdr is a sentinel then there is no block next to it
        &&& self.is_sentinel(blk)
                ==> self.phys_next_of(self.all_blocks@.index_of(blk)) is None
        // if BlockHdr has no link to previous block, corresponding blk is the head
        &&& self.block_common(blk).prev_phys_block is None ==> self.all_blocks@.first() == blk
        // prev_phys_block points to next node
        &&& self.block_common(blk).prev_phys_block matches Some(prev_ptr) ==> 
                self.phys_prev_of(i) matches Some(b) && prev_ptr == b.to_ptr()
        // header address = previous header address + block size
        &&& self.phys_prev_of(i) matches Some(prev_block) ==>
                blk.to_ptr() as int  == prev_block.to_ptr() as int + self.block_common(prev_block).size
        &&& self.phys_next_of(i) matches Some(next_block) ==>
                next_block.to_ptr() as int  == blk.to_ptr() as int + self.block_common(blk).size
    }


    /// all elements of all_blocks has a corresponding element in first_free/used_info
    pub closed spec fn wf_all_blocks(self) -> bool {
        &&& forall|i: int| 0 <= i < self.all_blocks@.len() ==> self.wf_block(i)

        // NOTE: We can proof that all pointers in all_blocks are distinct provided that
        //       1. all_blocks[i] has corresponding permission for the header in first_free / used_info
        //       2. FreeBlockHdr and UsedBlockHdr is non-zero-sized
        //       3. PointsTo::is_disjoint ensures all pointers are distinct
        // TODO: self.all_blocks.map_values(|b: Block| b.to_ptr()).no_duplicates()
    }

    /// Block is sentinel
    pub closed spec fn is_sentinel(self, blk: Block) -> bool {
        self.block_common(blk).size & SIZE_SENTINEL != 0
    }

    /// Extract common part of the header
    pub closed spec fn block_common(self, blk: Block) -> BlockHdr {
        match blk {
            Block::Used(ptr) =>
                self.used_info.perms@[ptr].value().common,
            Block::Free(ptr, i, j) =>
                self.first_free[i][j].perms@[ptr].value().common
        }
    }

    pub proof fn get_used_block_perm(self, blk: Block) -> PointsTo<UsedBlockHdr>
        requires blk is Used
    {
        if let Block::Used(ptr) = blk {
            self.used_info.perms@[ptr]
        } else { arbitrary() }
    }

    pub proof fn get_free_block_perm(self, blk: Block) -> PointsTo<FreeBlockHdr>
        requires blk is Free
    {
        if let Block::Free(ptr, i, j) = blk {
            self.first_free[i][j].perms@[ptr]
        } else { arbitrary() }
    }

    pub closed spec fn contains_block_pointer(self, ptr: *mut BlockHdr) -> bool {
        exists|b: Block| self.all_blocks@.contains(b) && b.to_ptr() == ptr
    }

    pub closed spec fn is_sentinel_pointer(self, ptr: *mut BlockHdr) -> bool
        recommends self.contains_block_pointer(ptr)
    {
        self.is_sentinel(self.choice_block_from_ptr(ptr))
    }

    pub closed spec fn choice_block_from_ptr(self, ptr: *mut BlockHdr) -> Block
        recommends self.contains_block_pointer(ptr)
    {
        choose|b: Block| self.all_blocks@.contains(b) && b.to_ptr() == ptr
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
        &&& forall|p: *mut UsedBlockHdr|
                self.ptrs@.contains(p) ==> self.perms@[p].ptr() == p
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
    pub closed spec fn to_ptr(self) -> *mut BlockHdr {
        match self {
            Block::Used(ptr) => ptr as *mut BlockHdr,
            Block::Free(ptr, _, _) => ptr as *mut BlockHdr,
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


pub enum BlockPerm {
    Used { block: Block, perm: Tracked<PointsTo<UsedBlockHdr>> },
    Free { block: Block, perm: Tracked<PointsTo<FreeBlockHdr>> }
}

impl BlockPerm {
    pub open spec fn wf(self) -> bool {
        match self {
            Self::Used { block, perm } => block is Used && perm@.ptr() as *mut BlockHdr == block.to_ptr(),
            Self::Free { block, perm } => block is Free && perm@.ptr() as *mut BlockHdr == block.to_ptr(),
        }
    }

    pub closed spec fn bhdr_ptr(self) -> *mut BlockHdr {
        match self {
            BlockPerm::Used { perm, .. } => perm@.ptr() as *mut BlockHdr,
            BlockPerm::Free { perm, .. } => perm@.ptr() as *mut BlockHdr
        }
    }
}

}

