use vstd::prelude::*;
use vstd::raw_ptr::{ptr_mut_write, ptr_ref2, ptr_ref, PointsToRaw, PointsTo, Metadata, Provenance};
use crate::{FreeBlockHdr, UsedBlockHdr, Tlsf, SIZE_SIZE_MASK, BlockHdr};
use crate::block_index::BlockIndex;
use vstd::set_lib::set_int_range;
use core::hint::unreachable_unchecked;

verus! {

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    //FIXME: error: external_type_specification: Const params not yet supported
    /// Invariant for the structure tracks global header information
    /// 
    /// We must ensure following holds for all operations allocator provides
    /// * block invariants
    ///   1. blocks precisely covers whole memory pool
    ///   2. no consecuitive free/used blocks
    ///   3. blocks must not be overwrapped
    /// * To ensure the invariant hold for every block, 
    ///   we must track all the pointers of registered blocks in GhostTlsf.
    /// * all blocks constitues a singly-linked list
    pub closed spec fn wf_ghost(self) -> bool {
        // all elements of all_ptrs has a corresponding element in first_free/block_used 
        //&&& forall|i: int| exists|j: int|
            //self.all_ptrs[i] as *mut UsedBlockHdr == 
        &&& forall|i: int, j: int| i < j ==> (self.all_ptrs@[i] as int) < (self.all_ptrs@[j] as int)
        // all_ptrs and all_block_headers are kept in sync
        &&& forall|i: int| 0 <= i < self.all_ptrs@.len() ==>
            ({
                //&&& self.all_block_headers@.contains_key(self.all_ptrs@[i])
                &&& self.phys_next_of(i) matches Some(hdr_ptr) ==> self.all_ptrs@.contains(hdr_ptr)
                &&& self.phys_prev_of(i) matches Some(hdr_ptr) ==> self.all_ptrs@.contains(hdr_ptr)
            })
        &&& self.root_provenances@.len() > 0
        // Free block header has corresponding permssion for the region
        &&& forall |i: int, j: int, k: int| BlockIndex::<FLLEN, SLLEN>::valid_block_index((i, j))
                && 0 <= k < self.first_free[i][j].ptrs@.len() ==>
                ({
                    let fbh_ptr = self.first_free[i][j].ptrs@[k];
                    let fbh_size = self.first_free[i][j].perms@[fbh_ptr].value().common.size & SIZE_SIZE_MASK;
                    true
                    //&&& self.all_block_perms@.contains_key(fbh_ptr)
                    //NOTE: hdr.size indicating free block size *includeing* the header size
                    //&&& self.all_block_perms@[fbh_ptr].is_range(
                        //fbh_ptr as usize as int + size_of::<FreeBlockHdr>(),
                        //fbh_ptr as usize as int + fbh_size)
                })
        // Elements alternating Free/Used i.e. no adjecent free blocks
        // FIXME
        //&&& forall|i: int| 0 <= i < self.all_ptrs@.len() - 1 ==>
        //({
            //&&& (self.all_ptrs@[i] is Free ==> !(self.all_ptrs@[i + 1] is Free))
            //&&& (self.all_ptrs@[i] is Used ==> !(self.all_ptrs@[i + 1] is Used))
        //})
    }

    pub closed spec fn phys_next_of(self, i: int) -> Option<*mut BlockHdr>
    {
        if i + 1 == self.all_ptrs@.len() {
            None
        } else {
            Some(self.all_ptrs@[i + 1])
        }
    }
    pub closed spec fn phys_prev_of(self, i: int) -> Option<*mut BlockHdr> {
        if i - 1 == 0 {
            None
        } else {
            Some(self.all_ptrs@[i - 1])
        }
    }

    pub closed spec fn contains_block(self, blk: *mut BlockHdr) -> bool {
        exists|i: int| self.all_ptrs@[i] == blk
    }
}

pub(crate) struct UsedInfo {
    pub ptrs: Ghost<Seq<*mut UsedBlockHdr>>,
    pub perms: Tracked<Map<*mut UsedBlockHdr, PointsTo<UsedBlockHdr>>>,
}

impl UsedInfo {
    pub fn wf(self) -> bool {
        false
    }

    pub closed spec fn contains_block(self, ptr: *mut UsedBlockHdr) -> bool {
        false
    }
}

}
