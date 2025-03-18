use vstd::prelude::*;
use vstd::raw_ptr::{ptr_mut_write, ptr_ref2, ptr_ref, PointsToRaw, PointsTo, Metadata, Provenance};
use crate::{FreeBlockHdr, UsedBlockHdr, Tlsf, SIZE_SIZE_MASK};
use crate::block_index::BlockIndex;
use vstd::set_lib::set_int_range;

verus! {

pub(crate) enum HeaderPointer {
    Used(*mut UsedBlockHdr),
    Free(*mut FreeBlockHdr),
}

pub(crate) enum HeaderPermToken {
    Used(PointsTo<UsedBlockHdr>),
    Free(int, int),
}

pub (crate) enum HeaderPointsTo {
    Used(PointsTo<UsedBlockHdr>),
    Free(PointsTo<FreeBlockHdr>),
}


/// A proof constract tracking information about Tlsf struct
///
/// Things we have to track
/// * all `PointsTo`s related to registered blocks
/// * things needed to track the list views 
///     * singly linked list by prev_phys_block chain 
///      NOTE: This contains allocated blocks
///     * doubly linked list by FreeBlockHdr fields
pub(crate) struct GhostTlsf<const FLLEN: usize, const SLLEN: usize> {
    pub ghost valid_range: Set<int>, // represents region managed by this allocator

    // ordered by address
    pub ghost all_ptrs: Seq<HeaderPointer>,

    // provenance of initially added blocks
    // NOTE: Using Seq for extending to allow multiple `insert_free_block_ptr` call
    pub ghost root_provenances: Seq<Provenance>,
    //TODO: We need a way to obtain permission from block to adjacent
    //      option: HList of *mut FreeBlockHdr/*mut UsedBlockHdr
    //          -> going with this
    // List of all BlockHdrs ordered by their addresses.
    pub tracked all_block_headers: Map<HeaderPointer, HeaderPermToken>,
    // Permission to the region managed by the header
    // TODO: add all_block_perms[ptr].is_range(ptr, ptr + ((*ptr).size & SIZE_SIZE_MASK))
    pub tracked all_block_perms: Map<*mut FreeBlockHdr, PointsToRaw>,
}

impl<const FLLEN: usize, const SLLEN: usize> GhostTlsf<FLLEN, SLLEN> {
    //FIXME: error: external_type_specification: Const params not yet supported
    //#[verifier::type_invariant]
    pub closed spec fn wf(self, tlsf: &Tlsf<FLLEN, SLLEN>) -> bool {
        &&& self.all_ptrs.no_duplicates()
        &&& forall|i: int| 0 <= i < self.all_ptrs.len() ==> self.all_block_headers.contains_key(self.all_ptrs[i])
        &&& forall|i: int| 0 <= i < self.all_ptrs.len() ==>
                (self.perm_from_pointer(tlsf, self.all_ptrs[i]) matches Some(p) &&
                    ({
                        &&& p matches HeaderPointsTo::Free(pt1) ==>
                            self.all_ptrs[i] matches HeaderPointer::Free(pt2) && pt1.ptr() == pt2
                        &&& p matches HeaderPointsTo::Used(pt1) ==>
                            self.all_ptrs[i] matches HeaderPointer::Used(pt2) && pt1.ptr() == pt2
                    }))
        &&& self.root_provenances.len() > 0
        &&& forall |i: int, j: int, k: int| BlockIndex::<FLLEN, SLLEN>::valid_block_index((i, j))
                && 0 <= k < tlsf.first_free[i][j].ptrs@.len() ==>
                ({
                    let fbh_ptr = tlsf.first_free[i][j].ptrs@[k];
                    let fbh_size = tlsf.first_free[i][j].perms@[fbh_ptr].value().common.size & SIZE_SIZE_MASK;
                    &&& self.all_block_perms.contains_key(fbh_ptr)
                    &&& self.all_block_perms[fbh_ptr].is_range(fbh_ptr as usize as int, fbh_ptr as usize as int + fbh_size)
                })
    }

    pub closed spec fn tlsf_ghost_free_list_wf(self) -> bool {
        // TODO: elements alternating Free/Used i.e. no adjecent free blocks
        //TODO: phys_next_of(i).is_some() <==> hdr.next_phys_block() == hdr.addr() + hdr.size
        true
    }

    pub open spec fn perm_from_pointer(self, tlsf: &Tlsf<FLLEN, SLLEN>, ptr: HeaderPointer) -> Option<HeaderPointsTo>
        requires self.wf(&tlsf)
    {
        if self.all_ptrs.contains(ptr) {
            match self.all_block_headers[ptr] {
                HeaderPermToken::Used(pt) => Some(HeaderPointsTo::Used(pt)),
                HeaderPermToken::Free(fl, sl) => {
                    if BlockIndex::<FLLEN, SLLEN>::valid_block_index((fl, sl)) {
                        let i = choose|i: int| self.all_ptrs[i] == ptr;
                        if let HeaderPointer::Free(ptr) = ptr {
                            self.all_ptrs = self.all_ptrs.remove(i);
                            Some(HeaderPointsTo::Free(tlsf.first_free[fl][sl].perms@[ptr]))
                        } else {
                            None // unreachable provided wf(self, tlsf)
                        }
                    } else {
                        None // unreachable provided wf(self, tlsf)
                    }
                }
            }
        } else {
            None // unreachable provided wf(self, tlsf)
        }
    }

    pub closed spec fn phys_next_of(self, i: int) -> Option<HeaderPointer>
    {
        if i + 1 == self.all_ptrs.len() {
            None
        } else {
            Some(self.all_ptrs[i + 1])
        }
    }
    pub closed spec fn phys_prev_of(self, i: int) -> Option<HeaderPointer> {
        if i - 1 == 0 {
            None
        } else {
            Some(self.all_ptrs[i - 1])
        }
    }
}

}
