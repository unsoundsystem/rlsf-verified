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

impl HeaderPointer {
    spec fn addr(self) -> usize {
        match self {
            Self::Free(p) => p.addr(),
            Self::Used(p) => p.addr(),
        }
    }
}

pub(crate) enum HeaderPermToken {
    Used(PointsTo<UsedBlockHdr>),
    Free(int, int),
}

pub (crate) enum HeaderPointsTo {
    Used(PointsTo<UsedBlockHdr>),
    Free(PointsTo<FreeBlockHdr>),
}

impl HeaderPointsTo {
    spec fn addr(self) -> usize {
        match self {
            Self::Free(p) => p.ptr().addr(),
            Self::Used(p) => p.ptr().addr(),
        }
    }

    spec fn ptr_eq(self, hdr_ptr: HeaderPointer) -> bool {
        match self {
            Self::Free(p) => hdr_ptr matches HeaderPointer::Free(pt) && pt == p.ptr(),
            Self::Used(p) => hdr_ptr matches HeaderPointer::Used(pt) && pt == p.ptr(),
        }
    }
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
    pub valid_range: Ghost<Set<int>>, // represents region managed by this allocator

    // ordered by address
    pub all_ptrs: Ghost<Seq<HeaderPointer>>,

    // provenance of initially added blocks
    // NOTE: Using Seq for extending to allow multiple `insert_free_block_ptr` call
    pub root_provenances: Ghost<Seq<Provenance>>,
    //TODO: We need a way to obtain permission from block to adjacent
    //      option: HList of *mut FreeBlockHdr/*mut UsedBlockHdr
    //          -> going with this
    // List of all BlockHdrs ordered by their addresses.
    pub all_block_headers: Tracked<Map<HeaderPointer, HeaderPermToken>>,
    // Permission to the region managed by the header
    pub tracked all_block_perms: Tracked<Map<*mut FreeBlockHdr, PointsToRaw>>,
}

impl<const FLLEN: usize, const SLLEN: usize> GhostTlsf<FLLEN, SLLEN> {
    //FIXME: error: external_type_specification: Const params not yet supported
    //#[verifier::type_invariant]
    pub closed spec fn wf(self, tlsf: &Tlsf<FLLEN, SLLEN>) -> bool {
        &&& self.all_ptrs@.no_duplicates()
        // all_ptrs and all_block_headers are kept in sync
        &&& forall|i: int| 0 <= i < self.all_ptrs@.len() ==>
            ({
                &&& self.all_block_headers@.contains_key(self.all_ptrs@[i])
                &&& self.perm_from_pointer(tlsf, self.all_ptrs@[i]) matches Some(p)
                    && p.ptr_eq(self.all_ptrs@[i])
                &&& self.phys_next_of(i) matches Some(hdr_ptr) ==> self.all_ptrs@.contains(hdr_ptr)
                &&& self.phys_prev_of(i) matches Some(hdr_ptr) ==> self.all_ptrs@.contains(hdr_ptr)
            })
        &&& self.root_provenances@.len() > 0
        // Free block header has corresponding permssion for the region
        &&& forall |i: int, j: int, k: int| BlockIndex::<FLLEN, SLLEN>::valid_block_index((i, j))
                && 0 <= k < tlsf.first_free[i][j].ptrs@.len() ==>
                ({
                    let fbh_ptr = tlsf.first_free[i][j].ptrs@[k];
                    let fbh_size = tlsf.first_free[i][j].perms@[fbh_ptr].value().common.size & SIZE_SIZE_MASK;
                    &&& self.all_block_perms@.contains_key(fbh_ptr)
                    //NOTE: hdr.size indicating free block size *includeing* the header size
                    &&& self.all_block_perms@[fbh_ptr].is_range(
                        fbh_ptr as usize as int + size_of::<FreeBlockHdr>(),
                        fbh_ptr as usize as int + fbh_size)
                })
        // Elements alternating Free/Used i.e. no adjecent free blocks
        &&& forall|i: int| 0 <= i < self.all_ptrs@.len() - 1 ==>
        ({
            &&& (self.all_ptrs@[i] is Free ==> !(self.all_ptrs@[i + 1] is Free))
            &&& (self.all_ptrs@[i] is Used ==> !(self.all_ptrs@[i + 1] is Used))
        })
    }


    pub closed spec fn perm_from_pointer(self, tlsf: &Tlsf<FLLEN, SLLEN>, ptr: HeaderPointer) -> Option<HeaderPointsTo>
        recommends self.wf(&tlsf)
    {
        if self.all_ptrs@.contains(ptr) {
            match self.all_block_headers@[ptr] {
                HeaderPermToken::Used(pt) => Some(HeaderPointsTo::Used(pt)),
                HeaderPermToken::Free(fl, sl) => {
                    if BlockIndex::<FLLEN, SLLEN>::valid_block_index((fl, sl)) {
                        let i = choose|i: int| self.all_ptrs@[i] == ptr;
                        if let HeaderPointer::Free(ptr) = ptr {
                            //self.all_ptrs = self.all_ptrs.remove(i);
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
        if i + 1 == self.all_ptrs@.len() {
            None
        } else {
            Some(self.all_ptrs@[i + 1])
        }
    }
    pub closed spec fn phys_prev_of(self, i: int) -> Option<HeaderPointer> {
        if i - 1 == 0 {
            None
        } else {
            Some(self.all_ptrs@[i - 1])
        }
    }

    // Get permission for the memory region managed by header `ptr`
    pub proof fn remove_block_perm(tracked &mut self, ptr: *mut FreeBlockHdr) -> (tracked r: PointsToRaw) {
        self.all_block_perms.borrow_mut().tracked_remove(ptr)
    }

    //Get permission for the header
    pub proof fn remove_block_used_header_perm(tracked &mut self, ptr: *mut UsedBlockHdr)
        -> (tracked r: Option<PointsTo<UsedBlockHdr>>)
        //requires self.all_block_headers@.contains_key(HeaderPointer::Used(ptr)),
        //ensures !self.all_block_headers@.contains_key(HeaderPointer::Used(ptr)),
    {
        match self.all_block_headers.borrow_mut().tracked_remove(HeaderPointer::Used(ptr)) {
            HeaderPermToken::Used(perm) => Some(perm),
            _ => None
        }
    }
}

}
