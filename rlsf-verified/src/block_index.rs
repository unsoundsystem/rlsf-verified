use vstd::prelude::*;
use crate::bits::usize_trailing_zeros;
use vstd::set_lib::set_int_range;
use vstd::{seq::*, seq_lib::*, bytes::*};
use vstd::arithmetic::{logarithm::log, power2::pow2};


verus! {

pub struct BlockIndex<const GRANULARITY: usize, const FLLEN: usize, const SLLEN: usize>(pub usize, pub usize);

impl<const GRANULARITY: usize, const FLLEN: usize, const SLLEN: usize> BlockIndex<GRANULARITY, FLLEN, SLLEN> {

    spec fn view(&self) -> (int, int) {
        (self.0 as int, self.1 as int)
    }

    //TODO: DRY
    spec fn granularity_log2_spec() -> int {
        usize_trailing_zeros(GRANULARITY)
    }

    spec fn valid_int_tuple(idx: (int, int)) -> bool {
        let (fl, sl) = idx;
        &&& 0 <= fl < FLLEN as int
        &&& 0 <= sl < SLLEN as int
    }

    spec fn from_int(idx: (int, int)) -> Self
    {
        BlockIndex(idx.0 as usize, idx.1 as usize)
    }

    /// Block index validity according to given parameters (GRANULARITY/FLLEN/SLLEN)
    spec fn wf(&self) -> bool {
        Self::valid_int_tuple(self@)
    }

    // Further properties about index calculation
    // - formalized on usize for interoperability with implementation
    // FIXME(if i wrong): is there any special reason for using `int` there?

    /// Calculate size range as set of usize for given block index.
    spec fn block_size_range(&self) -> Set<int> {
        let BlockIndex(fl, sl) = self;
        let fl_block_bytes = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
        // NOTE: This can be 0, when fl=0 && Self::granularity_log2_spec() < SLLEN
        let sl_block_bytes = fl_block_bytes / pow2(SLLEN as nat) as int;
        if sl_block_bytes == 0 {
            set![GRANULARITY as int]
        } else {
            set_int_range(fl_block_bytes + sl_block_bytes * sl as int, fl_block_bytes + sl_block_bytes * (sl + 1) as int)
        }
    }

    // TODO: Proof any block size in range fall into exactly one freelist index (fl, sl)
    /// Correspoinding size ranges for distict indices are not overwrapping.
    proof fn index_unique_range(idx1: Self, idx2: Self)
        requires
            idx1.wf(),
            idx2.wf(),
            idx1 != idx2
        ensures idx1.block_size_range().disjoint(idx2.block_size_range())
    {
    }

    //TODO: proof
    /// There is at least one index for valid size.
    proof fn index_exists_for_valid_size(size: usize)
        requires Self::valid_block_size(size)
        ensures exists|idx: Self| idx.block_size_range().contains(size as int)
    {
    }

    pub closed spec fn valid_block_size(size: usize) -> bool {
        &&& GRANULARITY <= size && size < (1 << FLLEN + Self::granularity_log2_spec())
        &&& size % GRANULARITY == 0
    }

}

} // verus!
