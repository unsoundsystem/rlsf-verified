use vstd::prelude::*;
use crate::bits::{ex_usize_trailing_zeros, usize_trailing_zeros, is_power_of_two};
use vstd::set_lib::set_int_range;
use vstd::{seq::*, seq_lib::*, bytes::*};
use vstd::arithmetic::{logarithm::log, power2::pow2};
use vstd::math::max;


verus! {
// Repeating definition here because of
// https://verus-lang.zulipchat.com/#narrow/channel/399078-help/topic/error.20and.20panic.20while.20verifying.20code.20with.20const.20generics/near/490367584
#[cfg(target_pointer_width = "64")]
pub const GRANULARITY: usize = 8 * 4;

pub struct BlockIndex<const FLLEN: usize, const SLLEN: usize>(pub usize, pub usize);

impl<const FLLEN: usize, const SLLEN: usize> BlockIndex<FLLEN, SLLEN> {

    spec fn view(&self) -> (int, int) {
        (self.0 as int, self.1 as int)
    }

    //TODO: DRY
    const fn granularity_log2() -> (r: u32)
        requires is_power_of_two(GRANULARITY as int)
        ensures r == Self::granularity_log2_spec()
    {
        // TODO: proof this in `crate::bits::usize_trailing_zeros_is_log2_when_pow2_given`
        assume(forall|x: usize| is_power_of_two(x as int) ==> usize_trailing_zeros(x) == log(2, x as int));
        ex_usize_trailing_zeros(GRANULARITY)
    }

    //TODO: DRY
    spec fn granularity_log2_spec() -> int {
        log(2, GRANULARITY as int)
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
    spec fn block_size_range_set(&self) -> Set<int>
        recommends self.wf()
    {
        let (start, end) = self.block_size_range();
        set_int_range(start, end)
    }

    spec fn block_size_range(&self) -> (int, int) {
        let BlockIndex(fl, sl) = self;
        // This is at least GRANULARITY
        let fl_block_bytes: int = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
        // NOTE: This can be 0, when fl=0 && Self::granularity_log2_spec() < SLLEN
        //                       vvvvvvvvvvvvvvvvvvvvvvvvvvvvv
        let sl_block_bytes = max(fl_block_bytes / SLLEN as int, GRANULARITY as int);
        (fl_block_bytes + sl_block_bytes * sl as int, fl_block_bytes + sl_block_bytes * (sl + 1) as int)
    }

    proof fn example_ranges() {
        let idx = BlockIndex::<28, 64>(0, 0);
        assert(idx.wf());
        reveal(log);
        reveal(pow2);
        assert(pow2(Self::granularity_log2_spec() as nat) == GRANULARITY) by (compute);
        vstd::set_lib::lemma_int_range(GRANULARITY as int, GRANULARITY as int + GRANULARITY as int);
        assert(!idx.block_size_range_set().is_empty());
        assert(idx.block_size_range_set().len() == GRANULARITY);
    }

    // TODO: Proof any block size in range fall into exactly one freelist index (fl, sl)
    /// Correspoinding size ranges for distict indices are not overwrapping.
    proof fn index_unique_range(idx1: Self, idx2: Self)
        requires
            idx1.wf(),
            idx2.wf(),
            idx1 != idx2
        ensures idx1.block_size_range_set().disjoint(idx2.block_size_range_set())
    {
        let (r1_start, r1_end) = idx1.block_size_range();
        let (r2_start, r2_end) = idx2.block_size_range();
        reveal(log);
        reveal(pow2);
        //let fl1_block_bytes: int = pow2((fl1 + Self::granularity_log2_spec()) as nat) as int;
        //let sl1_block_bytes = max(fl1_block_bytes / SLLEN as int, GRANULARITY as int);
        //assert(forall|x:int, y: int| x != y ==> pow2((x + Self::granularity_log2_spec()) as nat) as int != pow2((y + Self::granularity_log2_spec()) as nat) as int );

        assert(r1_end < r2_start || r2_end < r1_start);
        Self::int_range_disjoint_when((r1_start, r1_end), (r2_start, r2_end));
    }

    proof fn int_range_disjoint_when(r1: (int, int), r2: (int, int))
        requires
        ({
          let (r1_start, r1_end) = r1;
          let (r2_start, r2_end) = r2;
          r1_end < r2_start || r2_end < r1_start
        }),
        ensures
        ({
          let (r1_start, r1_end) = r1;
          let (r2_start, r2_end) = r2;
          set_int_range(r1_start, r1_end).disjoint(set_int_range(r2_start, r2_end))
        }),
    {
        // TODO
        let (r1_start, r1_end) = r1;
        let (r2_start, r2_end) = r2;
        assume(set_int_range(r1_start, r1_end).disjoint(set_int_range(r2_start, r2_end)));
    }


    //TODO: proof
    /// There is at least one index for valid size.
    proof fn index_exists_for_valid_size(size: usize)
        requires Self::valid_block_size(size)
        ensures exists|idx: Self| idx.wf() && idx.block_size_range_set().contains(size as int)
    {
    }

    pub closed spec fn valid_block_size(size: usize) -> bool {
        &&& GRANULARITY <= size && size < (1 << FLLEN + Self::granularity_log2_spec())
        &&& size % GRANULARITY == 0
    }

}

} // verus!
