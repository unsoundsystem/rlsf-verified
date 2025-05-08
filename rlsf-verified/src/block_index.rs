use vstd::prelude::*;
use crate::bits::{usize_trailing_zeros, is_power_of_two};
use vstd::set_lib::set_int_range;
use vstd::{seq::*, seq_lib::*, bytes::*};
use vstd::arithmetic::{logarithm::log, power2::pow2};
use vstd::math::{clip, max, min};
use vstd::arithmetic::power2::{lemma_pow2_unfold, lemma_pow2_strictly_increases, lemma_pow2};
use crate::half_open_range::{HalfOpenRangeOnRat,HalfOpenRange};
use crate::rational_numbers::Rational;

verus! {
// TODO: const generics fixed, rewrite
#[cfg(target_pointer_width = "64")]
pub const GRANULARITY: usize = 8 * 4;

#[derive(PartialEq, Eq)]
pub struct BlockIndex<const FLLEN: usize, const SLLEN: usize>(pub usize, pub usize);

impl<const FLLEN: usize, const SLLEN: usize> BlockIndex<FLLEN, SLLEN> {

    pub open spec fn view(&self) -> (int, int) {
        (self.0 as int, self.1 as int)
    }

    //TODO: DRY
    const fn granularity_log2() -> (r: u32)
        requires is_power_of_two(GRANULARITY as int)
        ensures r == Self::granularity_log2_spec()
    {
        // TODO: proof this in `crate::bits::usize_trailing_zeros_is_log2_when_pow2_given`
        assume(forall|x: usize| is_power_of_two(x as int) ==> #[trigger] usize_trailing_zeros(x) == log(2, x as int));
        GRANULARITY.trailing_zeros()
    }

    //TODO: DRY
    pub open spec fn granularity_log2_spec() -> int {
        log(2, GRANULARITY as int)
    }

    pub open spec fn valid_block_index(idx: (int, int)) -> bool {
        let (fl, sl) = idx;
        &&& 0 <= fl < FLLEN as int
        &&& 0 <= sl < SLLEN as int
    }

    spec fn from_int(idx: (int, int)) -> Self
    {
        BlockIndex(idx.0 as usize, idx.1 as usize)
    }

    /// Block index validity according to given parameters (GRANULARITY/FLLEN/SLLEN)
    pub open spec fn wf(&self) -> bool {
        Self::valid_block_index(self@)
    }

    // Further properties about index calculation
    // - formalized on usize for interoperability with implementation
    // FIXME(if i wrong): is there any special reason for using `int` there?

    /// Calculate size range as set of usize for given block index.
    pub open spec fn block_size_range_set(&self) -> Set<int>
        recommends self.wf()
    {
        self.block_size_range().to_set()
    }


    /// Calculate the correspoinding block size range for given BlockIndex
    #[verifier::opaque]
    pub open spec fn block_size_range(&self) -> HalfOpenRange
        recommends self.wf()
    {
        let BlockIndex(fl, sl) = self;
        let fl_block_bytes = pow2((fl + Self::granularity_log2_spec()) as nat) as int;

        if fl_block_bytes < SLLEN {
            // no matter `sl` all fall into first range
            // (because all requests aligned at GRANULARITY, no one using (0,n) n > 0)
            // only when
            // - 64bit: fl=0, SLLEN=64, GRANULARITY=32
            // - 32bit: fl=0, SLLEN=32, GRANULARITY=16
            HalfOpenRange::new(GRANULARITY as int, GRANULARITY as int)
        } else {
            // both fl_block_bytes and SLLEN is power of 2,  and fl_block_bytes > SLLEN
            // thus the reminder is 0
            let sl_block_bytes = fl_block_bytes / SLLEN as int;

            let start = fl_block_bytes + sl_block_bytes * (sl as int);
            let size = sl_block_bytes;
            HalfOpenRange::new(start, size)
        }
    }


    /// [DEPRECATED] Calculate the correspoinding block size range for given BlockIndex
    ///
    /// This currently not used for specification:
    ///     there reasonable alternative specification using `int` > `block_size_range`
    ///
    /// * The range is on *rational numbers*,
    ///     i.e. `[start, end) ⊆ { x ∈ Q | GRANULARITY ≤  x < (max valid block size) } `
    ///
    /// Depending on configuration of rlsf, there specific case that split size range of
    /// [GRANULARITY, 2*GRANULARITY) with SLLEN(< GRANULARITY).
    /// In implementation we don't using things like "free block size of GRANULARITY + half bytes"
    /// it's only theorical demands.
    pub closed spec fn block_size_range_rat(&self) -> HalfOpenRangeOnRat
        recommends self.wf()
    {
        let BlockIndex(fl, sl) = self;
        // This is at least GRANULARITY
        let fl_block_bytes = Rational::from_int(pow2((fl + Self::granularity_log2_spec()) as nat) as int);

        // This is at least `GRANULARITY / SLLEN` (possibly smaller than 1)
        // NOTE: using rational numbers here to prevent second-level block size to be zero.
        let sl_block_bytes = fl_block_bytes.div(Rational::from_int(SLLEN as int));

        let start = fl_block_bytes.add(sl_block_bytes.mul(Rational::from_int(sl as int)));
        let size = sl_block_bytes;

        // NOTE: Although the range specified in rational numbers,
        //      there cannot be stored blocks of aribtrary bytes, because rlsf provides only GRANULARITY aligned allocation.
        HalfOpenRangeOnRat::new(start, size)
    }


    proof fn lemma_ex_bsr_wf(self) by (nonlinear_arith)
        requires self.wf()
        ensures self.block_size_range().wf()
    {
        HalfOpenRange::lemma_new_wf();
    }

    proof fn lemma_ex_index_unique_range(idx1: Self, idx2: Self)
        requires
            idx1.wf(),
            idx2.wf(),
            idx1 != idx2
        ensures idx1.block_size_range().disjoint(idx2.block_size_range())
    {
        idx1.lemma_ex_bsr_wf();
        idx2.lemma_ex_bsr_wf();
        HalfOpenRange::lemma_is_empty_wf();

    }

    // minimal index fall into minimal block size (=GRANULARITY)
    //pub proof fn lemma_block_size_range_min(self)
        //requires self.wf(), vstd::relations::is_minimal(Set::full(), |i: Self, j: Self| block_index_lt(i, j), self)
        //ensures vstd::relations::is_minimal(self.block_size_range_set(), |i: int, j: int| i < j, GRANULARITY as int)
    //{}

    proof fn lemma_block_size_range_is_valid_half_open_range(&self)
        requires self.wf()
        ensures
            self.block_size_range().wf()
    {
    }

    proof fn example_ranges() {
        let idx = BlockIndex::<28, 64>(0, 0);
        assert(idx.wf()) by (compute);
        reveal(log);
        reveal(pow2);
        assert(pow2(Self::granularity_log2_spec() as nat) == GRANULARITY) by (compute);
    }

    // TODO
    proof fn lemma_index_unique_range_sl(idx1: Self, idx2: Self)
        requires
            idx1.wf(),
            idx2.wf(),
            idx1.0 == idx2.0,
            idx1.1 != idx2.1
        ensures
        ({  let r1 = idx1.block_size_range();
            let r2 = idx2.block_size_range();
            r1.wf() && r2.wf() && r1.disjoint(r2) })
    {
        // assuming sl1 < sl2
        // it suffice to prove
        // [0, SLB)⊥ [SLB*(sl2-sl1),SLB*(sl2-sl1+1)) i.e. sl2-sl1 >= 0
        admit()
    }

    // TODO
    proof fn lemma_index_unique_range_fl(idx1: Self, idx2: Self)
        requires
            idx1.wf(),
            idx2.wf(),
            idx1.0 != idx2.0,
        ensures
        ({  let r1 = idx1.block_size_range();
            let r2 = idx2.block_size_range();
            r1.wf() && r2.wf() && r1.disjoint(r2) })
    {
        // when first-level index differs they fall into different "first-level range [2^fl, 2^(fl+1))"
        admit()
    }

    // TODO: Proof all sub lemma
    /// Correspoinding size ranges for distict indices are not overwrapping.
    proof fn index_unique_range(idx1: Self, idx2: Self)
        requires
            idx1.wf(),
            idx2.wf(),
            idx1 != idx2
        ensures idx1.block_size_range().disjoint(idx2.block_size_range())
    {
        if idx1.block_index_lt(idx2) {
            if idx1.0 == idx2.0 {
                Self::lemma_index_unique_range_sl(idx1, idx2);
            } else {
                Self::lemma_index_unique_range_fl(idx1, idx2);
            }

            //assert(r1.wf() && r2.wf());
            //assert(r1.end().lte(r2.start()));
            //assert(r1.disjoint(r2));
        } else {
            if idx1.0 == idx2.0 {
                Self::lemma_index_unique_range_sl(idx1, idx2);
            } else {
                Self::lemma_index_unique_range_fl(idx1, idx2);
            }

            //assert(r1.wf() && r2.wf());
            //assume(r2.end().lte(r1.start()));
            //assert(r1.disjoint(r2));
        }
    }

    //TODO: proof
    /// There is at least one index for valid size.
    proof fn index_exists_for_valid_size(size: usize)
        requires Self::valid_block_size(size as int)
        ensures exists|idx: Self| idx.wf()
            && #[trigger] idx.block_size_range().contains(size as int)
    {
    }

    pub open spec fn valid_block_size(size: int) -> bool {
        &&& GRANULARITY <= size && size < (pow2(FLLEN as nat) * GRANULARITY)
        &&& size % (GRANULARITY as int) == 0
    }


    /// Order on BlockIndex
    /// this order doesn't assume well-formedness of BlockIndex
    /// (can contain overflowed index e.g. BlockIndex(FLLEN, SLLEN)
    spec fn block_index_lt(self, rhs: Self) -> bool {
        let (fl1, sl1) = self@;
        let (fl2, sl2) = rhs@;
        if fl1 == fl2 {
            sl1 < sl2
        } else {
            fl1 < fl2
        }
    }

    pub closed spec fn suc(self) -> Self
        recommends self.wf()
    {
        let BlockIndex(fl, sl) = self;
        if sl < SLLEN - 1 {
            BlockIndex(fl, (sl + 1) as usize)
        } else if sl == SLLEN - 1 {
            if fl < FLLEN - 1 {
                BlockIndex((fl + 1) as usize, 0)
            } else {
                self
            }
        } else {
            self
        }
    }

    pub proof fn lemma_suc_wf(self)
        requires self.wf()
        ensures self.suc().wf()
    {}

    proof fn lemma_block_index_lt_is_strict_and_total()
        ensures vstd::relations::strict_total_ordering(|idx1: Self, idx2: Self| idx1.block_index_lt(idx2))
    {
    }
}

proof fn lemma_max_lte_mono(x: int, y: int, c: int)
    requires x <= y
    ensures max(x, c) <= max(y, c)
{}

proof fn lemma_mult_lte_mono_pos(x: int, y: int, c: int) by (nonlinear_arith)
    requires x >= 0, y >= 0, c >= 0, x <= y
    ensures c*x <= c*y
{}

proof fn lemma_relax_pow2_strict_order(x: int, y: int)
    requires x >= 0, y >= 0, x < y
    ensures pow2((x + 1) as nat) <=  pow2(y as nat)
{
    lemma_pow2_mono((x + 1) as nat, y as nat);
}

proof fn lemma_pow2_mono(x: nat, y: nat)
    requires
        x <= y,
    ensures
        #[trigger] pow2(x) <= #[trigger] pow2(y),
{
    lemma_pow2(x);
    lemma_pow2(y);
    vstd::arithmetic::power::lemma_pow_increases(2, x, y);
}



} // verus!
