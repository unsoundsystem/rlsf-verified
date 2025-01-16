use vstd::prelude::*;
use crate::bits::{ex_usize_trailing_zeros, usize_trailing_zeros, is_power_of_two};
use vstd::set_lib::set_int_range;
use vstd::{seq::*, seq_lib::*, bytes::*};
use vstd::arithmetic::{logarithm::log, power2::pow2};
use vstd::math::{clip, max, min};
use vstd::arithmetic::power2::{lemma_pow2_unfold, lemma_pow2_strictly_increases, lemma_pow2};

verus! {
// Repeating definition here because of
// https://verus-lang.zulipchat.com/#narrow/channel/399078-help/topic/error.20and.20panic.20while.20verifying.20code.20with.20const.20generics/near/490367584
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
        assume(forall|x: usize| is_power_of_two(x as int) ==> usize_trailing_zeros(x) == log(2, x as int));
        ex_usize_trailing_zeros(GRANULARITY)
    }

    //TODO: DRY
    pub open spec fn granularity_log2_spec() -> int {
        log(2, GRANULARITY as int)
    }

    pub open spec fn valid_block_index(idx: (int, int)) -> bool {
        let (fl, sl) = idx;
        &&& Self::granularity_log2_spec() <= fl < FLLEN as int
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

    // FIXME: correct this using half-open range on Q
    pub open spec fn calculate_block_size_range(&self) -> (int, int)
        recommends self.wf()
    {
        let BlockIndex(fl, sl) = self;
        // This is at least GRANULARITY
        let fl_block_bytes: int = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
        // This is at least GRANULARITY
        // FIXME: is this correct?
        //        - to reflect behivor of actual implementation (rlsf),
        //          the least size of allcation specified as GRANULARITY.
        //        - but the *range* of size, specified in bytes (rlsf assume GRANULARITY aligned)
        //              - TODO: this seems reasonable as a spec but there would be inconsistency
        //                      between impl & spec
        // TODO: this is not correct!!!!! branching into GRANULARITY crossing the boundary of fl_block_bytes
        let sl_block_bytes = max(fl_block_bytes / SLLEN as int, GRANULARITY as int);
        // NOTE: Actually although the range specified in 1-byte granularity,
        //      there can be stored aribtrary size of blocks, because rlsf provides only GRANULARITY aligned allocation.
        (fl_block_bytes + sl_block_bytes * sl as int, fl_block_bytes + sl_block_bytes * (sl + 1) as int)
    }

    // minimal index fall into minimal block size (=GRANULARITY)
    //pub proof fn lemma_block_size_range_min(self)
        //requires self.wf(), vstd::relations::is_minimal(Set::full(), |i: Self, j: Self| block_index_lt(i, j), self)
        //ensures vstd::relations::is_minimal(self.block_size_range_set(), |i: int, j: int| i < j, GRANULARITY as int)
    //{}

    pub closed spec fn block_size_range(&self) -> HalfOpenRange
        recommends self.wf()
    {
        let (start, end) = self.calculate_block_size_range();
        HalfOpenRange(start, end)
    }

    proof fn lemma_block_size_range_is_valid_half_open_range(&self) -> (r: (int, int))
        requires self.wf()
        ensures
            r.0 < r.1
    {
        assert(self.wf());
        assert(forall|x: int, y: int| 0 < x && 0 <= y ==> #[trigger] (x * y) < #[trigger] (x * (y + 1))) by (nonlinear_arith);
        reveal(pow2);
        let (start, end) = self.calculate_block_size_range();
        assert(start < end) by (compute);
        (start, end)
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

    // TODO: this can be stronger e.g. all elements of idx1's range is bigger than idx2's range
    proof fn lemma_index_unique_range_for_fl(idx1: Self, idx2: Self)
        requires idx1.0 < idx2.0
        ensures idx1.block_size_range_set().disjoint(idx2.block_size_range_set())
    {
//
//        // (<=)
//        // pow2(idx1.0 + GRANULARITY_LOG2) + max(pow2(idx1.0 + GRANULARITY_LOG2) / SLLEN, GRANULARITY) * (idx1.1 + 1)
//        // pow2(idx2.0 + GRANULARITY_LOG2)
//        let fl1_bytes = pow2((idx1.0 + Self::granularity_log2_spec()) as nat) as int;
//        let fl2_bytes = pow2((idx2.0 + Self::granularity_log2_spec()) as nat) as int;
//        let sl1_bytes = max(fl1_bytes / SLLEN as int, GRANULARITY as int);
//        let sl2_bytes = max(fl2_bytes / SLLEN as int, GRANULARITY as int);
//        assert(idx1.0 >=  0 && idx2.0 >= 0 && Self::granularity_log2_spec() >= 0) by (compute);
//        assert(idx1.0 + Self::granularity_log2_spec() < idx2.0 + Self::granularity_log2_spec()) by (compute);
//        lemma_pow2_strictly_increases((idx1.0 + Self::granularity_log2_spec()) as nat, (idx2.0 + Self::granularity_log2_spec()) as nat);
//        assert(fl1_bytes < fl2_bytes);
//        assert(idx1.0 + 1 <= idx2.0);
//        assert((Self::granularity_log2_spec() + idx1.0 + 1) > 0) by (compute);
//        lemma_pow2_unfold((Self::granularity_log2_spec() + idx1.0 + 1) as nat);
//        assert(2 * fl1_bytes == pow2((Self::granularity_log2_spec() + idx1.0 + 1) as nat));
//        lemma_pow2_strictly_increases((idx1.0 + Self::granularity_log2_spec()) as nat, (idx1.0 + Self::granularity_log2_spec() + 1) as nat);
//        assert(fl1_bytes == pow2((idx1.0 + Self::granularity_log2_spec()) as nat) as int);
//        assert(fl1_bytes < pow2((Self::granularity_log2_spec() + idx1.0 + 1) as nat));
//        lemma_relax_pow2_strict_order(idx1.0 + Self::granularity_log2_spec(), idx2.0 + Self::granularity_log2_spec());
//        assert(2 * fl1_bytes <= fl2_bytes);
//        assert(idx1.1 + 1 <= SLLEN);
//        assume(sl1_bytes * SLLEN == fl1_bytes);
//        assert(idx1.1 < SLLEN);
//
//        // TODO: branch depend on sl(.)_bytes == GRANULARITY
//        assert(sl1_bytes * (idx1.1 + 1) <= fl1_bytes); // TODO
//        assert(fl1_bytes + sl1_bytes * (idx1.1 + 1) <= 2 * fl1_bytes);
//        assert(fl1_bytes + sl1_bytes * (idx1.1 + 1) <= fl2_bytes);
//        assert(r1.1 <= r2.0) by (compute);
//        assert(idx1.block_size_range_set().disjoint(idx2.block_size_range_set()));
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
        let r1 = idx1.block_size_range();
        let r2 = idx2.block_size_range();
        reveal(log);
        reveal(pow2);
        assert(forall|x: int, y: int| 0 < x && 0 <= y ==> #[trigger] (x * y) < #[trigger] (x * (y + 1))) by (nonlinear_arith);

        Self::lemma_block_index_lt_is_strict_and_total();
        idx1.lemma_block_size_range_is_valid_half_open_range();
        idx2.lemma_block_size_range_is_valid_half_open_range();
        assert(r1.0 < r1.1);
        if Self::block_index_lt(idx1, idx2) {
            // (<=)
            // pow2(idx1.0 + GRANULARITY_LOG2) + max(pow2(idx1.0 + GRANULARITY_LOG2) / SLLEN, GRANULARITY) * (idx1.1 + 1)
            // pow2(idx2.0 + GRANULARITY_LOG2) + max(pow2(idx2.0 + GRANULARITY_LOG2) / SLLEN, GRANULARITY) * idx2.1

            if (idx1.0 == idx2.0 && idx1.1 < idx2.1) {
                // (<=)
                // max(pow2(idx1.0 + GRANULARITY_LOG2) / SLLEN, GRANULARITY) * (idx1.1 + 1)
                // max(pow2(idx2.0 + GRANULARITY_LOG2) / SLLEN, GRANULARITY) * idx2.1
                let fl1_bytes = pow2((idx1.0 + Self::granularity_log2_spec()) as nat) as int;
                let fl2_bytes = pow2((idx2.0 + Self::granularity_log2_spec()) as nat) as int;
                assert(fl1_bytes == fl2_bytes);
                let sl1_bytes = max(fl1_bytes / SLLEN as int, GRANULARITY as int);
                let sl2_bytes = max(fl2_bytes / SLLEN as int, GRANULARITY as int);
                assert(sl1_bytes == sl2_bytes);
                assert(idx1.1 + 1 <= idx2.1);
                assert(idx1.1 + 1 >= 0 && idx2.1 >= 0);
                assert(sl1_bytes >= 0 && sl2_bytes >= 0);
                lemma_mult_lte_mono_pos(idx1.1 + 1 as int, idx2.1 as int, sl1_bytes);
                assert(sl1_bytes * (idx1.1 + 1) <= sl2_bytes * idx2.1);
                assert(r1.1 <= r2.0);
            } else if idx1.0 < idx2.0 {
                // (<=)
                // pow2(idx1.0 + GRANULARITY_LOG2) + max(pow2(idx1.0 + GRANULARITY_LOG2) / SLLEN, GRANULARITY) * (idx1.1 + 1)
                // pow2(idx2.0 + GRANULARITY_LOG2)

                Self::lemma_index_unique_range_for_fl(idx1, idx2);
            }
            assert(r1.1 <= r2.0);
        } else if Self::block_index_lt(idx2, idx1) {
            assert(r2.1 <= r1.0);
        }
        //if idx1.0 != idx2.0 {
            //if idx1.0 < idx2.0 {
                //assert(r1.1 < r2.0);
            //} else if idx1.0 > idx2.0 {
                //assert(r2.1 < r1.0);
            //} else {
                //assert(false);
            //}
        //} else if idx1.1 != idx2.1 {
            //if idx1.1 < idx2.1 {
                //assert(r1.1 < r2.0);
            //} else if idx1.1 > idx2.1 {
                //assert(r2.1 < r1.0);
            //} else {
                //assert(false);
            //}
        //}

        assert(r1.1 <= r2.0 || r2.1 <= r1.0); // TODO
        lemma_disjoint_condition(r1, r2);
    }

    // TODO: this is stronger than `index_unique_range`
    proof fn lemma_block_size_range_mono(&self, rhs: Self) -> (r: (HalfOpenRange, HalfOpenRange))
        requires
            self.wf(),
            rhs.wf()
        ensures
        ({ let (lhs_range, rhs_range) = r;
           lhs_range.disjoint(rhs_range) })
    {
        let lhs_range = self.block_size_range();
        let rhs_range = self.block_size_range();
        (lhs_range, rhs_range)
    }

    //TODO: proof
    /// There is at least one index for valid size.
    proof fn index_exists_for_valid_size(size: usize)
        requires Self::valid_block_size(size as int)
        ensures exists|idx: Self| idx.wf()
            && idx.block_size_range_set().contains(size as int)
    {
        let index = Self::calculate_index_from_block_size(size);
        assert(index.wf() && index.block_size_range_set().contains(size as int));
    }

    /// idealized map_floor
    spec fn calculate_index_from_block_size(size: usize) -> Self
        recommends Self::valid_block_size(size as int)
    {
        let fl = log(2, size as int) - Self::granularity_log2_spec();
        let sl = (size - pow2(fl as nat)) * pow2(min((fl + GRANULARITY - SLLEN), 0) as nat);
        BlockIndex(fl as usize, sl as usize)
    }

    // TODO: formalize idealized map_ceil & proof it returns block of size at least requested

    pub closed spec fn valid_block_size(size: int) -> bool {
        &&& GRANULARITY <= size && size < (1 << FLLEN + Self::granularity_log2_spec())
        &&& size % (GRANULARITY as int) == 0
    }


    /// Order on BlockIndex
    /// this order doesn't assume well-formedness of BlockIndex
    /// (can contain overflowed index e.g. BlockIndex(FLLEN, SLLEN)
    spec fn block_index_lt(idx1: Self, idx2: Self) -> bool {
        let (fl1, sl1) = idx1@;
        let (fl2, sl2) = idx2@;
        if fl1 == fl2 {
            sl1 < sl2
        } else {
            fl1 < fl2
        }
    }

    proof fn lemma_block_index_lt_is_strict_and_total()
        ensures vstd::relations::strict_total_ordering(|idx1: Self, idx2: Self| Self::block_index_lt(idx1, idx2))
    {
    }

}

// use core::cmp::Ordering;
// 
// impl<const FLLEN: usize, const SLLEN: usize> SpecOrd for BlockIndex<FLLEN, SLLEN> {
//     fn spec_lt(self, rhs: Self) -> bool
//         requires self.wf()
//     {
//         let Self(fl_l, sl_l) = self;
//         let Self(fl_r, sl_r) = rhs;
//         match fl_l.cmp(&fl_r) {
//             Ordering::Equal => {
//                 match sl_l.cmp(&sl_r) {
//                     // fl_l == fl_r && sl_l == sl_r ==> false
//                     Ordering::Equal => false,
//                     // fl_l == fl_r && sl_l < sl_r ==> true
//                     Ordering::Less => true,
//                     // fl_l == fl_r && sl_l > sl_r ==> false
//                     Ordering::Greater => false
//                 }
//             }
//             // fl_l < fl_r ==> true
//             Ordering::Less => true,
//             // fl_l > fl_r ==> false
//             Ordering::Greater => false
//         }
//     }
// 
//     fn spec_le(self, rhs: Self) -> bool
//         requires self.wf()
//     {
//         builtin::SpecOrd::<Self>::spec_lt(self, rhs) || self == rhs
//     }
//     fn spec_gt(self, rhs: Self) -> bool
//         requires self.wf()
//     {
//         !self.spec_le(rhs)
//     }
//     fn spec_ge(self, rhs: Self) -> bool
//         requires self.wf()
//     {
//         !self.spec_lt(rhs)
//     }
// }

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


/// Type for left half-open range
pub struct HalfOpenRange(int, int);

impl HalfOpenRange {
    /// Forbiding here invalid format of half-open range which start point is bigger than end. e.g. ]123, -42)
    #[verifier::type_invariant]
    pub open spec fn wf(self) -> bool {
        let Self(start, end) = self;
        start <= end
    }

    pub closed spec fn to_set(&self) -> Set<int> {
        set_int_range(self.0, self.1)
    }

    pub open spec fn disjoint(&self, rhs: Self) -> bool {
        self.to_set().disjoint(rhs.to_set())
    }
}

proof fn lemma_disjoint_condition(r1: HalfOpenRange, r2: HalfOpenRange)
    requires
    ({  let HalfOpenRange(r1_start, r1_end) = r1;
        let HalfOpenRange(r2_start, r2_end) = r2;
        r1_end <= r2_start || r2_end <= r1_start })
    ensures
        r1.disjoint(r2)
    
{}

} // verus!
