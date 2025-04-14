use vstd::prelude::*;
use crate::bits::{usize_trailing_zeros, is_power_of_two};
use vstd::set_lib::set_int_range;
use vstd::{seq::*, seq_lib::*, bytes::*};
use vstd::arithmetic::{logarithm::log, power2::pow2};
use vstd::math::{clip, max, min};
use vstd::arithmetic::power2::{lemma_pow2_unfold, lemma_pow2_strictly_increases, lemma_pow2};
use crate::half_open_range::{HalfOpenRangeOnRat,HalfOpenRange};
use crate::rational_numbers::{
    Rational, rational_number_facts, rational_number_equality, rational_number_inequality, rational_number_properties, rational_number_mul_properties,
    lemma_nonneg_div, lemma_rat_int_lte_equiv, lemma_lte_eq_equiv, lemma_eq_trans, lemma_neg_add_zero, lemma_add_eq_preserve, lemma_add_basics, lemma_from_int_inj
};

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
    pub open spec fn block_size_range_set(&self) -> Set<Rational>
        recommends self.wf()
    {
        self.block_size_range().to_set()
    }

    /// Calculate the correspoinding block size range for given BlockIndex
    ///
    /// * The range is on *rational numbers*,
    ///     i.e. `[start, end) ⊆ { x ∈ Q | GRANULARITY ≤  x < (max valid block size) } `
    ///
    /// Depending on configuration of rlsf, there specific case that split size range of
    /// [GRANULARITY, 2*GRANULARITY) with SLLEN(< GRANULARITY).
    /// In implementation we don't using things like "free block size of GRANULARITY + half bytes"
    /// it's only theorical demands.
    pub closed spec fn block_size_range(&self) -> HalfOpenRangeOnRat
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

    pub closed spec fn block_size_range_ex(&self) -> HalfOpenRange
        recommends self.wf()
    {
        let BlockIndex(fl, sl) = self;
        let fl_block_bytes = pow2((fl + Self::granularity_log2_spec()) as nat) as int;

        if fl_block_bytes < SLLEN {
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

    proof fn lemma_ex_bsr_wf(self) by (nonlinear_arith)
        requires self.wf()
        ensures self.block_size_range_ex().wf()
    {
        HalfOpenRange::lemma_new_wf();
    }

    proof fn lemma_ex_index_unique_range(idx1: Self, idx2: Self)
        requires
            idx1.wf(),
            idx2.wf(),
            idx1 != idx2
        ensures idx1.block_size_range_ex().disjoint(idx2.block_size_range_ex())
    {
        idx1.lemma_ex_bsr_wf();
        idx2.lemma_ex_bsr_wf();
        HalfOpenRange::lemma_is_empty_wf();

    }

    //pub proof fn lemma_block_size_range_contained(self, size: usize)
        //requires Self::valid_block_size(size),
            //Rational::from_int(pow2((fl + Self::granularity_log2_spec()) as nat) as int).lte(Rational::from_int(size)),
        //ensures 
    //{}

    // TODO
    proof fn lemma_block_size_range_size(self) by (nonlinear_arith)
        requires self.wf()
        ensures ({
            let BlockIndex(fl, sl) = self;
            let fl_block_bytes =
                Rational::from_int(pow2((fl + Self::granularity_log2_spec()) as nat) as int);
            let sl_block_bytes = fl_block_bytes.div(Rational::from_int(SLLEN as int));
            self.block_size_range().size().eq(sl_block_bytes)
        })
    {
        //broadcast use rational_number_equality;
        //broadcast use rational_number_facts;
        admit()
    }

    proof fn lemma_block_size_range_for_same_fl(idx1: Self, idx2: Self)
        requires idx1.wf(), idx2.wf(), idx1.0 == idx2.0
        ensures idx1.block_size_range().size().eq(idx2.block_size_range().size())
    {}

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
        broadcast use rational_number_facts;
        let BlockIndex(fl, sl) = self;
        let fl_block_bytes = Rational::from_int(pow2((fl + Self::granularity_log2_spec()) as nat) as int);
        let sl_block_bytes = fl_block_bytes.div(Rational::from_int(SLLEN as int));
        let start = fl_block_bytes.add(sl_block_bytes.mul(Rational::from_int(sl as int)));
        let size = sl_block_bytes;
        lemma_rat_int_lte_equiv(0, pow2((fl + Self::granularity_log2_spec()) as nat) as int);
        assert(Rational::from_int(0).lte(fl_block_bytes)) by (compute);
        assert(fl_block_bytes.is_nonneg());
        lemma_nonneg_div(fl_block_bytes, Rational::from_int(SLLEN as int));
        assert(sl_block_bytes.is_nonneg());
        HalfOpenRangeOnRat::lemma_wf_if_size_is_pos(start, size);
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

        if idx1.1 < idx2.1 {
            let r1 = idx1.block_size_range();
            let r2 = idx2.block_size_range();

            assert(r1.wf() && r2.wf()) by {
                idx1.lemma_block_size_range_is_valid_half_open_range();
                idx2.lemma_block_size_range_is_valid_half_open_range();
            };

            let fl_block_bytes1 = Rational::from_int(pow2((idx1.0 + Self::granularity_log2_spec()) as nat) as int);
            let fl_block_bytes2 = Rational::from_int(pow2((idx2.0 + Self::granularity_log2_spec()) as nat) as int);
            assert(fl_block_bytes1 == fl_block_bytes2);
            let sl_block_bytes1 = fl_block_bytes1.div(Rational::from_int(SLLEN as int));
            let sl_block_bytes2 = fl_block_bytes2.div(Rational::from_int(SLLEN as int));
            assert(sl_block_bytes1 == sl_block_bytes2);
            // TODO
            assume(sl_block_bytes1.is_nonneg());

            let delta = r1.start().neg();
            let r1_slide = r1.slide(delta);
            let r2_slide = r2.slide(delta);

            assert(r1_slide.end().eq(/* SLB */ sl_block_bytes1)) by {
                r1.lemma_slide_start(delta);
                r1.lemma_slide_end(delta);
                HalfOpenRangeOnRat::lemma_slide_wf(r1, delta);

                assert(r1_slide.size().eq(sl_block_bytes1)) by {

                    assert(r1.size().eq(sl_block_bytes1)) by {
                        idx1.lemma_block_size_range_size()
                    };

                    HalfOpenRangeOnRat::lemma_slide_size_eq(r1, delta);
                    lemma_eq_trans(r1_slide.size(), r1.size(), sl_block_bytes1);

                    assert(r1_slide.size().eq(r1.size()));
                };

                HalfOpenRangeOnRat::lemma_slide_wf(r1, delta);
                r1_slide.lemma_size_is_size();
                assert(r1_slide.end().eq(
                        r1_slide.start().add(r1_slide.size())
                ));
                assert(r1_slide.end().eq(sl_block_bytes1)) by {
                    assert(r1_slide.start().eq(Rational::zero())) by {
                        assert(r1_slide.start().eq(r1.start().add(delta)));
                        lemma_neg_add_zero(r1.start());
                        assert(r1.start().add(delta).eq(Rational::zero()));
                        lemma_eq_trans(r1_slide.start(), r1.start().add(delta), Rational::zero());
                    };

                    assert(r1_slide.start().add(r1_slide.size()).eq(r1_slide.size())) by {
                        lemma_add_basics(r1_slide.size());
                        lemma_add_eq_preserve(r1_slide.start(), Rational::zero(), r1_slide.size(), r1_slide.size());
                        broadcast use rational_number_equality;
                    };
                    HalfOpenRangeOnRat::lemma_slide_wf(r1, delta);
                    lemma_eq_trans(r1_slide.end(), r1_slide.start().add(r1_slide.size()), r1_slide.size());
                    lemma_eq_trans(r1_slide.end(), r1_slide.size(), sl_block_bytes1);
                };
            };

            //TODO
            assert(r2_slide.start().eq(/* SLB */
                    sl_block_bytes1.mul(Rational::from_int(idx2.1 as int).sub(Rational::from_int(idx1.1 as int))))) by {
                // r2.start() - r1.start()
                // r2 == idx2.block_size_range()
                //    == new(fl_block_bytes2 + sl_block_bytes2 * idx2.1, sl_block_bytes2)
                // r2.start() == fl_block_bytes2 + sl_block_bytes2 * idx2.1
                // r2_slide.start() == fl_block_bytes2 + sl_block_bytes2 * idx2.1 - r1.start()
                //                  == fl_block_bytes2 + sl_block_bytes2 * idx2.1
                //                       - fl_block_bytes1 + sl_block_bytes1 * idx1.1
                //                  == sl_block_bytes2 * idx2.1 - sl_block_bytes1 * idx1.1
                r2.lemma_slide_start(delta);
                assert(r2_slide.start().eq(r2.start().add(delta)));
                // FIXME
                assert(r2.start().eq(fl_block_bytes2.add(sl_block_bytes2.mul(Rational::from_int(idx2.1 as int)))))
                by {
                    //lemma_from_int_inj(idx2.0 as int, idx2.0 as int);

                    broadcast use rational_number_facts;
                    broadcast use rational_number_equality;
                    broadcast use rational_number_mul_properties;
                    //assert(r2.start().eq(fl_block_bytes2.add(sl_block_bytes2.mul(Rational::from_int(idx2.1 as int))))) by (nonlinear_arith);
                };
                admit();
            };

            //TODO
            assert(r1_slide.disjoint(r2_slide)) by {
                lemma_lte_eq_equiv(r1_slide.end(),
                    sl_block_bytes1, r2_slide.start(),
                    sl_block_bytes1.mul(Rational::from_int(idx2.1 as int).sub(Rational::from_int(idx1.1 as int))));

                assert(r1_slide.wf()) by {
                    assert(r1.wf() && r2.wf());
                    HalfOpenRangeOnRat::lemma_slide_wf(r1, delta);
                };
                assert(r2_slide.wf()) by {
                    assert(r1.wf() && r2.wf());
                    HalfOpenRangeOnRat::lemma_slide_wf(r2, delta);
                };

                //TODO
                assume(sl_block_bytes1.lte(sl_block_bytes1.mul(Rational::from_int(idx2.1 as int).sub(Rational::from_int(idx1.1 as int)))));

                broadcast use rational_number_equality;
                lemma_lte_eq_equiv(sl_block_bytes1, r1_slide.end(),
                    sl_block_bytes1.mul(Rational::from_int(idx2.1 as int).sub(Rational::from_int(idx1.1 as int))), r2_slide.start());
                assert(r1_slide.end().lte(r2_slide.start()));
            };
            HalfOpenRangeOnRat::lemma_disjoint_add_equiv(r1, r2, delta);
            assert(r1.disjoint(r2));
        } else {
            // TODO
            admit()
        }
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
            && #[trigger] idx.block_size_range_set().contains(Rational::from_int(size as int))
    {
        //let index = Self::calculate_index_from_block_size(size);
        //assert(index.wf() && index.block_size_range_set().contains(Rational::from_int(size as int)));
    }

    /// idealized map_floor
    pub closed spec fn calculate_index_from_block_size(size: usize) -> Self
        recommends Self::valid_block_size(size as int)
    {
        let fl = log(2, size as int) - Self::granularity_log2_spec();
        // FIXME: appearently incorrect
        let sl: usize = 0;//(size - pow2(fl as nat)) * log(2, SLLEN) / pow2(fl + Self::granularity_log2_spec());
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
