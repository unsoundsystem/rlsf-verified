use vstd::prelude::*;
use crate::bits::{usize_trailing_zeros, is_power_of_two};
use vstd::set_lib::set_int_range;
use vstd::{seq::*, seq_lib::*, bytes::*};
use vstd::arithmetic::{logarithm::log, power2::pow2, power::pow};
use vstd::arithmetic::power::lemma_pow_increases;
use vstd::math::{clip, max, min};
use vstd::arithmetic::power2::{lemma_pow2_unfold, lemma_pow2_strictly_increases, lemma_pow2, lemma_pow2_adds};
use crate::half_open_range::HalfOpenRange;
//use crate::half_open_range_rat::HalfOpenRangeOnRat;
//use crate::rational_numbers::Rational;

verus! {
// TODO: const generics fixed, rewrite
#[cfg(target_pointer_width = "64")]
pub const GRANULARITY: usize = 8 * 4;

#[derive(PartialEq, Eq)]
pub struct BlockIndex<const FLLEN: usize, const SLLEN: usize>(pub usize, pub usize);

impl<const FLLEN: usize, const SLLEN: usize> BlockIndex<FLLEN, SLLEN> {

    pub open spec fn view(self) -> (int, int) {
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


    //TODO: DRY
    pub open spec fn parameter_validity() -> bool {
        &&& 0 < FLLEN <= usize::BITS
        &&& 0 < SLLEN <= usize::BITS
            && is_power_of_two(SLLEN as int)
        &&& usize::BITS == 64 ==> GRANULARITY == 32 // 64bit platform
        &&& usize::BITS == 32 ==> GRANULARITY == 16 // 32bit platform
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
    pub open spec fn wf(self) -> bool {
        Self::valid_block_index(self@)
    }

    // Further properties about index calculation
    // - formalized on usize for interoperability with implementation
    // FIXME(if i wrong): is there any special reason for using `int` there?

    /// Calculate size range as set of usize for given block index.
    pub open spec fn block_size_range_set(self) -> Set<int>
        recommends self.wf(), Self::parameter_validity()
    {
        self.block_size_range().to_set()
    }


    /// Calculate the correspoinding block size range for given BlockIndex
    //#[verifier::opaque]
    pub open spec fn block_size_range(self) -> HalfOpenRange
        recommends self.wf(), Self::parameter_validity()
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


//    /// [DEPRECATED] Calculate the correspoinding block size range for given BlockIndex
//    ///
//    /// This currently not used for specification:
//    ///     there reasonable alternative specification using `int` > `block_size_range`
//    ///
//    /// * The range is on *rational numbers*,
//    ///     i.e. `[start, end) ⊆ { x ∈ Q | GRANULARITY ≤  x < (max valid block size) } `
//    ///
//    /// Depending on configuration of rlsf, there specific case that split size range of
//    /// [GRANULARITY, 2*GRANULARITY) with SLLEN(< GRANULARITY).
//    /// In implementation we don't using things like "free block size of GRANULARITY + half bytes"
//    /// it's only theorical demands.
//    pub closed spec fn block_size_range_rat(&self) -> HalfOpenRangeOnRat
//        recommends self.wf()
//    {
//        let BlockIndex(fl, sl) = self;
//        // This is at least GRANULARITY
//        let fl_block_bytes = Rational::from_int(pow2((fl + Self::granularity_log2_spec()) as nat) as int);
//
//        // This is at least `GRANULARITY / SLLEN` (possibly smaller than 1)
//        // NOTE: using rational numbers here to prevent second-level block size to be zero.
//        let sl_block_bytes = fl_block_bytes.div(Rational::from_int(SLLEN as int));
//
//        let start = fl_block_bytes.add(sl_block_bytes.mul(Rational::from_int(sl as int)));
//        let size = sl_block_bytes;
//
//        // NOTE: Although the range specified in rational numbers,
//        //      there cannot be stored blocks of aribtrary bytes, because rlsf provides only GRANULARITY aligned allocation.
//        HalfOpenRangeOnRat::new(start, size)
//    }


    pub proof fn lemma_bsr_wf(self) by (nonlinear_arith)
        requires self.wf(), Self::parameter_validity()
        ensures self.block_size_range().wf()
    {
        HalfOpenRange::lemma_new_wf();
    }


    // minimal index fall into minimal block size (=GRANULARITY)
    //pub proof fn lemma_block_size_range_min(self)
        //requires self.wf(), vstd::relations::is_minimal(Set::full(), |i: Self, j: Self| block_index_lt(i, j), self)
        //ensures vstd::relations::is_minimal(self.block_size_range_set(), |i: int, j: int| i < j, GRANULARITY as int)
    //{}

    proof fn lemma_block_size_range_is_valid_half_open_range(self)
        requires self.wf()
        ensures
            self.block_size_range().wf()
    {
        let r = self.block_size_range();
        if pow2((self.0 + Self::granularity_log2_spec()) as nat) < SLLEN {
            self.fl_is_zero();
        } else {
            self.fl_non_zero();
            assert(forall|i: int, j: int| i >= 0
                ==> #[trigger] (i * j) <= i * (j + 1))
                by (nonlinear_arith);
        }
    }

    proof fn example_ranges() {
        let idx = BlockIndex::<28, 64>(0, 0);
        assert(idx.wf()) by (compute);
        reveal(log);
        reveal(pow2);
        assert(pow2(Self::granularity_log2_spec() as nat)
            == GRANULARITY) by (compute);
    }


    proof fn lemma_block_size_range_mono(idx1: Self, idx2: Self)
        by (nonlinear_arith)
        requires idx1.wf(), idx2.wf(),
            idx1.block_index_lt(idx2),
            idx1.0 == 0 ==> idx2.0 != 0,
            Self::parameter_validity()
        ensures
        ({
            let r1 = idx1.block_size_range();
            let r2 = idx2.block_size_range();
            r1.end() <= r2.start()
        })
    {
        let r1 = idx1.block_size_range();
        let r2 = idx2.block_size_range();

        assert(Self::granularity_log2_spec() == 4
            || Self::granularity_log2_spec() == 5)
        by (compute);

        assert(pow2((idx2.0
                    + Self::granularity_log2_spec()) as nat)
            == pow2(idx2.0 as nat)
                * pow2(Self::granularity_log2_spec() as nat))
        by {
            lemma_pow2_adds(idx2.0 as nat,
                Self::granularity_log2_spec() as nat);
        };

        assert(pow2((idx1.0
                    + Self::granularity_log2_spec()) as nat)
            == pow2(idx1.0 as nat)
                * pow2(Self::granularity_log2_spec() as nat))
        by {
            lemma_pow2_adds(idx1.0 as nat,
                Self::granularity_log2_spec() as nat);
        }

        if idx1.fl_zero_cond() {
            assert(idx2.0 > 0);
            idx2.fl_zero_iff();
            idx2.fl_non_zero();
            idx1.fl_is_zero();
            assert(2*GRANULARITY
                <= pow2((idx2.0 + Self::granularity_log2_spec()) as nat))
            by {
                assert(GRANULARITY == pow2(Self::granularity_log2_spec() as nat)) by (compute);
                assert(idx2.0 >= 1);
                reveal(pow);
                lemma_pow2(1);
                lemma_pow2(idx2.0 as nat);
                assert(pow2(1) == 2) by (compute);
                lemma_pow_increases(2, 1, idx2.0 as nat);
                assert(2 <= pow2(idx2.0 as nat));
            }
        } else {
            assert(!idx1.fl_zero_cond()
                ==> !idx2.fl_zero_cond()) by {

                if !idx1.fl_zero_cond() {
                    assert(pow2(idx1.0 as nat) * pow2(Self::granularity_log2_spec() as nat) >= SLLEN);
                    assert(pow2(idx1.0 as nat)
                        <= pow2(idx2.0 as nat)) by {
                        assert(idx1.0 <= idx2.0);
                        lemma_pow2(idx1.0 as nat);
                        lemma_pow2(idx2.0 as nat);
                        lemma_pow_increases(2,
                            idx1.0 as nat, idx2.0 as nat);
                    };
                    assert(pow2(idx2.0 as nat) * pow2(Self::granularity_log2_spec() as nat) >= SLLEN);

                }
            };
            idx1.fl_non_zero();
            idx2.fl_non_zero();

            let flb1 =
                pow2((idx1.0 + Self::granularity_log2_spec()) as nat) as int;
            let slb1 = flb1 / SLLEN as int;
            let flb2 =
                pow2((idx2.0 + Self::granularity_log2_spec()) as nat) as int;
            let slb2 = flb2 / SLLEN as int;
            assert(r1.end() == flb1
                + slb1 * (idx1.1 as int + 1));
            assert(r2.start() == flb2
                + slb2 * (idx2.1 as int));

            HalfOpenRange::lemma_new_start();
            HalfOpenRange::lemma_new_end();

            if idx1.0 < idx2.0 {
                assert(flb1 == pow2(idx1.0 as nat)
                    * pow2(Self::granularity_log2_spec() as nat));
                assert(flb2 == pow2(idx2.0 as nat)
                    * pow2(Self::granularity_log2_spec() as nat));
                assert(flb1 * 2 <= flb2) by {
                    assert(idx1.0 <= idx2.0 - 1);
                    assert(pow2(idx1.0 as nat)
                        <= pow2((idx2.0 - 1) as nat)) by {
                        lemma_pow2(idx1.0 as nat);
                        lemma_pow2((idx2.0 - 1) as nat);
                        lemma_pow_increases(2, idx1.0 as nat, (idx2.0 - 1) as nat);
                    };
                    assert(pow2(idx1.0 as nat) * 2
                        <= pow2((idx2.0 - 1) as nat) * 2);
                    lemma_pow2_unfold(idx2.0 as nat);
                };
                assert(r1.end() <= r2.start());
            } else if idx1.0 == idx2.0 && idx1.1 < idx2.1 {
                // trivial
            }
        }
    }

    /// Correspoinding size ranges for distict indices are not overwrapping.
    proof fn index_unique_range(idx1: Self, idx2: Self)
        requires
            idx1.wf(),
            idx2.wf(),
            idx1 != idx2,
            idx1.0 == 0 ==> idx2.0 != 0, // fl=0 fall into [G,2G)
            Self::parameter_validity()
        ensures idx1.block_size_range()
            .disjoint(idx2.block_size_range())
    {
        idx1.lemma_block_size_range_is_valid_half_open_range();
        idx2.lemma_block_size_range_is_valid_half_open_range();
        assert(idx1.block_index_lt(idx2) || idx2.block_index_lt(idx1));
        if idx1.block_index_lt(idx2) {
            Self::lemma_block_size_range_mono(idx1, idx2);
        } else if idx2.block_index_lt(idx1) {
            Self::lemma_block_size_range_mono(idx2, idx1);
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
    pub open spec fn block_index_lt(self, rhs: Self) -> bool
        recommends self.wf(), rhs.wf(), Self::parameter_validity()
    {
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

    pub proof fn fl_is_zero(self)
        requires self.wf(), Self::parameter_validity(),
            pow2((self.0 + Self::granularity_log2_spec()) as nat) < SLLEN
        ensures ({
            &&& self.block_size_range().start()
                == GRANULARITY
            &&& self.block_size_range().end()
                == 2*GRANULARITY
        })
    {
        HalfOpenRange::lemma_new_start();
        HalfOpenRange::lemma_new_end();
    }

    pub proof fn fl_non_zero(self)
        requires self.wf(), Self::parameter_validity(),
            pow2((self.0 + Self::granularity_log2_spec()) as nat) >= SLLEN
        ensures ({
            let BlockIndex(fl, sl) = self;
            let fl_block_bytes =
                pow2((fl + Self::granularity_log2_spec()) as nat) as int;
            let sl_block_bytes = fl_block_bytes / SLLEN as int;

            &&& self.block_size_range().start()
                == fl_block_bytes + sl_block_bytes * (sl as int)
            &&& self.block_size_range().end()
                == fl_block_bytes
                    + sl_block_bytes * (sl as int + 1)
        })
    {
        let BlockIndex(fl, sl) = self;
        let fl_block_bytes =
            pow2((fl + Self::granularity_log2_spec()) as nat) as int;
        let sl_block_bytes = fl_block_bytes / SLLEN as int;
        //assume(fl_block_bytes >= SLLEN);


        HalfOpenRange::lemma_new_start();
        HalfOpenRange::lemma_new_end();

        assert(self.block_size_range()
            == HalfOpenRange::new(
                fl_block_bytes + sl_block_bytes * (sl as int), sl_block_bytes));
        assert(self.block_size_range().end()
                == fl_block_bytes + sl_block_bytes
                    * (sl as int + 1)) by {
            assert(self.block_size_range().end()
                            == fl_block_bytes + sl_block_bytes * (sl as int) + sl_block_bytes); 
            assert(sl_block_bytes * (sl as int) + sl_block_bytes
                == sl_block_bytes * (sl as int + 1)) by (nonlinear_arith);
        };

    }
    spec fn fl_zero_cond(self) -> bool
        recommends Self::parameter_validity()
    {
        pow2((self.0 + Self::granularity_log2_spec()) as nat) < SLLEN
    }

    proof fn fl_zero_iff(self)
        by (nonlinear_arith)
        requires self.wf(), Self::parameter_validity(),
        ensures SLLEN == usize::BITS && self.0 == 0 <==> self.fl_zero_cond()
    {
        reveal(pow);
        vstd::arithmetic::power2::lemma_pow2(5);
        vstd::arithmetic::power2::lemma_pow2(6);
        assert(pow2(5) == 32) by (compute);
        assert(pow2(6) == 64) by (compute);


        assert(Self::granularity_log2_spec() == 4
            || Self::granularity_log2_spec() == 5)
        by (compute);

        assert(pow2((self.0
                    + Self::granularity_log2_spec()) as nat)
            == pow2(self.0 as nat)
                * pow2(Self::granularity_log2_spec() as nat))
        by {
            lemma_pow2_adds(self.0 as nat,
                Self::granularity_log2_spec() as nat);
        };


        if self.0 == 0 && SLLEN == usize::BITS {
            assert(pow2((0 + Self::granularity_log2_spec()) as nat)
                < usize::BITS) by (compute);
        }
        if self.fl_zero_cond() {
            assert(pow2((self.0 + Self::granularity_log2_spec()) as nat) < SLLEN);
            if usize::BITS == 64 {
                assert(Self::parameter_validity());
                assert(GRANULARITY == 32
                    && Self::granularity_log2_spec() == 5) by (compute);
                assert(SLLEN <= usize::BITS);
                assert(usize::BITS == 64);
                assert(pow2(self.0 as nat) * pow2(Self::granularity_log2_spec() as nat) < SLLEN);
                assert(pow2(self.0 as nat) * pow2(5) < 64);
                assert(pow2(5) == 32) by (compute);
                assert(pow2(self.0 as nat) == 1) by {
                    if pow2(self.0 as nat) > 1 {
                        assert(2 * 32 < 64);
                        assert(false);
                    }
                    vstd::arithmetic::power2::lemma_pow2_pos(self.0 as nat);
                };
                assert(self.0 == 0) by {
                    if self.0 > 0 {
                        assert(pow2(0) < pow2(self.0 as nat)) by {
                            vstd::arithmetic::power2::lemma_pow2_strictly_increases(0, self.0 as nat);
                        };
                        assert(pow2(0) == 1) by (compute);
                        assert(pow2(self.0 as nat) != 1);
                    }
                };
                assert(pow2(self.0 as nat + 5) < SLLEN);
                assert(SLLEN == usize::BITS) by {
                    if SLLEN < usize::BITS {
                        assert(pow2((self.0 + Self::granularity_log2_spec()) as nat) < SLLEN);
                        assert(pow2(self.0 as nat)
                            * pow2(Self::granularity_log2_spec() as nat) < SLLEN);
                        assert(pow2(Self::granularity_log2_spec() as nat) < SLLEN);
                        let sli = choose|i: nat| pow2(i) == SLLEN;
                        assert(pow2(6) == 64);
                        assert(pow2(sli) < pow2(6));
                        assert(sli < 6) by {
                            lemma_pow2(sli);
                            lemma_pow2(6);
                            vstd::arithmetic::power::lemma_pow_increases_converse(2, sli, 6);
                        };
                        assert(pow2(sli) <= pow2(5)) by {
                            lemma_pow2(sli);
                            lemma_pow2(5);
                            lemma_pow_increases(2, sli, 5);
                        };

                        assert(pow2((self.0 + Self::granularity_log2_spec()) as nat)
                            == pow2(Self::granularity_log2_spec() as nat));
                        assert(pow2(5) < pow2(sli));

                        assert(false)
                    }
                };
                assert(self.0 == 0 && SLLEN == usize::BITS);
            } else if usize::BITS == 32 {
                assert(Self::parameter_validity());
                assert(GRANULARITY == 16
                    && Self::granularity_log2_spec() == 4);
                assert(GRANULARITY == 16);
                assert(SLLEN <= usize::BITS);
                assert(usize::BITS == 32);
                assert(pow2(self.0 as nat) * pow2(Self::granularity_log2_spec() as nat) < SLLEN);
                assert(pow2(self.0 as nat) * pow2(4) < 32);
                assert(pow2(4) == 16) by (compute);
                assert(pow2(self.0 as nat) == 1) by {
                    if pow2(self.0 as nat) > 1 {
                        assert(2 * 16 < 32);
                        assert(false);
                    }
                    vstd::arithmetic::power2::lemma_pow2_pos(self.0 as nat);
                };
                assert(self.0 == 0) by {
                    if self.0 > 0 {
                        assert(pow2(0) < pow2(self.0 as nat)) by {
                            vstd::arithmetic::power2::lemma_pow2_strictly_increases(0, self.0 as nat);
                        };
                        assert(pow2(0) == 1) by (compute);
                        assert(pow2(self.0 as nat) != 1);
                    }
                };
                assert(pow2(self.0 as nat + 5) < SLLEN);
                assert(SLLEN == usize::BITS) by {
                    if SLLEN < usize::BITS {
                        assert(pow2((self.0 + Self::granularity_log2_spec()) as nat) < SLLEN);
                        assert(pow2(self.0 as nat)
                            * pow2(Self::granularity_log2_spec() as nat) < SLLEN);
                        assert(pow2(Self::granularity_log2_spec() as nat) < SLLEN);
                        let sli = choose|i: nat| pow2(i) == SLLEN;
                        assert(pow2(5) == 32);
                        assert(pow2(sli) < pow2(5));
                        assert(sli < 5) by {
                            lemma_pow2(sli);
                            lemma_pow2(5);
                            vstd::arithmetic::power::lemma_pow_increases_converse(2, sli, 6);
                        };
                        assert(pow2(sli) <= pow2(4)) by {
                            lemma_pow2(sli);
                            lemma_pow2(4);
                            lemma_pow_increases(2, sli, 4);
                        };

                        assert(pow2((self.0 + Self::granularity_log2_spec()) as nat)
                            == pow2(Self::granularity_log2_spec() as nat));
                        assert(pow2(4) < pow2(sli));

                        assert(false)
                    }
                };
                assert(self.0 == 0 && SLLEN == usize::BITS);
            }
            assert(SLLEN <= usize::BITS);
            assert(self.0 == 0 && SLLEN == usize::BITS);
        }
    }
}


} // verus!
