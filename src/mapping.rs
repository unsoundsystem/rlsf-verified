use vstd::prelude::*;

verus! {

use crate::Tlsf;
use crate::parameters::*;
use vstd::calc_macro::calc;
use vstd::{seq::*, seq_lib::*, bytes::*};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::{logarithm::log, power2::pow2, power::pow};
use crate::bits::*;
use crate::block_index::BlockIndex;
//use crate::rational_numbers::{Rational, rational_number_facts, rational_number_properties};
use core::hint::unreachable_unchecked;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::bits::u64_trailing_zeros;


impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {

    pub fn map_ceil(size: usize) -> (r: Option<BlockIndex<FLLEN, SLLEN>>)
        requires
            size >= GRANULARITY,
            size % GRANULARITY == 0,
            Self::parameter_validity(),
            size as int <= Self::max_allocatable_size(),
        ensures
        ({
            if BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int) {
                r matches Some(idx) && idx.wf() &&
                // NOTE: ensure `idx` is index of freelist that all of its elements larger or equal to
                //       the requested size
                // TODO: This spec is too weak.
                //      To state the correctness of ceiling operation,
                //      it's should be like this: (idx - 1).block_size_range().contains(size)
                //      i.e. the result index is successor index of the one requested size is
                //      contained.
                //      But such precise specification, may be not mandatory for functional correctness
                size as int <= idx.block_size_range().start()
                //&& exists|i: BlockIndex<FLLEN,SLLEN>|
                    //i.block_size_range().contains(size)
                        //&& idx == i.suc()
            } else {
                r is None
            }
        })
    {
        proof {
            lemma_pow2_values();
            lemma_log2_values();
            Self::lemma_size_within_max_is_valid_block_size(size);
        }
        let floor = match Self::map_floor(size) {
            Some(idx) => idx,
            None => {
                proof {
                    Self::lemma_size_within_max_is_valid_block_size(size);
                    assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int));
                }
                return None;
            }
        };
        let BlockIndex(fl, sl) = floor;
        let idx =
            if sl < SLLEN - 1 {
                BlockIndex(fl, sl + 1)
            } else if fl < FLLEN - 1 {
                BlockIndex(fl + 1, 0)
            } else {
                floor
            };

        proof {
            Self::lemma_size_within_max_is_valid_block_size(size);
            assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int));
            assert(floor.wf());
            assert(floor.block_size_range().contains(size as int));
            assert(floor.block_size_range().start() <= (size as int));
            assert((size as int) < floor.block_size_range().end());

            if sl < SLLEN - 1 {
                assert(idx.wf());
                if floor.fl_zero_cond() {
                    floor.fl_is_zero();
                    idx.fl_is_zero();
                    assert(floor.block_size_range().start() == GRANULARITY as int);
                    assert(floor.block_size_range().end() == 2 * GRANULARITY as int);
                    assert(idx.block_size_range().start() == GRANULARITY as int);
                    assert((size as int) % (GRANULARITY as int) == 0);
                    assert((size as int) < (2 * (GRANULARITY as int)));
                    assert((GRANULARITY as int) <= (size as int));
                    assert((size as int) == (GRANULARITY as int));
                    assert((size as int) <= idx.block_size_range().start());
                } else {
                    floor.fl_non_zero();
                    idx.fl_non_zero();
                    assert(floor.block_size_range().end() == idx.block_size_range().start());
                    assert((size as int) < floor.block_size_range().end());
                    assert((size as int) <= idx.block_size_range().start());
                }
            } else if fl < FLLEN - 1 {
                assert(floor.wf());
                assert(idx.wf());
                assert(floor.block_index_lt(idx));
                assert(floor.0 == 0 ==> idx.0 != 0);
                BlockIndex::<FLLEN, SLLEN>::lemma_block_size_range_mono(floor, idx);
                assert(floor.block_size_range().end() <= idx.block_size_range().start());
                assert((size as int) < floor.block_size_range().end());
                assert((size as int) <= idx.block_size_range().start());
            } else {
                assert(idx == floor);
                assert(floor == BlockIndex::<FLLEN, SLLEN>((FLLEN - 1) as usize, (SLLEN - 1) as usize));
                Self::lemma_last_index_start_is_max_allocatable();
                assert(idx.wf());
                assert(idx.block_size_range().start() == Self::max_allocatable_size());
                assert((size as int) <= Self::max_allocatable_size());
                assert((size as int) <= idx.block_size_range().start());
            }
        }

        Some(idx)
    }


    #[inline]
    pub fn map_floor(size: usize) -> (r: Option<BlockIndex<FLLEN, SLLEN>>) //by (nonlinear_arith)
        requires
            // NOTE: in onriginal code following conditions are encoded as debug_assert!
            // and confirmed at the call site. But if violated they cause underflow
            size >= GRANULARITY,
            size % GRANULARITY == 0,
            Self::parameter_validity(),
        ensures
        ({
            if BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int) {
                r matches Some(idx) && idx.wf() &&
                    // NOTE: ensuring `r` is index of freelist appropriate to store the block of size requested
                    idx.block_size_range().contains(size as int)
            } else {
                r is None
            }
        })
    {
        proof {
            lemma_pow2_values();
            lemma_log2_values();
        }
        //assert(size >= GRANULARITY);
        //assert(size % GRANULARITY == 0);
        // 64bit: 64 - 5 - 1 - (at most 58)
        // 32bit: 32 - 4 - 1 - (at most 27)
        assert(Self::granularity_log2_spec() + usize_leading_zeros(size) < 64)
        by {
            assert(size % GRANULARITY == 0);
            assert(size >= GRANULARITY);
            // i.e. size.leading_zeros() < (BITS - GRANULARITY_LOG2)
            Self::fl_not_underflow(size);
        };
        proof {
            granularity_is_power_of_two();
        }
        // log2(size / GRANULARITY)
        let mut fl: u32 = usize::BITS - Self::granularity_log2() - 1 - size.leading_zeros();
        assert(fl == log(2, size as int) - Self::granularity_log2()) by {
            log2_using_leading_zeros_usize(size);
            assert(fl == usize::BITS - Self::granularity_log2() - 1 - usize_leading_zeros(size));
            assert(log(2, size as int) == usize::BITS - usize_leading_zeros(size) - 1);
        };

        //assume(nth_bit!(size, (fl + Self::granularity_log2()) as usize));
        // The shift amount can be negative, and rotation lets us handle both
        // cases without branching. Underflowed digits can be simply masked out
        // in `map_floor`.
        let mut sl = size.rotate_right((fl + Self::granularity_log2()).wrapping_sub(Self::sli()));

        // The most significant one of `size` should be now at `sl[SLI]`
        //assume(nth_bit!(sl, Self::sli()));
        //assert(((sl >> Self::sli_spec()) & 1) == 1);

        // TODO: modulize assumptions about parameters
        assert(Self::parameter_validity());

        assert(fl >= FLLEN <==> !BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int)) by {
            Self::granularity_basics();
            assert(fl == log(2, size as int) - Self::granularity_log2_spec());
            assert(fl < FLLEN <==>
                BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int)) by {

                // (==>)
                // 2^fl < 2^FLLEN
                // 2^fl * G < 2^FLLEN * G
                // 2^fl * 2^log2(G) < 2^FLLEN * G
                // 2^(fl - log2(G)) < 2^FLLEN * G
                // 2^log2(size) < 2^FLLEN * G, where fl = log2(size) - log2(G)
                // size / (2^FLLEN * G) < size / 2^log2(size)
                // size / (2^FLLEN * G) < 1
                // size / (2^FLLEN * G) == 0
                // size < (2^FLLEN * G)
                if fl < FLLEN {
                    assert(size < pow2(FLLEN as nat) * GRANULARITY
                        <==> (size as int) / (GRANULARITY as int) < pow2(FLLEN as nat));
                    assert((size as int) / (GRANULARITY as int) < pow2(FLLEN as nat)
                        <== log(2, (size as int) / (GRANULARITY as int)) < log(2, pow2(FLLEN as nat) as int)) by {
                        if log(2, (size as int) / (GRANULARITY as int)) < log(2, pow2(FLLEN as nat) as int) {
                            assert((size as int) / (GRANULARITY as int) > 0);
                            assert(pow2(FLLEN as nat) as int > 1) by {
                                vstd::arithmetic::power2::lemma_pow2_strictly_increases(0, FLLEN as nat);
                                assert(pow2(0) == 1);
                            };
                            log2_power_ordered((size as int) / (GRANULARITY as int), pow2(FLLEN as nat) as int);
                            assert((size as int) / (GRANULARITY as int) < pow2(FLLEN as nat));
                        }
                    }
                    assert(log(2, (size as int) / (GRANULARITY as int)) < log(2, pow2(FLLEN as nat) as int)
                        <==> log(2, (size as int) / (GRANULARITY as int)) < FLLEN) by {
                        assert(FLLEN as int == log(2, pow2(FLLEN as nat) as int)) by {
                            vstd::arithmetic::power2::lemma_pow2(FLLEN as nat);
                            vstd::arithmetic::logarithm::lemma_log_pow(2, FLLEN as nat);
                        };
                    };
                    assert(fl == log(2, size as int / GRANULARITY as int)) by {
                        lemma_log2_distributes(size as int, GRANULARITY as int)
                    }

                    assert(BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int));
                }

                assert(BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int)
                    ==> fl < FLLEN)
                by {
                    if size < GRANULARITY * pow2(FLLEN as nat) {
                        // log2 both sides
                        assert(log(2, size as int) < log(2, GRANULARITY * pow2(FLLEN as nat))) by {
                            assert(is_power_of_two(GRANULARITY * pow2(FLLEN as nat))) by {
                                vstd::arithmetic::power2::lemma_pow2_adds(
                                    Self::granularity_log2() as nat,
                                    FLLEN as nat
                                );
                            };
                            log2_is_strictly_ordered_if_rhs_is_pow2(
                                size as int,
                                GRANULARITY * pow2(FLLEN as nat)
                            );
                        };
                        assert(log(2, GRANULARITY as int) + FLLEN
                            ==  log(2, GRANULARITY * pow2(FLLEN as nat))) by {
                            lemma_log2_mul_pow2(FLLEN as nat, GRANULARITY as int);
                        };
                        assert(log(2, size as int) - Self::granularity_log2() < FLLEN);
                    }
                }
            };
        };
        if fl as usize >= FLLEN {
            assert(!BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int));
            return None;
        } else {
            assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int));
        }


        proof { mask_higher_bits_leq_mask(sl, SLLEN); }
        let idx = BlockIndex(fl as usize, sl & (SLLEN - 1));
        let sl_shift_amount: i32 = (fl + Self::granularity_log2()).wrapping_sub(Self::sli()) as i32;
        let BlockIndex(fl, sl) = idx;
        proof {
            Self::granularity_basics();
            assert(fl == log(2, size as int) - Self::granularity_log2_spec());
            assert(Self::granularity_log2() == Self::granularity_log2_spec());

            //assert(sl_shift_amount >= 0 <==> fl + Self::granularity_log2_spec() >= Self::sli_spec());
            if fl + Self::granularity_log2_spec() >= Self::sli_spec()  {

                let flb = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
                let slb = flb / SLLEN as int;
                assert(fl == log(2, size as int / GRANULARITY as int)) by {
                    lemma_log2_distributes(size as int, GRANULARITY as int)
                };
                assert(sl == ((size as int) / slb) % SLLEN as int) by {
                    assert(usize_rotate_right(size, sl_shift_amount) & low_mask_usize((usize::BITS - sl_shift_amount) as nat) as usize
                        == (size >> sl_shift_amount) & low_mask_usize((usize::BITS - sl_shift_amount) as nat) as usize) by {
                        lemma_usize_rotr_mask_lower(size, sl_shift_amount);
                    };
                    assert(sl == (size >> sl_shift_amount) & (SLLEN - 1) as usize) by {

                        assert(SLLEN - 1 == low_mask_usize(Self::sli_spec() as nat)) by {
                            Self::sli_pow2_is_sllen();
                            assert(SLLEN - 1 == pow2(Self::sli_spec() as nat) - 1);
                        };

                        calc! {
                            (==)
                            sl; {}

                            usize_rotate_right(size, sl_shift_amount) & (SLLEN - 1) as usize;
                            {
                                assert(fl + Self::granularity_log2_spec() <= usize::BITS);
                                lemma_duplicate_low_mask_usize(
                                    usize_rotate_right(size, sl_shift_amount),
                                    Self::sli_spec() as nat,
                                    (usize::BITS - sl_shift_amount) as nat
                                );
                            }

                            usize_rotate_right(size, sl_shift_amount)
                                & low_mask_usize((usize::BITS - sl_shift_amount) as nat)
                                & low_mask_usize(Self::sli_spec() as nat);
                            {
                                lemma_usize_rotr_mask_lower(size, sl_shift_amount)
                            }

                            (size >> sl_shift_amount)
                                & low_mask_usize((usize::BITS - sl_shift_amount) as nat)
                                & low_mask_usize(Self::sli_spec() as nat);
                            {
                                assert(fl + Self::granularity_log2_spec() <= usize::BITS);
                                lemma_duplicate_low_mask_usize(
                                    size >> sl_shift_amount,
                                    Self::sli_spec() as nat,
                                    (usize::BITS - sl_shift_amount) as nat
                                );
                            }
                            (size >> sl_shift_amount) & low_mask_usize(Self::sli_spec() as nat);
                        }
                    };

                    //assume(SLLEN - 1 == low_mask_usize(Self::sli_spec() as nat) == pow2(Self::sli_spec() as nat) - 1);
                    //assume(low_mask_usize((usize::BITS - sl_shift_amount) as nat) > SLLEN - 1);
                    assert((size >> sl_shift_amount) & (SLLEN - 1) as usize == (size >> sl_shift_amount) % SLLEN) by {
                        bit_mask_is_mod_for_pow2(size >> sl_shift_amount, SLLEN);
                    };
                    // pow2(fl) / pow2(sli) == slb
                    assert(slb == pow2((fl + Self::granularity_log2_spec() - Self::sli_spec()) as nat)) by {
                        assert(SLLEN == pow2(Self::sli_spec() as nat)) by { Self::sli_pow2_is_sllen() };
                        assert(pow2((fl + Self::granularity_log2_spec()) as nat) / SLLEN as nat
                                == pow2((fl + Self::granularity_log2_spec() - Self::sli_spec()) as nat)) by {
                            lemma_pow2_div_sub(
                                Self::sli_spec() as nat,
                                (fl + Self::granularity_log2_spec()) as nat
                            );
                        };
                    };
                    assert(size >> sl_shift_amount
                        == (size as nat /
                            (pow2((fl + Self::granularity_log2_spec()
                                   - Self::sli_spec()) as nat))))
                    by {
                        assert(0 <= sl_shift_amount < 64);
                        assert(sl_shift_amount == fl + Self::granularity_log2_spec()
                                   - Self::sli_spec());
                        lemma_usize_shr_is_div(size, sl_shift_amount as usize);
                    };
                    assert(size > 0);
                    vstd::arithmetic::power2::lemma_pow2_pos((fl + Self::granularity_log2_spec()
                                   - Self::sli_spec()) as nat);

                    assert((size >> sl_shift_amount) & (SLLEN - 1) as usize
                        == (size as int /
                            (pow2((fl + Self::granularity_log2_spec() - Self::sli_spec()) as nat)) as int)
                        % SLLEN as int);
                };
            } else {
                if GRANULARITY == 32 {
                    assert(Self::sli_spec() <= 6) by {
                        Self::sli_pow2_is_sllen();
                        assert(log(2, 64) == 6);
                        assert(pow2(6) == 64);
                        assert(SLLEN <= 64);
                        vstd::arithmetic::logarithm::lemma_log_is_ordered(2, SLLEN as int, 64);
                    };
                    assert(Self::granularity_log2_spec() == 5) by { assert(log(2, 32) == 5) };
                    assert(fl + Self::granularity_log2_spec() < Self::sli_spec());
                } else if GRANULARITY == 16 {
                    assert(Self::sli_spec() <= 5) by {
                        Self::sli_pow2_is_sllen();
                        assert(log(2, 32) == 5);
                        assert(pow2(5) == 32);
                        assert(SLLEN <= 32);
                    };
                    assert(Self::granularity_log2_spec() == 4) by { assert(log(2, 16) == 4) };
                    assert(fl + Self::granularity_log2_spec() < Self::sli_spec());
                    assert(Self::sli_spec() <= 4);
                }
            }

            // sl_shift_amount > 0 iff 2^fl > SLLEN
            if fl + Self::granularity_log2_spec() >= Self::sli_spec() {
                //assert(idx.1 == (size - pow2(fl as nat)) / pow2(sl_shift_amount as nat) as int) by (nonlinear_arith);
                let flb = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
                let slb = flb / SLLEN as int;

                assert(pow2(Self::sli_spec() as nat) == SLLEN as nat) by {
                    Self::sli_pow2_is_sllen();
                };

                assert(flb >= SLLEN) by {
                    lemma_pow2_increases(
                        Self::sli_spec() as nat,
                        (fl + Self::granularity_log2_spec()) as nat);
                };

                idx.fl_non_zero();

                assert(slb * SLLEN == flb) by {
                    // 2^(fl+g) / 2^sli * 2^sli == 2^fl
                    // while sli < fl + g, g=GRANULARITY_LOG2
                    lemma_div_before_mult_pow2(fl + Self::granularity_log2_spec(), Self::sli_spec());
                };
                // Assuming bit-arithmetic correspoinds to following
                assert(fl == log(2, size as int / GRANULARITY as int));
                assert(sl == ((size as int) / slb) % SLLEN as int);

                assert(slb > 0) by {
                    assert(pow2(Self::sli_spec() as nat)
                        <= pow2((fl + Self::granularity_log2_spec()) as nat)) by {
                        lemma_pow2_increases(
                            Self::sli_spec() as nat,
                            (fl + Self::granularity_log2_spec()) as nat);
                    };
                    vstd::arithmetic::div_mod::lemma_div_non_zero(flb, SLLEN as int);
                };

                assert(slb * sl == size as int % flb - size as int % slb) by {
                    vstd::arithmetic::div_mod::lemma_mod_breakdown(size as int, slb, SLLEN as int);
                }

                assert(idx.block_size_range().start() <= size as int) by {
                    assert(flb + size as int % flb - size as int % slb <= size) by {
                        assert(0 <= size as int % slb);
                        assert(size as int / flb as int == 1) by {
                            lemma_pow2_log2_div_is_one(size as int);
                        };
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(size as int, flb);
                        assert(size == flb + size as int % flb);
                    }
                };

                assert(size < idx.block_size_range().end()) by {
                    assert(idx.block_size_range().end() == flb + slb * sl + slb) by {
                        vstd::arithmetic::mul::lemma_mul_is_distributive_add(slb, sl as int, 1);
                    };

                    assert(flb + (size as int % flb - size as int % slb) + slb > size) by {
                        assert(0 <= size as int % slb);
                        assert(size as int / flb as int == 1) by {
                            lemma_pow2_log2_div_is_one(size as int);
                        };
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(size as int, flb);
                        assert(size == flb + size as int % flb);
                    }
                };
            } else {
                if GRANULARITY == 32 {
                    assert(pow2((fl + Self::granularity_log2_spec()) as nat)
                        <= pow2(Self::sli_spec() as nat)) by {
                        lemma_pow2_increases(
                            (fl + Self::granularity_log2_spec()) as nat,
                            Self::sli_spec() as nat
                        );
                    };
                    assert(fl + Self::granularity_log2_spec() < Self::sli_spec()
                        ==> fl == 0 && SLLEN == 64) by {

                        assert(Self::sli_spec() <= 6) by {
                            assert(SLLEN <= 64);
                            vstd::arithmetic::logarithm::lemma_log_is_ordered(2, SLLEN as int, 64);
                            assert(log(2, SLLEN as int) == Self::sli_spec());
                            reveal(log);
                            assert(log(2, 64) == 6);
                            Self::sli_pow2_is_sllen();
                        };
                        assert(Self::granularity_log2_spec() == 5);
                        Self::sli_pow2_is_sllen();
                        assert(pow2(6) == 64) by {
                            reveal(pow2);
                            assert(pow2(6) == 64);
                        };
                        assert(pow2(Self::sli_spec() as nat) == pow2(6));
                    };
                    assert(fl == 0 ==> GRANULARITY <= size < 2*GRANULARITY) by {
                        assert(log(2, size as int) == 5) by {
                            assert(Self::granularity_log2_spec() == 5) by {
                                assert(log(2, 32) == 5);
                            };
                            assert(fl == log(2, size as int) - Self::granularity_log2_spec());

                            assert(log(2, size as int) == Self::granularity_log2_spec());
                        };
                        assert(pow2(log(2, size as int) as nat + 1) == 2*GRANULARITY) by {
                            assert(pow2(log(2, size as int) as nat + 1) == pow2(6));
                            assert(pow2(6) == 64);
                            assert(2*GRANULARITY == 2*32 == 64);
                        };
                        log2_power_in_range(size as int);
                    };

                    idx.fl_is_zero();

                    assert(fl == 0 && SLLEN == 64);
                } else if GRANULARITY == 16 {
                    assert(pow2((fl + Self::granularity_log2_spec()) as nat)
                        <= pow2(Self::sli_spec() as nat)) by {
                        lemma_pow2_increases(
                            (fl + Self::granularity_log2_spec()) as nat,
                            Self::sli_spec() as nat
                        );
                    };
                    assert(fl + Self::granularity_log2_spec() < Self::sli_spec()
                        ==> fl == 0 && SLLEN == 32) by {

                        assert(Self::sli_spec() <= 5) by {
                            assert(SLLEN <= 32);
                            vstd::arithmetic::logarithm::lemma_log_is_ordered(2, SLLEN as int, 32);
                            assert(log(2, SLLEN as int) == Self::sli_spec());
                            reveal(log);
                            assert(log(2, 16) == 4);
                            Self::sli_pow2_is_sllen();
                        };
                        assert(Self::granularity_log2_spec() == 4);
                        Self::sli_pow2_is_sllen();
                        assert(pow2(4) == 16) by {
                            reveal(pow2);
                            assert(pow2(4) == 16);
                        };
                        assert(pow2(Self::sli_spec() as nat) == pow2(5));
                    };
                    assert(fl == 0 ==> GRANULARITY <= size < 2*GRANULARITY) by {
                        assert(log(2, size as int) == 5) by {
                            assert(Self::granularity_log2_spec() == 4) by {
                                assert(log(2, 16) == 4);
                            };
                            assert(fl == log(2, size as int) - Self::granularity_log2_spec());

                            assert(log(2, size as int) == Self::granularity_log2_spec());
                        };
                        assert(pow2(log(2, size as int) as nat + 1) == 2*GRANULARITY) by {
                            assert(pow2(log(2, size as int) as nat + 1) == pow2(5));
                            assert(pow2(5) == 32);
                            assert(2*GRANULARITY == 2*16 == 32);
                        };
                        log2_power_in_range(size as int);
                    };
                    assert(fl == 0 && SLLEN == 32);
                }
                // negative case is only SLLEN=64, fl=0, GRANULARITY=32
                // instantiate it
            }
        }

       Some(idx)
    }

    spec fn map_floor_spec(size: usize) -> BlockIndex<FLLEN, SLLEN>
        recommends
            Self::parameter_validity(),
            size % GRANULARITY == 0,
            size >= GRANULARITY
    {
        let fl = log(2, size as int / GRANULARITY as int);
        let flb = pow2((fl + Self::granularity_log2_spec()) as nat);
        //pow2((self.0 + Self::granularity_log2_spec()) as nat) < SLLEN
        if flb < SLLEN {
            BlockIndex(0, 0)
        } else {
            let slb = flb as int / SLLEN as int;
            let sl = ((size as int) / slb) % SLLEN as int;
            BlockIndex(fl as usize, sl as usize)
        }
    }

    //proof fn lemma_map_floor_zero_iff_granularity(size: usize)
            //requires Self::parameter_validity(),
                //size % GRANULARITY == 0,
                //size >= GRANULARITY
            //ensures size == GRANULARITY
                //<==> Self::map_floor_spec(size) matches BlockIndex(0, 0)
    //{
        //Self::lemma_map_floor_int_at_granularity();
        //if size != GRANULARITY {
            //assert(size >= GRANULARITY);
            //let fl = log(2, size as int / GRANULARITY as int);
            //let flb = pow2((fl + Self::granularity_log2_spec()) as nat);
            //assume(flb >= SLLEN);
            //assert(size > GRANULARITY);
            //// SLLEN != usize::BITS || self.0 != 0
            //if SLLEN == usize::BITS {
            //} else {
                //assert(SLLEN < usize::BITS);
            //}
            ////assume(Self::map_floor_spec(size).0 != 0 ==> flb <= SLLEN);
            //assert(#[trigger] Self::map_floor_spec(size).0 != 0);
        //}
    //}

    proof fn lemma_map_floor_spec_wf(size: usize)
        requires
            Self::parameter_validity(),
            size % GRANULARITY == 0,
            size >= GRANULARITY,
            BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int)
        ensures
            Self::map_floor_spec(size).wf()
    {
        assert(0 <= log(2, size as int / GRANULARITY as int) < FLLEN) by {
            assert(size < (pow2(FLLEN as nat) * GRANULARITY));
            assert(size / GRANULARITY < pow2(FLLEN as nat));
            log2_is_strictly_ordered_if_rhs_is_pow2(
                size as int / GRANULARITY as int,
                pow2(FLLEN as nat) as int);
            assert(log(2, size as int / GRANULARITY as int)
                < log(2, pow2(FLLEN as nat) as int));
            assert(log(2, pow2(FLLEN as nat) as int) == FLLEN) by {
                vstd::arithmetic::power2::lemma_pow2(FLLEN as nat);
                vstd::arithmetic::logarithm::lemma_log_pow(2, FLLEN as nat);
            };

            assert(log(2, size as int / GRANULARITY as int) < FLLEN as nat);

            assert(0 <= log(2, size as int / GRANULARITY as int)) by {
                vstd::arithmetic::logarithm::lemma_log_nonnegative(2, size as int / GRANULARITY as int)
            };
        };
    }

    proof fn lemma_map_floor_spec(size: usize)
        requires
            Self::parameter_validity(),
            size % GRANULARITY == 0,
            size >= GRANULARITY,
            BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int),
            Self::map_floor_spec(size).0 + Self::granularity_log2_spec()
                >= Self::sli_spec(),
            Self::map_floor_spec(size).0 != 0
        ensures ({
            let BlockIndex(fl, sl) = Self::map_floor_spec(size);
            let flb = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
            let slb = flb / SLLEN as int;

            &&& fl == log(2, size as int / GRANULARITY as int) as usize
            &&& sl == (((size as int) / slb) % SLLEN as int) as usize
        })
    {
        Self::lemma_map_floor_spec_wf(size);
        let idx = Self::map_floor_spec(size);
        let BlockIndex(fl, sl) = idx;

        assert(0 <= fl < FLLEN);
        assert(0 <= sl < SLLEN);
        let flb = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
        let slb = flb / SLLEN as int;
        assert(0 <= log(2, size as int / GRANULARITY as int) < usize::BITS) by {
            assert(size < (pow2(FLLEN as nat) * GRANULARITY));
            assert(size / GRANULARITY < pow2(FLLEN as nat));
            log2_is_strictly_ordered_if_rhs_is_pow2(
                size as int / GRANULARITY as int,
                pow2(FLLEN as nat) as int);
            assert(log(2, size as int / GRANULARITY as int)
                < log(2, pow2(FLLEN as nat) as int));
            assert(log(2, pow2(FLLEN as nat) as int) == FLLEN) by {
                vstd::arithmetic::power2::lemma_pow2(FLLEN as nat);
                vstd::arithmetic::logarithm::lemma_log_pow(2, FLLEN as nat);
            };

            assert(log(2, size as int / GRANULARITY as int) < FLLEN as nat);

            assert(0 <= log(2, size as int / GRANULARITY as int)) by {
                vstd::arithmetic::logarithm::lemma_log_nonnegative(2,
                    size as int / GRANULARITY as int)
            };
        };

        // pow2((self.0 + Self::granularity_log2_spec()) as nat) < SLLEN
        assert(flb == pow2((fl + Self::granularity_log2_spec()) as nat));
        //assert(fl == log(2, size as int / GRANULARITY as int) as usize);
        assert(SLLEN <= flb) by {

            assert(Self::sli_spec() <= fl + Self::granularity_log2_spec());
            assume(0 <= fl + Self::granularity_log2_spec());
            assume(0 <= Self::sli_spec());

            vstd::arithmetic::power2::lemma_pow2((fl + Self::granularity_log2_spec()) as nat);
            vstd::arithmetic::power2::lemma_pow2(Self::sli_spec() as nat);
            assert(pow(2, Self::sli_spec() as nat)
                <= pow(2, (fl + Self::granularity_log2_spec()) as nat)) by {
                vstd::arithmetic::power::lemma_pow_increases(2, Self::sli_spec() as nat,
                    (fl + Self::granularity_log2_spec()) as nat);
            };

            Self::sli_pow2_is_sllen();
        };

        assert(!(flb < SLLEN));
        //vstd::arithmetic::logarithm::lemma_log_nonnegative(2,
            //size as int / GRANULARITY as int);
        let slb = flb as int / SLLEN as int;
        let sl = ((size as int) / slb) % SLLEN as int;
        assert(0 <= log(2, size as int / GRANULARITY as int) < usize::BITS);
        //assert(pow2((self.0 + Self::granularity_log2_spec()) as nat) < SLLEN);
        assert(Self::sli_spec() <= fl + Self::granularity_log2_spec());
        // SLI - log2(G) <= fl
        // log2(SLLEN / G) <= fl
        assert(sl == ((size as int) / slb) % SLLEN as int);
        //assert(fl != 0) by {
        //};

    }


    proof fn lemma_map_floor_int_bsr_contained(size: usize)
        requires
            Self::parameter_validity(),
            // FIXME: appropriatly share constant GRANULARITY between block_index
            size % GRANULARITY == 0,
            size >= GRANULARITY,
            BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int)
        ensures ({
            let BlockIndex(fl, sl) = Self::map_floor_spec(size);
            let idx = BlockIndex::<FLLEN, SLLEN>(fl as usize, sl as usize);

            &&& idx.wf()
            &&& idx.block_size_range().contains(size as int)
        })

    {
    }

    proof fn lemma_map_floor_int_at_granularity() by (nonlinear_arith)
        requires Self::parameter_validity(),
        ensures Self::map_floor_spec(GRANULARITY) matches BlockIndex(0, 0)
    {
        lemma_log2_values();
        lemma_pow2_values();
        Self::plat_basics();
        assert(GRANULARITY as int / GRANULARITY as int == 1);
        let fl = log(2, GRANULARITY as int / GRANULARITY as int);
        let flb = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
        let slb = flb / SLLEN as int;
        let sl = ((GRANULARITY as int) / slb) % SLLEN as int;
        assert(flb == GRANULARITY) by {
            assert(log(2, 1) == 0);
            assert(fl == 0);
            assert(pow2(Self::granularity_log2_spec() as nat) == GRANULARITY);
        };
        if flb >= SLLEN {
            //assert(sl == GRANULARITY as int / (GRANULARITY as int / SLLEN) % SLLEN);
            assert(GRANULARITY == pow2(Self::granularity_log2_spec() as nat));
            assert(SLLEN == pow2(Self::sli_spec() as nat));
            calc! {
                (==)
                    GRANULARITY as int
                    / (GRANULARITY as int / SLLEN as int);
                {
                    vstd::arithmetic::div_mod::lemma_div_multiples_vanish_quotient(
                        SLLEN as int,
                        GRANULARITY as int,
                        GRANULARITY as int / SLLEN as int
                    );
                }
                (GRANULARITY * SLLEN) as int
                    / (GRANULARITY as int / SLLEN as int * SLLEN) as int;
                {
                    assert(GRANULARITY as int / SLLEN as int * SLLEN == GRANULARITY) by {
                        assert(pow2(Self::granularity_log2_spec() as nat)
                            / pow2(Self::sli_spec() as nat)
                            == pow2((Self::granularity_log2_spec() as nat - Self::sli_spec() as nat) as nat)) by {
                            assert(Self::granularity_log2_spec() as nat >= Self::sli_spec() as nat) by {
                                assert(SLLEN <= GRANULARITY);
                                vstd::arithmetic::logarithm::lemma_log_is_ordered(2,
                                    SLLEN as int,
                                    GRANULARITY as int);
                                assert(log(2, SLLEN as int) <= log(2, GRANULARITY as int));
                                Self::sli_pow2_is_sllen();
                                assert(Self::sli_spec() >= 0 && Self::granularity_log2_spec() > 0);
                            };
                            vstd::arithmetic::power2::lemma_pow2_subtracts(
                                Self::sli_spec() as nat,
                                Self::granularity_log2_spec() as nat);
                        };
                        assert(pow2((Self::granularity_log2_spec() as nat - Self::sli_spec() as nat) as nat)
                            * pow2(Self::sli_spec() as nat)
                            == pow2(Self::granularity_log2_spec() as nat)) by {
                            vstd::arithmetic::power2::lemma_pow2_adds(
                                (Self::granularity_log2_spec() as nat - Self::sli_spec() as nat) as nat,
                                Self::sli_spec() as nat);
                        };
                    };
                }
                (GRANULARITY * SLLEN) as int
                    / GRANULARITY as int;
                {
                    vstd::arithmetic::div_mod::lemma_div_by_multiple(
                        GRANULARITY as int,
                        SLLEN as int);
                }
                SLLEN as int;
            }
            assert(fl == 0 && sl == 0);
        } else {
            assert(!(flb >= SLLEN));
        }
    }

    proof fn lemma_fl_fllen_le_iff_valid_size(fl: u32, size: usize)
        requires
            size >= GRANULARITY,
            size % GRANULARITY == 0,
            Self::parameter_validity(),
            fl == log(2, size as int) - Self::granularity_log2_spec()
        ensures
            fl >= FLLEN <==> !BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int)
    {
        Self::granularity_basics();
        lemma_pow2_values();
        lemma_log2_values();
        granularity_is_power_of_two();
        assert(fl >= FLLEN <==> !BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int)) by {
            Self::granularity_basics();
            assert(fl < FLLEN <==>
                BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int)) by {

                // (==>)
                // 2^fl < 2^FLLEN
                // 2^fl * G < 2^FLLEN * G
                // 2^fl * 2^log2(G) < 2^FLLEN * G
                // 2^(fl - log2(G)) < 2^FLLEN * G
                // 2^log2(size) < 2^FLLEN * G, where fl = log2(size) - log2(G)
                // size / (2^FLLEN * G) < size / 2^log2(size)
                // size / (2^FLLEN * G) < 1
                // size / (2^FLLEN * G) == 0
                // size < (2^FLLEN * G)
                if fl < FLLEN {
                    assert(size < pow2(FLLEN as nat) * GRANULARITY
                        <==> (size as int) / (GRANULARITY as int) < pow2(FLLEN as nat));
                    assert(log(2, (size as int) / (GRANULARITY as int))
                            < log(2, pow2(FLLEN as nat) as int)
                        ==> (size as int) / (GRANULARITY as int)
                            < pow2(FLLEN as nat)) by {
                        if log(2, (size as int) / (GRANULARITY as int)) < log(2, pow2(FLLEN as nat) as int) {
                            assert((size as int) / (GRANULARITY as int) > 0);
                            assert(pow2(FLLEN as nat) as int > 1) by {
                                vstd::arithmetic::power2::lemma_pow2_strictly_increases(0, FLLEN as nat);
                                assert(pow2(0) == 1);
                            };
                            log2_power_ordered((size as int) / (GRANULARITY as int), pow2(FLLEN as nat) as int);
                            assert((size as int) / (GRANULARITY as int) < pow2(FLLEN as nat));
                        }
                    }
                    assert(log(2, (size as int) / (GRANULARITY as int)) < log(2, pow2(FLLEN as nat) as int)
                        <==> log(2, (size as int) / (GRANULARITY as int)) < FLLEN) by {
                        assert(FLLEN as int == log(2, pow2(FLLEN as nat) as int)) by {
                            vstd::arithmetic::power2::lemma_pow2(FLLEN as nat);
                            vstd::arithmetic::logarithm::lemma_log_pow(2, FLLEN as nat);
                        };
                    };
                    assert(fl == log(2, size as int / GRANULARITY as int)) by {
                        lemma_log2_distributes(size as int, GRANULARITY as int)
                    }

                    assert(BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int));
                }

                assert(BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int)
                    ==> fl < FLLEN)
                by {
                    if size < GRANULARITY * pow2(FLLEN as nat) {
                        // log2 both sides
                        assert(log(2, size as int) < log(2, GRANULARITY * pow2(FLLEN as nat))) by {
                            assert(is_power_of_two(GRANULARITY * pow2(FLLEN as nat))) by {
                                vstd::arithmetic::power2::lemma_pow2_adds(
                                    Self::granularity_log2() as nat,
                                    FLLEN as nat
                                );
                            };
                            log2_is_strictly_ordered_if_rhs_is_pow2(
                                size as int,
                                GRANULARITY * pow2(FLLEN as nat)
                            );
                        };
                        assert(log(2, GRANULARITY as int) + FLLEN
                            ==  log(2, GRANULARITY * pow2(FLLEN as nat))) by {
                            lemma_log2_mul_pow2(FLLEN as nat, GRANULARITY as int);
                        };
                        assert(log(2, size as int) - Self::granularity_log2() < FLLEN);
                    }
                }
            };
        };

    }

    proof fn lemma_last_index_start_is_max_allocatable()
        requires
            Self::parameter_validity(),
        ensures
            ({
                let idx = BlockIndex::<FLLEN, SLLEN>((FLLEN - 1) as usize, (SLLEN - 1) as usize);
                &&& idx.wf()
                &&& idx.block_size_range().start() == Self::max_allocatable_size()
            })
    {
        Self::lemma_parameter_validity_implies_block_index_parameter_validity();
        assert(BlockIndex::<FLLEN, SLLEN>::parameter_validity());
        let idx = BlockIndex::<FLLEN, SLLEN>((FLLEN - 1) as usize, (SLLEN - 1) as usize);
        assert(0 < FLLEN);
        assert(0 < SLLEN);
        assert(((FLLEN - 1) as int) < (FLLEN as int));
        assert(((SLLEN - 1) as int) < (SLLEN as int));
        assert(idx.wf());

        let flb = pow2((Self::granularity_log2_spec() + FLLEN as int - 1) as nat) as int;
        assert(flb == pow2((idx.0 + Self::granularity_log2_spec()) as nat) as int);

        if pow2((idx.0 + Self::granularity_log2_spec()) as nat) < SLLEN {
            idx.fl_is_zero();
            idx.fl_zero_iff();
            assert(idx.0 == 0);
            Self::granularity_basics();
            assert(flb == GRANULARITY) by {
                assert(FLLEN == 1);
                assert(Self::granularity_log2_spec() + FLLEN as int - 1 == Self::granularity_log2_spec());
            };
            assert(flb / SLLEN as int == 0);
            assert(Self::max_allocatable_size()
                == flb + (SLLEN as int - 1) * (flb / SLLEN as int));
            assert(Self::max_allocatable_size() == flb);
            assert(idx.block_size_range().start() == GRANULARITY);
            assert(idx.block_size_range().start() == Self::max_allocatable_size());
        } else {
            idx.fl_non_zero();
            assert(idx.block_size_range().start()
                == flb + (flb / SLLEN as int) * ((SLLEN - 1) as int));
            assert(Self::max_allocatable_size()
                == flb + (SLLEN as int - 1) * (flb / SLLEN as int));
            assert(idx.block_size_range().start() == Self::max_allocatable_size());
        }
    }

    proof fn lemma_size_within_max_is_valid_block_size(size: usize)
        requires
            size >= GRANULARITY,
            size % GRANULARITY == 0,
            Self::parameter_validity(),
            size as int <= Self::max_allocatable_size(),
        ensures
            BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int)
    {
        Self::granularity_basics();
        Self::lemma_parameter_validity_implies_block_index_parameter_validity();
        let g = Self::granularity_log2_spec();
        let flb = pow2((g + FLLEN as int - 1) as nat) as int;
        let d = SLLEN as int;
        let q = flb / d;
        let r = flb % d;
        assert(0 < d);
        vstd::arithmetic::power2::lemma_pow2_pos((g + FLLEN as int - 1) as nat);
        assert(0 < flb);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(flb, d);
        assert(flb == q * d + r);
        assert(0 <= r);
        assert(r < d);
        assert(q * d <= flb) by (nonlinear_arith);
        assert(0 <= q) by (nonlinear_arith);
        assert((d - 1) * q < flb) by {
            assert((d - 1) * q <= d * q) by (nonlinear_arith);
            assert(d * q <= flb) by (nonlinear_arith);
            if q == 0 {
                assert((d - 1) * q == 0);
                assert(0 < flb);
            } else {
                assert((d - 1) * q < d * q) by (nonlinear_arith);
            }
        };
        assert(Self::max_allocatable_size() == flb + (d - 1) * q);
        assert(Self::max_allocatable_size() < flb + flb) by (nonlinear_arith);
        assert(flb + flb == (pow2(FLLEN as nat) as int) * (GRANULARITY as int)) by {
            assert(GRANULARITY as int == pow2(g as nat));
            assert(pow2((g + FLLEN as int) as nat) as int
                == (pow2(FLLEN as nat) as int) * (pow2(g as nat) as int)) by {
                vstd::arithmetic::power2::lemma_pow2_adds(FLLEN as nat, g as nat);
            };
            assert(pow2((g + FLLEN as int) as nat) as int == flb + flb) by {
                assert(g + FLLEN as int == g + FLLEN as int - 1 + 1);
                vstd::arithmetic::power2::lemma_pow2_unfold((g + FLLEN as int) as nat);
            };
        };
        let max_valid = (pow2(FLLEN as nat) as int) * (GRANULARITY as int);
        assert((size as int) < max_valid) by (nonlinear_arith);
        assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int));
    }

    proof fn fl_not_underflow(size: usize)
        requires
            Self::parameter_validity(),
            size % GRANULARITY == 0,
            size >= GRANULARITY
        ensures
            Self::granularity_log2_spec() + usize_leading_zeros(size) < usize::BITS
    {
        Self::granularity_basics();
        assert(usize_leading_zeros(size) + usize_trailing_zeros(size) < usize::BITS);
        // NOT nessecessarily equality
        // proving trailing_zeros(size) >= trailing_zeros(G)
        // then
        // leading_zeros(size) + trailing_zeros(size) >= trailing_zeros(G) + leading_zeros(size)
        // we have leading_zeros(size) + trailing_zeros(size) < 64
        // thus trailing_zeros(G) + leading_zeros(size) < 64
        assert(usize_trailing_zeros(size) >= usize_trailing_zeros(GRANULARITY)) by {
            assert(size == (size / GRANULARITY) * GRANULARITY);
            lemma_usize_trailing_zero_be_log2(size, (size / GRANULARITY) as nat, Self::granularity_log2_spec() as nat);
        };
        assert(Self::granularity_log2_spec() == usize_trailing_zeros(GRANULARITY));
    }
}
#[inline(always)]
#[verifier::external_body]
#[verifier::when_used_as_spec(bool_to_usize_spec)]
fn bool_to_usize(b: bool) -> (r: usize)
    ensures
        b ==> r == 1,
        !b ==> r == 0
{
    b as usize
}

spec fn bool_to_usize_spec(b: bool) -> usize {
    if b {
        1
    } else {
        0
    }
}


}
