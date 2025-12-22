use vstd::prelude::*;

verus! {


use crate::{
    Tlsf, GRANULARITY
};
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
                idx.block_size_range().start() <= size as int
                //&& exists|i: BlockIndex<FLLEN,SLLEN>| i.block_size_range().contains(size)
                    //&& idx == i.suc()
            } else {
                r is None
            }
        })
    {
        assert(GRANULARITY < usize::BITS);
        // subtracting `Self::granularity_log2()` because actual freelist starts from `2^Self::granularity_log2()`
        let mut fl = usize::BITS - Self::granularity_log2() - 1 - size.leading_zeros();
        assert(fl == log(2, size as int) - log(2, GRANULARITY as int)); // TODO

        // The shift amount can be negative, and rotation lets us handle both
        // cases without branching.
        // negative case can occur when all of following holds
        // - fl == 0
        //   - log2(size) == GRANULARITY_LOG2 i.e. size == GRANULARITY
        // - SLI > GRANULARITY_LOG2 i.e. SLLEN > GRANULARITY
        // 
        // FIXME: guessing the negative case is for treating this specific case
        // FIXME(if i wrong):  the negative case occurs only when
        //                     requested size is GRANULARITY (i.e. fl=0)
        //      - Supposing 64bit platform, SLI <= 6 and GRANULARITY_LOG2 = 5.
        //        thus when `SLI > fl + GRANULARITY_LOG2` holds, fl must be 0
        //      - Supposing 32bit platform, SLI <= 5 and GRANULARITY_LOG2 = 4.
        //        thus when `SLI > fl + GRANULARITY_LOG2` holds, fl must be 0
        //      - Generally SLI <= log2(sizeof(usize)*8) = log2(sizeof(usize)) + 3 and
        //        GRANULARITY_LOG2 = log2(sizeof(usize)*4) = log2(sizeof(usize)) + 2
        //        thus when `SLI > fl + GRANULARITY_LOG2`
        //        (i.e. `3 > fl + 2`) holds, fl must be 0
        //
        // (NOTE: this *is* unusual case! target usecase configured as SLLEN = 64)
        let mut sl = size.rotate_right((fl + Self::granularity_log2()).wrapping_sub(Self::sli()));

        // The most significant one of `size` should be now at `sl[SLI]`
        assert(((sl >> Self::sli()) & 1) == 1);

        // Underflowed digits appear in `sl[SLI + 1..USIZE-BITS]`. They should
        // be rounded up
        // NOTE:
        // - `sl & (SLLEN - 1)` mask with second-level index set (sl[0..=SLI]
        // - because of rotating, if above underflowed, there bits present in sl[SLI+1..]
        //   so round up
        // NOTE: underflowed digits means reminder of dividing size by second-level block size
        //       thus they must be rounded up to return appropriate index for allocating from
        // TODO: how to formalize this?
        sl = (sl & (SLLEN - 1)) + bool_to_usize(sl >= (1 << (Self::sli() + 1)));

        // if sl[SLI] { fl += 1; sl = 0; }
        fl = fl + (sl >> Self::sli()) as u32;

        if fl as usize >= FLLEN {
            return None;
        }

        Some(BlockIndex(fl as usize, sl & (SLLEN - 1)))
    }

    #[inline(always)]
    pub fn map_floor(size: usize) -> (r: Option<BlockIndex<FLLEN, SLLEN>>)
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

        assert(Self::parameter_validity());

        assert(fl >= FLLEN <==> !BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int)) by {
            Self::lemma_fl_fllen_le_iff_valid_size(fl, size);
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
            assert(Self::map_floor_int(size) == idx) by {
                assert(fl + Self::granularity_log2_spec() >= Self::sli_spec()
                    ==> pow2((fl + Self::granularity_log2_spec()) as nat) >= SLLEN) by {
                    if fl + Self::granularity_log2_spec() >= Self::sli_spec() {
                        vstd::arithmetic::power::lemma_pow_increases(2,
                            Self::sli_spec() as nat,
                            (fl + Self::granularity_log2_spec()) as nat);
                        vstd::arithmetic::power2::lemma_pow2((fl + Self::granularity_log2_spec()) as nat);
                        vstd::arithmetic::power2::lemma_pow2(Self::sli_spec() as nat);
                        Self::sli_pow2_is_sllen();
                        assert(pow2((fl + Self::granularity_log2_spec()) as nat) >= SLLEN);
                    }
                };
                if fl + Self::granularity_log2_spec() >= Self::sli_spec()  {

                    let flb = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
                    let slb = flb / SLLEN as int;
                    assert(fl == log(2, size as int / GRANULARITY as int)) by {
                        lemma_log2_distributes(size as int, GRANULARITY as int)
                    };
                    assert(sl == ((size as int) / slb) % SLLEN as int) by {
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
                            (size >> sl_shift_amount) & low_mask_usize(Self::sli_spec() as nat); {}
                            (size >> sl_shift_amount) & (SLLEN - 1) as usize;
                        }

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

                        assert((size >> sl_shift_amount) & (SLLEN - 1) as usize
                            == (size as int /
                                (pow2((fl + Self::granularity_log2_spec() - Self::sli_spec()) as nat)) as int)
                            % SLLEN as int) by {

                            assert(sl == (size >> sl_shift_amount) & (SLLEN - 1) as usize);
                            assert(size > 0);
                            vstd::arithmetic::power2::lemma_pow2_pos((fl + Self::granularity_log2_spec()
                                    - Self::sli_spec()) as nat);

                            bit_mask_is_mod_for_pow2(size >> sl_shift_amount, SLLEN);
                        };
                    };
                } else {
                    Self::plat_basics();

                    assert(pow2((fl + Self::granularity_log2_spec()) as nat)
                        <= pow2(Self::sli_spec() as nat)) by {
                        lemma_pow2_increases(
                            (fl + Self::granularity_log2_spec()) as nat,
                            Self::sli_spec() as nat
                        );
                    };
                    if usize::BITS == 64 {
                        assert(fl + Self::granularity_log2_spec() < Self::sli_spec()
                            ==> fl == 0 && SLLEN == 64);
                        assert(fl == 0 ==> GRANULARITY <= size < 2*GRANULARITY) by {
                            assert(pow2(log(2, size as int) as nat + 1) == 2*GRANULARITY) by {
                                assert(pow2(log(2, size as int) as nat + 1) == pow2(6));
                                assert(pow2(6) == 64);
                                assert(2*GRANULARITY == 2*32 == 64);
                            };
                            log2_power_in_range(size as int);
                        };

                        idx.fl_is_zero();

                        assert(fl == 0 && SLLEN == 64);

                        assert(size == GRANULARITY);
                        assert(sl_shift_amount == -1) by {
                            assert(Self::granularity_log2() == 5);
                            assert(Self::sli() == 6) by {
                                Self::sli_pow2_is_sllen();
                                vstd::arithmetic::logarithm::lemma_log_pow(2, SLLEN as nat);
                                reveal(log);
                                assert(SLLEN == 64);
                                assert(log(2, 64 as int) == 6) by (compute);
                            };
                            assert(4294967295 as i32 == -1) by (bit_vector);
                            assert((5u32.wrapping_sub(6) as i32) == -1) by (compute);
                            assert(-1 == ((fl + Self::granularity_log2()) as u32).wrapping_sub(Self::sli()) as i32);
                        };
                        assert(usize_rotate_right(GRANULARITY, sl_shift_amount) == GRANULARITY << 1) by {
                            assert(sl_shift_amount < 0);
                            reveal(pow2);
                            reveal(pow);
                            assert(GRANULARITY << 1 == 32 << 1) by {
                                assert(GRANULARITY == 32);
                                assert(GRANULARITY << 1 == GRANULARITY * 2) by {
                                    vstd::bits::lemma_u64_shl_is_mul(GRANULARITY as u64, 1);
                                };
                                assert(32 << 1 == 32 * 2) by (bit_vector);
                                assert(Self::parameter_validity());
                                Self::plat_basics();
                            };
                            assert(sl_shift_amount == -1i32);
                            assert(usize_rotate_right(32, -1i32) == 32 << 1) by (compute);

                            // (32 & (pow2(63) - 1) as nat) << 1 | (32 & !((pow2(1) - 1) as nat)) >> 63
                        };
                        assert((GRANULARITY << 1) & (SLLEN - 1) as usize == 0) by {
                            vstd::bits::lemma_u64_shl_is_mul(GRANULARITY as u64, 1);
                            assert((GRANULARITY << 1) == 64 && SLLEN == 64);
                            assert(64 & (64 - 1) as usize == 0) by (bit_vector);
                        };

                        assert(sl == 0);

                        Self::lemma_map_floor_int_at_granularity();
                    } else if usize::BITS == 32 {
                        assert(fl + Self::granularity_log2_spec() < Self::sli_spec()
                            ==> fl == 0 && SLLEN == 32);
                        assert(fl == 0 ==> GRANULARITY <= size < 2*GRANULARITY) by {
                            assert(pow2(log(2, size as int) as nat + 1) == 2*GRANULARITY) by {
                                assert(pow2(log(2, size as int) as nat + 1) == pow2(5));
                                assert(pow2(4) == 16);
                                assert(2*GRANULARITY == 2*16 == 32);
                            };
                            log2_power_in_range(size as int);
                        };

                        idx.fl_is_zero();

                        assert(fl == 0 && SLLEN == 32);

                        assert(size == GRANULARITY);
                        assert(sl_shift_amount == -1) by {
                            assert(Self::granularity_log2() == 5);
                            assert(Self::sli() == 6) by {
                                Self::sli_pow2_is_sllen();
                                vstd::arithmetic::logarithm::lemma_log_pow(2, SLLEN as nat);
                                reveal(log);
                                assert(SLLEN == 32);
                                assert(log(2, 32 as int) == 5) by (compute);
                            };
                            assert(4294967295 as i32 == -1) by (bit_vector);
                            assert((4u32.wrapping_sub(5) as i32) == -1) by (compute);
                            assert(-1 == ((fl + Self::granularity_log2()) as u32).wrapping_sub(Self::sli()) as i32);
                        };
                        assert(usize_rotate_right(GRANULARITY, sl_shift_amount) == GRANULARITY << 1) by {
                            assert(sl_shift_amount < 0);
                            reveal(pow2);
                            reveal(pow);
                            assert(GRANULARITY << 1 == 16 << 1) by {
                                assert(GRANULARITY == 16);
                                assert(GRANULARITY << 1 == GRANULARITY * 2) by {
                                    vstd::bits::lemma_u64_shl_is_mul(GRANULARITY as u64, 1);
                                };
                                assert(32 << 1 == 32 * 2) by (bit_vector);
                                assert(Self::parameter_validity());
                                Self::plat_basics();
                            };
                            assert(sl_shift_amount == -1i32);
                            assert(usize_rotate_right(16, -1i32) == 16 << 1) by (compute);
                        };
                        assert((GRANULARITY << 1) & (SLLEN - 1) as usize == 0) by {
                            vstd::bits::lemma_u64_shl_is_mul(GRANULARITY as u64, 1);
                            assert((GRANULARITY << 1) == 32 && SLLEN == 32);
                            assert(32 & (32 - 1) as usize == 0) by (bit_vector);
                        };

                        assert(sl == 0);

                        Self::lemma_map_floor_int_at_granularity();
                    }
                    // negative case is only SLLEN=64, fl=0, GRANULARITY=32
                    // instantiate it
                }
            }

            // sl_shift_amount > 0 iff 2^fl > SLLEN
            if fl + Self::granularity_log2_spec() >= Self::sli_spec() {
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
                assert(Self::map_floor_int(size) matches BlockIndex(fl, sl));
                Self::lemma_map_floor_int(size);

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
                Self::plat_basics();
                if usize::BITS == 64 {
                    assert(pow2((fl + Self::granularity_log2_spec()) as nat)
                        <= pow2(Self::sli_spec() as nat)) by {
                        lemma_pow2_increases(
                            (fl + Self::granularity_log2_spec()) as nat,
                            Self::sli_spec() as nat
                        );
                    };
                    assert(fl + Self::granularity_log2_spec() < Self::sli_spec()
                        ==> fl == 0 && SLLEN == 64);
                    assert(fl == 0 ==> GRANULARITY <= size < 2*GRANULARITY) by {
                        assert(pow2(log(2, size as int) as nat + 1) == 2*GRANULARITY) by {
                            assert(pow2(log(2, size as int) as nat + 1) == pow2(6));
                            assert(pow2(6) == 64);
                            assert(2*GRANULARITY == 2*32 == 64);
                        };
                        log2_power_in_range(size as int);
                    };

                    idx.fl_is_zero();

                    assert(fl == 0 && SLLEN == 64);
                } else if usize::BITS == 32 {
                    assert(pow2((fl + Self::granularity_log2_spec()) as nat)
                        <= pow2(Self::sli_spec() as nat)) by {
                        lemma_pow2_increases(
                            (fl + Self::granularity_log2_spec()) as nat,
                            Self::sli_spec() as nat
                        );
                    };
                    assert(fl + Self::granularity_log2_spec() < Self::sli_spec()
                        ==> fl == 0 && SLLEN == 32);
                    assert(fl == 0 ==> GRANULARITY <= size < 2*GRANULARITY) by {
                        assert(log(2, size as int) == 5) by {
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

    spec fn map_floor_int(size: usize) -> BlockIndex<FLLEN, SLLEN>
        recommends
            Self::parameter_validity(),
            size % GRANULARITY == 0,
            size >= GRANULARITY
    {
        let fl = log(2, size as int / GRANULARITY as int);
        let flb = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
        if flb >= SLLEN {
            let slb = flb / SLLEN as int;
            let sl = ((size as int) / slb) % SLLEN as int;
            BlockIndex(fl as usize, sl as usize)
        } else {
            BlockIndex(0, 0)
        }
    }

    proof fn lemma_map_floor_int_wf(size: usize)
        requires
            Self::parameter_validity(),
            // FIXME: appropriatly share constant GRANULARITY between block_index
            size % GRANULARITY == 0,
            size >= GRANULARITY,
            BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int)
        ensures
            Self::map_floor_int(size) matches BlockIndex(fl, sl) &&
                BlockIndex::<FLLEN, SLLEN>(fl as usize, sl as usize).wf()
    {
        admit()
    }

    proof fn lemma_map_floor_int(size: usize)
        requires
            Self::parameter_validity(),
            size % GRANULARITY == 0,
            size >= GRANULARITY,
            BlockIndex::<FLLEN,SLLEN>::valid_block_size(size as int)
        ensures ({
            let BlockIndex(fl, sl) = Self::map_floor_int(size);
            if Self::map_floor_int(size).fl_zero_cond() {
                fl == 0 && sl == 0
            } else { 
                let flb = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
                let slb = flb / SLLEN as int;
                &&& fl == log(2, size as int / GRANULARITY as int) as usize
                &&& sl == (((size as int) / slb) % SLLEN as int) as usize
            }
        })
    {
        Self::lemma_map_floor_int_wf(size);
        let idx = Self::map_floor_int(size);
        let BlockIndex(fl, sl) = idx;

        let flb = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
        let slb = flb / SLLEN as int;
        assume(flb >= SLLEN <==> !idx.fl_zero_cond());
        assume(0 <= log(2, size as int / GRANULARITY as int) < FLLEN);
        if idx.fl_zero_cond() {
            idx.fl_zero_iff();
            //assert(size == GRANULARITY);
        } else {
            // FIXME: SMT transcript looks identical but cannot prove this
            assume(fl == log(2, size as int / GRANULARITY as int) as usize);
        }
    }


    proof fn lemma_map_floor_int_bsr_contained(size: usize)
        requires
            Self::parameter_validity(),
            // FIXME: appropriatly share constant GRANULARITY between block_index
            size % GRANULARITY == 0,
            size >= GRANULARITY,
            BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int)
        ensures ({
            let BlockIndex(fl, sl) = Self::map_floor_int(size);
            let idx = BlockIndex::<FLLEN, SLLEN>(fl as usize, sl as usize);

            &&& idx.wf()
            &&& idx.block_size_range().contains(size as int)
        })

    {
    }

    proof fn lemma_map_floor_int_at_granularity() by (nonlinear_arith)
        requires Self::parameter_validity(),
        ensures Self::map_floor_int(GRANULARITY) matches BlockIndex(0, 0)
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

                            calc! {
                                (==)
                                log(2, GRANULARITY as int * pow2(FLLEN as nat)); {
                                    assert(GRANULARITY as int * pow2(FLLEN as nat)
                                        == pow2((Self::granularity_log2() + FLLEN) as nat)) by {
                                        vstd::arithmetic::power2::lemma_pow2_adds(
                                            Self::granularity_log2() as nat,
                                            FLLEN as nat
                                        );
                                    }
                                }
                                log(2, pow2((Self::granularity_log2() + FLLEN) as nat) as int); {
                                    vstd::arithmetic::power2::lemma_pow2(
                                        (Self::granularity_log2() + FLLEN) as nat
                                    );
                                    vstd::arithmetic::logarithm::lemma_log_pow(
                                        2,
                                        (Self::granularity_log2() + FLLEN) as nat
                                    );
                                }
                                Self::granularity_log2() as int + FLLEN as int;
                            }
                        };
                        assert(log(2, size as int) - Self::granularity_log2() < FLLEN);
                    }
                }
            };
        };

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
fn bool_to_usize(b: bool) -> (r: usize)
    ensures
        b ==> r == 1,
        !b ==> r == 0
{
    b as usize
}


}
