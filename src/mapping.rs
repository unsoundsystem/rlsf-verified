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
        // Preliminary proofs
        proof {
            lemma_pow2_values();
            lemma_log2_values();
            Self::lemma_size_within_max_is_valid_block_size(size);
        }
        assert(Self::granularity_log2_spec() + usize_leading_zeros(size) < 64) by {
            Self::fl_not_underflow(size);
        };
        proof { granularity_is_power_of_two(); }

        // FL computation
        let mut fl = usize::BITS - Self::granularity_log2() - 1 - size.leading_zeros();
        assert(fl == log(2, size as int) - Self::granularity_log2()) by {
            log2_using_leading_zeros_usize(size);
            assert(fl == usize::BITS - Self::granularity_log2() - 1 - usize_leading_zeros(size));
            assert(log(2, size as int) == usize::BITS - usize_leading_zeros(size) - 1);
        };

        // SL via rotation
        let mut sl = size.rotate_right((fl + Self::granularity_log2()).wrapping_sub(Self::sli()));

        // Save ghost floor values
        let ghost fl_floor: u32 = fl;
        let ghost sl_raw: usize = sl;
        let ghost sl_shift_amount: i32 = ((fl + Self::granularity_log2()) as int - Self::sli() as int) as i32;
        let ghost sl_floor_usize: usize = sl_raw & (SLLEN - 1) as usize;
        let ghost sl_floor_val: int = sl_floor_usize as int;

        // Establish floor mapping correctness
        // Prove fl_floor < FLLEN
        assert(fl_floor >= FLLEN <==> !BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int)) by {
            Self::lemma_fl_fllen_le_iff_valid_size(fl_floor, size);
        };
        assert(BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int));
        assert(fl_floor < FLLEN);

        // Prove sl_floor_val is in range
        proof {
            mask_higher_bits_leq_mask(sl_raw, SLLEN);
        }
        assert(0 <= sl_floor_val < SLLEN as int);

        // Prove sl_floor_val = (size / slb) % SLLEN (same calc! as map_floor)
        proof {
            Self::granularity_basics();
            assert(fl_floor == log(2, size as int) - Self::granularity_log2_spec());
            assert(Self::granularity_log2() == Self::granularity_log2_spec());

            assert(Self::sli_spec() >= 0) by {
                vstd::arithmetic::logarithm::lemma_log_nonnegative(2, SLLEN as int);
            };
            assert(Self::granularity_log2_spec() >= 0) by {
                vstd::arithmetic::logarithm::lemma_log_nonnegative(2, GRANULARITY as int);
            };

            if fl_floor + Self::granularity_log2_spec() >= Self::sli_spec() {
                let flb = pow2((fl_floor + Self::granularity_log2_spec()) as nat) as int;
                let slb = flb / SLLEN as int;

                assert(fl_floor == log(2, size as int / GRANULARITY as int)) by {
                    lemma_log2_distributes(size as int, GRANULARITY as int)
                };

                assert(sl_floor_val == ((size as int) / slb) % SLLEN as int) by {
                    assert(usize_rotate_right(size, sl_shift_amount) & low_mask_usize((usize::BITS - sl_shift_amount) as nat) as usize
                        == (size >> sl_shift_amount) & low_mask_usize((usize::BITS - sl_shift_amount) as nat) as usize) by {
                        lemma_usize_rotr_mask_lower(size, sl_shift_amount);
                    };
                    assert(sl_floor_usize == (size >> sl_shift_amount) & (SLLEN - 1) as usize) by {
                        assert(SLLEN - 1 == low_mask_usize(Self::sli_spec() as nat)) by {
                            Self::sli_pow2_is_sllen();
                            assert(SLLEN - 1 == pow2(Self::sli_spec() as nat) - 1);
                        };

                        calc! {
                            (==)
                            sl_floor_usize; {}

                            usize_rotate_right(size, sl_shift_amount) & (SLLEN - 1) as usize;
                            {
                                assert(fl_floor + Self::granularity_log2_spec() <= usize::BITS);
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
                                assert(fl_floor + Self::granularity_log2_spec() <= usize::BITS);
                                lemma_duplicate_low_mask_usize(
                                    size >> sl_shift_amount,
                                    Self::sli_spec() as nat,
                                    (usize::BITS - sl_shift_amount) as nat
                                );
                            }
                            (size >> sl_shift_amount) & low_mask_usize(Self::sli_spec() as nat);
                        }
                    };

                    assert((size >> sl_shift_amount) & (SLLEN - 1) as usize == (size >> sl_shift_amount) % SLLEN) by {
                        bit_mask_is_mod_for_pow2(size >> sl_shift_amount, SLLEN);
                    };
                    assert(slb == pow2((fl_floor + Self::granularity_log2_spec() - Self::sli_spec()) as nat)) by {
                        assert(SLLEN == pow2(Self::sli_spec() as nat)) by { Self::sli_pow2_is_sllen() };
                        assert(pow2((fl_floor + Self::granularity_log2_spec()) as nat) / SLLEN as nat
                                == pow2((fl_floor + Self::granularity_log2_spec() - Self::sli_spec()) as nat)) by {
                            lemma_pow2_div_sub(
                                Self::sli_spec() as nat,
                                (fl_floor + Self::granularity_log2_spec()) as nat
                            );
                        };
                    };
                    assert(size >> sl_shift_amount
                        == (size as nat /
                            (pow2((fl_floor + Self::granularity_log2_spec()
                                   - Self::sli_spec()) as nat))))
                    by {
                        assert(0 <= sl_shift_amount < 64);
                        assert(sl_shift_amount == fl_floor + Self::granularity_log2_spec()
                                   - Self::sli_spec());
                        lemma_usize_shr_is_div(size, sl_shift_amount as usize);
                    };
                    assert(size > 0);
                    vstd::arithmetic::power2::lemma_pow2_pos((fl_floor + Self::granularity_log2_spec()
                                   - Self::sli_spec()) as nat);

                    assert((size >> sl_shift_amount) & (SLLEN - 1) as usize
                        == (size as int /
                            (pow2((fl_floor + Self::granularity_log2_spec() - Self::sli_spec()) as nat)) as int)
                        % SLLEN as int);
                };
            }
        }

        // Call lemma_floor_index_contains_size
        proof {
            if fl_floor + Self::granularity_log2_spec() >= Self::sli_spec() {
                // non-fl_zero: sl_floor_val = (size / slb) % SLLEN already proven
                Self::lemma_floor_index_contains_size(size, fl_floor as int, sl_floor_val);
            } else {
                // fl_zero case: size == GRANULARITY, same as map_floor
                if GRANULARITY == 32 {
                    assert(Self::sli_spec() <= 6) by {
                        Self::sli_pow2_is_sllen();
                        assert(log(2, 64) == 6);
                        assert(pow2(6) == 64);
                        assert(SLLEN <= 64);
                        vstd::arithmetic::logarithm::lemma_log_is_ordered(2, SLLEN as int, 64);
                    };
                    assert(Self::granularity_log2_spec() == 5) by { assert(log(2, 32) == 5) };
                } else if GRANULARITY == 16 {
                    assert(Self::sli_spec() <= 5) by {
                        Self::sli_pow2_is_sllen();
                        assert(log(2, 32) == 5);
                        assert(pow2(5) == 32);
                        assert(SLLEN <= 32);
                    };
                    assert(Self::granularity_log2_spec() == 4) by { assert(log(2, 16) == 4) };
                }
                assert(fl_floor == 0usize);
                assert(fl_floor == log(2, size as int / GRANULARITY as int)) by {
                    lemma_log2_distributes(size as int, GRANULARITY as int);
                };
                assert(size as int / GRANULARITY as int == 1) by {
                    assert(log(2, size as int / GRANULARITY as int) == 0);
                    assert(size as int / GRANULARITY as int >= 1);
                    if size as int / GRANULARITY as int >= 2 {
                        vstd::arithmetic::logarithm::lemma_log_is_ordered(
                            2, 2, size as int / GRANULARITY as int
                        );
                        assert(log(2, 2) >= 1);
                    }
                };
                assert(size == GRANULARITY);

                // sl_floor_val for fl_zero: prove from concrete rotation
                lemma_low_mask_u64_values();
                assert(high_mask_u64(1) == !low_mask_u64(1));
                assert(!0x1u64 == 0xfffffffffffffffeu64) by(bit_vector);
                if GRANULARITY == 32 {
                    assert(Self::sli_spec() == 6);
                    assert(SLLEN == 64) by { Self::sli_pow2_is_sllen(); };
                    assert(5u32.wrapping_sub(6u32) == u32::MAX);
                    assert(u32::MAX as i32 == -1i32) by(bit_vector);
                    assert(low_mask_u64(63) == 0x7fffffffffffffffu64);
                    assert(
                        ((32u64 & 0x7fffffffffffffffu64) << 1u64)
                        | ((32u64 & 0xfffffffffffffffeu64) >> 63u64)
                        == 64u64
                    ) by(bit_vector);
                    assert(usize_rotate_right(32, -1i32) == 64usize);
                    assert((64usize & 63usize) == 0usize) by(bit_vector);
                    assert(sl_floor_val == 0);
                } else if GRANULARITY == 16 {
                    assert(Self::sli_spec() == 5);
                    assert(SLLEN == 32) by { Self::sli_pow2_is_sllen(); };
                    assert(4u32.wrapping_sub(5u32) == u32::MAX);
                    assert(u32::MAX as i32 == -1i32) by(bit_vector);
                    assert(low_mask_u64(63) == 0x7fffffffffffffffu64);
                    assert(
                        ((16u64 & 0x7fffffffffffffffu64) << 1u64)
                        | ((16u64 & 0xfffffffffffffffeu64) >> 63u64)
                        == 32u64
                    ) by(bit_vector);
                    assert(usize_rotate_right(16, -1i32) == 32usize);
                    assert((32usize & 31usize) == 0usize) by(bit_vector);
                    assert(sl_floor_val == 0);
                }
                Self::lemma_floor_index_contains_size(size, 0, 0);
            }
        }
        // Now have: floor_idx.wf() && floor_idx.block_size_range().contains(size)
        // where floor_idx = BlockIndex(fl_floor as usize, sl_floor_val as usize)

        // Ceiling arithmetic
        // Ghost ceiling value (computed from the original sl_raw before mutation)
        let ghost needs_ceil: usize = bool_to_usize_spec(sl_raw >= (1usize << (Self::sli() + 1)));

        // The most significant one of `size` should be now at `sl[SLI]`
        // Underflowed digits appear in `sl[SLI + 1..USIZE-BITS]`. They should
        // be rounded up
        sl = (sl & (SLLEN - 1)) + bool_to_usize(sl >= (1 << (Self::sli() + 1))) as usize;

        // After ceiling adjustment: sl = sl_floor_usize + needs_ceil
        // sl_floor_usize < SLLEN, needs_ceil ∈ {0,1}, so sl ≤ SLLEN
        proof {
            assert(sl == sl_floor_usize + needs_ceil);
            assert(sl <= SLLEN);
            // sl >> sli ≤ 1 (since sl ≤ SLLEN = pow2(sli))
            assert(sl >> Self::sli() <= 1usize) by {
                Self::sli_pow2_is_sllen();
                assert(SLLEN == pow2(Self::sli_spec() as nat));
                lemma_usize_shr_is_div(sl, Self::sli() as usize);
                vstd::arithmetic::power2::lemma_pow2_pos(Self::sli_spec() as nat);
                vstd::arithmetic::div_mod::lemma_div_is_ordered(
                    sl as int, SLLEN as int, pow2(Self::sli_spec() as nat) as int);
                assert(sl as int / pow2(Self::sli_spec() as nat) as int
                    <= SLLEN as int / pow2(Self::sli_spec() as nat) as int);
                assert(SLLEN as int / pow2(Self::sli_spec() as nat) as int == 1);
            };
            // fl_floor < FLLEN ≤ usize::BITS ≤ 64, so fl_floor + 1 ≤ 65 < u32::MAX
            Self::lemma_parameter_validity_implies_block_index_parameter_validity();
            assert(FLLEN <= usize::BITS);
            assert(fl_floor < usize::BITS);
            let ghost fl_val: int = fl as int;
            let ghost carry_val: int = (sl >> Self::sli()) as int;
            assert(fl_val + carry_val < 4294967296);
        }

        // if sl[SLI] { fl += 1; sl = 0; }
        fl += (sl >> Self::sli()) as u32;

        // `fl` must be in a valid range
        if fl as usize >= FLLEN {
            proof {
                // Prove this branch is unreachable (contradiction).
                // Establish: fl = fl_floor + (sl >> sli), where sl = sl_floor_usize + needs_ceil.
                let ghost carry: u32 = (sl >> Self::sli()) as u32;
                assert(fl == fl_floor + carry);
                assert(carry <= 1);

                // fl >= FLLEN and fl_floor < FLLEN, so carry == 1.
                assert(carry == 1);
                assert(fl_floor + 1 >= FLLEN);
                assert(fl_floor == FLLEN - 1);

                // carry == 1 means sl >> sli >= 1, i.e., sl >= SLLEN.
                // sl = sl_floor_usize + needs_ceil, sl_floor_usize < SLLEN, needs_ceil ∈ {0,1}.
                // So needs_ceil == 1 and sl_floor_usize == SLLEN - 1.
                assert(sl >> Self::sli() >= 1usize);
                Self::sli_pow2_is_sllen();
                lemma_usize_shr_is_div(sl, Self::sli() as usize);
                assert(sl as nat / pow2(Self::sli_spec() as nat) >= 1);
                vstd::arithmetic::power2::lemma_pow2_pos(Self::sli_spec() as nat);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(sl as int, pow2(Self::sli_spec() as nat) as int);
                assert(sl >= SLLEN);
                assert(sl == sl_floor_usize + needs_ceil);
                assert(sl_floor_usize < SLLEN);
                assert(needs_ceil == 1);
                assert(sl_floor_usize == (SLLEN - 1) as usize);
                assert(sl_floor_val == SLLEN - 1);

                // The floor index is the last bin.
                let floor_idx = BlockIndex::<FLLEN, SLLEN>((FLLEN - 1) as usize, (SLLEN - 1) as usize);

                // floor.start == max_allocatable_size
                Self::lemma_last_index_start_is_max_allocatable();
                assert(floor_idx.block_size_range().start() == Self::max_allocatable_size());

                // floor contains size => floor.start <= size
                // (already established above via lemma_floor_index_contains_size)
                assert(floor_idx.block_size_range().contains(size as int));
                assert(floor_idx.block_size_range().start() <= size);

                // Combined with size <= max_allocatable_size:
                assert(size as int == Self::max_allocatable_size());
                assert(size as int == floor_idx.block_size_range().start());

                // Now show needs_ceil == 0 (contradiction with needs_ceil == 1).
                // size == floor.start means size is at an exact bin boundary.
                // In the non-fl_zero case: floor.start = flb + slb * sl_floor
                // where flb = slb * SLLEN, so floor.start % slb == 0, hence size % slb == 0.
                if fl_floor + Self::granularity_log2_spec() >= Self::sli_spec() {
                    let flb = pow2((fl_floor + Self::granularity_log2_spec()) as nat) as int;
                    let slb = flb / SLLEN as int;

                    assert(pow2((fl_floor + Self::granularity_log2_spec()) as nat) >= SLLEN) by {
                        Self::sli_pow2_is_sllen();
                        lemma_pow2_increases(Self::sli_spec() as nat, (fl_floor + Self::granularity_log2_spec()) as nat);
                    };
                    floor_idx.fl_non_zero();
                    assert(floor_idx.block_size_range().start()
                        == flb + slb * (SLLEN - 1) as int);

                    // size = flb + slb * (SLLEN - 1), and flb = slb * SLLEN
                    assert(slb > 0) by {
                        vstd::arithmetic::div_mod::lemma_div_non_zero(flb, SLLEN as int);
                    };

                    assert(slb * SLLEN == flb) by {
                        Self::sli_pow2_is_sllen();
                        lemma_div_before_mult_pow2(
                            fl_floor + Self::granularity_log2_spec(),
                            Self::sli_spec());
                    };

                    assert((size as int) % slb == 0) by (nonlinear_arith)
                        requires
                            size as int == flb + slb * (SLLEN - 1) as int,
                            flb == slb * SLLEN as int,
                            slb > 0,
                    ;

                    // Establish slb == pow2(fl_floor + g_log2 - sli)
                    assert(slb == pow2((fl_floor + Self::granularity_log2_spec() - Self::sli_spec()) as nat)) by {
                        Self::sli_pow2_is_sllen();
                        lemma_pow2_div_sub(
                            Self::sli_spec() as nat,
                            (fl_floor + Self::granularity_log2_spec()) as nat
                        );
                    };
                    assert(is_power_of_two(slb));
                    bit_mask_is_mod_for_pow2(size, slb as usize);
                    assert(size & (slb - 1) as usize == 0usize);

                    assert(sl_shift_amount == fl_floor + Self::granularity_log2_spec() - Self::sli_spec());
                    assert(sl_shift_amount >= 0);
                    assert(slb == pow2(sl_shift_amount as nat));
                    assert(low_mask_usize(sl_shift_amount as nat) == (slb - 1) as usize) by {
                        assert(low_mask_usize(sl_shift_amount as nat)
                            == (pow2(sl_shift_amount as nat) - 1) as usize);
                    };
                    assert(size & low_mask_usize(sl_shift_amount as nat) as usize == 0usize);

                    // With lower sa bits of size == 0, rotate_right == shift_right.
                    // usize_rotate_right(size, sa) for sa > 0:
                    //   = ((size & high_mask(sa)) >> sa) | ((size & low_mask(sa)) << (64-sa))
                    //   = ((size & high_mask(sa)) >> sa) | (0 << (64-sa))
                    //   = (size & high_mask(sa)) >> sa
                    //   = size >> sa
                    // And size >> sa = size / slb < 2*SLLEN = pow2(sli+1).
                    // So sl_raw < pow2(sli+1), hence needs_ceil == 0.

                    // From lemma_usize_rotr_mask_lower:
                    lemma_usize_rotr_mask_lower(size, sl_shift_amount);
                    assert(sl_raw & low_mask_usize((usize::BITS - sl_shift_amount) as nat) as usize
                        == (size >> sl_shift_amount) & low_mask_usize((usize::BITS - sl_shift_amount) as nat) as usize);

                    // size >> sa < pow2(sli+1)
                    assert(size >> sl_shift_amount < pow2(Self::sli_spec() as nat + 1)) by {
                        lemma_usize_shr_is_div(size, sl_shift_amount as usize);
                        assert(size >> sl_shift_amount == size as nat / pow2(sl_shift_amount as nat));
                        log2_power_in_range(size as int);
                        assert(size < pow2(log(2, size as int) as nat + 1));
                        assert(log(2, size as int) == fl_floor + Self::granularity_log2_spec());
                        assert(size < pow2((fl_floor + Self::granularity_log2_spec() + 1) as nat));
                        let p = pow2(sl_shift_amount as nat) as int;
                        let q = pow2((Self::sli_spec() + 1) as nat) as int;
                        vstd::arithmetic::power2::lemma_pow2_pos(sl_shift_amount as nat);
                        vstd::arithmetic::power2::lemma_pow2_pos((Self::sli_spec() + 1) as nat);
                        assert(p > 0 && q > 0);
                        assert(p * q == pow2((fl_floor + Self::granularity_log2_spec() + 1) as nat)) by {
                            vstd::arithmetic::power2::lemma_pow2_adds(
                                sl_shift_amount as nat,
                                (Self::sli_spec() + 1) as nat
                            );
                        };
                        // size < p * q, so size / p < q
                        assert(size as int / p < q) by {
                            vstd::arithmetic::div_mod::lemma_div_is_ordered(
                                size as int, p * q - 1, p);
                            // (p*q-1)/p = q-1: use div_multiples_vanish
                            // p*q/p = q, and (p*q-1)/p = q - 1 (since p*q-1 = p*(q-1) + (p-1))
                            vstd::arithmetic::div_mod::lemma_div_multiples_vanish(q - 1, p);
                            assert(p * (q - 1) / p == q - 1);
                            // (p*q - 1) / p: p*q-1 = p*(q-1) + (p-1), and 0 <= p-1 < p
                            // By fundamental_div_mod on p*(q-1):
                            //   p*(q-1) = p * ((p*(q-1))/p) + (p*(q-1)) % p
                            //   = p * (q-1) + 0
                            // p*q - 1 = p*(q-1) + (p-1)
                            assert(p * q - 1 == p * (q - 1) + (p - 1)) by (nonlinear_arith)
                                requires p > 0, q > 0;
                            // p*q-1 = p*(q-1) + (p-1), 0 <= p-1 < p
                            // So (p*q-1)/p <= (p*(q-1) + p - 1)/p
                            // Use: for any a >= 0 and 0 <= b < p: (a*p + b)/p = a
                            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p * q - 1, p);
                            // The remainder (p*q-1)%p should be p-1
                            // Let's show (p*q-1) - p*(q-1) = p-1
                            assert((p * q - 1) - p * (q - 1) == p - 1) by (nonlinear_arith)
                                requires p > 0, q > 0;
                            // From fundamental_div_mod: p*q-1 = p * ((p*q-1)/p) + (p*q-1)%p
                            // Also: p*q-1 = p*(q-1) + (p-1)
                            // Since 0 <= p-1 < p and 0 <= (p*q-1)%p < p, and quotients are unique:
                            // (p*q-1)/p = q-1
                            vstd::arithmetic::div_mod::lemma_mod_bound(p * q - 1, p);
                            // p * ((p*q-1)/p) + (p*q-1)%p = p*(q-1) + (p-1)
                            // => p*((p*q-1)/p - (q-1)) = (p-1) - (p*q-1)%p
                            // Both sides must be 0 (since |rhs| < p and lhs is multiple of p)
                            assert((p * q - 1) / p == q - 1) by (nonlinear_arith)
                                requires p > 0, q > 0,
                                    p * q - 1 == p * ((p * q - 1) / p) + (p * q - 1) % p,
                                    0 <= (p * q - 1) % p < p,
                                    p * q - 1 == p * (q - 1) + (p - 1);
                        };
                    };

                    assert(Self::sli_spec() + 1 <= usize::BITS - sl_shift_amount);

                    // Since sl_raw < pow2(sli+1) would mean sl_raw == sl_raw & low_mask(64-sa) == size >> sa,
                    // and we want to show sl_raw < pow2(sli+1).
                    // Use contrapositive: size % slb != 0 => needs_ceil == 1.
                    // We proved size % slb == 0, so if needs_ceil were 1,
                    // sl_raw >= pow2(sli+1) >= SLLEN + SLLEN > SLLEN.
                    // But let's show directly that sl_raw == size >> sa < pow2(sli+1).

                    // sl_raw = usize_rotate_right(size, sa).
                    // When size & low_mask(sa) == 0:
                    // The wrapped part (size & low_mask(sa)) << (64-sa) == 0.
                    // So sl_raw = (size >> sa) (the shift part only).
                    // We need: sl_raw == size >> sa.
                    // We already have: sl_raw & low_mask(64-sa) == size >> sa.
                    // And: the wrapped part contributes to bits [64-sa, 63] of sl_raw,
                    // which are NOT in low_mask(64-sa). Since wrapped part == 0,
                    // those bits are 0. So sl_raw == sl_raw & low_mask(64-sa) == size >> sa.
                    assert(sl_raw == size >> sl_shift_amount) by {
                        if sl_shift_amount == 0 {
                            // rotate_right(x, 0) = x, and x >> 0 = x
                            assert(usize_rotate_right(size, 0i32) == size);
                            assert(size >> 0int == size) by {
                                lemma_usize_shr_is_div(size, 0usize);
                                lemma_pow2_values();
                            };
                        } else {
                        assert(sl_shift_amount > 0);
                        let sa = sl_shift_amount;
                        let sa_ctr = (usize::BITS as int - sa) as int;
                        assert(sl_raw == usize_rotate_right(size, sa as i32));

                        // rotate_right for n > 0:
                        //   shifted = (x & high_mask(sa)) >> sa
                        //   wrapped = (x & low_mask(sa)) << sa_ctr
                        //   result = shifted | wrapped
                        let shifted = (size as u64 & high_mask_u64(sa as nat)) >> sa;
                        let wrapped = (size as u64 & low_mask_u64(sa as nat)) << sa_ctr;
                        assert(sl_raw as u64 == shifted | wrapped);

                        // size & low_mask(sa) == 0, so wrapped == 0
                        assert(size & low_mask_usize(sa as nat) as usize == 0usize);
                        assert(low_mask_usize(sa as nat) == low_mask_u64(sa as nat) as usize);
                        assert(size as u64 & low_mask_u64(sa as nat) == 0u64);
                        assert(wrapped == 0u64) by {
                            let sa_ctr_u64 = sa_ctr as u64;
                            assert((0u64 << sa_ctr_u64) == 0u64) by(bit_vector);
                        };

                        // shifted | 0 == shifted
                        assert(sl_raw as u64 == shifted) by {
                            assert((shifted | 0u64) == shifted) by(bit_vector);
                        };

                        // (x & high_mask(sa)) >> sa == x >> sa for any x
                        // This holds because >> sa discards the lower sa bits,
                        // and high_mask only zeros those same lower sa bits.
                        assert(shifted == size as u64 >> sa) by {
                            let x = size as u64;
                            let n = sa as u64;
                            // high_mask_u64(sa) = !low_mask_u64(sa)
                            assert(!low_mask_u64(sa as nat) == high_mask_u64(sa as nat));
                            // (x & !low_mask(n)) >> n == x >> n
                            // This is because the bits masked out by !low_mask are exactly
                            // the bits discarded by >> n.
                            // Use the fact: x >> n == (x & high_mask(n)) >> n + (x & low_mask(n)) >> n
                            // and (x & low_mask(n)) >> n == 0 when n > 0.
                            assert(((x & low_mask_u64(sa as nat)) >> n) == 0u64) by {
                                assert(x & low_mask_u64(sa as nat) == 0);
                                assert((0u64 >> n) == 0u64) by(bit_vector);
                            };
                            // x & low_mask == 0, so x == x & high_mask == (x >> sa) << sa
                            assert(x & low_mask_u64(sa as nat) == 0u64);
                            // Therefore (x & high_mask) >> sa == x >> sa
                            // since x has no bits in the low_mask region
                            // Simplest: x >> sa drops low bits, & high_mask also drops low bits
                            // (x & high_mask) >> sa = x >> sa always (high_mask keeps bits >= sa, >> sa shifts them down)
                            // Just use arithmetic: both equal x / pow2(sa)
                            vstd::bits::lemma_u64_shr_is_div(x, sa as u64);
                            vstd::bits::lemma_u64_shr_is_div(x & high_mask_u64(sa as nat), sa as u64);
                            // x & high_mask = x - (x & low_mask) = x - 0 = x
                            assert(x & high_mask_u64(sa as nat) == x) by {
                                assert(!low_mask_u64(sa as nat) == high_mask_u64(sa as nat));
                                let lm = low_mask_u64(sa as nat);
                                assert(x & lm == 0u64);
                                assert((x & !lm) == x) by {
                                    // x & !lm = x when x & lm == 0
                                    // (because x = (x & !lm) | (x & lm) = (x & !lm) | 0 = x & !lm)
                                    assert(forall|a: u64, b: u64| a & b == 0u64 ==> a & !b == a) by(bit_vector);
                                };
                            };
                        };

                        // usize >> sa == u64 >> sa
                        assert(size >> sl_shift_amount == (size as u64 >> sa) as usize) by {
                            vstd::bits::lemma_u64_shr_is_div(size as u64, sa as u64);
                            lemma_usize_shr_is_div(size, sa as usize);
                        };
                        } // end else (sl_shift_amount > 0)
                    };

                    // Now sl_raw == size >> sa < pow2(sli+1), so needs_ceil == 0.
                    assert(sl_raw < pow2(Self::sli_spec() as nat + 1));

                    Self::sli_pow2_is_sllen();
                    assert(pow2(Self::sli_spec() as nat + 1) == 2 * SLLEN) by {
                        vstd::arithmetic::power2::lemma_pow2_unfold((Self::sli_spec() as nat + 1) as nat);
                    };
                    assert(1usize << (Self::sli() + 1) == pow2(Self::sli_spec() as nat + 1)) by {
                        assert(Self::sli() == Self::sli_spec());
                        vstd::bits::lemma_u64_shl_is_mul(1, (Self::sli() + 1) as u64);
                    };
                    assert(!(sl_raw >= (1usize << (Self::sli() + 1))));
                    assert(needs_ceil == 0);
                } else {
                    // fl_zero case: fl_floor == FLLEN - 1 but fl + g_log2 < sli.
                    // This means FLLEN - 1 + g_log2 < sli, so FLLEN - 1 < sli - g_log2.
                    // For GRANULARITY==32: g_log2=5, sli<=6, so FLLEN-1 < 1, FLLEN < 2, FLLEN == 1.
                    // For GRANULARITY==16: g_log2=4, sli<=5, so FLLEN-1 < 1, FLLEN < 2, FLLEN == 1.
                    // With FLLEN == 1 and fl_floor == 0: size == GRANULARITY (proven above).
                    // sl_raw = rotate_right(GRANULARITY, -1) = 2*GRANULARITY = SLLEN.
                    // needs_ceil check: SLLEN >= (1 << (sli+1))?
                    // (1 << (sli+1)) = 2*SLLEN. So SLLEN < 2*SLLEN. needs_ceil == 0.
                    if GRANULARITY == 32 {
                        assert(SLLEN == 64) by { Self::sli_pow2_is_sllen(); };
                        assert(sl_raw == 64usize);
                        assert(Self::sli() == 6);
                        assert(!(64usize >= (1usize << 7u32))) by(bit_vector);
                    } else if GRANULARITY == 16 {
                        assert(SLLEN == 32) by { Self::sli_pow2_is_sllen(); };
                        assert(sl_raw == 32usize);
                        assert(Self::sli() == 5);
                        assert(!(32usize >= (1usize << 6u32))) by(bit_vector);
                    }
                    assert(needs_ceil == 0);
                }

                // In all cases: needs_ceil == 0, contradicting needs_ceil == 1.
                assert(false);
            }
            return None;
        }

        proof { mask_higher_bits_leq_mask(sl, SLLEN); }
        let idx = BlockIndex(fl as usize, sl & (SLLEN - 1));

        // Main proof: size <= idx.start()
        proof {
            Self::granularity_basics();

            let floor_idx = BlockIndex::<FLLEN, SLLEN>(fl_floor as usize, sl_floor_val as usize);
            // floor_idx.wf() and floor_idx.block_size_range().contains(size) already established

            if fl_floor + Self::granularity_log2_spec() >= Self::sli_spec() {
                // Non-fl_zero case
                let flb = pow2((fl_floor + Self::granularity_log2_spec()) as nat) as int;
                let slb = flb / SLLEN as int;

                assert(flb >= SLLEN) by {
                    Self::sli_pow2_is_sllen();
                    lemma_pow2_increases(
                        Self::sli_spec() as nat,
                        (fl_floor + Self::granularity_log2_spec()) as nat);
                };

                assert(slb > 0) by {
                    vstd::arithmetic::div_mod::lemma_div_non_zero(flb, SLLEN as int);
                };

                assert(slb * SLLEN == flb) by {
                    Self::sli_pow2_is_sllen();
                    lemma_div_before_mult_pow2(
                        fl_floor + Self::granularity_log2_spec(),
                        Self::sli_spec());
                };

                floor_idx.fl_non_zero();
                assert(floor_idx.block_size_range().start()
                    == flb + slb * sl_floor_val);
                assert(floor_idx.block_size_range().end()
                    == flb + slb * (sl_floor_val + 1)) by {
                    vstd::arithmetic::mul::lemma_mul_is_distributive_add(slb, sl_floor_val, 1);
                };

                assert(floor_idx.block_size_range().start() <= size);
                assert(size < floor_idx.block_size_range().end());

                // Case split on needs_ceil
                if needs_ceil == 0 {
                    // sl = sl_floor_usize + 0 = sl_floor_usize
                    assert(sl == sl_floor_usize);
                    // sl < SLLEN, so sl >> sli == 0, hence fl == fl_floor
                    assert(sl < SLLEN);
                    assert(sl >> Self::sli() == 0usize) by {
                        Self::sli_pow2_is_sllen();
                        lemma_usize_shr_is_div(sl, Self::sli() as usize);
                        let m = pow2(Self::sli_spec() as nat) as int;
                        vstd::arithmetic::power2::lemma_pow2_pos(Self::sli_spec() as nat);
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(sl as int, m);
                        let q = sl as int / m;
                        assert(q == 0) by (nonlinear_arith)
                            requires sl as int == m * q + sl as int % m,
                                     0 <= sl as int % m < m,
                                     sl < m, m > 0;
                    };
                    assert(fl == fl_floor);
                    // sl & (SLLEN-1) == sl_floor_usize since sl_floor_usize < SLLEN
                    assert(sl & (SLLEN - 1) as usize == sl_floor_usize) by {
                        bit_mask_is_mod_for_pow2(sl, SLLEN);
                        assert(sl & (SLLEN - 1) as usize == sl % SLLEN);
                        vstd::arithmetic::div_mod::lemma_small_mod(sl as nat, SLLEN as nat);
                    };
                    assert(idx.0 == floor_idx.0 && idx.1 == floor_idx.1);

                    // needs_ceil == 0 => size % slb == 0 => size == floor.start
                    // Contrapositive: size % slb != 0 => needs_ceil == 1
                    // Prove slb == pow2(sa) where sa = sl_shift_amount
                    assert(slb == pow2((fl_floor + Self::granularity_log2_spec() - Self::sli_spec()) as nat)) by {
                        Self::sli_pow2_is_sllen();
                        lemma_pow2_div_sub(
                            Self::sli_spec() as nat,
                            (fl_floor + Self::granularity_log2_spec()) as nat
                        );
                    };
                    assert(sl_shift_amount == fl_floor + Self::granularity_log2_spec() - Self::sli_spec());
                    assert(sl_shift_amount >= 0);
                    assert(slb == pow2(sl_shift_amount as nat));
                    assert(is_power_of_two(slb));

                    assert((size as int) % slb == 0) by {
                        if (size as int) % slb != 0 {
                            bit_mask_is_mod_for_pow2(size, slb as usize);
                            assert(size & (slb - 1) as usize != 0usize);

                            // low_mask(sa) == slb - 1
                            assert(low_mask_usize(sl_shift_amount as nat) == (slb - 1) as usize) by {
                                assert(slb == pow2(sl_shift_amount as nat));
                                assert(low_mask_usize(sl_shift_amount as nat)
                                    == (pow2(sl_shift_amount as nat) - 1) as usize);
                            };
                            assert(size & low_mask_usize(sl_shift_amount as nat) as usize != 0usize);

                            // The wrapped part B = (size & low_mask(sa)) << (64-sa)
                            // is nonzero, so sl_raw >= B >= pow2(64-sa) >= pow2(sli+1).
                            // Therefore needs_ceil == 1, contradicting needs_ceil == 0.
                            let sa = sl_shift_amount;
                            let sa_ctr = (usize::BITS as int - sa) as int;
                            assert(sa > 0);
                            assert(sa_ctr >= Self::sli_spec() + 1) by {
                                assert(sa == fl_floor + Self::granularity_log2_spec() - Self::sli_spec());
                                assert(fl_floor < FLLEN);
                                assert(FLLEN <= usize::BITS);
                            };

                            // size & low_mask(sa) != 0, and it's shifted left by sa_ctr positions
                            // So the result has a bit set at position >= sa_ctr
                            let wrapped = (size as u64 & low_mask_u64(sa as nat)) << sa_ctr;
                            let shifted = (size as u64 & high_mask_u64(sa as nat)) >> sa;
                            assert(sl_raw == usize_rotate_right(size, sa as i32));
                            assert(usize_rotate_right(size, sa as i32) == (shifted | wrapped) as usize);

                            assert(size as u64 & low_mask_u64(sa as nat) != 0u64) by {
                                assert(low_mask_usize(sa as nat) == low_mask_u64(sa as nat) as usize);
                            };

                            assert(wrapped >= pow2(sa_ctr as nat)) by {
                                let low_bits = size as u64 & low_mask_u64(sa as nat);
                                assert(low_bits != 0);
                                assert(low_bits >= 1);
                                assert(wrapped == low_bits << sa_ctr);
                                let n = sa_ctr as u64;
                                let sa_u64 = sa as u64;
                                assert(0 < n && n < 64);
                                assert(0 < sa_u64 && sa_u64 < 64);
                                assert(n + sa_u64 == 64);
                                // low_bits < pow2(sa) since it's masked with low_mask(sa)
                                mask_higher_bits_leq_mask(low_bits as usize, pow2(sa as nat) as usize);
                                assert(low_bits < pow2(sa as nat));
                                // low_bits < 1 << sa (since pow2(sa) == 1 << sa for sa < 64)
                                vstd::bits::lemma_u64_shl_is_mul(1u64, sa_u64);
                                assert((1u64 << sa_u64) == pow2(sa as nat)) by {
                                    vstd::arithmetic::mul::lemma_mul_basics(pow2(sa as nat) as int);
                                };
                                assert(low_bits < (1u64 << sa_u64));
                                // With low_bits >= 1, low_bits < (1 << sa), and n + sa == 64:
                                // low_bits << n >= 1 << n (no overflow since low_bits < 2^sa = 2^(64-n))
                                assert((low_bits << n) >= (1u64 << n)) by(bit_vector)
                                    requires low_bits >= 1u64, low_bits < (1u64 << sa_u64),
                                             0 < n, n < 64u64, n + sa_u64 == 64u64;
                                // 1u64 << n == pow2(n)
                                vstd::bits::lemma_u64_shl_is_mul(1u64, n);
                                assert((1u64 << n) == pow2(n as nat)) by {
                                    vstd::arithmetic::mul::lemma_mul_basics(pow2(n as nat) as int);
                                };
                            };
                            assert(sl_raw as u64 >= wrapped) by {
                                assert(sl_raw as u64 == shifted | wrapped);
                                assert((shifted | wrapped) >= wrapped) by(bit_vector)
                                    requires shifted >= 0, wrapped >= 0;
                            };
                            assert(sl_raw >= pow2(sa_ctr as nat)) by {
                                assert(sl_raw as u64 >= wrapped);
                                assert(wrapped >= pow2(sa_ctr as nat));
                            };

                            assert(pow2(sa_ctr as nat) >= pow2((Self::sli_spec() + 1) as nat)) by {
                                lemma_pow2_increases(
                                    (Self::sli_spec() + 1) as nat,
                                    sa_ctr as nat);
                            };

                            Self::sli_pow2_is_sllen();
                            vstd::bits::lemma_u64_shl_is_mul(1, (Self::sli() + 1) as u64);
                            assert(1usize << (Self::sli() + 1) == pow2((Self::sli_spec() + 1) as nat));
                            assert(sl_raw >= (1usize << (Self::sli() + 1)));
                            assert(needs_ceil == 1);
                        }
                    };

                    // size == floor.start (since size % slb == 0 and floor.start <= size < floor.start + slb)
                    assert(size as int == floor_idx.block_size_range().start()) by {
                        let start = flb + slb * sl_floor_val;
                        assert(floor_idx.block_size_range().start() == start);
                        assert(floor_idx.block_size_range().contains(size as int));
                        assert(start <= size);
                        // floor.end = flb + slb * (sl_floor_val + 1) = start + slb
                        vstd::arithmetic::mul::lemma_mul_is_distributive_add(slb, sl_floor_val, 1int);
                        assert(slb * (sl_floor_val + 1) == slb * sl_floor_val + slb);
                        assert(floor_idx.block_size_range().end() == flb + slb * (sl_floor_val + 1));
                        assert(size < floor_idx.block_size_range().end());
                        assert(size < start + slb);
                        // size % slb == 0, so size = slb * q
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(size as int, slb);
                        let q = size as int / slb;
                        assert(size == slb * q);
                        // start = flb + slb * sl_floor_val = slb * SLLEN + slb * sl_floor_val
                        vstd::arithmetic::mul::lemma_mul_is_distributive_add(slb, SLLEN as int, sl_floor_val);
                        let k = SLLEN as int + sl_floor_val;
                        assert(start == slb * k);
                        // slb * k <= slb * q < slb * (k + 1) => q == k
                        assert(q == k) by {
                            // size == slb * q, start == slb * k, start + slb == slb * (k+1)
                            vstd::arithmetic::mul::lemma_mul_is_distributive_add(slb, k, 1int);
                            assert(slb * (k + 1) == slb * k + slb);
                            assert(slb * k <= slb * q);  // start <= size
                            assert(slb * q < slb * (k + 1));  // size < start + slb
                            // q == k follows from: slb*k <= slb*q < slb*k + slb, slb > 0
                            assert(q == k) by (nonlinear_arith)
                                requires slb > 0, slb * k <= slb * q, slb * q < slb * k + slb;
                        };
                        assert(size == start);
                    };

                    assert(size as int <= idx.block_size_range().start());
                } else {
                    // needs_ceil == 1
                    assert(needs_ceil == 1);

                    if sl_floor_val < SLLEN - 1 {
                        // No carry: sl = sl_floor_usize + 1 < SLLEN
                        assert(sl == sl_floor_usize + 1);
                        assert(sl < SLLEN);
                        assert(sl >> Self::sli() == 0usize) by {
                            Self::sli_pow2_is_sllen();
                            lemma_usize_shr_is_div(sl, Self::sli() as usize);
                            let m = pow2(Self::sli_spec() as nat) as int;
                            vstd::arithmetic::power2::lemma_pow2_pos(Self::sli_spec() as nat);
                            assert(m > 0);
                            assert(0 <= sl as int && sl < m);
                            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(sl as int, m);
                            let q = sl as int / m;
                            assert(sl == m * q + sl as int % m);
                            assert(0 <= sl as int % m < m);
                            // If q >= 1, then sl >= m, contradiction
                            assert(q == 0) by (nonlinear_arith)
                                requires sl as int == m * q + sl as int % m,
                                         0 <= sl as int % m < m,
                                         sl < m, m > 0;
                        };
                        assert(fl == fl_floor);
                        assert(sl & (SLLEN - 1) as usize == sl as usize) by {
                            bit_mask_is_mod_for_pow2(sl, SLLEN);
                            vstd::arithmetic::div_mod::lemma_small_mod(sl as nat, SLLEN as nat);
                        };
                        assert(idx.0 == fl_floor as usize);
                        assert(idx.1 == (sl_floor_val + 1) as usize);

                        let ceil_idx = BlockIndex::<FLLEN, SLLEN>(fl_floor as usize, (sl_floor_val + 1) as usize);
                        assert(idx.0 == ceil_idx.0 && idx.1 == ceil_idx.1);

                        assert(pow2((fl_floor + Self::granularity_log2_spec()) as nat) >= SLLEN);
                        ceil_idx.fl_non_zero();
                        assert(ceil_idx.block_size_range().start()
                            == flb + slb * (sl_floor_val + 1));

                        // floor.end == ceil_idx.start
                        assert(floor_idx.block_size_range().end()
                            == ceil_idx.block_size_range().start());

                        // size < floor.end == ceil_idx.start == idx.start
                        assert(size < ceil_idx.block_size_range().start());
                        assert(size as int <= idx.block_size_range().start());
                    } else {
                        // Carry: sl_floor_val == SLLEN - 1, idx = (fl_floor + 1, 0)
                        assert(sl_floor_val == SLLEN - 1);
                        // sl = sl_floor_usize + 1 = SLLEN
                        assert(sl == SLLEN);
                        assert(sl >> Self::sli() == 1usize) by {
                            Self::sli_pow2_is_sllen();
                            lemma_usize_shr_is_div(sl, Self::sli() as usize);
                        };
                        assert(fl == fl_floor + 1);
                        assert(idx.0 == (fl_floor + 1) as usize);
                        assert(idx.1 == 0usize) by {
                            // SLLEN & (SLLEN - 1) == 0 for power of 2
                            assert(SLLEN as usize & (SLLEN - 1) as usize == 0usize) by {
                                Self::sli_pow2_is_sllen();
                                bit_mask_is_mod_for_pow2(SLLEN, SLLEN);
                            };
                        };

                        let ceil_idx = BlockIndex::<FLLEN, SLLEN>((fl_floor + 1) as usize, 0usize);
                        assert(idx.0 == ceil_idx.0 && idx.1 == ceil_idx.1);

                        // ceil_idx.start == 2*flb
                        ceil_idx.fl_non_zero();
                        assert(pow2(((fl_floor + 1) as int + Self::granularity_log2_spec()) as nat)
                            == 2 * flb) by {
                            vstd::arithmetic::power2::lemma_pow2_unfold(
                                ((fl_floor + 1) as int + Self::granularity_log2_spec()) as nat);
                        };
                        assert(ceil_idx.block_size_range().start() == 2 * flb);

                        // floor.end == flb + slb * SLLEN == flb + flb == 2*flb
                        assert(floor_idx.block_size_range().end() == flb + slb * SLLEN as int);
                        assert(slb * SLLEN as int == flb);
                        assert(floor_idx.block_size_range().end() == 2 * flb);

                        // size < floor.end == 2*flb == ceil_idx.start
                        assert(size < ceil_idx.block_size_range().start());
                        assert(size as int <= idx.block_size_range().start());
                    }
                }
            } else {
                // fl_zero case: size == GRANULARITY
                assert(size == GRANULARITY);

                // needs_ceil == 0 in fl_zero case (proven in the NONE branch analysis)
                if GRANULARITY == 32 {
                    assert(SLLEN == 64) by { Self::sli_pow2_is_sllen(); };
                    assert(sl_raw == 64usize);
                    assert(Self::sli() == 6);
                    assert(!(64usize >= (1usize << 7u32))) by(bit_vector);
                    assert(needs_ceil == 0);
                } else if GRANULARITY == 16 {
                    assert(SLLEN == 32) by { Self::sli_pow2_is_sllen(); };
                    assert(sl_raw == 32usize);
                    assert(Self::sli() == 5);
                    assert(!(32usize >= (1usize << 6u32))) by(bit_vector);
                    assert(needs_ceil == 0);
                }

                // With needs_ceil == 0: sl = sl_floor_usize, sl < SLLEN, carry == 0
                assert(sl == sl_floor_usize);
                assert(sl < SLLEN);
                assert(sl >> Self::sli() == 0usize) by {
                    Self::sli_pow2_is_sllen();
                    lemma_usize_shr_is_div(sl, Self::sli() as usize);
                };
                assert(fl == fl_floor);
                assert(idx.0 == 0usize);
                assert(idx.1 == 0usize) by {
                    bit_mask_is_mod_for_pow2(sl, SLLEN);
                };

                // idx.start() == GRANULARITY == size
                floor_idx.fl_is_zero();
                assert(floor_idx.block_size_range().start() == GRANULARITY);
                assert(size as int <= idx.block_size_range().start());
            }
        }

        Some(idx)
    }


    /// Proves that BlockIndex(fl, sl) computed from size via the floor mapping
    /// has block_size_range().contains(size).
    /// Shared between map_floor and map_ceil.
    proof fn lemma_floor_index_contains_size(size: usize, fl: int, sl: int)
        requires
            Self::parameter_validity(),
            size >= GRANULARITY,
            size % GRANULARITY == 0,
            BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int),
            fl == log(2, size as int) - Self::granularity_log2_spec(),
            0 <= fl < FLLEN as int,
            0 <= sl < SLLEN as int,
            fl + Self::granularity_log2_spec() >= Self::sli_spec() ==>
                sl == ((size as int) / (pow2((fl + Self::granularity_log2_spec()) as nat) as int / SLLEN as int)) % SLLEN as int,
        ensures
            BlockIndex::<FLLEN, SLLEN>(fl as usize, sl as usize).wf(),
            BlockIndex::<FLLEN, SLLEN>(fl as usize, sl as usize).block_size_range().contains(size as int),
    {
        lemma_pow2_values();
        lemma_log2_values();
        Self::granularity_basics();
        granularity_is_power_of_two();
        assert(Self::sli_spec() >= 0) by {
            vstd::arithmetic::logarithm::lemma_log_nonnegative(2, SLLEN as int);
        };
        assert(Self::granularity_log2_spec() >= 0) by {
            vstd::arithmetic::logarithm::lemma_log_nonnegative(2, GRANULARITY as int);
        };
        let idx = BlockIndex::<FLLEN, SLLEN>(fl as usize, sl as usize);
        assert(idx.wf());
        if fl + Self::granularity_log2_spec() >= Self::sli_spec() {
            assert(Self::sli_spec() as nat <= (fl + Self::granularity_log2_spec()) as nat);
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
                lemma_div_before_mult_pow2(fl + Self::granularity_log2_spec(), Self::sli_spec());
            };
            assert(fl == log(2, size as int / GRANULARITY as int)) by {
                lemma_log2_distributes(size as int, GRANULARITY as int)
            };
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
        }
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
                    idx.block_size_range().contains(size as int) &&
                    idx == Self::map_floor_spec(size)
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

                // Prove idx == map_floor_spec(size) for fl >= sli case
                assert(fl == log(2, size as int / GRANULARITY as int)) by {
                    lemma_log2_distributes(size as int, GRANULARITY as int);
                };
                let ghost flb_if = pow2((fl + Self::granularity_log2_spec()) as nat);
                assert(flb_if >= SLLEN) by {
                    Self::sli_pow2_is_sllen();
                    if (fl + Self::granularity_log2_spec()) as nat
                        > Self::sli_spec() as nat {
                        vstd::arithmetic::power2::lemma_pow2_strictly_increases(
                            Self::sli_spec() as nat,
                            (fl + Self::granularity_log2_spec()) as nat,
                        );
                    }
                };
                assert(idx == Self::map_floor_spec(size));
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

                // Prove idx == map_floor_spec(size) for fl < sli case
                // map_floor_spec returns BlockIndex(0, 0) when flb < SLLEN
                assert(fl == 0usize) by {
                    // fl + g_log2 < sli, sli <= 6, g_log2 >= 4, so fl < 2
                    // For 64-bit: g_log2 == 5, sli <= 6, so fl < 1
                    // For 32-bit: g_log2 == 4, sli <= 5, so fl < 1
                };
                assert(fl == log(2, size as int / GRANULARITY as int)) by {
                    lemma_log2_distributes(size as int, GRANULARITY as int);
                };
                // fl == 0 means log(2, size/GRANULARITY) == 0, so size/GRANULARITY == 1
                assert(size as int / GRANULARITY as int == 1) by {
                    assert(log(2, size as int / GRANULARITY as int) == 0);
                    assert(size as int / GRANULARITY as int >= 1);
                    if size as int / GRANULARITY as int >= 2 {
                        vstd::arithmetic::logarithm::lemma_log_is_ordered(
                            2, 2, size as int / GRANULARITY as int
                        );
                        assert(log(2, 2) >= 1);
                    }
                };
                assert(size == GRANULARITY);
                let ghost flb_else = pow2((fl + Self::granularity_log2_spec()) as nat);
                assert(flb_else < SLLEN) by {
                    Self::sli_pow2_is_sllen();
                    vstd::arithmetic::power2::lemma_pow2_strictly_increases(
                        (fl + Self::granularity_log2_spec()) as nat,
                        Self::sli_spec() as nat,
                    );
                };
                assert(Self::map_floor_spec(size) == BlockIndex::<FLLEN, SLLEN>(0usize, 0usize));
                assert(sl == 0usize) by {
                    // sl (post-destructure) = idx.1
                    //   = usize_rotate_right(size, ws as i32) & (SLLEN - 1)
                    // where ws: u32 = (fl_u32 + g_log2).wrapping_sub(sli)
                    // With fl == 0, size == GRANULARITY:
                    //   ws = g_log2.wrapping_sub(sli) = u32::MAX (since g_log2 < sli)
                    //   ws as i32 = -1 (spec-level reinterpretation)
                    //   rotate_right(GRANULARITY, -1) = GRANULARITY << 1 = 2*GRAN
                    //   (2*GRAN) & (SLLEN - 1) = 0 since 2*GRAN == SLLEN
                    lemma_low_mask_u64_values();
                    assert(high_mask_u64(1) == !low_mask_u64(1));
                    assert(!0x1u64 == 0xfffffffffffffffeu64) by(bit_vector);
                    if GRANULARITY == 32 {
                        assert(Self::sli_spec() == 6);
                        assert(SLLEN == 64) by {
                            Self::sli_pow2_is_sllen();
                        };
                        // wrapping_sub(5u32, 6u32) = u32::MAX
                        assert(5u32.wrapping_sub(6u32) == u32::MAX);
                        // u32::MAX as i32 == -1 (spec-level)
                        assert(u32::MAX as i32 == -1i32) by(bit_vector);
                        // Unfold usize_rotate_right(32, -1):
                        // n=-1<0, sa=abs(-1)%64=1, sa_ctr=63
                        // ((32u64 & low_mask_u64(63)) << 1) | ((32u64 & high_mask_u64(1)) >> 63)
                        assert(low_mask_u64(63) == 0x7fffffffffffffffu64);
                        assert(
                            ((32u64 & 0x7fffffffffffffffu64) << 1u64)
                            | ((32u64 & 0xfffffffffffffffeu64) >> 63u64)
                            == 64u64
                        ) by(bit_vector);
                        assert(usize_rotate_right(32, -1i32) == 64usize);
                        assert((64usize & 63usize) == 0usize) by(bit_vector);
                    } else if GRANULARITY == 16 {
                        assert(Self::sli_spec() == 5);
                        assert(SLLEN == 32) by {
                            Self::sli_pow2_is_sllen();
                        };
                        assert(4u32.wrapping_sub(5u32) == u32::MAX);
                        assert(u32::MAX as i32 == -1i32) by(bit_vector);
                        assert(low_mask_u64(63) == 0x7fffffffffffffffu64);
                        assert(
                            ((16u64 & 0x7fffffffffffffffu64) << 1u64)
                            | ((16u64 & 0xfffffffffffffffeu64) >> 63u64)
                            == 32u64
                        ) by(bit_vector);
                        assert(usize_rotate_right(16, -1i32) == 32usize);
                        assert((32usize & 31usize) == 0usize) by(bit_vector);
                    }
                };
                assert(idx == Self::map_floor_spec(size));
            }

            Self::lemma_floor_index_contains_size(size, fl as int, sl as int);
        }

       Some(idx)
    }

    pub closed spec fn map_floor_spec(size: usize) -> BlockIndex<FLLEN, SLLEN>
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

    /// Bridge lemma: map_floor_spec(size) gives an index whose block_size_range contains size.
    /// Allows callers that only know `idx == map_floor_spec(size)` to recover range containment.
    pub proof fn lemma_map_floor_spec_range_contains(size: usize)
        requires
            Self::parameter_validity(),
            size >= GRANULARITY,
            size % GRANULARITY == 0,
            BlockIndex::<FLLEN, SLLEN>::valid_block_size(size as int),
        ensures
            Self::map_floor_spec(size).wf(),
            Self::map_floor_spec(size).block_size_range().contains(size as int),
    {
        reveal(Tlsf::map_floor_spec);
        lemma_pow2_values();
        lemma_log2_values();
        granularity_is_power_of_two();
        Self::granularity_basics();

        let fl = log(2, size as int / GRANULARITY as int);
        let flb = pow2((fl + Self::granularity_log2_spec()) as nat);

        // fl == log(2, size) - g_log2 (needed as precondition for lemma_floor_index_contains_size)
        assert(fl == log(2, size as int) - Self::granularity_log2_spec()) by {
            lemma_log2_distributes(size as int, GRANULARITY as int);
        };
        assert(0 <= fl) by {
            vstd::arithmetic::logarithm::lemma_log_nonnegative(2, size as int / GRANULARITY as int);
        };

        // fl < FLLEN follows from valid_block_size
        assert(fl < FLLEN as int) by {
            // log2_power_in_range gives pow2(fl) <= size/G < pow2(fl + 1)
            log2_power_in_range(size as int / GRANULARITY as int);
            assert(pow2(fl as nat) <= size as int / GRANULARITY as int);
            // valid_block_size: size < pow2(FLLEN) * GRANULARITY, so size/G < pow2(FLLEN)
            assert(pow2(FLLEN as nat) as int > size as int / GRANULARITY as int);
            // So pow2(fl) < pow2(FLLEN), meaning fl < FLLEN
            if fl >= FLLEN as int {
                lemma_pow2_increases(FLLEN as nat, fl as nat);
                assert(pow2(FLLEN as nat) <= pow2(fl as nat));
                assert(false);
            }
        };

        if flb < SLLEN {
            // fl=0 case: map_floor_spec returns BlockIndex(0, 0)
            assert(fl == 0) by {
                Self::sli_pow2_is_sllen();
                if fl > 0 {
                    vstd::arithmetic::power2::lemma_pow2_strictly_increases(
                        Self::sli_spec() as nat,
                        (fl + Self::granularity_log2_spec()) as nat,
                    );
                    assert(false);
                }
            };
            assert(size == GRANULARITY) by {
                assert(log(2, size as int / GRANULARITY as int) == 0);
                assert(size as int / GRANULARITY as int >= 1);
                if size as int / GRANULARITY as int >= 2 {
                    vstd::arithmetic::logarithm::lemma_log_is_ordered(
                        2, 2, size as int / GRANULARITY as int
                    );
                    assert(log(2, 2) >= 1);
                }
            };
            // Establish: 0 == log(2, size) - g_log2 (needed for lemma_floor_index_contains_size)
            assert(0 == log(2, size as int) - Self::granularity_log2_spec());
            // For the conditional precondition: 0 + g_log2 >= sli ==> 0 == (...)
            assert(0 + Self::granularity_log2_spec() >= Self::sli_spec() ==>
                0 == ((size as int) / (pow2((0 + Self::granularity_log2_spec()) as nat) as int / SLLEN as int)) % SLLEN as int)
            by {
                if Self::granularity_log2_spec() >= Self::sli_spec() {
                    Self::sli_pow2_is_sllen();
                    assert(Self::sli_spec() >= 0) by {
                        vstd::arithmetic::logarithm::lemma_log_nonnegative(2, SLLEN as int);
                    };
                    assert(Self::granularity_log2_spec() >= 0) by {
                        vstd::arithmetic::logarithm::lemma_log_nonnegative(2, GRANULARITY as int);
                    };
                    assert(pow2(Self::granularity_log2_spec() as nat) == GRANULARITY);
                    let g = pow2(Self::granularity_log2_spec() as nat) as int;
                    assert(g == GRANULARITY as int);
                    assert(g >= SLLEN as int) by {
                        lemma_pow2_increases(Self::sli_spec() as nat, Self::granularity_log2_spec() as nat);
                    };
                    let slb = g / SLLEN as int;
                    assert(slb >= 1);
                    assert(slb * SLLEN as int == g) by {
                        assert(SLLEN as int * slb == g);
                    };
                }
            };
            Self::lemma_floor_index_contains_size(size, 0, 0);
        } else {
            // fl >= 1 case
            let slb = flb as int / SLLEN as int;
            let sl = ((size as int) / slb) % SLLEN as int;
            assert(0 <= sl < SLLEN as int);
            assert(fl + Self::granularity_log2_spec() >= Self::sli_spec()) by {
                Self::sli_pow2_is_sllen();
                if fl + Self::granularity_log2_spec() < Self::sli_spec() {
                    vstd::arithmetic::power2::lemma_pow2_strictly_increases(
                        (fl + Self::granularity_log2_spec()) as nat,
                        Self::sli_spec() as nat,
                    );
                    assert(false);
                }
            };
            Self::lemma_floor_index_contains_size(size, fl, sl);
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
        // pow2((self.0 + Self::granularity_log2_spec()) as nat) < SLLEN
        assert(flb == pow2((fl + Self::granularity_log2_spec()) as nat));
        //assert(fl == log(2, size as int / GRANULARITY as int) as usize);
        assert(SLLEN <= flb) by {

            assert(Self::sli_spec() <= fl + Self::granularity_log2_spec());
            assert(0 <= fl + Self::granularity_log2_spec()) by {
                assert(0 <= fl);
                vstd::arithmetic::logarithm::lemma_log_nonnegative(2, GRANULARITY as int);
            };
            assert(0 <= Self::sli_spec()) by {
                vstd::arithmetic::logarithm::lemma_log_nonnegative(2, SLLEN as int);
            };

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
        assert(q * d <= flb) by {
            assert(flb == q * d + r);
            assert(0 <= r);
        };
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(flb, d);
        assert(0 <= q);
        assert((d - 1) * q < flb) by {
            vstd::arithmetic::mul::lemma_mul_inequality(d - 1, d, q);
            assert((d - 1) * q <= d * q);
            assert(d * q <= flb);
            if q == 0 {
                assert((d - 1) * q == 0) by {
                    vstd::arithmetic::mul::lemma_mul_basics(d - 1);
                };
                assert(0 < flb);
            } else {
                vstd::arithmetic::mul::lemma_mul_strict_inequality(d - 1, d, q);
                assert((d - 1) * q < d * q);
            }
        };
        assert(Self::max_allocatable_size() == flb + (d - 1) * q);
        assert(Self::max_allocatable_size() < flb + flb);
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
        assert(Self::max_allocatable_size() < max_valid);
        assert((size as int) <= Self::max_allocatable_size());
        assert((size as int) < max_valid);
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
