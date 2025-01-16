use vstd::prelude::*;

verus! {
use vstd::std_specs::bits::{
    u64_trailing_zeros, u64_leading_zeros,
    u32_leading_zeros, u32_trailing_zeros,
    axiom_u64_trailing_zeros
};
use vstd::arithmetic::logarithm::{log, lemma_log_nonnegative};
use vstd::arithmetic::power::{pow, lemma_pow_adds};
use vstd::arithmetic::div_mod::lemma_mod_breakdown;
use vstd::math::abs;

//#[cfg(target_pointer_width = "32")]
//global layout usize is size == 4;

//#[cfg(target_pointer_width = "64")]
//global layout usize is size == 8;

// NOTE: following compatibility layer for usize formalization should be removed in future once
//       Verus implements equivalent functionalities

// NOTE: vstd's interface returns u32 for u(64|32)_(leading|trailing)_zeros,
//       except for u64_leading_zeros (this returns int).
//       Thus, aligned the return type at int for spec functions here.

#[cfg(target_pointer_width = "32")]
pub open spec fn usize_leading_zeros(x: usize) -> int
{
    u32_leading_zeros(x as u32) as int
}

#[cfg(target_pointer_width = "64")]
pub open spec fn usize_leading_zeros(x: usize) -> int
{
    u64_leading_zeros(x as u64)
}


#[cfg(target_pointer_width = "32")]
pub open spec fn usize_trailing_zeros(x: usize) -> int
{
    u32_trailing_zeros(x as u32) as int
}

#[cfg(target_pointer_width = "64")]
pub open spec fn usize_trailing_zeros(x: usize) -> int
{
    u64_trailing_zeros(x as u64) as int
}

pub assume_specification [usize::leading_zeros] (x: usize) -> (r: u32)
    ensures r == usize_leading_zeros(x)
    opens_invariants none
    no_unwind;

pub assume_specification [usize::trailing_zeros] (x: usize) -> (r: u32)
    ensures r == usize_trailing_zeros(x)
    opens_invariants none
    no_unwind;

#[cfg(target_pointer_width = "64")]
pub proof fn axiom_usize_trailing_zeros(x: usize) {
    axiom_u64_trailing_zeros(x as u64);
}

//pub proof fn power2_log2(x: int)
    //requires is_power_of_two(x)
    //ensures x >> log(2, x) >= 1
use vstd::arithmetic::power::lemma_pow_strictly_increases_converse;
pub proof fn pow2_is_single_bit(x: usize, y: nat)
    requires pow(2, y) == x, x > 0,
    ensures x == 1 << y,
    decreases y,
{
    // TODO
    assert((x as int) < pow(2, usize::BITS as nat)) by (compute);
    assert(pow(2, y) < pow(2, usize::BITS as nat));
    lemma_pow_strictly_increases_converse(2, y, usize::BITS as nat);
    assert(y < usize::BITS as nat);
    assert(y < 64);
    if x == 1 {
        assert(y == 0);
        assert(pow(2, 0) == 1) by (compute);
        assert(1 == 1 << 0) by (bit_vector);
        assert(x == 1 << y);
    } else {
        pow2_is_single_bit(x / 2, (y - 1) as nat);
        assert((x / 2) == 1 << (y - 1));
        lemma_u64_shl_is_mul(1, y as u64);
        assert(1 << y == pow(2, y));
        assert(1 << (y - 1) == pow(2, (y - 1) as nat));
        assert(2*pow(2, (y - 1) as nat) == pow(2, y));
        assert(2*(1 << (y - 1)) == 1 << y);
        //assert(y > 0);
        //assert(pow(2, (y - 1) as nat + 1) == pow(2, y));
        //lemma_pow_adds(2, (y - 1) as nat, 1);
        //assert(pow(2, y) == pow(2, (y - 1) as nat) * pow(2, 1));
        //assert(pow(2, y) == pow(2, (y - 1) as nat) * 2);
        //assert(pow(2, y) == pow(2, (y - 1) as nat) * 2);
        //assert(x / 2 == pow(2, (y - 1) as nat));

    }
}

proof fn usize_trailing_zeros_is_log2_when_pow2_given(x: usize, y: nat)
    requires pow(2, y) == x as int, x > 0
    ensures usize_trailing_zeros(x) == y //log(2, x as int)
{
    axiom_usize_trailing_zeros(x);
    //lemma_log_nonnegative(x);
    if x == 1 {
        reveal(usize_trailing_zeros);
        axiom_usize_trailing_zeros(1);
        axiom_u64_trailing_zeros(1);
        assert(0 <= usize_trailing_zeros(1) <= 64);
        assert(u64_trailing_zeros(1) == 0) by (compute);
        assert(usize_trailing_zeros(1) == 0) by(compute);
        assert(log(2, x as int) == 1);
        assert(usize_trailing_zeros(x) == log(2, x as int));
    } else {
    }
    //assert(usize_trailing_zeros(x) == log(2, x as int)) by (compute);
    //TODO
}


pub open spec fn usize_rotate_right(x: usize, n: int) -> usize {
    let sa: nat = abs(n) as nat % usize::BITS as nat;
    let sa_ctr: nat = (usize::BITS as nat - sa) as nat;
    // TODO: justification
    if n == 0 {
        x
    } else if n > 0 {
        (x & high_mask(sa)) >> sa | ((x & low_mask(sa)) << (sa_ctr))
    } else { // n < 0
        (x & low_mask(sa_ctr)) << sa | ((x & high_mask(sa)) >> (sa_ctr))
    }
}

proof fn lemma_usize_rotate_right_low_mask_shl(x: usize, n: int)
    requires
        usize::BITS > n >= 0,
        x == x & high_mask(n as nat)
    ensures
        x >> n == usize_rotate_right(x, n)
{
    //TODO
}

proof fn lemma_usize_rotate_right_0_eq(x: usize)
    ensures x == usize_rotate_right(x, 0)
{}

proof fn lemma_usize_shr_0(x: usize) by (bit_vector)
    ensures x == x >> 0
{}

proof fn lemma_usize_shl_0(x: usize) by (bit_vector)
    ensures x == x << 0
{}

proof fn lemma_usize_shr_over(x: usize) by (bit_vector)
    ensures x >> usize::BITS == 0
{}

proof fn lemma_usize_full_mask(x: usize)
    ensures x & usize::MAX == x
{
    assert(x & usize::MAX == x) by (compute);
}

proof fn lemma_usize_rotate_right_mod0_noop(x: usize, n: int)
    requires n % usize::BITS as int == 0
    ensures x == usize_rotate_right(x, n)
{
    let sa = 0nat;
    let sa_ctr = usize::BITS as nat;
    assert(high_mask(0) == usize::MAX) by (compute_only);
    assert(low_mask(0) == 0) by (compute_only);
    assert(low_mask(usize::BITS as nat) == usize::MAX) by (compute_only);
    if n == 0 {
        assert(x == x);
    } else if n > 0 {
        lemma_usize_full_mask(x);
        lemma_usize_shr_0(x);
        lemma_usize_shl_0(x);
        assert(x == (x & usize::MAX) >> 0 | ((x & 0) << (usize::BITS as nat))) by (compute);
    } else {
        lemma_usize_full_mask(x);
        lemma_usize_shr_over(x);
        lemma_usize_shl_0(x);
        assert(x == x | 0) by (bit_vector);
        assert(x == (x & usize::MAX) << 0 | ((x & usize::MAX) >> (usize::BITS as nat))) by (compute);
    }
}

proof fn lemma_usize_rotate_right_distr(x: usize, m: int, n: int, l: int)
    requires m == n + l
    ensures usize_rotate_right(x, m) == usize_rotate_right(usize_rotate_right(x, n), l)
{
    // TODO
}

proof fn lemma_usize_rotate_right_reversible(x: usize, n: int)
    ensures x == usize_rotate_right(usize_rotate_right(x, n), -n)
{
    // TODO
    if n == 0 {
        assert(x == usize_rotate_right(usize_rotate_right(x, 0), 0));
    } else if n > 0 {
        assert(-n < 0);
        let sa1: nat = abs(n) as nat % usize::BITS as nat;
        let sa_ctr1: nat = (usize::BITS as nat - sa1) as nat;
        let sa2: nat = abs(-n) as nat % usize::BITS as nat;
        let sa_ctr2: nat = (usize::BITS as nat - sa2) as nat;
    } else {
        assert(-n > 0);
    }
}


use vstd::bits::low_bits_mask;
// mask with n or higher bits n..usize::BITS set
pub open spec fn high_mask(n: nat) -> usize {
    !low_mask(n)
}

// masks with bits 0..n set
pub open spec fn low_mask(n: nat) -> usize {
    low_bits_mask(n) as usize
}

#[cfg(target_pointer_width = "64")]
pub assume_specification [usize::rotate_right] (x: usize, n: u32) -> (r: usize)
    // This primitive cast just work as usual exec code
    // NOTE: is it ok? primitive cast really just reinterpet bytes?
    //      ref. `unsigned_to_signed`
    ensures r == usize_rotate_right(x, n as i32 as int)
    opens_invariants none
    no_unwind;

use vstd::bits::*;
use vstd::arithmetic::power2::*;

proof fn example5() {
    reveal(pow2);
    lemma_low_bits_mask_values();
    assert(usize_rotate_right(1, 1) == 1usize << 63) by (compute);
    assert(usize_rotate_right(1usize << 63, -1) == 1) by (compute);
    assert(usize_rotate_right(0xbeef00000000dead, -16) == 0xdeadbeef) by (compute);
    assert(usize_rotate_right(0xbeef00000000dead, 16) == 0xdeadbeef00000000) by (compute);
    assert(usize_rotate_right(0xdeadbeef, 128) == 0xdeadbeef) by (compute);
    assert(usize_rotate_right(0xdeadbeef, -128) == 0xdeadbeef) by (compute);
    assert(usize_rotate_right(usize_rotate_right(0xdeadbeef, -1234), 1234) == 0xdeadbeef) by (compute);
    assert(0xfffffff0u32 as i32 as int == -16int) by (bit_vector);
    assert(usize_rotate_right(0xbeef00000000dead, 0xfffffff0u32 as i32 as int) == 0xdeadbeef);
    // NOTE: 
    // - it seems `0xXXXu32 as i32` can be solved by bit_vector only 
    //   (by (compute) doesn't terminate)
    // - lemma around `usize_rotate_right` requires separate `assert` for `0xXXu32 as i32`
}

proof fn unsigned_to_signed(n: u32) by (bit_vector)
    ensures
        0 <= n && n <= 0x7fffffffu32 ==> (n as i32 as int) >= 0,
        0x7fffffff < n ==> (n as i32 as int) < 0,
{}

// NOTE: no need to conditoinal compilation for external spec using `usize_wrapping_*`
//      because `usize::` implicitly branch for the appropriate architecture.


pub open spec fn is_power_of_two(n: int) -> bool
    decreases n,
{
     if n <= 0 {
         false
     } else if n == 1 {
         true
     } else {
         n % 2 == 0 && is_power_of_two(n / 2)
     } 
}

use vstd::bits::lemma_u64_low_bits_mask_is_mod;

#[cfg(target_pointer_width = "64")]
proof fn lemma_usize_low_bits_mask_is_mod(x: usize, n: nat) {
    lemma_u64_low_bits_mask_is_mod(x as u64, n);
}

} // verus!
