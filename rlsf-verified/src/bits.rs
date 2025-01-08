use vstd::prelude::*;

verus! {
use vstd::std_specs::bits::{
    u64_trailing_zeros, u64_leading_zeros,
    u32_leading_zeros, u32_trailing_zeros,
    ex_u64_leading_zeros, ex_u64_trailing_zeros,
    ex_u32_leading_zeros, ex_u32_trailing_zeros,
    axiom_u64_trailing_zeros
};
use vstd::bytes::{spec_u32_to_le_bytes, spec_u64_to_le_bytes};
use vstd::arithmetic::logarithm::{log, lemma_log_nonnegative};
use vstd::arithmetic::power::{pow, lemma_pow_adds};

//#[cfg(target_pointer_width = "32")]
//global layout usize is size == 4;

//#[cfg(target_pointer_width = "64")]
//global layout usize is size == 8;

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

#[verifier::external_body]
#[cfg(target_pointer_width = "32")]
pub const fn ex_usize_leading_zeros(x: usize) -> (r: u32)
    ensures
    0 <= r <= usize::BITS,
    r == u32_leading_zeros(x as u32)
{
    ex_u32_leading_zeros(x as u32)
}

#[verifier::external_body]
#[cfg(target_pointer_width = "64")]
pub const fn ex_usize_leading_zeros(x: usize) -> (r: u32)
    ensures
    0 <= r <= usize::BITS,
    r == u64_leading_zeros(x as u64)
{
    //ex_u64_leading_zeros(x as u64)
    (x as u64).leading_zeros()
}


#[cfg(target_pointer_width = "32")]
#[verifier::external_body]
pub const fn ex_usize_trailing_zeros(x: usize) -> (r: u32)
    ensures
    0 <= r <= usize::BITS,
    r == u32_trailing_zeros(x as u32)
{
    //ex_u32_trailing_zeros(x as u32)
    (x as u32).trailing_zeros()
}

#[cfg(target_pointer_width = "64")]
#[verifier::external_body]
pub const fn ex_usize_trailing_zeros(x: usize) -> (r: u32)
    ensures
    0 <= r <= usize::BITS,
    r == u64_trailing_zeros(x as u64)
{
    //ex_u64_trailing_zeros(x as u64)
    (x as u64).trailing_zeros()
}

#[cfg(target_pointer_width = "64")]
pub open spec fn spec_usize_to_le_bytes(x: usize) -> Seq<u8> {
    spec_u64_to_le_bytes(x as u64)
}

#[verifier::external_body]
#[cfg(target_pointer_width = "64")]
pub fn usize_to_le_bytes(x: usize) -> (r: [u8; 8])
    ensures
    spec_usize_to_le_bytes(x) == r@
{
    // NOTE: don't using u64_to_le_bytes in vstd because they using Vec<u8>
    x.to_le_bytes()
}

pub open spec fn spec_i32_from_le_bytes(b: Seq<u8>) -> i32
    recommends b.len() == 4
{
    (
        (b[0] as u32) | (b[1] as u32) << 8 | (b[2] as u32) << 16 | (b[3] as u32) << 24
    ) as i32
}


#[verifier::external_body]
pub fn u32_to_le_bytes(x: u32) -> (r: [u8; 4])
    ensures
    spec_u32_to_le_bytes(x) == r@
{
    // NOTE: don't using u32_to_le_bytes in vstd because they use Vec<u8>
    x.to_le_bytes()
}


#[verifier::external_body]
pub fn i32_from_le_bytes(b: [u8; 4]) -> (r: i32)
    ensures
    spec_i32_from_le_bytes(b@) == r
{
    i32::from_le_bytes(b)
}

use core::cmp::Ordering;
use builtin::*;
use vstd::math::abs;

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

proof fn lemma_usize_rotate_right_mod0_eq(x: usize, n: int)
    requires n % usize::BITS as int == 0
    ensures x == usize_rotate_right(x, n)
{
    //TODO
}

proof fn lemma_usize_rotate_right_reversible(x: usize, n: int)
    ensures x == usize_rotate_right(usize_rotate_right(x, n), -n)
{
    // TODO
}


use vstd::bits::low_bits_mask;
// mask with n or higher bits n+1..usize::BITS set
pub open spec fn high_mask(n: nat) -> usize {
    !low_mask(n)
}

// masks with bits 0..=n set
pub open spec fn low_mask(n: nat) -> usize {
    low_bits_mask(n) as usize
}

#[verifier::external_body]
pub fn ex_usize_rotate_right(x: usize, n: u32) -> (r: usize)
    ensures
    // This primitive cast just work as usual exec code
    // NOTE: is it ok? primitive cast really just reinterpet bytes?
    //      ref. `unsigned_to_signed`
    r == usize_rotate_right(x, n as i32 as int)
    { x.rotate_right(n) }

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

pub open spec fn usize_wrapping_sub(lhs: int, rhs: int) -> int {
    let sub = lhs - rhs;
    if sub < usize::MIN {
        sub + (usize::MAX - usize::MIN + 1)
    } else {
        sub
    }
}

proof fn example2() {
    assert(usize_wrapping_sub(1, 2) == usize::MAX as int);
    assert(usize_wrapping_sub(2, 1) == 1);
    assert(usize_wrapping_sub(usize::MIN as int, usize::MAX as int) == 1);
}

pub proof fn lemma_spec_wrapping_sub_usize_in_range(lhs: int, rhs: int)
    requires
        usize::MIN <= lhs <= usize::MAX,
        usize::MIN <= rhs <= usize::MAX,
    ensures
        usize::MIN <= usize_wrapping_sub(lhs, rhs) <= usize::MAX
{
        assert(usize::MIN <= usize_wrapping_sub(lhs, rhs) <= usize::MAX) by (compute);
}

#[verifier::external_body]
pub fn ex_usize_wrapping_sub(lhs: usize, rhs: usize) -> (r: usize)
    ensures r@ == usize_wrapping_sub(lhs as int, rhs as int)
{
    lhs.wrapping_sub(rhs)
}


pub open spec fn u32_wrapping_sub(lhs: int, rhs: int) -> int {
    let sub = lhs - rhs;
    if sub < u32::MIN {
        sub + (u32::MAX - u32::MIN + 1)
    } else {
        sub
    }
}

proof fn example4() {
    assert(u32_wrapping_sub(1, 2) == u32::MAX as int);
    assert(u32_wrapping_sub(2, 1) == 1);
    assert(u32_wrapping_sub(u32::MIN as int, u32::MAX as int) == 1);
}

pub proof fn lemma_spec_wrapping_sub_u32_in_range(lhs: int, rhs: int)
    requires
        u32::MIN <= lhs <= u32::MAX,
        u32::MIN <= rhs <= u32::MAX,
    ensures
        u32::MIN <= u32_wrapping_sub(lhs, rhs) <= u32::MAX
{
        assert(u32::MIN <= u32_wrapping_sub(lhs, rhs) <= u32::MAX) by (compute);
}

#[verifier::external_body]
pub fn ex_u32_wrapping_sub(lhs: u32, rhs: u32) -> (r: u32)
    ensures r@ == u32_wrapping_sub(lhs as int, rhs as int)
{
    lhs.wrapping_sub(rhs)
}


pub open spec fn usize_wrapping_add(lhs: int, rhs: int) -> int {
    let add = lhs + rhs;
    if add > usize::MAX {
        add - (usize::MAX - usize::MIN + 1)
    } else {
        add
    }
}

proof fn example3() {
    assert(usize_wrapping_add(usize::MAX as int, 1) == usize::MIN);
    assert(usize_wrapping_add(2, 1) == 3);
    assert(usize_wrapping_add(usize::MAX as int, usize::MAX as int) == usize::MAX - 1);
}

pub proof fn lemma_usize_wrapping_add_in_range(lhs: int, rhs: int)
    requires
        usize::MIN <= lhs <= usize::MAX,
        usize::MIN <= rhs <= usize::MAX,
    ensures
        usize::MIN <= usize_wrapping_add(lhs, rhs) <= usize::MAX
{
        assert(usize::MIN <= usize_wrapping_add(lhs, rhs) <= usize::MAX) by (compute);
}

#[verifier::external_body]
pub fn ex_usize_wrapping_add(lhs: usize, rhs: usize) -> (r: usize)
    ensures r@ == usize_wrapping_add(lhs as int, rhs as int)
{
    lhs.wrapping_add(rhs)
}


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

}
