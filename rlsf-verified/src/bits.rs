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
use vstd::arithmetic::logarithm::log;

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

proof fn usize_trailing_zeros_is_log2_when_pow2_given(x: usize)
    requires is_power_of_two(x as int)
    ensures usize_trailing_zeros(x) == log(2, x as int)
{
    axiom_usize_trailing_zeros(x);
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

// TODO: more properties about rotating shift? e.g. rotated bits appears at (shift_amount mod BITS)
//       there, stating only "`rotate_right` is equivalent to less efficient software emulation" ...
pub open spec fn is_usize_rotate_right(x: usize, r: usize, n: int) -> bool {
    let sa: nat = abs(n) as nat % usize::BITS as nat;
    let sa_ctr: nat = (usize::BITS as nat - sa) as nat;
    // TODO: justification
    &&& (n == 0) ==> (r == x)
    &&& (n > 0) ==> r == ((x & high_mask(sa)) >> sa | ((x & low_mask(sa)) << (sa_ctr)))
    &&& (n < 0) ==> r == ((x & low_mask(sa_ctr)) << sa | ((x & high_mask(sa)) >> (sa_ctr)))
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
    // TODO: is it ok? primitive cast really just reinterpet bytes?
    is_usize_rotate_right(x, r, n as i32 as int)
    { x.rotate_right(n) }

use vstd::bits::*;
use vstd::arithmetic::power2::*;
proof fn example() {
    reveal(pow2);
    //reveal(low_bits_mask);
    lemma_low_bits_mask_values();
    //assert(low_mask(1) == 1);
    //assert((1usize & !1) >> 1 | (1usize & 1) << 63 == 1usize << 63) by (bit_vector);
    //assert((1 & high_mask(1)) >> 1 | ((1 & low_mask(1)) << 63) == (1usize << 63)) by (compute);
    //reveal(abs);
    //assert(abs(1) % usize::BITS as nat == 1);
    //assert(usize::BITS == 64);
    assert(is_usize_rotate_right(1, 1usize << 63, 1)) by (compute);
    assert(is_usize_rotate_right(1usize << 63, 1, -1)) by (compute);
    assert(is_usize_rotate_right(0xbeef00000000dead, 0xdeadbeef, -16)) by (compute);
    assert(is_usize_rotate_right(0xbeef00000000dead, 0xdeadbeef00000000, 16)) by (compute);
    assert(is_usize_rotate_right(0xdeadbeef, 0xdeadbeef, 128)) by (compute);
    assert(is_usize_rotate_right(0xdeadbeef, 0xdeadbeef, -128)) by (compute);
    //assert(u32::MAX as i32 as int == -1) by (bit_vector);
    assert(0xfffffff0u32 as i32 as int == -16int) by (bit_vector);
    assert(is_usize_rotate_right(0xbeef00000000dead, 0xdeadbeef, 0xfffffff0u32 as i32 as int));
    // NOTE: 
    // - it seems `0xXXXu32 as i32` can be solved by bit_vector only 
    //   (by (compute) doesn't terminate)
    // - lemma around `usize_rotate_right` requires separate `assert` for `0xXXu32 as i32`
    // TODO:
    // - resoning abstractly about `usize_rotate_right` requires lemmas about unsigned to signed
    //   cast.
}

proof fn unsigned_to_signed(n: u32)
    ensures
        0 <= n && n <= 0x7fffffffu32 ==> (n as i32 as int) >= 0,
        0x7fffffff < n ==> (n as i32 as int) < 0,
{
    if 0 <= n && n <= 0x7fffffffu32 {
        assert((n as i32 as int) >= 0) by (bit_vector)
            requires 0 <= n && n <= 0x7fffffffu32;
    } else {
        assert((n as i32 as int) < 0) by (bit_vector)
            requires 0x7fffffff < n;
    };
    //assert((0 <= n <= 0x7fffffffu32) ==> n as i32 as int >= 0)
}


//proof fn rotate_right_mod_0_id(x: usize, n: u32)
    //requires n % usize::BITS == 0
    //ensures usize_rotate_right

//pub open spec fn usize_view(x: usize) -> Seq<bool> {
//Seq::new(8*vstd::layout::size_of::<usize>(), |i: int| nth_bit!(x, i as usize))
//}

//pub open spec fn seq_rotate_right_pos(x: int, bs: Seq<bool>) -> Seq<bool>
//recommends x > 0
//{
//let rot = x % bs.len();
//bs.drop_first(rot).add(bs.subrange(bs.len() - rot, bs.len()))
//}

//pub open spec fn seq_rotate_right_neg(x: int, bs: Seq<bool>) -> Seq<bool>
//recommends x > 0
//{
//let rot = x % bs.len();
//bs.subrange(bs.len() - rot, bs.len()).add(bs.drop(rot))
//}

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
