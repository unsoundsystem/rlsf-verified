use vstd::prelude::*;

verus! {
use vstd::std_specs::bits::{
    u64_trailing_zeros, u64_leading_zeros,
    u32_leading_zeros, u32_trailing_zeros,
    ex_u64_leading_zeros, ex_u64_trailing_zeros,
    ex_u32_leading_zeros, ex_u32_trailing_zeros
};
use vstd::bytes::{spec_u32_to_le_bytes, spec_u64_to_le_bytes};
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
/// TODO: External specification for usize::rotate_right
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
pub fn usize_rotate_right(x: usize, n: u32) -> (r: usize)
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
    assert(low_mask(1) == 1);
    assert((1usize & !1) >> 1 | (1usize & 1) << 63 == 1usize << 63) by (bit_vector);
    assert((1 & high_mask(1)) >> 1 | ((1 & low_mask(1)) << 63) == (1usize << 63)) by (compute);
    reveal(abs);
    assert(abs(1) % usize::BITS as nat == 1);
    assert(usize::BITS - 1 == 63);
    assert(is_usize_rotate_right(1, 1usize << 63, 1)) ;
}

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

}
