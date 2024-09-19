#![rr::import("extras", "bitops")]
#![rr::import("caesium", "int_type")]

// TODO: negative case of `rhs`
// NOTE: n ∈ i32 due to usize as negative value (should find other way)
#[rr::only_spec]
#[rr::params("x" : "Z", "n" : "Z")]
#[rr::requires("x ∈ usize_t", "n ∈ i32")]
#[rr::returns("rotate_right_usize x n")]
pub fn rotate_right(lhs: usize, rhs: u32) -> usize {
    lhs.rotate_right(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::requires("x ∈ usize_t", "y ∈  usize_t")]
#[rr::returns("if decide (x + y ≤ max_int usize_t) then x + y else (max_int usize_t)")]
pub fn saturating_add(lhs: usize, rhs: usize) -> usize {
    lhs.saturating_add(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::requires("x ∈ usize_t", "y ∈  usize_t")]
#[rr::returns("if decide (x - y ≥ min_int usize_t) then x - y else (min_int usize_t)")]
pub fn saturating_add(lhs: usize, rhs: usize) -> usize {
    lhs.saturating_add(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::requires("x ∈ usize_t", "y ∈  usize_t")]
#[rr::returns("if decide (x > y) then x - y else max_int usize + (x - y)")]
pub fn wrapping_sub(lhs: usize, rhs: usize) -> usize {
    lhs.wrapping_sub(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::requires("x ∈ usize_t", "y ∈  usize_t")]
#[rr::returns("wrap_unsigned (x + y) usize_t")]
pub fn wrapping_add(lhs: usize, rhs: usize) -> usize {
    lhs.wrapping_add(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z")]
#[rr::requires("x ∈ usize_t")]
// TODO: `Z.log2` must not appear in this spec
//#[rr::returns("")]
pub fn leading_zeros(x: usize) -> usize {
}

pub fn trailing_zeros(u: usize) -> usize {
}
