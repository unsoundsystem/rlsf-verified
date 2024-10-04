#![rr::import("extras", "bitops")]
#![rr::import("caesium", "int_type")]

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
#[rr::returns("Z.min (x + y) (max_int usize_t)")]
pub fn saturating_add(lhs: usize, rhs: usize) -> usize {
    lhs.saturating_add(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::requires("x ∈ usize_t", "y ∈  usize_t")]
#[rr::returns("Z.max (x - y) (min_int usize_t)")]
pub fn saturating_sub(lhs: usize, rhs: usize) -> usize {
    lhs.saturating_sub(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::requires("x ∈ usize_t", "y ∈  usize_t")]
#[rr::returns("if decide (x > y) then x - y else max_int usize_t + (x - y)")]
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
pub fn leading_zeros(u: usize) -> u32 {
    u.leading_zeros()
}

pub fn trailing_zeros(u: usize) -> u32 {
    u.trailing_zeros()
}

mod examples {
    use super::*;

    // TODO: Make this work (sidecondisions remain when using above defined specifications with
    //       bitwise ops.
    #[rr::returns("Z.shiftl 1 63")]
    fn rotr_higher() -> usize {
        let x: usize = 1;
        let sa: u32 = 1;
        rotate_right(x, sa)
    }
}
