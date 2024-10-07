#![rr::import("extras", "bitops")]
#![rr::import("caesium", "int_type")]

// TODO: How to handle *negative* usize?
#[rr::only_spec]
#[rr::params("x" : "Z", "n" : "Z")]
#[rr::args("x" @ "int usize_t", "n" @ "int u32")]
#[rr::returns("rotate_right_usize x n")]
pub fn rotate_right(lhs: usize, rhs: u32) -> usize {
    lhs.rotate_right(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::args("x" @ "int usize_t", "y" @ "int usize_t")]
#[rr::returns("Z.min (x + y) (max_int usize_t)")]
pub fn saturating_add(lhs: usize, rhs: usize) -> usize {
    lhs.saturating_add(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::args("x" @ "int usize_t", "y" @ "int usize_t")]
#[rr::returns("Z.max (x - y) (min_int usize_t)")]
pub fn saturating_sub(lhs: usize, rhs: usize) -> usize {
    lhs.saturating_sub(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::args("x" @ "int usize_t", "y" @ "int usize_t")]
#[rr::returns("if decide (x > y) then x - y else int_modulus usize_t + (x - y)")]
pub fn wrapping_sub(lhs: usize, rhs: usize) -> usize {
    lhs.wrapping_sub(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::args("x" @ "int usize_t", "y" @ "int usize_t")]
#[rr::returns("wrap_unsigned (x + y) usize_t")]
pub fn wrapping_add(lhs: usize, rhs: usize) -> usize {
    lhs.wrapping_add(rhs)
}

#[rr::only_spec]
#[rr::params("x" : "Z")]
#[rr::args("x" @ "int usize_t")]
// TODO: `Z.log2` must not appear in this spec
#[rr::returns("count_leading_zeros usize_t x")]
pub fn leading_zeros(u: usize) -> u32 {
    u.leading_zeros()
}

// TODO
pub fn trailing_zeros(u: usize) -> u32 {
    u.trailing_zeros()
}

 mod examples {
     use super::*;
 
     #[rr::returns("Z.shiftl 1 63")]
     fn rotr_higher() -> usize {
         let x: usize = 1;
         let sa: u32 = 1;
         rotate_right(x, sa)
     }

     #[rr::returns("max_int usize_t")]
     fn wrap_sub_max() -> usize {
         wrapping_sub(0, 1)
     }

     #[rr::returns("0")]
     fn wrap_add_max() -> usize {
         wrapping_add(usize::MAX, 1)
     }

     #[rr::returns("max_int usize_t")]
     fn sat_add_max() -> usize {
         saturating_add(usize::MAX, 1)
     }

     #[rr::returns("0")]
     fn sat_sub_min() -> usize {
         saturating_sub(0, 1)
     }

     #[rr::returns("62")]
     fn clz_2() -> u32 {
         leading_zeros(2)
     }
 }
