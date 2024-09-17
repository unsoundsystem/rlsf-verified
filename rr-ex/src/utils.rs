#[rr::only_spec]
#[rr::params("x" : "Z", "n" : "Z")]
#[rr::requires("x" @ "usize_t", "n" @ "usize_t")]
#[rr::returns("rotate_right_usize x n")]
pub fn rotate_right(lhs: usize, rhs: u32) -> usize {
    lhs.rotate_right(rhs)
}
