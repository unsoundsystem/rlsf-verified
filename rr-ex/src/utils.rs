#![rr::import("extras", "bitops")]
#![rr::import("extras", "model")]
#![rr::import("caesium", "int_type")]
//#![rr::include("option")]

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
#[rr::args("x" @ "int u32", "y" @ "int u32")]
#[rr::returns("if decide (x > y) then x - y else int_modulus u32 + (x - y)")]
pub fn wrapping_sub_u32(lhs: u32, rhs: u32) -> u32 {
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

     //#[rr::returns("-[1;1]" @ "tuple2_ty (int USize) (int USize)")]
     //fn silly() -> (usize, usize) {
         //(1, 1)
     //}
     //
     //#[rr::params("x" : "Z", "y" : "Z")]
     //#[rr::args("x" @ "usize_t", "y" @ "usize_t")]
     //#[rr::returns("-[#x;#y]" @ "tuple2_ty (int USize) (int USize)")]
     //fn silly3(x: usize, y: usize) -> (usize, usize) {
         //(x, y)
     //}

     //#[rr::returns("[1;1]")]
     //fn silly2() -> [usize; 2] {
         //[1, 1]
     //}

     #[rr::refined_by("Z")]
     const GRANULARITY: usize = core::mem::size_of::<usize>() * 4;
     #[rr::refined_by("Z")]
     const GRANULARITY_LOG2: u32 = GRANULARITY.trailing_zeros();
     const SLLEN: usize = 4usize;
     const FLLEN: usize = 8usize;
     const SLI: u32 = SLLEN.trailing_zeros();

    // > Find the free block list to store a free block of the specified size.
    // ensures("block_size_range res size")
    //  TODO: use conditional compilation or something to avoid hardcoding `GRANULARITY`.
    #[rr::params("size" : "Z", "fl" : "Z", "sl" : "Z")]
    #[rr::args("size" @ "int usize_t")]
    //#[rr::requires("fl" @ "Z", "sl" : "Z")]
    #[rr::requires("(Z.ge size 32) (* GRANULARITY *)")]
    #[rr::requires("(size `mod` 32 = 0)%Z (* GRANULARITY = 32 *)")]
    #[rr::returns("if decide (Z.ge (fl - (Z.log2 size) - 5 (* GRANULARITY_LOG2 *)) 8)%Z then None else Some #(-[#fl; #sl])%Z")]
    #[rr::ensures("block_size_range 4 (* SLLEN *) (fl, sl) size")]
    #[rr::ensures("block_index_valid 8 (* FLLEN *) 4 (* SLLEN *) (fl, sl)")]
    // false due to the mask #[rr::ensures("Z.testbit (sl >> Z.log2 SLLEN) 0")]
    fn map_floor(size: usize) -> Option<(usize, usize)> {
        //debug_assert!(size >= GRANULARITY);
        //debug_assert!(size % GRANULARITY == 0);
        let fl = usize::BITS - GRANULARITY_LOG2 - 1 - leading_zeros(size);

        // The shift amount can be negative, and rotation lets us handle both
        // cases without branching. Underflowed digits can be simply masked out
        // in `map_floor`.
        let sl = rotate_right(size, wrapping_sub_u32((fl + GRANULARITY_LOG2), SLI));

        // The most significant one of `size` should be now at `sl[SLI]`
        //debug_assert!(((sl >> SLI) & 1) == 1);

        // `fl` must be in a valid range
        if fl as usize >= FLLEN {
            return None;
        }

        Some((fl as usize, sl & (SLLEN - 1)))
    }

    #[rr::params("b" : "bool")]
    #[rr::args("b" @ "bool_t")]
    #[rr::returns("if b then Some #b else None")]
    fn silly_option(b: bool) -> Option<bool> {
        if b {
            Some(true)
        } else {
            None
        }
    }

    // OOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOhKey
    #[rr::returns("-[#1; #1]")]
    fn silly_tuple() -> (usize, usize) {
        (1, 1)
    }

     //fn index_calc() -> usize {
         //let granularity = core::mem::size_of::<usize>() * 4;
         //let granularity_log2 = granularity.trailing_zeros();
         //let size: usize = granularity_log2 + 1;
         //let fl = usize::BITS - GRANULARITY_LOG2 - 1 - size.leading_zeros();
         //let sl = size.rotate_right((fl + GRANULARITY_LOG2).wrapping_sub(Self::SLI));
         //unimplemented!()
     //}
 }
