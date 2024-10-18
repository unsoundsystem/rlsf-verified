#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::package("refinedrust-stdlib-contrib")]
#![rr::coq_prefix("stdlib.ptr.nonull")]
#![allow(unused)]

#[rr::refined_by("l" : "loc")]
#[rr::invariant("l ≠  NULL_loc")]
#[rr::export_as(core::ptr::NonNull)]
pub struct NonNull<T: ?Sized> {
    #[rr::field("l")]
    pointer: *const T,
}

#[rr::export_as(core::ptr::NonNull)]
#[rr::only_spec]
impl<T> NonNull<T> {

    #[rr::params("l" : "loc")]
    #[rr::args("l" @ "alias_ptr_t")]
    #[rr::requires("l ≠  NULL_loc")]
    #[rr::ensures("l ≠  NULL_loc")]
    #[rr::returns("l")]
    pub const unsafe fn new_unchecked(ptr: *mut T) -> Self {
        unimplemented!()
    }

    #[rr::params("l" : "loc")]
    #[rr::args("l" @ "alias_ptr_t")]
    #[rr::returns("if decide (l ≠ NULL_loc) then Some #l else None")]
    pub const fn new(ptr: *mut T) -> Option<Self> {
        unimplemented!()
    }
}
