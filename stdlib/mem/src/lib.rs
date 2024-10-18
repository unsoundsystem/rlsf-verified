#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(const_mut_refs)]
#![rr::package("refinedrust-stdlib-contrib")]
#![rr::coq_prefix("stdlib.mem")]
#![allow(unused)]

// TODO: verify actual implementation?
#[rr::only_spec]
#[rr::export_as(core::mem::replace)]
#[rr::params("d", "γ", "s")]
#[rr::args("(#d, γ)", "s")]
#[rr::returns("d")]
#[rr::observe("γ" : "s")]
pub const fn replace<T>(dest: &mut T, src: T) -> T {
    unimplemented!()
}
