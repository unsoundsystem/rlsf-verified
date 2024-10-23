#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(const_mut_refs)]
#![feature(const_ptr_write)]
#![rr::package("refinedrust-stdlib-contrib")]
#![rr::coq_prefix("stdlib.mem")]
#![allow(unused)]

#[rr::export_as(core::mem::replace)]
#[rr::params("d", "γ", "s")]
#[rr::args("(#d, γ)", "s")]
#[rr::returns("d")]
#[rr::observe("γ" : "s")]
pub const fn replace<T>(dest: &mut T, src: T) -> T {
    unsafe {
        let result = core::ptr::read(dest);
        core::ptr::write(dest, src);
        result
    }
}
