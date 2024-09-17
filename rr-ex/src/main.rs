#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(core_intrinsics)]

mod utils;
use std::ptr::NonNull;

const SIZE_USED: usize = 1;

#[rr::params(z)]
#[rr::args("z")]
#[rr::requires("z ∈ usize_t")]
#[rr::returns("negb (Z.land z 1 =? 0)")]
fn bitop(x: usize) -> bool {
    (x & SIZE_USED) != 0
}

//#[rr::params(z)]
//#[rr::requires("z ∈ usize_t")]
//#[rr::returns("max_int usize_t")]
//fn usizeops() -> usize {
    //rrusize::saturating_add(usize::MAX, usize::MAX)
//}


//#[rr::params(z)]
//#[rr::invariant("z ∈ usize_t")] 
//#[rr::refined_by("(s, b)" : "(Z * option (place_rfn loc))")]
//struct BlockHdr {
    //#[rr::field("s")]
    //size: usize,
    //#[rr::field("b")]
    //prev_phys_block: Option<*const BlockHdr>,
//}
#[rr::returns("()")]
fn main() {
    assert!(bitop(0xfusize));
    //assert_eq!(usizeops(), usize::MAX);
    //let a = BlockHdr {
        //size: 1,
        //prev_phys_block: None
    //};
    //assert_eq!(a.size, 1);
    assert_eq!(utils::rotate_right(1, u32::MAX), 2);
    //assert!(a.prev_phys_block.is_none());
    //let x = A { e: 1, next: std::ptr::null() };
    //assert_eq!(x.e, 1);
}


//#[rr::refined_by("(e, xs)" @ "(Z * list Z)")]
//struct A {
    //#[rr::field("e" @ "Z")]
    //e: usize,
    //#[rr::field("next")]
    //next: *const A
//}

mod rrusize {

    //thread 'rustc' panicked at /rustc/ca2b74f1ae5075d62e223c0a91574a1fc3f51c7c/compiler/rustc_hir/src/def.rs:617:45:
    //attempted .def_id() on invalid res: PrimTy(Uint(Usize))
    // https://github.com/rust-lang/rust/blob/master/compiler/rustc_hir/src/def.rs#L677
    // primitive typeにはdefidが付かない？っぽいのでusizeのメソッド呼び出しを含むような記述は書き換
    // えたほうが良さそう
    // なんにせよllvm intrinsicになるので外部APIとしてspecを書くことしかできない
    // 適当に関数でラップしつつ内部でメソッド呼び出しして#[rr::only_spec]でも良いかも
    //#[rr::shim("saturating_add", "saturating_add_spec")]
    //pub fn saturating_add(u1: usize, u2: usize) -> usize {
        //core::intrinsics::saturating_add(u1, u2)
    //}
}


//mod rrptr {
    //use std::ptr::NonNull;


    //#[rr::shim("ptr_dangling", "type_of_ptr_dangling")]
    //pub fn dangling<T>() -> *mut T{
        //NonNull::dangling().as_ptr()
    //}

    //// We only need these shims because we cannot get their DefIds in the frontend currently..
    //#[rr::shim("ptr_offset", "type_of_ptr_offset")]
    //pub unsafe fn mut_offset<T>(ptr: *mut T, count: isize) -> *mut T {
        //ptr.offset(count)
    //}

    //#[rr::shim("ptr_add", "type_of_ptr_offset")]
    //pub unsafe fn const_offset<T>(ptr: *const T, count: isize) -> *const T {
        //ptr.offset(count)
    //}
    //#[rr::shim("ptr_add", "type_of_ptr_add")]
    //pub unsafe fn mut_add<T>(ptr: *mut T, count: usize) -> *mut T {
        //ptr.add(count)
    //}

    //#[rr::shim("ptr_add", "type_of_ptr_add")]
    //pub unsafe fn const_add<T>(ptr: *const T, count: usize) -> *const T {
        //ptr.add(count)
    //}
//}
