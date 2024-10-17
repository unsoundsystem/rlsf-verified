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

use core::marker::PhantomData;
#[rr::trust_me]
#[rr::refined_by("(s, ppb)" : "(Z * option (place_rfn loc))%type")]
#[rr::invariant("s >= 32 (* GRANULARITY *)")] 
struct BlockHdr {
    #[rr::field("s")]
    size: usize,
    #[rr::field("ppb")]
    prev_phys_block: Option<*const BlockHdr>,
}


#[rr::trust_me]
#[rr::refined_by("(b, nf, pf)" : "((Z * option (place_rfn loc)) * option (place_rfn loc) * option (place_rfn loc))")]
struct FreeBlockHdr {
    #[rr::field("b")]
    common: BlockHdr,
    #[rr::field("nf")]
    next_free: Option<*const FreeBlockHdr>,
    #[rr::field("pf")]
    prev_free: Option<*const FreeBlockHdr>,
}

#[rr::trust_me]
#[rr::refined_by("(flbm, slbm, freelist)": "(Z * list Z * list (list (option (place_rfn loc))))")]
#[rr::invariant("freelist" @ "array_t (array_t (option (place_rfn loc)) 4 (* SLLEN *)) 8 (* FLLEN *)")]
pub struct Tlsf<'pool, const FLLEN: usize, const SLLEN: usize> {
    #[rr::field("flbm")]
    fl_bitmap: usize,
    #[rr::field("slbm")]
    /// `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
    sl_bitmap: [usize; FLLEN],
    #[rr::field("freelist")]
    first_free: [[Option<*const FreeBlockHdr>; SLLEN]; FLLEN],
    #[rr::field("tt")]
    _phantom: PhantomData<&'pool ()>,
}

// FIXME
//#[rr::trust_me]
//#[rr::refined_by("(x, n)": "(Z * loc)")]
//struct Silly {
    //#[rr::field("x")]
    //x: usize,
    //#[rr::field("n" @ "alias_ptr_t")]
    //n: *const Silly
//}
//#[rr::params("z" : "Z")]
//#[rr::args("z" @ "int usize_t")]
//#[rr::returns("z")]
//fn silly(u: usize) -> usize {
    //let a = Box::new(Silly {
        //x: u,
        //n: rrptr::dangling(),
    //});

    //let b = Silly {
        //x: 0x5e14,
        //n: &*a
    //};
    //return unsafe { (&*b.n).x };
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
    //assert_eq!(utils::rotate_right(1, u32::MAX), 2);
    //assert!(a.prev_phys_block.is_none());
    //let x = A { e: 1, next: std::ptr::null() };
    //assert_eq!(x.e, 1);
    //let x = FreeBlockHdr {
        //common: BlockHdr {
            //size: 32,
            //prev_phys_block: None
        //},
        //next_free: None,
        //prev_free: None
    //};
    //let a = silly(42);
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


mod rrptr {
    use std::ptr::NonNull;


    #[rr::shim("ptr_dangling", "type_of_ptr_dangling")]
    pub fn dangling<T>() -> *mut T{
        NonNull::dangling().as_ptr()
    }

    // We only need these shims because we cannot get their DefIds in the frontend currently..
    #[rr::shim("ptr_offset", "type_of_ptr_offset")]
    pub unsafe fn mut_offset<T>(ptr: *mut T, count: isize) -> *mut T {
        ptr.offset(count)
    }

    #[rr::shim("ptr_add", "type_of_ptr_offset")]
    pub unsafe fn const_offset<T>(ptr: *const T, count: isize) -> *const T {
        ptr.offset(count)
    }
    #[rr::shim("ptr_add", "type_of_ptr_add")]
    pub unsafe fn mut_add<T>(ptr: *mut T, count: usize) -> *mut T {
        ptr.add(count)
    }

    #[rr::shim("ptr_add", "type_of_ptr_add")]
    pub unsafe fn const_add<T>(ptr: *const T, count: usize) -> *const T {
        ptr.add(count)
    }
}
