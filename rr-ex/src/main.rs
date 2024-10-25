#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(core_intrinsics)]
#![feature(const_mut_refs)]
#![feature(const_ptr_write)]
//#![rr::import("extras.shims")]
//#![rr::include("ptr")]
//#![rr::include("mem")]

mod utils;
use std::ptr;
use std::ptr::NonNull;
use rrptr::RNonNull;

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


//#[rr::trust_me]
#[rr::refined_by("(s, ppb)" : "(Z * option (place_rfn loc))%type")]
#[rr::invariant("s >= 32 (* GRANULARITY *)")] 
struct BlockHdr {
    #[rr::field("s")]
    size: usize,
    #[rr::field("ppb")]
    prev_phys_block: Option<*const BlockHdr>,
}


#[rr::refined_by("l" : "loc")]
#[rr::invariant("l ≠  NULL_loc")]
struct NonNullFBH {
    // NOTE: mutability of raw pointer differs from the original NonNull
    //      this is just for simplicity.
    #[rr::field("l")]
    x: *mut FreeBlockHdr
}

// Copied from ptr::NonNull
impl NonNullFBH {
    pub const unsafe fn new(ptr: *mut FreeBlockHdr) -> NonNullFBH {
        NonNullFBH { x: ptr as _ }
    }

    #[rr::params("l" : "loc", "v", "α")]
    #[rr::args("l")]
    #[rr::requires("l ↦ v ∗ ⌜ l `has_layout_loc` {ly_of FreeBlockHdr_ty} ⌝ ∗ ⌜ v `has_layout_val` {ly_of FreeBlockHdr_ty} ⌝")]
    #[rr::returns("(#v, α)" @ "shr_ref NoNullFBH_ty {'a} ")]
    pub const unsafe fn as_mut<'a>(&mut self) -> &'a mut FreeBlockHdr {
           unsafe { &mut *self.x }
    }
}

impl Clone for NonNullFBH {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl Copy for NonNullFBH {}

//#[rr::trust_me]
// FIXME: why `*const FreeBlockHdr` works but `NonNull<FreeBlockHdr>` doesn't?
#[rr::refined_by("(b, nf, pf)" : "((Z * option (place_rfn loc)) * option (place_rfn loc) * option (place_rfn loc))")]
struct FreeBlockHdr {
    #[rr::field("b")]
    common: BlockHdr,
    #[rr::field("nf")]
    next_free: Option<NonNullFBH>,
    #[rr::field("pf")]
    prev_free: Option<NonNullFBH>,
}

const SLLEN: usize = 4usize;
const FLLEN: usize = 8usize;

//#[rr::trust_me]
#[rr::refined_by("(flbm, slbm, freelist)" : "(Z * loc * loc)")]
pub struct Tlsf
//<'pool, const FLLEN: usize, const SLLEN: usize>
{
    #[rr::field("flbm")]
    fl_bitmap: usize,
    #[rr::field("slbm")]
    /// `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
    // [usize; FLLEN]
    sl_bitmap: *mut usize,
    // TODO: find way work with static arrays
    #[rr::field("freelist" @ "array_t (array_t (std_option_Option_ty (place_rfn loc)) 4 (* SLLEN *)) 8 (* FLLEN *)")]
    first_free: *mut (*mut Option<NonNullFBH>),
    //#[rr::field("tt")]
    //_phantom: PhantomData<&'pool ()>,
}

impl Tlsf
//<'_, 8usize, 4usize>
{
//impl<const FLLEN: usize, const SLLEN: usize> Tlsf<'_, FLLEN, SLLEN> {
    #[rr::params("m" : "block_matrix", "fl", "sl")]
    #[rr::args("#(_, _, m)", "fl", "sl")]
    #[rr::requires("0 ≤ fl < 8 (* FLLEN *)")]
    #[rr::requires("0 ≤ sl < 4 (* SLLEN *)")]
    #[rr::returns("#(m !! (fl, sl))")]
    #[inline]
    unsafe fn get_first_free<'a>(&'a mut self, fl: usize, sl: usize) -> &'a mut Option<NonNullFBH> {
        //debug_assert!(fl < FLLEN);
        //debug_assert!(sl < SLLEN);
        //self.first_free[fl][sl]
        let sl_list: *mut Option<NonNullFBH> = *rrptr::mut_add(self.first_free, fl); // self.first_free[fl]
        &mut *rrptr::mut_add(sl_list, sl)
    }
}

// FIXME
//#[rr::refined_by("(n, x)": "(loc * Z)")]
////#[rr::invariant(#own "freeable n (size_of_st Silly_st) 1 HeapAlloc")]
//pub struct Silly {
//    #[rr::field("n")]
//    n: *const Silly,
//    #[rr::field("x")]
//    x: usize
//}
//#[rr::params("z" : "Z")]
//#[rr::args("z" @ "int usize_t")]
////#[rr::exists("l")]
////#[rr::returns("(l, z)")]
//#[rr::returns("z" @ "int usize_t")]
//pub fn silly(u: usize) -> usize {
    //let a = Silly {
        //x: u,
        //n: rrptr::dangling(),
    //};

    //let b = Silly {
        //x: u,
        //n: &a
    //};
    //return unsafe { (&*b.n).x };
    ////return b;
//}


//#[rr::exists("l")]
//#[rr::returns("(l, 1)")]
//pub fn sill() -> Silly {
    //Silly {
        //x: 1,
        //n: rrptr::dangling()
    //}
//}

#[rr::shim("box_new", "type_of_box_new")]
fn box_new<T>(x: T) -> Box<T> {
    Box::new(x)
}

//#[rr::trust_me]
#[rr::params("flbm", "slbm", "freelist", "ls" : "option loc", "α", "blk" : "option loc", "β", "sz")]
#[rr::args("(#(flbm, slbm, freelist), γ)", "(#blk, β)", "sz" @ "int usize_t")]
unsafe fn link_free_block(tlsf: &mut Tlsf, mut block: NonNullFBH, size: usize) {
    let first_free = tlsf.get_first_free(1, 1);
    let next_free = rrptr::replace(first_free, Some(block));
    block.as_mut().next_free = next_free;
    block.as_mut().prev_free = None;
    if let Some(mut next_free) = next_free {
        next_free.as_mut().prev_free = Some(block);
    }
}

//#[rr::params("u", "l")]
//#[rr::args("u" @ "int usize_t", "l" @ "alias_ptr_t")]
//#[rr::returns("u")]
unsafe fn ptr_rw(u: usize, l: *mut usize) -> usize {
    ptr::write(l, u);
    rrptr::read::<usize>(l)
}

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

    // FIXME: This possibly cause inconsistency, we must specialize to some struct. cf.
    // `type_of_ptr_read`
    //#[rr::shim("ptr_read_ax", "type_of_ptr_read_ax")]
    pub unsafe fn read<T>(ptr: *mut T) -> T {
        ptr.read()
    }


    #[rr::refined_by("l" : "loc")]
    #[rr::invariant("l ≠  NULL_loc")]
    pub struct RNonNull<T: ?Sized> {
        #[rr::field("l")]
        pointer: *const T,
    }


    //#[rr::export_as(core::ptr::NonNull)]
    //#[rr::only_spec]
    //impl<T> NonNull<T> {

        //#[rr::params("l" : "loc")]
        //#[rr::args("l" @ "alias_ptr_t")]
        //#[rr::requires("l ≠  NULL_loc")]
        //#[rr::ensures("l ≠  NULL_loc")]
        //#[rr::returns("l")]
        //pub const unsafe fn new_unchecked(ptr: *mut T) -> Self {
            //unimplemented!()
        //}

        //#[rr::params("l" : "loc")]
        //#[rr::args("l" @ "alias_ptr_t")]
        //#[rr::returns("if decide (l ≠ NULL_loc) then Some #l else None")]
        //pub const fn new(ptr: *mut T) -> Option<Self> {
            //unimplemented!()
        //}
    //}

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
}
