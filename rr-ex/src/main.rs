#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(core_intrinsics)]

const SIZE_USED: usize = 1;

#[rr::params(z)]
#[rr::args("z")]
#[rr::requires("z ∈ usize_t")]
#[rr::returns("negb (Z.land z 1 =? 0)")]
fn bitop(x: usize) -> bool {
    (x & SIZE_USED) != 0
}

#[rr::params(z)]
#[rr::requires("z ∈ usize_t")]
#[rr::returns("max_int usize_t")]
fn usizeops() -> usize {
    rrusize::saturating_add(usize::MAX, usize::MAX)
}


#[rr::params(z)]
#[rr::invariant("z ∈ usize_t")] 
#[rr::field("size @ z")]
struct BlockHdr {
    size: usize,
    prev_phys_block: Option<Box<BlockHdr>>,
}

fn main() {
    assert!(bitop(0xfusize));
    assert_eq!(usizeops(), usize::MAX);
    let a = BlockHdr { size: 1, prev_phys_block: None };
    assert_eq!(a.size, 1);
    assert!(a.prev_phys_block.is_none());
}

mod rrusize {

    //thread 'rustc' panicked at /rustc/ca2b74f1ae5075d62e223c0a91574a1fc3f51c7c/compiler/rustc_hir/src/def.rs:617:45:
    //attempted .def_id() on invalid res: PrimTy(Uint(Usize))
    // https://github.com/rust-lang/rust/blob/master/compiler/rustc_hir/src/def.rs#L677
    // primitive typeにはdefidが付かない？っぽいのでusizeのメソッド呼び出しを含むような記述は書き換
    // えたほうが良さそう
    // なんにせよllvm intrinsicになるので外部APIとしてspecを書くことしかできない
    // 適当に関数でラップしつつ内部でメソッド呼び出しして#[rr::only_spec]でも良いかも
    #[rr::shim("saturating_add", "saturating_add_spec")]
    pub fn saturating_add(u1: usize, u2: usize) -> usize {
        core::intrinsics::saturating_add(u1, u2)
    }
}
