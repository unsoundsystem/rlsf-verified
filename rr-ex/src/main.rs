#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

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
    //usize::MAX.saturating_add(usize::MAX)
//}

#[rr::params(z)]
#[rr::invariant("z ∈ usize_t")] 
#[rr::field("size @ z")]
struct BlockHdr {
    size: usize,
    prev_phys_block: Option<Box<BlockHdr>>,
}

fn main() {
    assert!(bitop(0xfusize));
    //assert_eq!(usizeops(), usize::MAX);
    let a = BlockHdr { size: 1, prev_phys_block: None };
    assert_eq!(a.size, 1);
    assert!(a.prev_phys_block.is_none());
}
