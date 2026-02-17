extern crate rlsf_verified;
use std::hint::black_box;
use std::mem::MaybeUninit;
use std::ptr::NonNull;

const BUF_SIZE: usize = 65536;
const FLLEN: usize = 12;
const SLLEN: usize = 16;

pub fn run_verified(size: usize, iters: usize) {
    use rlsf_verified::{parameters::GRANULARITY, round_up, Tlsf};
    let mut pool = [MaybeUninit::<u8>::uninit(); BUF_SIZE];
    let mut tlsf = Tlsf::<FLLEN, SLLEN>::new();
    // align varies
    let align = size.next_power_of_two();
    unsafe {
        let block = NonNull::new((&mut pool) as *mut [_] as _).unwrap();
        let unaligned_start = block.as_ptr() as *mut u8;
        let start = round_up(unaligned_start, GRANULARITY);
        let size = BUF_SIZE;
        tlsf.insert_free_block_ptr_aligned_test(start as *mut u8, size);
    }

    for _ in 0..iters {
        unsafe {
            let (p, _, _) = tlsf.allocate(black_box(size), align).unwrap();
            black_box(p);
            tlsf.deallocate_ext(p, align);
        }
    }
}

pub fn run_original(size: usize, iters: usize) {
    use rlsf::Tlsf;
    use std::alloc::Layout;
    let layout = Layout::from_size_align(size, size.next_power_of_two()).unwrap();

    let mut pool = [MaybeUninit::uninit(); BUF_SIZE];

    let mut tlsf: Tlsf<'_, u16, u16, FLLEN, SLLEN> = Tlsf::new();
    tlsf.insert_free_block(&mut pool);

    for _ in 0..iters {
        unsafe {
            let mut p = tlsf.allocate(layout).unwrap();
            black_box(p);
            tlsf.deallocate(p, layout.align());
        }
    }
}
