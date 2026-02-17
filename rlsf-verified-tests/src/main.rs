extern crate rlsf_verified;
use rlsf_verified::{parameters::GRANULARITY, round_up, Tlsf};
use std::hint::black_box;
use std::mem::MaybeUninit;
use std::ptr::NonNull;

fn main() {
    for i in 0..200000 {
        let mut pool = [MaybeUninit::<u8>::uninit(); 65536];
        let mut tlsf = Tlsf::<12usize, 16usize>::new();
        unsafe {
            let block = NonNull::new((&mut pool) as *mut [_] as _).unwrap();

            let unaligned_start = block.as_ptr() as *mut u8;
            let start = round_up(unaligned_start, GRANULARITY);
            let size = 65536;
            tlsf.insert_free_block_ptr_aligned_test(start as *mut u8, size);
            for _ in 0..20 {
                let (x, _, _) = tlsf.allocate(black_box(32), GRANULARITY).unwrap();
                *x.as_mut().unwrap() = 1;
                println!("x = {:?}", x);
                tlsf.deallocate_ext(x, GRANULARITY);
            }
        }
    }
}
