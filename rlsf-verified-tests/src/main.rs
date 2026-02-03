extern crate rlsf_verified;
use rlsf_verified::{Tlsf, parameters::GRANULARITY, round_up};
use std::num::NonZeroUsize;
use std::slice::SliceIndex;
use std::{alloc::Layout, cell::UnsafeCell, mem::MaybeUninit, ptr::NonNull};

fn main() {
    let mut pool = [MaybeUninit::<u8>::uninit(); 65536];
    let mut tlsf = Tlsf::<12usize, 16usize>::new();
    unsafe {
        let block = NonNull::new((&mut pool) as *mut [_] as _).unwrap();

        let unaligned_start = block.as_ptr() as *mut u8;
        let start = round_up(unaligned_start, GRANULARITY);
        let size = 65536;
        tlsf.insert_free_block_ptr_aligned_test(start as *mut u8, size);
        tlsf.print_stat();
        let mut i = 0;
        while let Some((m, _, _)) = tlsf.allocate((i + 1) * 32, GRANULARITY) {
            *m.as_mut().unwrap() = 0;
            i += 1;
        }
        println!("num allocated: {}", i);
    }
}
