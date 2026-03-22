extern crate rlsf_verified;
use rlsf_verified::{parameters::GRANULARITY, Tlsf};
use std::hint::black_box;
use std::mem::MaybeUninit;

#[repr(align(32))] // GRANULARITY == 32
struct AlignedPool([MaybeUninit<u8>; 65536]);

fn main() {
    for i in 0..200000 {
        let mut pool = AlignedPool([MaybeUninit::uninit(); 65536]);
        let mut tlsf = Tlsf::<12usize, 16usize>::new();
        unsafe {
            let start = pool.0.as_mut_ptr() as *mut u8;
            tlsf.insert_free_block_ptr_aligned_test(start, 65536);
            for i in 1..200 {
                let (x, _, _) = tlsf
                    .allocate(black_box(size_of::<usize>() * i), GRANULARITY)
                    .unwrap();
                *x.as_mut().unwrap() = 1;
                //println!("x = {:?}", x);
                tlsf.deallocate_ext(x, GRANULARITY);
            }
        }
    }
}
