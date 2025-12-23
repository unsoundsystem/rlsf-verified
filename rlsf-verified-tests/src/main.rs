extern crate rlsf_verified;
use rlsf_verified::{Tlsf, parameters::GRANULARITY, round_up};
use std::num::NonZeroUsize;
use std::slice::SliceIndex;
use std::{alloc::Layout, cell::UnsafeCell, mem::MaybeUninit, ptr::NonNull};

fn main() {
    let mut pool = [MaybeUninit::<u8>::uninit(); 65536];
    let mut tlsf = Tlsf::<12usize, 16usize>::new();
    unsafe {
        let buf_ptr = NonNull::new((&mut pool) as *mut [_] as _).unwrap();
        insert_free_block_ptr(&mut tlsf, buf_ptr);
        tlsf.allocate(32, GRANULARITY);
    }
}

pub unsafe fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize {
    (&*(ptr.as_ptr() as *const [MaybeUninit<UnsafeCell<T>>])).len()
}

pub unsafe fn insert_free_block_ptr<const F: usize, const S: usize>(
    tlsf: &mut Tlsf<F, S>,
    block: NonNull<[u8]>,
) -> Option<NonZeroUsize> {
    let len = nonnull_slice_len(block);

    // Round up the starting address
    let unaligned_start = block.as_ptr() as *mut u8;
    let start = round_up(unaligned_start, GRANULARITY);

    let len = if let Some(x) = len
        .checked_sub((start as usize).wrapping_sub(unaligned_start as usize))
        .filter(|&x| x >= GRANULARITY * 2)
    {
        // Round down
        x & !(GRANULARITY - 1)
    } else {
        // The block is too small
        return None;
    };

    // Safety: The slice being created here
    let pool_len = tlsf.insert_free_block_ptr_aligned_test(start as *mut u8, len)?;

    // Safety: The sum should not wrap around because it represents the size
    //         of a memory pool on memory
    //Some(NonZeroUsize::new_unchecked(
    //pool_len.get() + (start as usize).wrapping_sub(unaligned_start as usize),
    //))
    None
}
