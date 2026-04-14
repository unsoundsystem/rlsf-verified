extern crate rlsf_verified;
use std::hint::black_box;
use std::mem::MaybeUninit;

const BUF_SIZE: usize = 131072;
const FLLEN: usize = 12;
const SLLEN: usize = 16;

#[repr(align(32))] // GRANULARITY == 32
struct AlignedPool([MaybeUninit<u8>; BUF_SIZE]);

pub fn run_alt_verified(size: usize, iters: usize) {
    use rlsf_verified::{parameters::GRANULARITY, Tlsf};
    let mut pool = AlignedPool([MaybeUninit::uninit(); BUF_SIZE]);
    let mut tlsf = Tlsf::<FLLEN, SLLEN>::new();
    // align varies
    let align = size.next_power_of_two();
    unsafe {
        let start = pool.0.as_mut_ptr() as *mut u8;
        tlsf.insert_free_block_ptr_aligned_test(start, BUF_SIZE);
    }

    for _ in 0..iters {
        unsafe {
            let (p, _, _) = tlsf.allocate(black_box(size), align).unwrap();
            black_box(p);
            tlsf.deallocate_ext(p, align);
        }
    }
}

pub fn run_alt_original(size: usize, iters: usize) {
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

pub fn run_aaaddd_verified(size: usize, iters: usize) {
    use rlsf_verified::{parameters::GRANULARITY, Tlsf};
    let mut pool = AlignedPool([MaybeUninit::uninit(); BUF_SIZE]);
    let mut tlsf = Tlsf::<FLLEN, SLLEN>::new();
    let align = size.next_power_of_two();
    unsafe {
        let start = pool.0.as_mut_ptr() as *mut u8;
        tlsf.insert_free_block_ptr_aligned_test(start, BUF_SIZE);
    }

    for _ in 0..iters {
        unsafe {
            let (x1, _, _) = tlsf.allocate(black_box(size), align).unwrap();
            let (x2, _, _) = tlsf.allocate(black_box(size), align).unwrap();
            let (x3, _, _) = tlsf.allocate(black_box(size), align).unwrap();

            tlsf.deallocate_ext(black_box(x1), align);
            tlsf.deallocate_ext(black_box(x3), align);
            tlsf.deallocate_ext(black_box(x2), align);
        }
    }
}

pub fn run_aaaddd_original(size: usize, iters: usize) {
    use rlsf::Tlsf;
    use std::alloc::Layout;
    let layout = Layout::from_size_align(size, size.next_power_of_two()).unwrap();

    let mut pool = [MaybeUninit::uninit(); BUF_SIZE];

    let mut tlsf: Tlsf<'_, u16, u16, FLLEN, SLLEN> = Tlsf::new();
    tlsf.insert_free_block(&mut pool);

    for _ in 0..iters {
        unsafe {
            let x1 = black_box(tlsf.allocate(layout).unwrap());
            let x2 = black_box(tlsf.allocate(layout).unwrap());
            let x3 = black_box(tlsf.allocate(layout).unwrap());

            tlsf.deallocate(black_box(x1), layout.align());
            tlsf.deallocate(black_box(x3), layout.align());
            tlsf.deallocate(black_box(x2), layout.align());
        }
    }
}

pub fn run_deref_verified(size: usize, iters: usize) {
    use rlsf_verified::Tlsf;
    let mut pool = AlignedPool([MaybeUninit::uninit(); BUF_SIZE]);
    let mut tlsf = Tlsf::<FLLEN, SLLEN>::new();
    let align = size.next_power_of_two().min(4096);
    unsafe {
        let start = pool.0.as_mut_ptr() as *mut u8;
        tlsf.insert_free_block_ptr_aligned_test(start, BUF_SIZE);
    }

    for _ in 0..iters {
        unsafe {
            let (p, _, _) = tlsf.allocate(black_box(size), align).unwrap();
            core::ptr::write_bytes(p, black_box(0xABu8), size);
            let mut sum: u8 = 0;
            for i in 0..size {
                sum = sum.wrapping_add(*p.add(i));
            }
            black_box(sum);
            tlsf.deallocate_ext(p, align);
        }
    }
}

pub fn run_deref_original(size: usize, iters: usize) {
    use rlsf::Tlsf;
    use std::alloc::Layout;
    let layout = Layout::from_size_align(size, size.next_power_of_two().min(4096)).unwrap();

    let mut pool = [MaybeUninit::uninit(); BUF_SIZE];

    let mut tlsf: Tlsf<'_, u16, u16, FLLEN, SLLEN> = Tlsf::new();
    tlsf.insert_free_block(&mut pool);

    for _ in 0..iters {
        unsafe {
            let p = tlsf.allocate(layout).unwrap();
            let ptr = p.as_ptr();
            core::ptr::write_bytes(ptr, black_box(0xABu8), size);
            let mut sum: u8 = 0;
            for i in 0..size {
                sum = sum.wrapping_add(*ptr.add(i));
            }
            black_box(sum);
            tlsf.deallocate(p, layout.align());
        }
    }
}

pub fn run_coalesce_verified(size: usize, iters: usize) {
    use rlsf_verified::Tlsf;
    let mut pool = AlignedPool([MaybeUninit::uninit(); BUF_SIZE]);
    let mut tlsf = Tlsf::<FLLEN, SLLEN>::new();
    let align = size.next_power_of_two().min(4096);
    unsafe {
        let start = pool.0.as_mut_ptr() as *mut u8;
        tlsf.insert_free_block_ptr_aligned_test(start, BUF_SIZE);
    }

    // probe: count how many blocks fit in pool
    let n = {
        let mut count = 0usize;
        unsafe {
            while tlsf.allocate(size, align).is_some() {
                count += 1;
            }
        }
        tlsf = Tlsf::<FLLEN, SLLEN>::new();
        unsafe {
            let start = pool.0.as_mut_ptr() as *mut u8;
            tlsf.insert_free_block_ptr_aligned_test(start, BUF_SIZE);
        }
        count
    };
    assert!(n >= 2, "pool too small for coalesce bench at size {}", size);

    let mut ptrs: Vec<*mut u8> = Vec::with_capacity(n);

    for _ in 0..iters {
        unsafe {
            ptrs.clear();
            for _ in 0..n {
                let (p, _, _) = tlsf.allocate(black_box(size), align).unwrap();
                ptrs.push(p);
            }
            // even indices: no coalescing (neighbors still allocated)
            for i in (0..n).step_by(2) {
                tlsf.deallocate_ext(black_box(ptrs[i]), align);
            }
            // odd indices: both neighbors free → dual merge
            for i in (1..n).step_by(2) {
                tlsf.deallocate_ext(black_box(ptrs[i]), align);
            }
        }
    }
}

pub fn run_coalesce_original(size: usize, iters: usize) {
    use rlsf::Tlsf;
    use std::alloc::Layout;
    let layout = Layout::from_size_align(size, size.next_power_of_two().min(4096)).unwrap();

    let mut pool = [MaybeUninit::uninit(); BUF_SIZE];
    let mut tlsf: Tlsf<'_, u16, u16, FLLEN, SLLEN> = Tlsf::new();
    tlsf.insert_free_block(&mut pool);

    // probe
    let n = {
        let mut count = 0usize;
        while tlsf.allocate(layout).is_some() {
            count += 1;
        }
        tlsf = Tlsf::new();
        tlsf.insert_free_block(&mut pool);
        count
    };
    assert!(n >= 2, "pool too small for coalesce bench at size {}", size);

    let mut ptrs: Vec<std::ptr::NonNull<u8>> = Vec::with_capacity(n);

    for _ in 0..iters {
        unsafe {
            ptrs.clear();
            for _ in 0..n {
                ptrs.push(tlsf.allocate(layout).unwrap());
            }
            for i in (0..n).step_by(2) {
                tlsf.deallocate(black_box(ptrs[i]), layout.align());
            }
            for i in (1..n).step_by(2) {
                tlsf.deallocate(black_box(ptrs[i]), layout.align());
            }
        }
    }
}
