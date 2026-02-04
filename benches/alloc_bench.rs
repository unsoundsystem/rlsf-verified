use criterion::BenchmarkId;
use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use std::mem::MaybeUninit;
use std::ptr::NonNull;

fn criterion_benchmark(c: &mut Criterion) {
    use rlsf_verified::{parameters::*, round_up, Tlsf};
    let mut group = c.benchmark_group("Allocation");
    for i in (0..1023).step_by(10) {
        group.bench_with_input(BenchmarkId::new("rlsf_allocate", i), &i, |b, i| {
            b.iter_with_large_drop(move || {
                use rlsf::Tlsf;
                use std::{alloc::Layout, mem::MaybeUninit};

                let mut pool = [MaybeUninit::uninit(); 65536];
                let mut tlsf: Tlsf<'_, u16, u16, 12, 16> = Tlsf::new();
                tlsf.insert_free_block(&mut pool);

                for i in 0..(*i) {
                    unsafe {
                        let l =
                            Layout::from_size_align(black_box(32), black_box(GRANULARITY)).unwrap();
                        let x = tlsf.allocate(Layout::new::<[u64; 4]>());
                        *x.unwrap().as_ptr() = 1;
                    }
                }
            })
        });
        group.bench_with_input(BenchmarkId::new("rlsf-verified_allocate", i), &i, |b, i| {
            b.iter_with_large_drop(move || {
                let mut pool = [MaybeUninit::<u8>::uninit(); 65536];
                let mut tlsf = Tlsf::<12usize, 16usize>::new();
                unsafe {
                    let block = NonNull::new((&mut pool) as *mut [_] as _).unwrap();

                    let unaligned_start = block.as_ptr() as *mut u8;
                    let start = round_up(unaligned_start, GRANULARITY);
                    let size = 65535;
                    tlsf.insert_free_block_ptr_aligned_test(start as *mut u8, size);
                    for _ in 0..(*i) {
                        let (x, _, _) = tlsf
                            .allocate(black_box(32), black_box(GRANULARITY))
                            .unwrap();
                        *x.as_mut().unwrap() = 1;
                    }
                }
            })
        });
    }
    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
