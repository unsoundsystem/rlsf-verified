use rlsf_verified::{parameters::GRANULARITY, Tlsf};
use std::alloc::Layout;
use std::collections::BTreeMap;
use std::mem::MaybeUninit;
use std::ops::Range;

// ---------------------------------------------------------------------------
// ShadowAllocator — ported from rlsf's src/tests.rs
// Tracks address-space regions as Free/Used/Invalid to detect:
//   - alignment violations
//   - overlapping allocations (Free→Used on already-Used region panics)
//   - double frees (Used→Free on already-Free region panics)
// ---------------------------------------------------------------------------

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
enum SaRegion {
    Free,
    Used,
    Invalid,
}

struct ShadowAllocator {
    regions: BTreeMap<usize, SaRegion>,
}

impl ShadowAllocator {
    fn new() -> Self {
        Self {
            regions: Some((0, SaRegion::Invalid)).into_iter().collect(),
        }
    }

    fn convert_range(&mut self, range: Range<usize>, old_region: SaRegion, new_region: SaRegion) {
        if range.is_empty() {
            return;
        }
        assert_ne!(old_region, new_region);

        let (&addr, &region) = self.regions.range(0..range.end).next_back().unwrap();
        if addr > range.start {
            panic!("discontinuity in range {:?}", range);
        } else if region != old_region {
            panic!(
                "range {:?} is {:?} (expected {:?})",
                range, region, old_region
            );
        }

        if addr == range.start {
            *self.regions.get_mut(&addr).unwrap() = new_region;
        } else {
            self.regions.insert(range.start, new_region);
        }

        if let Some((_, &region)) = self.regions.range(0..range.start).next_back() {
            if region == new_region {
                self.regions.remove(&range.start);
            }
        }

        if let Some(&end_region) = self.regions.get(&range.end) {
            if end_region == new_region {
                self.regions.remove(&range.end);
            }
        } else {
            self.regions.insert(range.end, old_region);
        }
    }

    fn insert_free_block(&mut self, start: usize, len: usize) {
        self.convert_range(start..start + len, SaRegion::Invalid, SaRegion::Free);
    }

    fn allocate(&mut self, ptr: *mut u8, size: usize, align: usize) {
        let start = ptr as usize;
        assert!(
            start % align == 0,
            "0x{:x} is not properly aligned (0x{:x} bytes alignment required)",
            start,
            align
        );
        self.convert_range(start..start + size, SaRegion::Free, SaRegion::Used);
    }

    fn deallocate(&mut self, ptr: *mut u8, size: usize, align: usize) {
        let start = ptr as usize;
        assert!(
            start % align == 0,
            "0x{:x} is not properly aligned (0x{:x} bytes alignment required)",
            start,
            align
        );
        self.convert_range(start..start + size, SaRegion::Used, SaRegion::Free);
    }
}

// ---------------------------------------------------------------------------
// gen_test! macro — generates a test module per (FLLEN, SLLEN) combination,
// mirroring rlsf's crates/rlsf/src/tlsf/tests.rs structure.
//
// rlsf-verified differences from rlsf:
//   - No bitmap type parameters (always usize)
//   - No reallocate / append_free_block_ptr / deallocate_unknown_align
//   - Pool must be GRANULARITY-aligned
//   - insert_free_block_ptr_aligned_test(start, size) instead of insert_free_block_ptr(NonNull<[u8]>)
// ---------------------------------------------------------------------------

macro_rules! gen_test {
    ($mod:ident, $fllen:expr, $sllen:expr) => {
        mod $mod {
            use super::*;

            const FLLEN: usize = $fllen;
            const SLLEN: usize = $sllen;

            /// max_pool_size = 2^FLLEN * GRANULARITY
            fn max_pool_size() -> usize {
                // Avoid overflow for large FLLEN
                let shift = FLLEN + GRANULARITY.trailing_zeros() as usize;
                if shift >= usize::BITS as usize {
                    usize::MAX
                } else {
                    1usize << shift
                }
            }

            /// max_allocatable_size mirrors the Verus spec:
            ///   flb = 2^(granularity_log2 + FLLEN - 1)
            ///   max = flb + (SLLEN - 1) * (flb / SLLEN)
            fn max_allocatable_size() -> usize {
                let g_log2 = GRANULARITY.trailing_zeros() as usize;
                let shift = g_log2 + FLLEN - 1;
                if shift >= usize::BITS as usize {
                    usize::MAX
                } else {
                    let flb = 1usize << shift;
                    flb + (SLLEN - 1) * (flb / SLLEN)
                }
            }

            /// Check allocate preconditions (Verus specs erased at runtime)
            fn alloc_preconditions_ok(size: usize, align: usize) -> bool {
                let mas = max_allocatable_size();
                let hdr = 16usize; // size_of::<UsedBlockHdr>()
                let gran_sub = GRANULARITY - 1;
                // Both preconditions must hold:
                //   size + align + hdr + (GRANULARITY-1) <= mas
                //   size + align.saturating_sub(GRANULARITY/2) + hdr + (GRANULARITY-1) <= mas
                let overhead1 = match align.checked_add(hdr).and_then(|v| v.checked_add(gran_sub)) {
                    Some(v) => v,
                    None => return false,
                };
                let overhead2 = match align.saturating_sub(GRANULARITY / 2)
                    .checked_add(hdr).and_then(|v| v.checked_add(gran_sub)) {
                    Some(v) => v,
                    None => return false,
                };
                size > 0
                    && size <= mas
                    && size.checked_add(overhead1).map_or(false, |v| v <= mas)
                    && size.checked_add(overhead2).map_or(false, |v| v <= mas)
                    && align < max_pool_size()
            }

            /// Effective pool size: min(65536, max_pool_size), rounded down to GRANULARITY
            fn pool_size() -> usize {
                let mps = max_pool_size();
                let size = 65536usize.min(mps);
                size & !(GRANULARITY - 1)
            }

            #[repr(align(64))]
            struct AlignedBuf([MaybeUninit<u8>; 65536]);

            #[test]
            fn minimal() {
                let ps = pool_size();
                if ps < GRANULARITY * 2 {
                    return; // pool too small for any allocation
                }
                let mut tlsf = Tlsf::<FLLEN, SLLEN>::new();
                let mut buf = AlignedBuf([MaybeUninit::uninit(); 65536]);
                unsafe {
                    let start = buf.0.as_mut_ptr() as *mut u8;
                    tlsf.insert_free_block_ptr_aligned_test(start, ps);
                    let ptr = tlsf.allocate(GRANULARITY, GRANULARITY);
                    if let Some((ptr, _, _)) = ptr {
                        tlsf.deallocate_ext(ptr, GRANULARITY);
                    }
                }
            }

            #[test]
            fn adaa() {
                let ps = pool_size();
                if ps < GRANULARITY * 2 {
                    return;
                }
                let mut tlsf = Tlsf::<FLLEN, SLLEN>::new();
                let mut buf = AlignedBuf([MaybeUninit::uninit(); 65536]);
                unsafe {
                    let start = buf.0.as_mut_ptr() as *mut u8;
                    tlsf.insert_free_block_ptr_aligned_test(start, ps);
                    if let Some((p1, _, _)) = tlsf.allocate(GRANULARITY, GRANULARITY) {
                        tlsf.deallocate_ext(p1, GRANULARITY);
                    }
                    let _ = tlsf.allocate(GRANULARITY, GRANULARITY);
                    let _ = tlsf.allocate(GRANULARITY, GRANULARITY);
                }
            }

            #[test]
            fn aadd() {
                let ps = pool_size();
                if ps < GRANULARITY * 2 {
                    return;
                }
                let mut tlsf = Tlsf::<FLLEN, SLLEN>::new();
                let mut buf = AlignedBuf([MaybeUninit::uninit(); 65536]);
                unsafe {
                    let start = buf.0.as_mut_ptr() as *mut u8;
                    tlsf.insert_free_block_ptr_aligned_test(start, ps);
                    let p1 = tlsf.allocate(GRANULARITY, GRANULARITY);
                    let p2 = tlsf.allocate(GRANULARITY, GRANULARITY);
                    if let (Some((p1, _, _)), Some((p2, _, _))) = (p1, p2) {
                        tlsf.deallocate_ext(p1, GRANULARITY);
                        tlsf.deallocate_ext(p2, GRANULARITY);
                    }
                }
            }

            #[quickcheck_macros::quickcheck]
            fn random(pool_offset: usize, pool_size_rand: usize, bytecode: Vec<u8>) {
                random_inner(pool_offset, pool_size_rand, bytecode);
            }

            fn random_inner(
                pool_offset: usize,
                pool_size_rand: usize,
                bytecode: Vec<u8>,
            ) -> Option<()> {
                let mut sa = ShadowAllocator::new();
                let mut tlsf = Tlsf::<FLLEN, SLLEN>::new();

                let mut buf = AlignedBuf([MaybeUninit::uninit(); 65536]);
                let pool_ptr: *mut u8;
                let pool_len: usize;
                unsafe {
                    // Randomize pool start (GRANULARITY-aligned) within the buffer
                    let granularity_slots = 65536 / GRANULARITY;
                    let offset = if granularity_slots > 0 {
                        (pool_offset % granularity_slots) * GRANULARITY
                    } else {
                        0
                    };
                    let max_size = 65536 - offset;
                    // Cap to max_pool_size and round down to GRANULARITY
                    let size = (pool_size_rand % (max_size + 1))
                        .min(max_pool_size())
                        & !(GRANULARITY - 1);

                    pool_ptr = (buf.0.as_mut_ptr() as *mut u8).wrapping_add(offset);
                    pool_len =
                        if let Some(actual) = tlsf.insert_free_block_ptr_aligned_test(pool_ptr, size)
                        {
                            sa.insert_free_block(pool_ptr as usize, actual);
                            actual
                        } else {
                            return Some(());
                        };
                }

                let mut allocs: Vec<(*mut u8, Layout)> = Vec::new();
                let mut it = bytecode.iter().cloned();

                loop {
                    match it.next()? % 4 {
                        0..=1 => {
                            // allocate
                            let len_bytes = [it.next()?, it.next()?, it.next()?, 0];
                            let len = u32::from_le_bytes(len_bytes);
                            let len = ((len as u64 * pool_len as u64) >> 24) as usize;
                            let len = len.max(1);
                            let align_shift = it.next()? % 4;
                            let align = GRANULARITY << align_shift;
                            if !alloc_preconditions_ok(len, align) {
                                continue;
                            }
                            let layout = Layout::from_size_align(len, align).unwrap();
                            if let Some((ptr, _, _)) =
                                tlsf.allocate(layout.size(), layout.align())
                            {
                                sa.allocate(ptr, layout.size(), layout.align());
                                allocs.push((ptr, layout));
                            }
                        }
                        2..=3 => {
                            // deallocate
                            let alloc_i = it.next()?;
                            if !allocs.is_empty() {
                                let i = alloc_i as usize % allocs.len();
                                let (ptr, layout) = allocs.swap_remove(i);
                                sa.deallocate(ptr, layout.size(), layout.align());
                                unsafe {
                                    tlsf.deallocate_ext(ptr, layout.align());
                                }
                            }
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }
    };
}

// rlsf-verified uses usize bitmaps, so no type params.
// FLLEN must satisfy: 0 < FLLEN < usize::BITS - 5 (= 59 on 64-bit)
// SLLEN must satisfy: 0 < SLLEN <= usize::BITS, power of 2

// Small FLLEN (equivalent to rlsf's u8 bitmap tests)
gen_test!(tlsf_1_1, 1, 1);
gen_test!(tlsf_1_2, 1, 2);
gen_test!(tlsf_1_4, 1, 4);
gen_test!(tlsf_1_8, 1, 8);
gen_test!(tlsf_3_4, 3, 4);
gen_test!(tlsf_5_4, 5, 4);
gen_test!(tlsf_8_1, 8, 1);
gen_test!(tlsf_8_8, 8, 8);

// Medium FLLEN (equivalent to rlsf's u16 bitmap tests)
gen_test!(tlsf_11_4, 11, 4);
gen_test!(tlsf_16_4, 16, 4);
gen_test!(tlsf_3_16, 3, 16);
gen_test!(tlsf_11_16, 11, 16);
gen_test!(tlsf_16_16, 16, 16);
gen_test!(tlsf_3_32, 3, 32);
gen_test!(tlsf_11_32, 11, 32);
gen_test!(tlsf_16_32, 16, 32);

// Large FLLEN (equivalent to rlsf's u32 bitmap tests)
gen_test!(tlsf_20_32, 20, 32);
gen_test!(tlsf_27_32, 27, 32);
gen_test!(tlsf_28_32, 28, 32);
gen_test!(tlsf_29_32, 29, 32);
gen_test!(tlsf_32_32, 32, 32);

// Max FLLEN (equivalent to rlsf's u64 bitmap tests, capped at 58)
gen_test!(tlsf_54_8, 54, 8);
gen_test!(tlsf_55_8, 55, 8);
gen_test!(tlsf_56_8, 56, 8);
gen_test!(tlsf_57_8, 57, 8);
gen_test!(tlsf_58_8, 58, 8);
