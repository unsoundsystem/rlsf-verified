//! perf_event_open + mmap + rdpmc-based per-call instrumentation for
//! `link_free_block`.
//!
//! Entire module is gated behind `feature = "rdpmc-bench"` from `lib.rs`.
//! Single-threaded by contract — the bench harness pins to one core.
//!
//! Verified builds must not enable this feature; the gated probe calls inside
//! `link_free_block` are removed at `cfg` expansion, so verus never sees them.

extern crate std;

use core::arch::asm;
use core::arch::x86_64::{_mm_lfence, _mm_mfence};
use core::cell::UnsafeCell;
use core::mem;
use core::ptr;
use core::sync::atomic::{compiler_fence, Ordering};

use std::io;
use std::os::unix::io::RawFd;
use std::sync::OnceLock;

// ----- Local definitions of perf_event ABI structures -----------------------
//
// libc 0.2.x does not export `perf_event_attr` / `perf_event_mmap_page`, so we
// declare the minimum subset we need with the exact kernel layout. Field
// offsets cross-checked against Linux 6.x include/uapi/linux/perf_event.h.

#[repr(C)]
#[derive(Default)]
struct PerfEventAttr {
    type_: u32,
    size: u32,
    config: u64,
    sample_period_or_freq: u64,
    sample_type: u64,
    read_format: u64,
    // Bitfield of feature flags: disabled, inherit, pinned, exclusive,
    // exclude_user, exclude_kernel, exclude_hv, exclude_idle, ...
    flags: u64,
    wakeup_events_or_watermark: u32,
    bp_type: u32,
    bp_addr_or_config1: u64,
    bp_len_or_config2: u64,
    branch_sample_type: u64,
    sample_regs_user: u64,
    sample_stack_user: u32,
    clockid: i32,
    sample_regs_intr: u64,
    aux_watermark: u32,
    sample_max_stack: u16,
    reserved_2: u16,
    aux_sample_size: u32,
    reserved_3: u32,
}

const PERF_ATTR_FLAG_DISABLED: u64 = 1 << 0;
const PERF_ATTR_FLAG_PINNED: u64 = 1 << 2;
const PERF_ATTR_FLAG_EXCLUDE_KERNEL: u64 = 1 << 5;
const PERF_ATTR_FLAG_EXCLUDE_HV: u64 = 1 << 6;

#[repr(C)]
struct PerfEventMmapPage {
    version: u32,
    compat_version: u32,
    lock: u32,
    index: u32,
    offset: i64,
    time_enabled: u64,
    time_running: u64,
    capabilities: u64,
    pmc_width: u16,
    // remaining fields (time_shift, time_mult, ...) intentionally omitted —
    // we never read past pmc_width.
}

// ----- Counter and slot enumerations ----------------------------------------

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CounterKind {
    Cycles,
    Instructions,
    L1dLoads,
    L1dLoadMisses,
    LlcLoadMisses,
    DtlbLoadMisses,
    MemLoads,
    MemStores,
}

impl CounterKind {
    pub fn parse(s: &str) -> Option<Self> {
        Some(match s {
            "cycles" => Self::Cycles,
            "instructions" | "insns" => Self::Instructions,
            "l1d_loads" => Self::L1dLoads,
            "l1d_load_misses" => Self::L1dLoadMisses,
            "llc_load_misses" => Self::LlcLoadMisses,
            "dtlb_load_misses" => Self::DtlbLoadMisses,
            "mem_loads" => Self::MemLoads,
            "mem_stores" => Self::MemStores,
            _ => return None,
        })
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Cycles => "cycles",
            Self::Instructions => "instructions",
            Self::L1dLoads => "l1d_loads",
            Self::L1dLoadMisses => "l1d_load_misses",
            Self::LlcLoadMisses => "llc_load_misses",
            Self::DtlbLoadMisses => "dtlb_load_misses",
            Self::MemLoads => "mem_loads",
            Self::MemStores => "mem_stores",
        }
    }
}

#[derive(Copy, Clone, Debug)]
#[repr(usize)]
pub enum ProbeSlot {
    Whole = 0,
    FirstFreeRead = 1,
    FirstFreeWrite = 2,
    NewNodeWrite = 3,
    EmptyBranchWrite = 4,
    // get_freelink_ptr(...) call sites — measures the address-computation
    // (ptrtoint / add / inttoptr) cost of the verified pointer-from-int
    // helper. Only attached in the verified non-empty branch (caller-visible
    // `let X = get_freelink_ptr(Y);` sites at linked_list.rs L1522 / L1537).
    GetFreeLinkFirstFree = 5,
    GetFreeLinkNewNode = 6,
}

pub const NUM_SLOTS: usize = 7;

const SLOT_NAMES: [&str; NUM_SLOTS] = [
    "Whole",
    "FirstFreeRead",
    "FirstFreeWrite",
    "NewNodeWrite",
    "EmptyBranchWrite",
    "GetFreeLinkFirstFree",
    "GetFreeLinkNewNode",
];

// ----- Per-slot accumulator -------------------------------------------------

#[derive(Copy, Clone)]
struct SlotAccum {
    count: u64,
    sum: u64,
    min: u64,
    max: u64,
    drops: u64,
}

impl SlotAccum {
    const EMPTY: Self = Self {
        count: 0,
        sum: 0,
        min: u64::MAX,
        max: 0,
        drops: 0,
    };
}

#[derive(Copy, Clone, Debug)]
pub struct SlotStats {
    pub slot: &'static str,
    pub count: u64,
    pub sum: u64,
    pub min: u64,
    pub max: u64,
    pub mean: f64,
    pub drops: u64,
}

// ----- Global state ---------------------------------------------------------

struct State {
    fd: RawFd,
    mmap_ptr: *mut u8,
    mmap_size: usize,
    counter: CounterKind,
    vendor: Vendor,
    // Pre-begin timestamps per slot. Single-threaded so no races.
    last_begin: [u64; NUM_SLOTS],
    // Whether the previous begin saw counter assigned (idx != 0).
    last_valid: [bool; NUM_SLOTS],
    accum: [SlotAccum; NUM_SLOTS],
    // Calibration: avg overhead of begin+end pair with no work between.
    overhead: u64,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Vendor {
    Intel,
    Amd,
    Unknown,
}

struct StateCell(UnsafeCell<State>);
// SAFETY: bench is single-threaded; init runs once, begin/end run on same
// thread thereafter. Sync/Send impls are load-bearing promises enforced by
// the bench harness via taskset -c 1.
unsafe impl Sync for StateCell {}
unsafe impl Send for StateCell {}

// ----- rdpmc via inline asm (stable; core::arch::x86_64::__rdpmc absent) ----

#[inline(always)]
unsafe fn rdpmc(idx: u32) -> u64 {
    let low: u32;
    let high: u32;
    asm!(
        "rdpmc",
        in("ecx") idx,
        out("eax") low,
        out("edx") high,
        options(nostack, preserves_flags),
    );
    ((high as u64) << 32) | (low as u64)
}

static STATE: OnceLock<StateCell> = OnceLock::new();

// ----- perf_event_open syscall wrapper -------------------------------------

unsafe fn perf_event_open(
    attr: &PerfEventAttr,
    pid: libc::pid_t,
    cpu: libc::c_int,
    group_fd: libc::c_int,
    flags: libc::c_ulong,
) -> libc::c_long {
    libc::syscall(
        libc::SYS_perf_event_open,
        attr as *const _,
        pid,
        cpu,
        group_fd,
        flags,
    )
}

// PERF_EVENT_IOC_ENABLE is _IO('$', 0) on Linux. The value 0x2400 holds on
// every architecture Linux supports for the perf event ioctls.
const PERF_EVENT_IOC_ENABLE: libc::c_ulong = 0x2400;
const PERF_EVENT_IOC_RESET: libc::c_ulong = 0x2403;
const PERF_FLAG_FD_CLOEXEC: libc::c_ulong = 8;

// ----- Vendor detection -----------------------------------------------------

fn detect_vendor() -> Vendor {
    if let Ok(s) = std::fs::read_to_string("/proc/cpuinfo") {
        for line in s.lines() {
            if let Some(v) = line.strip_prefix("vendor_id") {
                let v = v.trim_start_matches(|c: char| c == ':' || c.is_whitespace());
                if v.starts_with("Genuine") || v.contains("Intel") {
                    return Vendor::Intel;
                }
                if v.starts_with("Authentic") || v.contains("AMD") {
                    return Vendor::Amd;
                }
            }
        }
    }
    Vendor::Unknown
}

// ----- perf_event_attr construction ----------------------------------------

fn build_attr(counter: CounterKind, vendor: Vendor) -> Result<PerfEventAttr, io::Error> {
    let mut attr: PerfEventAttr = unsafe { mem::zeroed() };
    attr.size = mem::size_of::<PerfEventAttr>() as u32;
    attr.flags = PERF_ATTR_FLAG_DISABLED
        | PERF_ATTR_FLAG_PINNED
        | PERF_ATTR_FLAG_EXCLUDE_KERNEL
        | PERF_ATTR_FLAG_EXCLUDE_HV;

    // Constants for PERF_TYPE_HARDWARE config IDs.
    const PERF_TYPE_HARDWARE: u32 = 0;
    const PERF_TYPE_HW_CACHE: u32 = 3;
    const PERF_TYPE_RAW: u32 = 4;

    const PERF_COUNT_HW_CPU_CYCLES: u64 = 0;
    const PERF_COUNT_HW_INSTRUCTIONS: u64 = 1;

    const PERF_COUNT_HW_CACHE_L1D: u64 = 0;
    const PERF_COUNT_HW_CACHE_LL: u64 = 2;
    const PERF_COUNT_HW_CACHE_DTLB: u64 = 3;
    const PERF_COUNT_HW_CACHE_OP_READ: u64 = 0;
    const PERF_COUNT_HW_CACHE_RESULT_ACCESS: u64 = 0;
    const PERF_COUNT_HW_CACHE_RESULT_MISS: u64 = 1;

    let cache_cfg = |cache_id: u64, op: u64, result: u64| -> u64 {
        cache_id | (op << 8) | (result << 16)
    };

    let (ty, cfg) = match counter {
        CounterKind::Cycles => (PERF_TYPE_HARDWARE, PERF_COUNT_HW_CPU_CYCLES),
        CounterKind::Instructions => (PERF_TYPE_HARDWARE, PERF_COUNT_HW_INSTRUCTIONS),
        CounterKind::L1dLoads => (
            PERF_TYPE_HW_CACHE,
            cache_cfg(
                PERF_COUNT_HW_CACHE_L1D,
                PERF_COUNT_HW_CACHE_OP_READ,
                PERF_COUNT_HW_CACHE_RESULT_ACCESS,
            ),
        ),
        CounterKind::L1dLoadMisses => (
            PERF_TYPE_HW_CACHE,
            cache_cfg(
                PERF_COUNT_HW_CACHE_L1D,
                PERF_COUNT_HW_CACHE_OP_READ,
                PERF_COUNT_HW_CACHE_RESULT_MISS,
            ),
        ),
        CounterKind::LlcLoadMisses => (
            PERF_TYPE_HW_CACHE,
            cache_cfg(
                PERF_COUNT_HW_CACHE_LL,
                PERF_COUNT_HW_CACHE_OP_READ,
                PERF_COUNT_HW_CACHE_RESULT_MISS,
            ),
        ),
        CounterKind::DtlbLoadMisses => (
            PERF_TYPE_HW_CACHE,
            cache_cfg(
                PERF_COUNT_HW_CACHE_DTLB,
                PERF_COUNT_HW_CACHE_OP_READ,
                PERF_COUNT_HW_CACHE_RESULT_MISS,
            ),
        ),
        CounterKind::MemLoads => match vendor {
            // mem_inst_retired.all_loads on Skylake+: event=0xD0, umask=0x81
            Vendor::Intel => (PERF_TYPE_RAW, 0x81d0),
            // ls_dispatch.ld_dispatch on Zen: PMCx29, umask=0x01
            Vendor::Amd => (PERF_TYPE_RAW, 0x0129),
            Vendor::Unknown => (PERF_TYPE_RAW, 0x81d0),
        },
        CounterKind::MemStores => match vendor {
            // mem_inst_retired.all_stores: event=0xD0, umask=0x82
            Vendor::Intel => (PERF_TYPE_RAW, 0x82d0),
            // ls_dispatch.st_dispatch on Zen: PMCx29, umask=0x02
            Vendor::Amd => (PERF_TYPE_RAW, 0x0229),
            Vendor::Unknown => (PERF_TYPE_RAW, 0x82d0),
        },
    };
    attr.type_ = ty;
    attr.config = cfg;
    Ok(attr)
}

// ----- Initialization -------------------------------------------------------

pub fn init(counter: CounterKind) -> io::Result<()> {
    let vendor = detect_vendor();
    let attr = build_attr(counter, vendor)?;

    let fd = unsafe {
        perf_event_open(&attr, 0, -1, -1, PERF_FLAG_FD_CLOEXEC)
    };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    let fd = fd as RawFd;

    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;
    let mmap_size = page_size;
    let mmap_ptr = unsafe {
        libc::mmap(
            ptr::null_mut(),
            mmap_size,
            libc::PROT_READ,
            libc::MAP_SHARED,
            fd,
            0,
        )
    };
    if mmap_ptr == libc::MAP_FAILED {
        let err = io::Error::last_os_error();
        unsafe { libc::close(fd); }
        return Err(err);
    }

    let enable_ret = unsafe { libc::ioctl(fd, PERF_EVENT_IOC_ENABLE as _) };
    if enable_ret < 0 {
        let err = io::Error::last_os_error();
        unsafe {
            libc::munmap(mmap_ptr, mmap_size);
            libc::close(fd);
        }
        return Err(err);
    }

    let state = State {
        fd,
        mmap_ptr: mmap_ptr as *mut u8,
        mmap_size,
        counter,
        vendor,
        last_begin: [0; NUM_SLOTS],
        last_valid: [false; NUM_SLOTS],
        accum: [SlotAccum::EMPTY; NUM_SLOTS],
        overhead: 0,
    };

    STATE
        .set(StateCell(UnsafeCell::new(state)))
        .map_err(|_| io::Error::new(io::ErrorKind::AlreadyExists, "perf_probe already initialized"))?;

    // Empty-probe calibration to estimate begin+end overhead.
    calibrate_overhead();
    Ok(())
}

fn calibrate_overhead() {
    const N: u64 = 4096;
    let mut total: u64 = 0;
    let mut ok: u64 = 0;
    let cell = STATE.get().expect("init must be done");
    // SAFETY: single-threaded by contract.
    let state = unsafe { &mut *cell.0.get() };
    let mmap = state.mmap_ptr as *const PerfEventMmapPage;
    for _ in 0..N {
        let a = unsafe { rdpmc_seqlock(mmap) };
        unsafe { _mm_lfence(); }
        let b = unsafe { rdpmc_seqlock(mmap) };
        if let (Some(a), Some(b)) = (a, b) {
            total = total.wrapping_add(b.wrapping_sub(a));
            ok += 1;
        }
    }
    if ok > 0 {
        state.overhead = total / ok;
    }
}

// ----- rdpmc with mmap seqlock ---------------------------------------------

#[inline(always)]
unsafe fn rdpmc_seqlock(pc: *const PerfEventMmapPage) -> Option<u64> {
    // Use volatile reads for the seqlock fields so the compiler cannot hoist
    // them across the rdpmc.
    loop {
        let seq0 = ptr::read_volatile(&(*pc).lock as *const u32);
        compiler_fence(Ordering::Acquire);
        if seq0 & 1 != 0 {
            // Kernel writer in progress; spin until it leaves.
            core::hint::spin_loop();
            continue;
        }
        let idx = ptr::read_volatile(&(*pc).index as *const u32);
        if idx == 0 {
            // Counter not currently assigned to a hardware PMC.
            return None;
        }
        let offset = ptr::read_volatile(&(*pc).offset as *const i64);
        let pmc_width = ptr::read_volatile(&(*pc).pmc_width as *const u16);
        let raw = rdpmc(idx - 1);
        let mask: u64 = if pmc_width >= 64 {
            !0u64
        } else {
            (1u64 << pmc_width) - 1
        };
        let val = (raw & mask).wrapping_add(offset as u64) & mask;
        compiler_fence(Ordering::Acquire);
        let seq1 = ptr::read_volatile(&(*pc).lock as *const u32);
        if seq0 == seq1 {
            return Some(val);
        }
        // Sequence mismatch: kernel updated mid-read. Retry.
    }
}

// ----- Public hot path -----------------------------------------------------

#[inline(always)]
pub fn begin(slot: ProbeSlot) {
    // SAFETY: STATE was set in init; single-threaded access.
    let cell = match STATE.get() {
        Some(c) => c,
        None => return,
    };
    unsafe {
        _mm_mfence();
        _mm_lfence();
        let state = &mut *cell.0.get();
        let mmap = state.mmap_ptr as *const PerfEventMmapPage;
        let idx = slot as usize;
        match rdpmc_seqlock(mmap) {
            Some(v) => {
                state.last_begin[idx] = v;
                state.last_valid[idx] = true;
            }
            None => {
                state.last_valid[idx] = false;
                state.accum[idx].drops = state.accum[idx].drops.wrapping_add(1);
            }
        }
    }
}

#[inline(always)]
pub fn end(slot: ProbeSlot) {
    let cell = match STATE.get() {
        Some(c) => c,
        None => return,
    };
    unsafe {
        _mm_lfence();
        let state = &mut *cell.0.get();
        let mmap = state.mmap_ptr as *const PerfEventMmapPage;
        let idx = slot as usize;
        if !state.last_valid[idx] {
            return;
        }
        let v = match rdpmc_seqlock(mmap) {
            Some(v) => v,
            None => {
                state.last_valid[idx] = false;
                state.accum[idx].drops = state.accum[idx].drops.wrapping_add(1);
                return;
            }
        };
        let begin = state.last_begin[idx];
        state.last_valid[idx] = false;
        let delta = v.wrapping_sub(begin);
        let a = &mut state.accum[idx];
        a.count = a.count.wrapping_add(1);
        a.sum = a.sum.wrapping_add(delta);
        if delta < a.min {
            a.min = delta;
        }
        if delta > a.max {
            a.max = delta;
        }
    }
}

// ----- Stats reporting ------------------------------------------------------

pub fn reset_stats() {
    let cell = match STATE.get() {
        Some(c) => c,
        None => return,
    };
    unsafe {
        let state = &mut *cell.0.get();
        for i in 0..NUM_SLOTS {
            state.accum[i] = SlotAccum::EMPTY;
            state.last_valid[i] = false;
        }
    }
}

pub fn dump_stats() -> std::vec::Vec<SlotStats> {
    let cell = match STATE.get() {
        Some(c) => c,
        None => return std::vec::Vec::new(),
    };
    // SAFETY: single-threaded.
    let state = unsafe { &*cell.0.get() };
    let mut out = std::vec::Vec::with_capacity(NUM_SLOTS);
    for i in 0..NUM_SLOTS {
        let a = state.accum[i];
        let mean = if a.count > 0 {
            a.sum as f64 / a.count as f64
        } else {
            0.0
        };
        out.push(SlotStats {
            slot: SLOT_NAMES[i],
            count: a.count,
            sum: a.sum,
            min: if a.count == 0 { 0 } else { a.min },
            max: a.max,
            mean,
            drops: a.drops,
        });
    }
    out
}

pub fn current_counter() -> Option<CounterKind> {
    STATE.get().map(|cell| {
        // SAFETY: single-threaded.
        unsafe { (*cell.0.get()).counter }
    })
}

pub fn overhead() -> u64 {
    STATE
        .get()
        .map(|cell| unsafe { (*cell.0.get()).overhead })
        .unwrap_or(0)
}

