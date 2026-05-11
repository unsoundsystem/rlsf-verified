// rdpmc microbench harness for link_free_block.
//
// Usage:
//   link_free_block_rdpmc <scenario> <size_bytes> <iters> --counter <name>
//
//   scenario  ∈ { coalesce, aaaddd, alt }
//   size_bytes ∈ { 32, 64, 512, 2048, 4096, ... }
//   counter   ∈ { cycles, instructions, l1d_loads, l1d_load_misses,
//                 llc_load_misses, dtlb_load_misses, mem_loads, mem_stores }
//
// Output: one CSV row per slot, plus a calibration row, on stdout.

mod common;

use common::{run_aaaddd_verified, run_alt_verified, run_coalesce_verified};
use rlsf_verified::perf_probe::{self, CounterKind};

fn usage_and_exit() -> ! {
    eprintln!(
        "usage: link_free_block_rdpmc <scenario:coalesce|aaaddd|alt> <size> <iters> --counter <name>"
    );
    std::process::exit(2);
}

fn run_workload(scenario: &str, size: usize, iters: usize) {
    match scenario {
        "coalesce" => run_coalesce_verified(size, iters),
        "aaaddd" => run_aaaddd_verified(size, iters),
        "alt" => run_alt_verified(size, iters),
        other => {
            eprintln!("unknown scenario: {other}");
            usage_and_exit();
        }
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let scenario = match args.next() {
        Some(s) => s,
        None => usage_and_exit(),
    };
    let size: usize = match args.next().and_then(|s| s.parse().ok()) {
        Some(v) => v,
        None => usage_and_exit(),
    };
    let iters: usize = match args.next().and_then(|s| s.parse().ok()) {
        Some(v) => v,
        None => usage_and_exit(),
    };

    let mut counter_name: Option<String> = None;
    while let Some(arg) = args.next() {
        if arg == "--counter" {
            counter_name = args.next();
        } else {
            eprintln!("unrecognized arg: {arg}");
            usage_and_exit();
        }
    }

    let counter_name = counter_name.unwrap_or_else(|| "cycles".to_string());
    let counter = match CounterKind::parse(&counter_name) {
        Some(c) => c,
        None => {
            eprintln!("unknown counter: {counter_name}");
            usage_and_exit();
        }
    };

    if let Err(e) = perf_probe::init(counter) {
        eprintln!("perf_probe::init failed: {e}");
        eprintln!("hint: enable user-mode rdpmc and lower perf_event_paranoid:");
        eprintln!("  echo 2 | sudo tee /sys/bus/event_source/devices/cpu/rdpmc");
        eprintln!("  echo 1 | sudo tee /proc/sys/kernel/perf_event_paranoid");
        std::process::exit(1);
    }

    let warmup_iters = (iters / 10).max(1);
    run_workload(&scenario, size, warmup_iters);
    perf_probe::reset_stats();

    run_workload(&scenario, size, iters);

    let stats = perf_probe::dump_stats();
    let overhead = perf_probe::overhead();

    println!("scenario,size,iters,counter,slot,count,sum,min,max,mean,drops");
    for s in &stats {
        println!(
            "{},{},{},{},{},{},{},{},{},{:.3},{}",
            scenario,
            size,
            iters,
            counter.as_str(),
            s.slot,
            s.count,
            s.sum,
            s.min,
            s.max,
            s.mean,
            s.drops,
        );
    }
    println!(
        "{},{},{},{},overhead,1,{},{},{},{:.3},0",
        scenario, size, iters, counter.as_str(), overhead, overhead, overhead, overhead as f64,
    );
}
