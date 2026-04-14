mod common;
use common::run_alt_original;

fn main() {
    let iters: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(5_000_000);
    run_alt_original(8192, iters);
}
