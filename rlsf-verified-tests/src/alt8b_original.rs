mod common;
use common::run_original;

fn main() {
    let iters: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(5_000_000);
    run_original(8, iters);
}
