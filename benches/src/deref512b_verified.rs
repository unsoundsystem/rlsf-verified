mod common;
use common::run_deref_verified;

fn main() {
    let iters: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(5_000_000);
    run_deref_verified(512, iters);
}
