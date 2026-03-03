#!/usr/bin/env python3
import argparse
import os
import shutil
import subprocess
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt


########################################
# Fixed policy (no options)
########################################
CPU = "1"
RT_PRIO = "99"

BENCH_PROJ = Path("./rlsf-verified-tests")
SIZES = ["64b", "32b", "16b", "8b"]
KINDS = ["original", "verified"]

# Jitter probe: minimum events
JITTER_EVENTS = "task-clock"  # plus implicit "time elapsed" from perf stat

# Main measurement: richer events
MAIN_EVENTS = (
    "cycles,instructions,branches,branch-misses,cache-misses,"
    "dTLB-load-misses,minor-faults,task-clock"
)


@dataclass(frozen=True)
class Paths:
    outdir: Path
    meta_log: Path
    jitter_csv: Path
    fig_dir: Path
    perf_csv_original: Path
    perf_csv_verified: Path


def require_cmd(name: str):
    if shutil.which(name) is None:
        raise SystemExit(f"ERROR: {name} not found")


def env_checks():
    for c in ["cargo", "perf", "chrt", "taskset"]:
        require_cmd(c)


def make_outdir(user_outdir: str | None) -> Paths:
    outdir = Path(
        user_outdir if user_outdir else f"results_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    ).resolve()
    outdir.mkdir(parents=True, exist_ok=True)
    fig_dir = outdir / "fig"
    fig_dir.mkdir(parents=True, exist_ok=True)

    return Paths(
        outdir=outdir,
        meta_log=outdir / "meta.log",
        jitter_csv=outdir / "jitter_time_distribution.csv",
        fig_dir=fig_dir,
        perf_csv_original=outdir / "perf_original.csv",
        perf_csv_verified=outdir / "perf_verified.csv",
    )


def build_project():
    print(f"[*] Building in {BENCH_PROJ}")
    if not BENCH_PROJ.exists():
        raise SystemExit(f"ERROR: BENCH_PROJ not found: {BENCH_PROJ}")

    for s in SIZES:
        for k in KINDS:
            bin_name = f"alt{s}-{k}"
            print(f"  - build {bin_name}")
            env = os.environ.copy()
            env["RUSTFLAGS"] = "-C target-cpu=native"
            subprocess.run(
                ["cargo", "build", "--release", "--bin", bin_name],
                cwd=str(BENCH_PROJ),
                env=env,
                check=True,
            )


########################################
# perf -x, parsing helpers
########################################
def parse_perf_xcsv(stderr_text: str) -> dict[str, tuple[float, str]]:
    """
    Parse `perf stat -x,` stderr into: event -> (value, unit)
    Includes "time elapsed" line (event contains "time elapsed").
    """
    out: dict[str, tuple[float, str]] = {}
    for line in stderr_text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        cols = [c.strip() for c in line.split(",")]
        if len(cols) < 3:
            continue
        val_s, unit, event = cols[0], cols[1], cols[2]
        if not val_s or val_s.startswith("<"):
            continue
        val_s = val_s.replace(",", "")
        try:
            val = float(val_s)
        except ValueError:
            continue
        event = event or "(unknown)"
        out[event] = (val, unit)
    return out


def extract_time_elapsed_s(perf_map: dict[str, tuple[float, str]]) -> float:
    for ev, (val, _unit) in perf_map.items():
        if "time elapsed" in ev:
            return float(val)
    raise KeyError("time elapsed not found")


def run_perf_stat(bin_path: Path, num_iter: int, events: str) -> tuple[int, dict[str, tuple[float, str]], str]:
    """
    Run perf stat with fixed scheduling policy.
    Return: (returncode, perf_map, raw_stderr)
    """
    cmd = [
        "sudo", "chrt", "-f", RT_PRIO,
        "taskset", "-c", CPU,
        "perf", "stat", "-x,", "-e", events,
        str(bin_path), str(num_iter),
    ]
    p = subprocess.run(
        cmd,
        cwd=str(BENCH_PROJ),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    perf_map = parse_perf_xcsv(p.stderr)
    return p.returncode, perf_map, p.stderr


########################################
# 1) Jitter probe: runtime distribution only
########################################
def measure_jitter(num_iter: int, runs: int, paths: Paths):
    """
    Measure run-to-run jitter (distribution of time elapsed).
    Output: jitter_time_distribution.csv and per-size violin plots.
    """
    records: list[dict] = []

    for s in SIZES:
        for k in KINDS:
            bin_path = BENCH_PROJ / f"target/release/alt{s}-{k}"
            if not bin_path.exists():
                raise SystemExit(f"ERROR: binary not found: {bin_path} (build first)")

            print(f"[*] JITTER size={s} kind={k}")
            for i in range(1, runs + 1):
                rc, perf_map, _raw = run_perf_stat(bin_path, num_iter, JITTER_EVENTS)
                t = extract_time_elapsed_s(perf_map)

                # (optional) task-clock in msec, useful to see CPU-time jitter too
                task_clock = None
                if "task-clock" in perf_map:
                    task_clock = perf_map["task-clock"][0]

                records.append({
                    "kind": k,
                    "size": s,
                    "run": i,
                    "return_code": rc,
                    "time_s": t,
                    "task_clock": task_clock,
                })

    df = pd.DataFrame.from_records(records)
    df.to_csv(paths.jitter_csv, index=False)
    print(f"[*] Saved jitter CSV: {paths.jitter_csv}")

    plot_jitter_violins(df, paths.fig_dir)


def plot_jitter_violins(df: pd.DataFrame, fig_dir: Path):
    def violinplot_by_kind(sub: pd.DataFrame, outpath: Path, title: str):
        kinds = sorted(sub["kind"].unique().tolist())
        data = [sub[sub["kind"] == k]["time_s"].to_numpy() for k in kinds]

        fig = plt.figure(figsize=(8, 4.5))
        ax = fig.add_subplot(111)
        ax.violinplot(data, showmeans=False, showmedians=True, showextrema=True)

        ax.set_xticks(np.arange(1, len(kinds) + 1))
        ax.set_xticklabels(kinds)
        ax.set_ylabel("seconds time elapsed (s)")
        ax.set_title(title)

        for idx, k in enumerate(kinds, start=1):
            med = float(np.median(sub[sub["kind"] == k]["time_s"].to_numpy()))
            ax.plot(idx, med, marker="o")

        ax.grid(True, axis="y", linestyle=":", linewidth=0.5)
        fig.tight_layout()
        fig.savefig(outpath)
        plt.close(fig)

    # per-size
    for s in SIZES:
        sub = df[df["size"] == s].copy()
        if sub.empty:
            continue
        violinplot_by_kind(
            sub,
            fig_dir / f"jitter_violin_time_{s}.png",
            title=f"Jitter (runtime distribution) size={s}",
        )

    # all sizes mixed (reference)
    violinplot_by_kind(
        df,
        fig_dir / "jitter_violin_time_all_sizes.png",
        title="Jitter (runtime distribution) all sizes",
    )
    print(f"[*] Jitter figures saved under: {fig_dir}")


########################################
# 2) Main measurement: your bench.py run equivalent (perf CSV)
########################################
def run_main_measurement(num_iter: int, runs: int, paths: Paths):
    """
    Main perf measurement (events like cycles/instructions/...).
    Output:
      - meta.log
      - perf_original.csv / perf_verified.csv (raw perf -x, stderr appended)
      - main_summary.csv (one row per run, with time elapsed extracted)
    """
    meta_fp = open(paths.meta_log, "a")
    summary_rows: list[dict] = []

    try:
        for s in SIZES:
            for k in KINDS:
                bin_path = BENCH_PROJ / f"target/release/alt{s}-{k}"
                if not bin_path.exists():
                    raise SystemExit(f"ERROR: binary not found: {bin_path} (build first)")

                print(f"[*] MAIN size={s} kind={k}")
                for i in range(1, runs + 1):
                    meta_fp.write(f"{k},{s},run={i}\n")
                    meta_fp.flush()

                    rc, perf_map, raw = run_perf_stat(bin_path, num_iter, MAIN_EVENTS)

                    # append raw perf output to kind-specific CSV (like your bash)
                    perf_out = paths.perf_csv_original if k == "original" else paths.perf_csv_verified
                    with open(perf_out, "a") as f:
                        f.write(raw)
                        if not raw.endswith("\n"):
                            f.write("\n")

                    # also store a structured per-run summary (handy for stats/plots)
                    t = extract_time_elapsed_s(perf_map)
                    row = {
                        "kind": k,
                        "size": s,
                        "run": i,
                        "return_code": rc,
                        "time_s": t,
                    }
                    # pull a few events if present
                    for ev in ["cycles", "instructions", "cache-misses", "branch-misses", "dTLB-load-misses", "task-clock"]:
                        if ev in perf_map:
                            row[ev] = perf_map[ev][0]
                    summary_rows.append(row)

        df = pd.DataFrame(summary_rows)
        out = paths.outdir / "main_summary.csv"
        df.to_csv(out, index=False)
        print(f"[*] Saved main summary: {out}")
        print(f"[*] Raw perf: {paths.perf_csv_original} / {paths.perf_csv_verified}")

    finally:
        meta_fp.close()


########################################
# CLI
########################################
def main():
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--build", action="store_true")
    mode.add_argument("--jitter", action="store_true", help="Measure runtime jitter + violin plots")
    mode.add_argument("--run", action="store_true", help="Main perf measurement (run equivalent)")
    mode.add_argument("--all", action="store_true", help="Build + jitter + run")

    ap.add_argument("NUM_ITER", nargs="?", type=int, help="Iteration count passed to each benchmark binary")
    ap.add_argument("--runs", type=int, default=50)
    ap.add_argument("--outdir", default=None)

    args = ap.parse_args()

    env_checks()
    paths = make_outdir(args.outdir)

    if args.build:
        build_project()
        return

    if args.NUM_ITER is None:
        raise SystemExit("ERROR: NUM_ITER is required for --jitter/--run/--all")

    if args.all:
        build_project()
        measure_jitter(args.NUM_ITER, args.runs, paths)
        run_main_measurement(args.NUM_ITER, args.runs, paths)
        print(f"[*] Done. Results in {paths.outdir}/")
        return

    if args.jitter:
        measure_jitter(args.NUM_ITER, args.runs, paths)
        print(f"[*] Done. Results in {paths.outdir}/")
        return

    if args.run:
        run_main_measurement(args.NUM_ITER, args.runs, paths)
        print(f"[*] Done. Results in {paths.outdir}/")
        return


if __name__ == "__main__":
    main()
