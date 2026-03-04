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

# Adjust if your repo layout differs.
BENCH_PROJ = Path(__file__).resolve().parent.parent.parent / "rlsf-verified-tests"
SIZES = ["64b", "32b", "16b", "8b"]
KINDS = ["original", "verified"]

# Jitter probe: minimum events
JITTER_EVENTS = "cycles,instructions,task-clock,L1-dcache-loads,L1-dcache-load-misses"

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
    for c in ["cargo", "perf", "chrt", "taskset", "cpupower", "tee", "sudo"]:
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

    NOTE (your environment):
      - 'time elapsed' line is NOT printed.
      - unit field for task-clock may be empty.
      - trailing 'CPUs utilized' can appear on the same line.
    We only rely on: value (col0), unit (col1), event (col2).
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


def extract_runtime_s(perf_map: dict[str, tuple[float, str]]) -> float:
    """
    In this environment, perf stat -x, does NOT include 'time elapsed'.
    Use task-clock as runtime proxy.

    Special handling:
      - unit may be empty; interpret as nanoseconds (observed).
    """
    if "task-clock" not in perf_map:
        raise KeyError("task-clock not found in perf output")

    val, unit = perf_map["task-clock"]
    unit = (unit or "").strip().lower()

    if unit in ("msec", "ms"):
        return float(val) * 1e-3
    if unit in ("usec", "us"):
        return float(val) * 1e-6
    if unit in ("nsec", "ns"):
        return float(val) * 1e-9
    if unit in ("sec", "secs", "second", "seconds", "s"):
        return float(val)

    # Your observed case: unit == "" -> assume nanoseconds
    if unit == "":
        return float(val) * 1e-9

    raise ValueError(f"Unknown task-clock unit: {unit!r}")


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
# 0) Common kernel/OS setup
########################################
def setup_common():
    print("[*] Setting up kernel/OS knobs (needs sudo)")

    def run(cmd, input_text=None):
        print(">>", " ".join(cmd))
        subprocess.run(
            cmd,
            input=input_text,
            text=True,
            check=True,
            stdout=subprocess.DEVNULL,
        )

    # fix frequency
    run(["sudo", "cpupower", "frequency-set", "-g", "performance"])

    # disable THP
    if Path("/sys/kernel/mm/transparent_hugepage/enabled").exists():
        run(["sudo", "tee", "/sys/kernel/mm/transparent_hugepage/enabled"], input_text="never\n")

    # disable ASLR
    run(["sudo", "tee", "/proc/sys/kernel/randomize_va_space"], input_text="0\n")

    # relax perf restrictions
    run(["sudo", "tee", "/proc/sys/kernel/perf_event_paranoid"], input_text="1\n")


########################################
# 1) Run-to-run variability probe (distribution + violin)
########################################
def measure_jitter(num_iter: int, runs: int, paths: Paths):
    """
    Measure run-to-run variability using task-clock (converted to seconds).
    Output: jitter_time_distribution.csv and per-size violin plots.
    """
    records: list[dict] = []

    for s in SIZES:
        for k in KINDS:
            bin_path = BENCH_PROJ / f"target/release/alt{s}-{k}"
            if not bin_path.exists():
                raise SystemExit(f"ERROR: binary not found: {bin_path} (build first)")

            print(f"[*] VARIABILITY size={s} kind={k}")
            for i in range(1, runs + 1):
                rc, perf_map, _raw = run_perf_stat(bin_path, num_iter, JITTER_EVENTS)
                t_s = extract_runtime_s(perf_map)

                # store raw task-clock too (value/unit)
                task_clock_val, task_clock_unit = perf_map.get("task-clock", (None, None))
                records.append({
                    "kind": k,
                    "size": s,
                    "run": i,
                    "return_code": rc,
                    "time_s": t_s,  # task-clock converted to seconds
                    "task_clock": task_clock_val,
                    "task_clock_unit": task_clock_unit,
                    "cycles": perf_map["cycles"][0],
                    "instructions": perf_map["instructions"][0],
                    "L1-dcache-loads": perf_map["L1-dcache-loads"][0],
                    "L1-dcache-load-misses": perf_map["L1-dcache-load-misses"][0],
                })

    df = pd.DataFrame.from_records(records)
    df.to_csv(paths.jitter_csv, index=False)
    print(f"[*] Saved variability CSV: {paths.jitter_csv}")

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
        ax.set_ylabel("task-clock (s)")
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
            fig_dir / f"variability_violin_taskclock_{s}.png",
            title=f"Run-to-run variability (task-clock) size={s}",
        )

    # all sizes mixed (reference)
    violinplot_by_kind(
        df,
        fig_dir / "variability_violin_taskclock_all_sizes.png",
        title="Run-to-run variability (task-clock) all sizes",
    )
    print(f"[*] Variability figures saved under: {fig_dir}")


########################################
# 2) Main measurement (perf CSV + summary)
########################################
def run_main_measurement(num_iter: int, runs: int, paths: Paths):
    """
    Main perf measurement (events like cycles/instructions/...).
    Output:
      - meta.log
      - perf_original.csv / perf_verified.csv (raw perf -x, stderr appended)
      - main_summary.csv (one row per run, with task-clock seconds as time_s)
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

                    # per-run structured summary
                    t_s = extract_runtime_s(perf_map)  # task-clock seconds
                    row = {
                        "kind": k,
                        "size": s,
                        "run": i,
                        "return_code": rc,
                        "time_s": t_s,
                    }
                    for ev in ["cycles", "instructions", "cache-misses", "branch-misses", "dTLB-load-misses", "minor-faults", "task-clock"]:
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
    mode.add_argument("--jitter", action="store_true", help="Measure run-to-run variability + violin plots")
    mode.add_argument("--run", action="store_true", help="Main perf measurement (run equivalent)")
    mode.add_argument("--all", action="store_true", help="Setup + build + jitter + run")

    ap.add_argument("NUM_ITER", nargs="?", type=int, help="Iteration count passed to each benchmark binary")
    ap.add_argument("--runs", type=int, default=100)
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
        setup_common()
        build_project()
        measure_jitter(args.NUM_ITER, args.runs, paths)
        run_main_measurement(args.NUM_ITER, args.runs, paths)
        print(f"[*] Done. Results in {paths.outdir}/")
        return

    if args.jitter:
        setup_common()
        measure_jitter(args.NUM_ITER, args.runs, paths)
        print(f"[*] Done. Results in {paths.outdir}/")
        return

    if args.run:
        setup_common()
        run_main_measurement(args.NUM_ITER, args.runs, paths)
        print(f"[*] Done. Results in {paths.outdir}/")
        return


if __name__ == "__main__":
    main()
