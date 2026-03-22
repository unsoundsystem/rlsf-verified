#!/usr/bin/env python3
import argparse
import os
import shutil
import subprocess
from dataclasses import dataclass
from datetime import datetime
from html import escape
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
BENCH_PROJ = Path(__file__).resolve().parent.parent.parent / "benches"
SIZES = ["16k", "2k", "256b", "64b", "32b", "16b", "8b"]
KINDS = ["original", "verified"]
TASKS = ["alt", "aaaddd"]
LTO_MODES = ["none", "fat"]

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


def build_project(task: str, lto_mode: str):
    print(f"[*] Building in {BENCH_PROJ}")
    if not BENCH_PROJ.exists():
        raise SystemExit(f"ERROR: BENCH_PROJ not found: {BENCH_PROJ}")
    print(f"[*] Build config: task={task} lto={lto_mode}")

    for s in SIZES:
        for k in KINDS:
            bin_name = bin_name_for(task, s, k)
            print(f"  - build {bin_name}")
            env = os.environ.copy()
            env["RUSTFLAGS"] = "-C target-cpu=native"
            if lto_mode == "fat":
                env["CARGO_PROFILE_RELEASE_LTO"] = "fat"
            else:
                env.pop("CARGO_PROFILE_RELEASE_LTO", None)
            subprocess.run(
                ["cargo", "build", "--release", "--bin", bin_name],
                cwd=str(BENCH_PROJ),
                env=env,
                check=True,
            )


def parse_sizes_arg(sizes_arg: str | None) -> list[str]:
    if sizes_arg is None:
        return SIZES

    raw = [s.strip() for s in sizes_arg.split(",")]
    selected = [s for s in raw if s]
    if not selected:
        raise SystemExit("ERROR: --sizes is empty")

    invalid = [s for s in selected if s not in SIZES]
    if invalid:
        raise SystemExit(
            f"ERROR: unknown size(s): {', '.join(invalid)}. valid: {', '.join(SIZES)}"
        )

    # keep user order, drop duplicates
    return list(dict.fromkeys(selected))


def parse_task_arg(task_arg: str | None) -> str:
    if task_arg is None:
        return "alt"

    task = task_arg.strip().lower()
    if task not in TASKS:
        raise SystemExit(
            f"ERROR: unknown task: {task_arg}. valid: {', '.join(TASKS)}"
        )
    return task


def parse_lto_arg(lto_arg: str | None) -> str:
    if lto_arg is None:
        return "none"

    lto = lto_arg.strip().lower()
    if lto not in LTO_MODES:
        raise SystemExit(
            f"ERROR: unknown lto mode: {lto_arg}. valid: {', '.join(LTO_MODES)}"
        )
    return lto


def bin_name_for(task: str, size: str, kind: str) -> str:
    return f"{task}{size}-{kind}"


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
def measure_jitter(num_iter: int, runs: int, paths: Paths, sizes: list[str], task: str):
    """
    Measure run-to-run variability using task-clock (converted to seconds).
    Output: jitter_time_distribution.csv and per-size violin plots.
    """
    records: list[dict] = []

    for s in sizes:
        for k in KINDS:
            bin_path = BENCH_PROJ / f"target/release/{bin_name_for(task, s, k)}"
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

    plot_jitter_violins(df, paths.fig_dir, sizes)


def plot_jitter_violins(df: pd.DataFrame, fig_dir: Path, sizes: list[str]):
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
    for s in sizes:
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


def write_violin_gallery_html(fig_dir: Path, out_html: Path) -> bool:
    """
    Write an HTML gallery listing violin plot PNGs generated by plot_jitter_violins.
    """
    size_order = {s: i for i, s in enumerate(SIZES)}

    def key_for(path: Path):
        stem = path.stem  # variability_violin_taskclock_<size|all_sizes>
        suffix = stem.removeprefix("variability_violin_taskclock_")
        if suffix == "all_sizes":
            return (10_000, suffix)
        return (size_order.get(suffix, 9_999), suffix)

    pngs = sorted(fig_dir.glob("variability_violin_taskclock_*.png"), key=key_for)
    if not pngs:
        print(f"[!] Skip violin HTML: no violin plot PNGs found in {fig_dir}")
        return False

    cards: list[str] = []
    for p in pngs:
        label = escape(p.stem.removeprefix("variability_violin_taskclock_"))
        src = escape(p.name)
        cards.append(
            f"<figure><img src=\"{src}\" alt=\"{label}\"><figcaption>{label}</figcaption></figure>"
        )

    html = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Violin Plot Gallery</title>
  <style>
    body {{
      margin: 24px;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
      background: #fafafa;
      color: #1a1a1a;
    }}
    h1 {{
      margin: 0 0 16px 0;
      font-size: 1.4rem;
    }}
    .grid {{
      display: grid;
      gap: 16px;
      grid-template-columns: repeat(auto-fit, minmax(320px, 1fr));
    }}
    figure {{
      margin: 0;
      border: 1px solid #ddd;
      background: white;
      border-radius: 10px;
      overflow: hidden;
    }}
    img {{
      display: block;
      width: 100%;
      height: auto;
    }}
    figcaption {{
      padding: 10px 12px;
      font-size: 0.95rem;
      border-top: 1px solid #eee;
      background: #f7f7f7;
    }}
  </style>
</head>
<body>
  <h1>Variability violin plots (task-clock)</h1>
  <div class="grid">
    {"".join(cards)}
  </div>
</body>
</html>
"""
    out_html.write_text(html, encoding="utf-8")
    print(f"[*] Saved violin gallery HTML: {out_html}")
    return True


########################################
# 2) Main measurement (perf CSV + summary)
########################################
def run_main_measurement(num_iter: int, runs: int, paths: Paths, sizes: list[str], task: str):
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
        for s in sizes:
            for k in KINDS:
                bin_path = BENCH_PROJ / f"target/release/{bin_name_for(task, s, k)}"
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
    ap.add_argument("--task", default="alt", help=f"Benchmark task prefix. valid: {','.join(TASKS)}")
    ap.add_argument("--lto", default="none", help=f"Release LTO mode for build/all. valid: {','.join(LTO_MODES)}")
    ap.add_argument("--sizes", default=None, help=f"Comma-separated sizes to run (default: all). valid: {','.join(SIZES)}")
    ap.add_argument("--violin-html", action="store_true", help="Write an HTML gallery for variability violin plots")
    ap.add_argument("--outdir", default=None)

    args = ap.parse_args()

    env_checks()
    paths = make_outdir(args.outdir)
    selected_task = parse_task_arg(args.task)
    selected_lto = parse_lto_arg(args.lto)
    selected_sizes = parse_sizes_arg(args.sizes)

    if args.build:
        build_project(selected_task, selected_lto)
        return

    if args.NUM_ITER is None:
        raise SystemExit("ERROR: NUM_ITER is required for --jitter/--run/--all")

    if args.all:
        setup_common()
        build_project(selected_task, selected_lto)
        measure_jitter(args.NUM_ITER, args.runs, paths, selected_sizes, selected_task)
        if args.violin_html:
            write_violin_gallery_html(paths.fig_dir, paths.outdir / "variability_violin_gallery.html")
        run_main_measurement(args.NUM_ITER, args.runs, paths, selected_sizes, selected_task)
        print(f"[*] Done. Results in {paths.outdir}/")
        return

    if args.jitter:
        setup_common()
        measure_jitter(args.NUM_ITER, args.runs, paths, selected_sizes, selected_task)
        if args.violin_html:
            write_violin_gallery_html(paths.fig_dir, paths.outdir / "variability_violin_gallery.html")
        print(f"[*] Done. Results in {paths.outdir}/")
        return

    if args.run:
        setup_common()
        run_main_measurement(args.NUM_ITER, args.runs, paths, selected_sizes, selected_task)
        if args.violin_html:
            write_violin_gallery_html(paths.fig_dir, paths.outdir / "variability_violin_gallery.html")
        print(f"[*] Done. Results in {paths.outdir}/")
        return


if __name__ == "__main__":
    main()
