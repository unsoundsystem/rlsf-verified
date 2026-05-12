#!/usr/bin/env python3
import argparse
import os
import pwd
import shutil
import subprocess
from dataclasses import dataclass
from datetime import datetime
from html import escape
from pathlib import Path


def _drop_privileges_for_cargo(cmd: list[str], env: dict) -> tuple[list[str], dict]:
    """
    When the script is run with sudo, cargo invocations break because rustup
    is configured for the invoking user, not root. Detect sudo via SUDO_USER
    and wrap the command with `sudo -u <SUDO_USER> env VAR=...` so cargo runs
    as the original user and rustup can locate its toolchain.

    The env vars (HOME / CARGO_HOME / RUSTUP_HOME / PATH / RUSTFLAGS / ...) are
    passed via an explicit `env` prefix because sudoers' env_keep policy may
    strip them otherwise.
    """
    sudo_user = os.environ.get("SUDO_USER")
    if not (sudo_user and os.geteuid() == 0):
        return cmd, env
    try:
        user = pwd.getpwnam(sudo_user)
    except KeyError:
        return cmd, env
    env = dict(env)
    env["HOME"] = user.pw_dir
    env.setdefault("CARGO_HOME", f"{user.pw_dir}/.cargo")
    env.setdefault("RUSTUP_HOME", f"{user.pw_dir}/.rustup")
    cargo_bin = f"{user.pw_dir}/.cargo/bin"
    existing_path = env.get("PATH", os.environ.get("PATH", ""))
    if cargo_bin not in existing_path.split(":"):
        env["PATH"] = cargo_bin + ":" + existing_path
    # Variables to forward explicitly through `env VAR=...`. Pick keys that
    # affect cargo/rustup so we don't depend on sudoers env_keep settings.
    forward_keys = [
        "HOME", "PATH", "CARGO_HOME", "RUSTUP_HOME",
        "RUSTFLAGS", "CARGO_PROFILE_RELEASE_LTO", "RUSTC_BOOTSTRAP",
        "RUSTUP_TOOLCHAIN",
    ]
    env_prefix = ["env"] + [f"{k}={env[k]}" for k in forward_keys if k in env]
    return ["sudo", "-u", sudo_user, "--"] + env_prefix + cmd, env

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches


########################################
# Fixed policy (no options)
########################################
CPU = "1"
RT_PRIO = "99"

# Adjust if your repo layout differs.
BENCH_PROJ = Path(__file__).resolve().parent.parent.parent / "benches"
SIZES = ["32b", "64b", "512b", "2k", "4k", "8k"]
KINDS = ["original", "verified"]
TASKS = ["alt", "aaaddd", "deref", "coalesce", "exhaust"]
LTO_MODES = ["none", "fat"]

# Per-task size variants. Tasks whose workload sweeps allocation sizes
# internally (e.g. "exhaust": fill pool with G, G+10, G+20, ... until None)
# have no per-size binary variants — their bin name has no size token.
TASK_SIZES: dict[str, list[str]] = {
    "alt": SIZES,
    "aaaddd": SIZES,
    "deref": SIZES,
    "coalesce": SIZES,
    "exhaust": ["all"],
}

# rdpmc microbench dimensions (per-call link_free_block measurement)
RDPMC_COUNTERS = [
    "cycles", "instructions",
    "l1d_loads", "l1d_load_misses",
    "llc_load_misses", "dtlb_load_misses",
    "mem_loads", "mem_stores",
]
RDPMC_SCENARIOS = ["coalesce", "aaaddd", "alt"]
RDPMC_IMPLS = ["verified", "original"]

# Jitter probe: minimum events
JITTER_EVENTS = "cycles,instructions,task-clock,L1-dcache-loads,L1-dcache-load-misses,cache-misses,branch-misses,dTLB-load-misses"

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

    for s in TASK_SIZES[task]:
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


def ensure_binaries(task: str, sizes: list[str], lto_mode: str = "none"):
    """Build any missing binaries for the given task/sizes."""
    missing = []
    for s in sizes:
        for k in KINDS:
            bin_path = BENCH_PROJ / f"target/release/{bin_name_for(task, s, k)}"
            if not bin_path.exists():
                missing.append(bin_name_for(task, s, k))
    if missing:
        print(f"[*] Missing binaries: {', '.join(missing)}. Building...")
        build_project(task, lto_mode)


def parse_sizes_arg(sizes_arg: str | None, task: str) -> list[str]:
    valid = TASK_SIZES[task]

    # Tasks with a single synthetic size (e.g. "all" for "exhaust") have no
    # per-size variants; --sizes is ignored.
    if len(valid) == 1:
        if sizes_arg is not None:
            print(f"[!] --sizes ignored for task={task} (no per-size variants)")
        return list(valid)

    if sizes_arg is None:
        return list(valid)

    raw = [s.strip() for s in sizes_arg.split(",")]
    selected = [s for s in raw if s]
    if not selected:
        raise SystemExit("ERROR: --sizes is empty")

    invalid = [s for s in selected if s not in valid]
    if invalid:
        raise SystemExit(
            f"ERROR: unknown size(s) for task={task}: {', '.join(invalid)}. "
            f"valid: {', '.join(valid)}"
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
    # Synthetic "all" tag means the task has no per-size binary variant;
    # its [[bin]] is registered as e.g. "exhaust-verified" (no size token).
    if size == "all":
        return f"{task}-{kind}"
    return f"{task}{size}-{kind}"


def violin_pdf_name(task: str, sizes: list[str]) -> str:
    """Filename for the paper violin PDF (instructions per cycle)."""
    if sizes == ["all"]:
        return f"violin_paper_{task}.pdf"
    return f"violin_paper_{task}_{'_'.join(sizes)}.pdf"


def _sizes_in_order(task: str, sizes: list[str], present_in_df) -> list[str]:
    """Order `sizes` according to the task's canonical size list, keeping only
    entries that actually have data. `present_in_df` is a callable taking a
    size tag and returning True if the dataframe contains any row for it."""
    canonical = TASK_SIZES.get(task, SIZES)
    return [s for s in canonical if s in sizes and present_in_df(s)]


def size_to_int(size_str: str) -> int:
    """Convert SIZES-style tag ("32b", "512b", "2k", "4k", "8k") to bytes."""
    s = size_str.strip().lower()
    if s.endswith("b"):
        return int(s[:-1])
    if s.endswith("k"):
        return int(s[:-1]) * 1024
    return int(s)


def parse_csv_subset(arg: str | None, valid: list[str], label: str) -> list[str]:
    """Parse comma-separated subset of `valid`. None → all."""
    if arg is None:
        return list(valid)
    raw = [s.strip() for s in arg.split(",") if s.strip()]
    if not raw:
        raise SystemExit(f"ERROR: --{label} is empty")
    invalid = [s for s in raw if s not in valid]
    if invalid:
        raise SystemExit(
            f"ERROR: unknown {label}: {', '.join(invalid)}. valid: {', '.join(valid)}"
        )
    return list(dict.fromkeys(raw))


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

    # enable user-mode rdpmc (required by the rdpmc microbench).
    # 2 = unconditional user-mode rdpmc; 1 = only when a perf event is mapped.
    rdpmc_knob = Path("/sys/bus/event_source/devices/cpu/rdpmc")
    if rdpmc_knob.exists():
        run(["sudo", "tee", str(rdpmc_knob)], input_text="2\n")
    else:
        print(f"WARNING: {rdpmc_knob} not found; --rdpmc bench will fail at perf_event_open")

    # page size check (benchmark assumes 4KB pages)
    page_size = os.sysconf("SC_PAGESIZE")
    if page_size != 4096:
        print(f"WARNING: page size is {page_size}, not 4096. "
              f"Benchmark sizes 4k/8k are designed for 4KB pages.")


########################################
# 1) Run-to-run variability probe (distribution + violin)
########################################
def measure_jitter(num_iter: int, runs: int, paths: Paths, sizes: list[str], task: str):
    """
    Measure run-to-run variability using task-clock (converted to seconds).
    Output: jitter_time_distribution.csv and per-size violin plots.
    """
    ensure_binaries(task, sizes)
    records: list[dict] = []

    for s in sizes:
        for k in KINDS:
            bin_path = BENCH_PROJ / f"target/release/{bin_name_for(task, s, k)}"

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
                    "num_iter": num_iter,
                    "return_code": rc,
                    "time_s": t_s,  # task-clock converted to seconds
                    "task_clock": task_clock_val,
                    "task_clock_unit": task_clock_unit,
                    "cycles": perf_map["cycles"][0],
                    "instructions": perf_map["instructions"][0],
                    "L1-dcache-loads": perf_map["L1-dcache-loads"][0],
                    "L1-dcache-load-misses": perf_map["L1-dcache-load-misses"][0],
                    "cache-misses": perf_map.get("cache-misses", (0, ""))[0],
                    "branch-misses": perf_map.get("branch-misses", (0, ""))[0],
                    "dTLB-load-misses": perf_map.get("dTLB-load-misses", (0, ""))[0],
                })

    df = pd.DataFrame.from_records(records)
    df.to_csv(paths.jitter_csv, index=False)
    print(f"[*] Saved variability CSV: {paths.jitter_csv}")

    plot_jitter_violins(df, paths.fig_dir, sizes, task)
    plot_jitter_violin_paper(df, paths.fig_dir, sizes, task)


def plot_jitter_violins(df: pd.DataFrame, fig_dir: Path, sizes: list[str], task: str):
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
            fig_dir / f"variability_violin_{task}_{s}.png",
            title=f"[{task}] Run-to-run variability (task-clock) size={s}",
        )

    # all sizes mixed (reference)
    violinplot_by_kind(
        df,
        fig_dir / f"variability_violin_{task}_all_sizes.png",
        title=f"[{task}] Run-to-run variability (task-clock) all sizes",
    )
    print(f"[*] Variability figures saved under: {fig_dir}")


def plot_jitter_violin_paper(df: pd.DataFrame, fig_dir: Path,
                              sizes: list[str], task: str):
    """
    Paper-grade combined violin plot of cycles per (allocate+free) iteration.
    One subplot per size, sharing the y axis so cycle counts are visually
    comparable across sizes. Output is a single SVG with svg.fonttype="none"
    so text remains <text> elements (editable in Inkscape, small file).
    """
    required = {"kind", "size", "num_iter", "cycles"}
    missing = required - set(df.columns)
    if missing:
        print(f"[!] Paper violin: jitter df missing columns {sorted(missing)}; skipping")
        return
    df = df[df["kind"].isin(KINDS) & df["size"].isin(sizes)].copy()
    if df.empty:
        print(f"[!] Paper violin: no rows match kind/size selection; skipping")
        return
    df["cycles_per_iter"] = df["cycles"] / df["num_iter"]

    sizes_in_order = _sizes_in_order(
        task, sizes, lambda s: (df["size"] == s).any()
    )
    if not sizes_in_order:
        print(f"[!] Paper violin: no data for any selected size; skipping")
        return
    n = len(sizes_in_order)
    single_panel = sizes_in_order == ["all"]

    impls = ["original", "verified"]
    hatches = {"original": "..", "verified": "///"}
    facecolor = (0.85, 0.85, 0.85)

    stats: dict[tuple[str, str], dict] = {}
    for k in impls:
        for s in sizes_in_order:
            vals = df[(df["kind"] == k) & (df["size"] == s)][
                "cycles_per_iter"
            ].to_numpy()
            if vals.size == 0:
                print(f"[!] Paper violin: no samples for kind={k} size={s}; skipping")
                return
            stats[(k, s)] = {
                "median": float(np.median(vals)),
                "p99":    float(np.percentile(vals, 99)),
                "values": vals,
            }

    prev_rc = {
        "font.size": plt.rcParams["font.size"],
        "axes.labelsize": plt.rcParams["axes.labelsize"],
        "xtick.labelsize": plt.rcParams["xtick.labelsize"],
        "ytick.labelsize": plt.rcParams["ytick.labelsize"],
        "legend.fontsize": plt.rcParams["legend.fontsize"],
        "svg.fonttype": plt.rcParams["svg.fonttype"],
    }
    plt.rcParams.update({
        "font.size": 8,
        "axes.labelsize": 8,
        "xtick.labelsize": 7,
        "ytick.labelsize": 7,
        "legend.fontsize": 7,
        # Keep <text> elements rather than path-converted glyphs; smaller
        # file and trivially editable in Inkscape. Switch to "path" if the
        # viewer may lack the renderer's font.
        "svg.fonttype": "none",
    })

    # 1 row × n subplots, scaled to fit IEEE double-column (≤7 in wide).
    per_w = max(0.9, 6.5 / n)
    fig_w = min(7.0, per_w * n + 0.7)
    fig, axes = plt.subplots(
        1, n, sharey=True, figsize=(fig_w, 2.4), constrained_layout=True
    )
    if n == 1:
        axes = [axes]

    for i, s in enumerate(sizes_in_order):
        ax = axes[i]
        data = [stats[(k, s)]["values"] for k in impls]
        positions = [0, 1]
        parts = ax.violinplot(
            data, positions=positions, widths=0.7,
            showmedians=False, showextrema=False,
            quantiles=[[0.25, 0.75]] * 2,
        )
        for j, body in enumerate(parts["bodies"]):
            body.set_facecolor(facecolor)
            body.set_edgecolor("black")
            body.set_linewidth(0.5)
            body.set_alpha(1.0)
            body.set_hatch(hatches[impls[j]])
        if "cquantiles" in parts:
            parts["cquantiles"].set_color("gray")
            parts["cquantiles"].set_linewidth(0.4)
        for j, k in enumerate(impls):
            ax.hlines(
                stats[(k, s)]["median"],
                positions[j] - 0.25, positions[j] + 0.25,
                colors="white", linewidth=1.2, zorder=3,
            )

        m_o = stats[("original", s)]["median"]
        m_v = stats[("verified", s)]["median"]
        ratio = m_v / m_o if m_o > 0 else float("nan")
        p99_pair = max(stats[(k, s)]["p99"] for k in impls)
        ax.text(
            0.5, p99_pair * 1.02, f"×{ratio:.2f}",
            ha="center", va="bottom", fontsize=7,
        )

        ax.set_xticks(positions)
        ax.set_xticklabels(impls, rotation=15)
        ax.set_xlim(-0.6, 1.6)
        if not single_panel:
            ax.set_title(s, fontsize=8)
        ax.yaxis.grid(True, linestyle=":", linewidth=0.4, color="gray")
        ax.xaxis.grid(False)
        ax.set_axisbelow(True)
        for spine in ("top", "right"):
            ax.spines[spine].set_visible(False)

    ylabel = "Cycles per fill+drain" if single_panel else "Cycles per allocate+free"
    axes[0].set_ylabel(ylabel)

    out_svg = fig_dir / f"variability_violin_paper_{task}.svg"
    out_png = fig_dir / f"variability_violin_paper_{task}.png"
    out_svg.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_svg, bbox_inches="tight")
    fig.savefig(out_png, dpi=300, bbox_inches="tight")
    plt.close(fig)
    plt.rcParams.update(prev_rc)

    print(f"[*] Saved paper violin SVG: {out_svg}")
    print(f"[*] Saved paper violin PNG: {out_png}")


def _build_summary_table_html(jitter_csv: Path) -> str:
    """
    Read jitter CSV and build an HTML summary table with median cycles,
    median time_s, and regression ratios (verified / original) per size.
    Returns empty string if the CSV is missing or has no data.
    """
    if not jitter_csv.exists():
        return ""

    df = pd.read_csv(jitter_csv)
    if df.empty or "cycles" not in df.columns or "time_s" not in df.columns:
        return ""

    num_iter = int(df["num_iter"].iloc[0]) if "num_iter" in df.columns else None

    size_order = {s: i for i, s in enumerate(SIZES)}

    med = df.groupby(["size", "kind"])[["cycles", "time_s"]].median()
    med = med.reset_index()

    orig = med[med["kind"] == "original"].set_index("size")
    veri = med[med["kind"] == "verified"].set_index("size")

    all_sizes = sorted(
        set(orig.index) | set(veri.index),
        key=lambda s: size_order.get(s, 9_999),
    )

    rows: list[str] = []
    for s in all_sizes:
        c_o = orig.loc[s, "cycles"] if s in orig.index else float("nan")
        c_v = veri.loc[s, "cycles"] if s in veri.index else float("nan")
        t_o = orig.loc[s, "time_s"] if s in orig.index else float("nan")
        t_v = veri.loc[s, "time_s"] if s in veri.index else float("nan")

        c_ratio = c_v / c_o if c_o else float("nan")
        t_ratio = t_v / t_o if t_o else float("nan")

        def fmt_cycles(v):
            if v != v:  # NaN
                return "&mdash;"
            return f"{v:,.0f}"

        def fmt_time(v):
            if v != v:
                return "&mdash;"
            if v < 1e-6:
                return f"{v * 1e9:.1f} ns"
            if v < 1e-3:
                return f"{v * 1e6:.1f} &micro;s"
            if v < 1:
                return f"{v * 1e3:.2f} ms"
            return f"{v:.4f} s"

        def fmt_ratio(v):
            if v != v:
                return "&mdash;"
            pct = (v - 1) * 100
            sign = "+" if pct >= 0 else ""
            cls = "regress" if pct > 1 else "improve" if pct < -1 else "neutral"
            return f'<span class="{cls}">{v:.3f}x ({sign}{pct:.1f}%)</span>'

        rows.append(
            f"<tr>"
            f"<td>{escape(s)}</td>"
            f"<td class='num'>{fmt_cycles(c_o)}</td>"
            f"<td class='num'>{fmt_cycles(c_v)}</td>"
            f"<td class='num'>{fmt_ratio(c_ratio)}</td>"
            f"<td class='num'>{fmt_time(t_o)}</td>"
            f"<td class='num'>{fmt_time(t_v)}</td>"
            f"<td class='num'>{fmt_ratio(t_ratio)}</td>"
            f"</tr>"
        )

    iter_note = f" (num_iter={num_iter})" if num_iter is not None else ""
    return f"""
  <section>
    <h2>Summary: cycles &amp; time (median, verified / original){iter_note}</h2>
    <table class="summary">
      <thead>
        <tr>
          <th rowspan="2">Size</th>
          <th colspan="3">Cycles</th>
          <th colspan="3">Time</th>
        </tr>
        <tr>
          <th>original</th><th>verified</th><th>ratio</th>
          <th>original</th><th>verified</th><th>ratio</th>
        </tr>
      </thead>
      <tbody>
        {"".join(rows)}
      </tbody>
    </table>
  </section>
"""


def write_violin_gallery_html(fig_dir: Path, out_html: Path, jitter_csv: Path | None = None) -> bool:
    """
    Write an HTML gallery listing violin plot PNGs grouped by task name,
    plus a summary table of cycles/time regression if jitter_csv is provided.
    Expects filenames like: variability_violin_{task}_{size}.png
    """
    import re as _re

    size_order = {s: i for i, s in enumerate(SIZES)}
    task_order = {t: i for i, t in enumerate(TASKS)}

    pat = _re.compile(r"^variability_violin_([a-z]+)_(.+)\.png$")

    pngs = sorted(fig_dir.glob("variability_violin_*.png"))
    if not pngs:
        print(f"[!] Skip violin HTML: no violin plot PNGs found in {fig_dir}")
        return False

    # group by task
    groups: dict[str, list[Path]] = {}
    for p in pngs:
        m = pat.match(p.name)
        if not m:
            continue
        task_name = m.group(1)
        groups.setdefault(task_name, []).append(p)

    if not groups:
        print(f"[!] Skip violin HTML: no matching PNGs in {fig_dir}")
        return False

    def size_key(path: Path):
        m = pat.match(path.name)
        suffix = m.group(2) if m else ""
        if suffix == "all_sizes":
            return (10_000, suffix)
        return (size_order.get(suffix, 9_999), suffix)

    sections: list[str] = []
    for task_name in sorted(groups, key=lambda t: task_order.get(t, 9_999)):
        cards: list[str] = []
        for p in sorted(groups[task_name], key=size_key):
            m = pat.match(p.name)
            label = escape(m.group(2)) if m else escape(p.stem)
            src = escape(f"fig/{p.name}")
            cards.append(
                f'<figure><img src="{src}" alt="{label}"><figcaption>{label}</figcaption></figure>'
            )
        sections.append(
            f'<section><h2>{escape(task_name)}</h2><div class="grid">{"".join(cards)}</div></section>'
        )

    summary_html = ""
    if jitter_csv is not None:
        summary_html = _build_summary_table_html(jitter_csv)

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
    h2 {{
      margin: 24px 0 12px 0;
      font-size: 1.15rem;
      border-bottom: 2px solid #ddd;
      padding-bottom: 4px;
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
    table.summary {{
      border-collapse: collapse;
      width: 100%;
      max-width: 960px;
      margin: 12px 0 24px 0;
      font-size: 0.9rem;
    }}
    table.summary th, table.summary td {{
      border: 1px solid #ccc;
      padding: 6px 10px;
      text-align: center;
    }}
    table.summary th {{
      background: #f0f0f0;
      font-weight: 600;
    }}
    table.summary td.num {{
      text-align: right;
      font-variant-numeric: tabular-nums;
    }}
    .regress {{ color: #c0392b; font-weight: 600; }}
    .improve {{ color: #27ae60; font-weight: 600; }}
    .neutral {{ color: #555; }}
  </style>
</head>
<body>
  <h1>Variability violin plots (task-clock)</h1>
  {summary_html}
  {"".join(sections)}
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
    ensure_binaries(task, sizes)
    meta_fp = open(paths.meta_log, "a")
    summary_rows: list[dict] = []

    try:
        for s in sizes:
            for k in KINDS:
                bin_path = BENCH_PROJ / f"target/release/{bin_name_for(task, s, k)}"

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
                        "num_iter": num_iter,
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
# Paper figure: instructions-per-cycle violin (multi-size on one plot)
########################################
def plot_main_violin(summary_csv: Path, out_pdf: Path, sizes: list[str], task: str):
    """
    Render a single violin plot of instructions per allocate+free cycle,
    side-by-side original vs verified across the given size set.

    Reads main_summary.csv (must contain columns: kind, size, num_iter,
    instructions). Per-run `instructions` is divided by `num_iter` to obtain
    per-cycle counts. PDF is sized for IEEE single-column unless many sizes
    are plotted (then widened).
    """
    if not summary_csv.exists():
        print(f"[!] Violin: summary CSV not found: {summary_csv}")
        return

    df = pd.read_csv(summary_csv)
    required = {"kind", "size", "num_iter", "instructions"}
    missing = required - set(df.columns)
    if missing:
        print(f"[!] Violin: main_summary.csv missing columns {sorted(missing)}; skipping")
        return

    df = df[df["kind"].isin(KINDS) & df["size"].isin(sizes)].copy()
    if df.empty:
        print(f"[!] Violin: no rows match kind/size selection; skipping")
        return

    df["instructions_per_cycle"] = df["instructions"] / df["num_iter"]

    sizes_in_order = _sizes_in_order(
        task, sizes, lambda s: (df["size"] == s).any()
    )
    if not sizes_in_order:
        print("[!] Violin: no data for any selected size; skipping")
        return
    single_panel = sizes_in_order == ["all"]

    impls = ["original", "verified"]
    hatches = {"original": "..", "verified": "///"}
    facecolor = (0.85, 0.85, 0.85)

    stats: dict[tuple[str, str], dict] = {}
    for k in impls:
        for s in sizes_in_order:
            vals = df[(df["kind"] == k) & (df["size"] == s)][
                "instructions_per_cycle"
            ].to_numpy()
            if vals.size == 0:
                print(f"[!] Violin: no samples for kind={k} size={s}")
                return
            stats[(k, s)] = {
                "median": float(np.median(vals)),
                "p99": float(np.percentile(vals, 99)),
                "values": vals,
            }
    y_clip = max(v["p99"] for v in stats.values()) * 1.05

    prev_rc = {
        "font.size": plt.rcParams["font.size"],
        "axes.labelsize": plt.rcParams["axes.labelsize"],
        "xtick.labelsize": plt.rcParams["xtick.labelsize"],
        "ytick.labelsize": plt.rcParams["ytick.labelsize"],
        "legend.fontsize": plt.rcParams["legend.fontsize"],
        "pdf.fonttype": plt.rcParams["pdf.fonttype"],
        "ps.fonttype": plt.rcParams["ps.fonttype"],
    }
    plt.rcParams.update({
        "font.size": 8,
        "axes.labelsize": 8,
        "xtick.labelsize": 7,
        "ytick.labelsize": 7,
        "legend.fontsize": 7,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })

    n = len(sizes_in_order)
    fig_w = 3.5 if n <= 4 else max(3.5, 0.85 * n + 1.5)
    fig, ax = plt.subplots(figsize=(fig_w, 2.5))

    for j, k in enumerate(impls):
        data = [stats[(k, s)]["values"] for s in sizes_in_order]
        offset = -0.18 if j == 0 else 0.18
        positions = [i + offset for i in range(n)]
        parts = ax.violinplot(
            data, positions=positions, widths=0.3,
            showmedians=False, showextrema=False,
            quantiles=[[0.25, 0.75]] * n,
        )
        for body in parts["bodies"]:
            body.set_facecolor(facecolor)
            body.set_edgecolor("black")
            body.set_linewidth(0.5)
            body.set_alpha(1.0)
            body.set_hatch(hatches[k])
        if "cquantiles" in parts:
            parts["cquantiles"].set_color("gray")
            parts["cquantiles"].set_linewidth(0.4)
        for i, s in enumerate(sizes_in_order):
            ax.hlines(
                stats[(k, s)]["median"],
                positions[i] - 0.12, positions[i] + 0.12,
                colors="white", linewidth=1.2, zorder=3,
            )

    for i, s in enumerate(sizes_in_order):
        m_o = stats[("original", s)]["median"]
        m_v = stats[("verified", s)]["median"]
        ratio = m_v / m_o
        p99_pair = max(stats[(k, s)]["p99"] for k in impls)
        y_text = min(p99_pair * 1.02, y_clip * 0.98)
        ax.text(i, y_text, f"×{ratio:.2f}",
                ha="center", va="bottom", fontsize=7)

    ax.set_xticks(range(n))
    ax.set_xticklabels([task] if single_panel else sizes_in_order)
    ax.set_xlim(-0.5, n - 0.5)
    ax.set_xlabel("" if single_panel else "Allocation size")
    ylabel_main = (
        "Instructions per fill+drain"
        if single_panel
        else "Instructions per allocate+free cycle"
    )
    ax.set_ylabel(ylabel_main)
    ax.set_ylim(0, y_clip)
    ax.yaxis.grid(True, linestyle=":", linewidth=0.4, color="gray")
    ax.xaxis.grid(False)
    ax.set_axisbelow(True)
    for spine in ("top", "right"):
        ax.spines[spine].set_visible(False)

    legend_handles = [
        mpatches.Patch(facecolor=facecolor, edgecolor="black",
                       hatch=hatches[k], label=k)
        for k in impls
    ]
    ax.legend(
        handles=legend_handles, loc="lower center",
        bbox_to_anchor=(0.5, 1.02), ncol=2,
        frameon=False, fontsize=7,
        handlelength=2.0, handleheight=1.2,
    )

    fig.tight_layout()
    out_pdf.parent.mkdir(parents=True, exist_ok=True)
    out_png = out_pdf.with_suffix(".png")
    fig.savefig(out_pdf, dpi=300, bbox_inches="tight")
    fig.savefig(out_png, dpi=300, bbox_inches="tight")
    plt.close(fig)
    plt.rcParams.update(prev_rc)

    print(f"[*] Saved violin PDF: {out_pdf}")
    print(f"[*] Saved violin PNG: {out_png}")
    _print_violin_summary(stats, sizes_in_order, impls)


def _print_violin_summary(stats: dict, sizes_in_order: list[str], impls: list[str]):
    print()
    print("| impl     | size    | median   | IQR      |")
    print("|----------|---------|----------|----------|")
    for k in impls:
        for s in sizes_in_order:
            vals = stats[(k, s)]["values"]
            q25 = float(np.percentile(vals, 25))
            q75 = float(np.percentile(vals, 75))
            print(f"| {k:<8} | {s:<7} | "
                  f"{stats[(k, s)]['median']:>8.1f} | {q75 - q25:>8.1f} |")

    print()
    print("| size    | median ratio (verified/original) |")
    print("|---------|----------------------------------|")
    ratios = []
    for s in sizes_in_order:
        r = stats[("verified", s)]["median"] / stats[("original", s)]["median"]
        ratios.append(r)
        print(f"| {s:<7} | {r:>32.3f} |")
    if ratios:
        geo = float(np.exp(np.mean(np.log(ratios))))
        print()
        print(f"Overall median ratio (geometric mean across sizes): {geo:.3f}")


########################################
# rdpmc microbench (per-call link_free_block measurement)
########################################
def build_rdpmc_bench(lto_mode: str):
    """Build the link_free_block_rdpmc binary with the rdpmc-bench feature."""
    print(f"[*] Building link_free_block_rdpmc (--features rdpmc-bench, lto={lto_mode})")
    env = os.environ.copy()
    env["RUSTFLAGS"] = "-C target-cpu=native"
    if lto_mode == "fat":
        env["CARGO_PROFILE_RELEASE_LTO"] = "fat"
    else:
        env.pop("CARGO_PROFILE_RELEASE_LTO", None)
    cmd = ["cargo", "build", "--release",
           "--features", "rdpmc-bench",
           "--bin", "link_free_block_rdpmc"]
    cmd, env = _drop_privileges_for_cargo(cmd, env)
    subprocess.run(cmd, cwd=str(BENCH_PROJ), env=env, check=True)


def run_rdpmc_sweep(num_iter: int, paths: Paths,
                    sizes: list[str], scenarios: list[str],
                    counters: list[str], impls: list[str]):
    """
    Run the rdpmc microbench across the (impl, scenario, size, counter) grid.
    Accumulates CSV rows into <outdir>/rdpmc_results.csv.
    """
    bin_path = BENCH_PROJ / "target/release/link_free_block_rdpmc"
    if not bin_path.exists():
        raise SystemExit(f"ERROR: {bin_path} not found. Run build_rdpmc_bench() first.")

    out_csv = paths.outdir / "rdpmc_results.csv"
    header_written = False
    n_runs = len(impls) * len(scenarios) * len(sizes) * len(counters)
    print(f"[*] RDPMC sweep: {n_runs} runs ({num_iter} iters each) -> {out_csv}")

    with open(out_csv, "w") as f:
        for impl_ in impls:
            for sc in scenarios:
                for size_str in sizes:
                    size_bytes = size_to_int(size_str)
                    for c in counters:
                        cmd = [
                            "sudo", "chrt", "-f", RT_PRIO,
                            "taskset", "-c", CPU,
                            str(bin_path), sc, str(size_bytes), str(num_iter),
                            "--counter", c, "--impl", impl_,
                        ]
                        print(f"[*] RDPMC impl={impl_} sc={sc} size={size_str} counter={c}")
                        p = subprocess.run(
                            cmd, capture_output=True, text=True, check=False
                        )
                        if p.returncode != 0:
                            print(f"  [!] returncode={p.returncode}: {p.stderr.strip()}")
                            continue
                        lines = p.stdout.splitlines()
                        if not lines:
                            print(f"  [!] empty stdout")
                            continue
                        # First line is the CSV header; emit once.
                        if not header_written:
                            f.write(lines[0] + "\n")
                            header_written = True
                        for ln in lines[1:]:
                            f.write(ln + "\n")
                        f.flush()
    print(f"[*] Saved: {out_csv}")


########################################
# Paper figure (--paper): standalone path that does not share code with the
# jitter measurement. Uses sudo+chrt+taskset+perf when passwordless sudo is
# available, else falls back to taskset+perf (no RT priority).
########################################
def _sudo_nopw_available() -> bool:
    """True if `sudo -n true` succeeds (passwordless sudo for this user)."""
    try:
        p = subprocess.run(["sudo", "-n", "true"],
                           capture_output=True, text=True, check=False)
        return p.returncode == 0
    except FileNotFoundError:
        return False


def _parse_perf_xcsv_paper(stderr_text: str) -> dict[str, tuple[float, str]]:
    """Like parse_perf_xcsv, but strips the ':u' suffix that appears when
    perf_event_paranoid >= 2 (userspace-only counters). Local to --paper so
    the existing jitter parser stays unchanged."""
    out: dict[str, tuple[float, str]] = {}
    for line in stderr_text.splitlines():
        cols = [c.strip() for c in line.split(",")]
        if len(cols) < 3 or not cols[0] or cols[0].startswith("<"):
            continue
        try:
            val = float(cols[0].replace(",", ""))
        except ValueError:
            continue
        event = (cols[2] or "(unknown)").removesuffix(":u")
        out[event] = (val, cols[1])
    return out


def _run_perf_stat_paper(bin_path: Path, num_iter: int, events: str,
                         use_rt: bool) -> tuple[int, dict[str, tuple[float, str]], str]:
    cmd: list[str] = []
    if use_rt:
        cmd += ["sudo", "-n", "chrt", "-f", RT_PRIO]
    cmd += ["taskset", "-c", CPU,
            "perf", "stat", "-x,", "-e", events,
            str(bin_path), str(num_iter)]
    p = subprocess.run(cmd, stdout=subprocess.DEVNULL,
                       stderr=subprocess.PIPE, text=True, check=False)
    return p.returncode, _parse_perf_xcsv_paper(p.stderr), p.stderr


PAPER_EVENTS = "cycles,instructions,task-clock"


def measure_paper(num_iter: int, runs: int, paths: Paths,
                  sizes: list[str], task: str, use_rt: bool,
                  csv_name: str = "paper_perf.csv") -> "pd.DataFrame":
    """Sweep perf stat across (kind, size, run) for the paper figure.
    Output: <outdir>/<csv_name>. The csv_name override lets callers run
    multiple tasks in one invocation without clobbering each other."""
    ensure_binaries(task, sizes)
    records: list[dict] = []
    rt_label = "RT (sudo+chrt)" if use_rt else "no-RT (plain perf)"
    print(f"[*] PAPER sweep: task={task} sizes={sizes} runs={runs}  [{rt_label}]")
    for s in sizes:
        for k in KINDS:
            bin_path = BENCH_PROJ / f"target/release/{bin_name_for(task, s, k)}"
            for i in range(1, runs + 1):
                rc, m, raw = _run_perf_stat_paper(bin_path, num_iter, PAPER_EVENTS, use_rt)
                if rc != 0:
                    print(f"  [!] {bin_path.name} run {i}: rc={rc} stderr={raw.strip()[:200]}")
                    continue
                records.append({
                    "task": task, "kind": k, "size": s, "run": i,
                    "num_iter": num_iter,
                    "cycles": m.get("cycles", (float("nan"), ""))[0],
                    "instructions": m.get("instructions", (float("nan"), ""))[0],
                    "task_clock": m.get("task-clock", (float("nan"), ""))[0],
                })
                if i == 1 or i == runs or i % max(1, runs // 5) == 0:
                    cy = records[-1]["cycles"]
                    print(f"  [{k} {s} run {i:>3}/{runs}] cycles={cy:.3e}", flush=True)
    df = pd.DataFrame(records)
    csv_path = paths.outdir / csv_name
    df.to_csv(csv_path, index=False)
    print(f"[*] Saved CSV: {csv_path}")
    return df


def plot_paper_violin(df: "pd.DataFrame", fig_dir: Path,
                      sizes: list[str], task: str, num_iter: int):
    """Paper-grade violin. Single-size tasks (e.g. exhaust) get a 2-panel
    (cycles, instructions) layout; multi-size tasks get one cycles panel
    per size."""
    df = df[df["kind"].isin(KINDS) & df["size"].isin(sizes)].copy()
    if df.empty:
        print("[!] Paper plot: no rows match; skipping")
        return

    canonical = TASK_SIZES.get(task, SIZES)
    sizes_in_order = [s for s in canonical if s in sizes and (df["size"] == s).any()]
    if not sizes_in_order:
        print("[!] Paper plot: no matching sizes")
        return

    prev_rc = {kk: plt.rcParams[kk] for kk in [
        "font.size", "axes.labelsize", "xtick.labelsize",
        "ytick.labelsize", "legend.fontsize",
        "pdf.fonttype", "ps.fonttype", "svg.fonttype",
    ]}
    plt.rcParams.update({
        "font.size": 8, "axes.labelsize": 8,
        "xtick.labelsize": 7, "ytick.labelsize": 7,
        "legend.fontsize": 7,
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "svg.fonttype": "none",
    })
    hatches = {"original": "..", "verified": "///"}
    facecolor = (0.85, 0.85, 0.85)

    def _draw_pair(ax, data_list, ymax_p99, ratio_text, ylabel, xticklabels):
        parts = ax.violinplot(data_list, positions=[0, 1], widths=0.7,
                              showmedians=False, showextrema=False,
                              quantiles=[[0.25, 0.75]] * 2)
        for j, body in enumerate(parts["bodies"]):
            body.set_facecolor(facecolor)
            body.set_edgecolor("black"); body.set_linewidth(0.5)
            body.set_alpha(1.0); body.set_hatch(hatches[xticklabels[j]])
        if "cquantiles" in parts:
            parts["cquantiles"].set_color("gray")
            parts["cquantiles"].set_linewidth(0.4)
        for j, d in enumerate(data_list):
            ax.hlines(float(np.median(d)),
                      j - 0.25, j + 0.25,
                      colors="white", linewidth=1.2, zorder=3)
        ax.text(0.5, ymax_p99 * 1.03, ratio_text,
                ha="center", va="bottom", fontsize=7)
        ax.set_xticks([0, 1]); ax.set_xticklabels(xticklabels, rotation=15)
        ax.set_xlim(-0.6, 1.6); ax.set_ylabel(ylabel)
        ax.yaxis.grid(True, linestyle=":", linewidth=0.4, color="gray")
        ax.xaxis.grid(False); ax.set_axisbelow(True)
        for sp in ("top", "right"):
            ax.spines[sp].set_visible(False)

    if len(sizes_in_order) == 1:
        s = sizes_in_order[0]
        fig, axes = plt.subplots(1, 2, figsize=(6.5, 2.4),
                                  constrained_layout=True)
        for ax, (metric, ylabel) in zip(axes, [
            ("cycles",       f"Cycles per {task} round"),
            ("instructions", f"Instructions per {task} round"),
        ]):
            data = [
                (df[(df["kind"] == k) & (df["size"] == s)][metric] / num_iter).to_numpy()
                for k in KINDS
            ]
            meds = [float(np.median(d)) for d in data]
            ratio = meds[1] / meds[0] if meds[0] > 0 else float("nan")
            p99 = max(float(np.percentile(d, 99)) for d in data)
            _draw_pair(ax, data, p99, f"×{ratio:.2f}", ylabel, KINDS)
    else:
        n = len(sizes_in_order)
        per_w = max(0.9, 6.5 / n)
        fig_w = min(7.0, per_w * n + 0.7)
        fig, axes = plt.subplots(1, n, sharey=True, figsize=(fig_w, 2.4),
                                  constrained_layout=True)
        if n == 1:
            axes = [axes]
        for i, s in enumerate(sizes_in_order):
            ax = axes[i]
            data = [
                (df[(df["kind"] == k) & (df["size"] == s)]["cycles"] / num_iter).to_numpy()
                for k in KINDS
            ]
            meds = [float(np.median(d)) for d in data]
            ratio = meds[1] / meds[0] if meds[0] > 0 else float("nan")
            p99 = max(float(np.percentile(d, 99)) for d in data)
            _draw_pair(ax, data, p99, f"×{ratio:.2f}",
                       "Cycles per allocate+free" if i == 0 else "",
                       KINDS)
            ax.set_title(s, fontsize=8)

    legend_handles = [
        mpatches.Patch(facecolor=facecolor, edgecolor="black",
                       hatch=hatches[k], label=k)
        for k in KINDS
    ]
    fig.legend(handles=legend_handles, loc="upper center",
               bbox_to_anchor=(0.5, 1.05), ncol=2,
               frameon=False, fontsize=7)

    out_svg = fig_dir / f"paper_violin_{task}.svg"
    out_pdf = fig_dir / f"paper_violin_{task}.pdf"
    out_svg.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_svg, bbox_inches="tight")
    fig.savefig(out_pdf, dpi=300, bbox_inches="tight")
    plt.close(fig)
    plt.rcParams.update(prev_rc)

    print(f"[*] Saved figure: {out_svg}")
    print(f"[*] Saved figure: {out_pdf}")

    # Stats summary table
    print()
    print("| impl     | size    | metric         | median      | IQR         |")
    print("|----------|---------|----------------|-------------|-------------|")
    for k in KINDS:
        for s in sizes_in_order:
            for metric, label in [("cycles", "cycles/iter "),
                                   ("instructions", "insn/iter   ")]:
                v = (df[(df["kind"] == k) & (df["size"] == s)][metric] / num_iter).to_numpy()
                if v.size == 0:
                    continue
                med = float(np.median(v))
                iqr = float(np.percentile(v, 75) - np.percentile(v, 25))
                print(f"| {k:<8} | {s:<7} | {label} | {med:>10.1f}  | {iqr:>10.1f}  |")
    for s in sizes_in_order:
        for metric, label in [("cycles", "cycles"), ("instructions", "insn  ")]:
            m_o = float(np.median(
                (df[(df["kind"] == "original") & (df["size"] == s)][metric] / num_iter).to_numpy()))
            m_v = float(np.median(
                (df[(df["kind"] == "verified") & (df["size"] == s)][metric] / num_iter).to_numpy()))
            if m_o > 0:
                print(f"  size={s}  {label} median ratio (verified/original) = {m_v / m_o:.3f}")


def plot_paper_grouped(df: "pd.DataFrame", fig_dir: Path,
                       sizes: list[str], task: str, num_iter: int):
    """Single-panel grouped violin: x-axis = size, two violins per size
    (original / verified, offset by ±0.18), y-axis = cycles per iteration.
    Companion to plot_paper_violin's per-size panel layout. Modeled after
    plot_main_violin (instructions variant); adapted to read cycles directly
    from the paper-perf dataframe."""
    df = df[df["kind"].isin(KINDS) & df["size"].isin(sizes)].copy()
    if df.empty:
        print("[!] Paper grouped: no rows match; skipping")
        return

    df["cycles_per_iter"] = df["cycles"] / num_iter

    canonical = TASK_SIZES.get(task, SIZES)
    sizes_in_order = [s for s in canonical if s in sizes and (df["size"] == s).any()]
    if not sizes_in_order:
        print("[!] Paper grouped: no data for any selected size; skipping")
        return

    impls = ["original", "verified"]
    hatches = {"original": "..", "verified": "///"}
    facecolor = (0.85, 0.85, 0.85)

    stats: dict[tuple[str, str], dict] = {}
    for k in impls:
        for s in sizes_in_order:
            vals = df[(df["kind"] == k) & (df["size"] == s)]["cycles_per_iter"].to_numpy()
            if vals.size == 0:
                print(f"[!] Paper grouped: no samples for kind={k} size={s}")
                return
            stats[(k, s)] = {
                "median": float(np.median(vals)),
                "p99": float(np.percentile(vals, 99)),
                "values": vals,
            }
    y_clip = max(v["p99"] for v in stats.values()) * 1.05

    prev_rc = {kk: plt.rcParams[kk] for kk in [
        "font.size", "axes.labelsize", "xtick.labelsize",
        "ytick.labelsize", "legend.fontsize",
        "pdf.fonttype", "ps.fonttype", "svg.fonttype",
    ]}
    plt.rcParams.update({
        "font.size": 8, "axes.labelsize": 8,
        "xtick.labelsize": 7, "ytick.labelsize": 7,
        "legend.fontsize": 7,
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "svg.fonttype": "none",
    })

    n = len(sizes_in_order)
    fig_w = 3.5 if n <= 4 else max(3.5, 0.85 * n + 1.5)
    fig, ax = plt.subplots(figsize=(fig_w, 2.5))

    for j, k in enumerate(impls):
        data = [stats[(k, s)]["values"] for s in sizes_in_order]
        offset = -0.18 if j == 0 else 0.18
        positions = [i + offset for i in range(n)]
        parts = ax.violinplot(
            data, positions=positions, widths=0.3,
            showmedians=False, showextrema=False,
            quantiles=[[0.25, 0.75]] * n,
        )
        for body in parts["bodies"]:
            body.set_facecolor(facecolor)
            body.set_edgecolor("black")
            body.set_linewidth(0.5)
            body.set_alpha(1.0)
            body.set_hatch(hatches[k])
        if "cquantiles" in parts:
            parts["cquantiles"].set_color("gray")
            parts["cquantiles"].set_linewidth(0.4)
        for i, s in enumerate(sizes_in_order):
            ax.hlines(
                stats[(k, s)]["median"],
                positions[i] - 0.12, positions[i] + 0.12,
                colors="white", linewidth=1.2, zorder=3,
            )

    for i, s in enumerate(sizes_in_order):
        m_o = stats[("original", s)]["median"]
        m_v = stats[("verified", s)]["median"]
        if m_o <= 0:
            continue
        ratio = m_v / m_o
        p99_pair = max(stats[(k, s)]["p99"] for k in impls)
        y_text = min(p99_pair * 1.02, y_clip * 0.98)
        ax.text(i, y_text, f"×{ratio:.2f}",
                ha="center", va="bottom", fontsize=7)

    ax.set_xticks(range(n))
    ax.set_xticklabels(sizes_in_order)
    ax.set_xlim(-0.5, n - 0.5)
    ax.set_xlabel("Allocation size")
    ax.set_ylabel("Cycles per allocate+free")
    ax.set_ylim(0, y_clip)
    ax.yaxis.grid(True, linestyle=":", linewidth=0.4, color="gray")
    ax.xaxis.grid(False)
    ax.set_axisbelow(True)
    for sp in ("top", "right"):
        ax.spines[sp].set_visible(False)

    legend_handles = [
        mpatches.Patch(facecolor=facecolor, edgecolor="black",
                       hatch=hatches[k], label=k)
        for k in impls
    ]
    ax.legend(
        handles=legend_handles, loc="lower center",
        bbox_to_anchor=(0.5, 1.02), ncol=2,
        frameon=False, fontsize=7,
        handlelength=2.0, handleheight=1.2,
    )

    fig.tight_layout()
    out_svg = fig_dir / f"paper_violin_grouped_{task}.svg"
    out_pdf = fig_dir / f"paper_violin_grouped_{task}.pdf"
    out_svg.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_svg, bbox_inches="tight")
    fig.savefig(out_pdf, dpi=300, bbox_inches="tight")
    plt.close(fig)
    plt.rcParams.update(prev_rc)

    print(f"[*] Saved figure: {out_svg}")
    print(f"[*] Saved figure: {out_pdf}")


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
    mode.add_argument("--rdpmc", action="store_true",
                      help="rdpmc per-call link_free_block microbench (verified vs original)")
    mode.add_argument("--paper", action="store_true",
                      help="Paper-grade violin figure via raw perf+taskset; "
                           "uses sudo+chrt for RT priority if passwordless sudo is available")

    ap.add_argument("NUM_ITER", nargs="?", type=int, help="Iteration count passed to each benchmark binary")
    ap.add_argument("--runs", type=int, default=100)
    ap.add_argument("--task", default=None,
                    help=f"Benchmark task prefix. valid: {','.join(TASKS)}. "
                         f"For --paper, may be a comma-separated list (e.g. coalesce,exhaust); "
                         f"if omitted, --paper defaults to 'coalesce,exhaust'.")
    ap.add_argument("--lto", default="none", help=f"Release LTO mode for build/all. valid: {','.join(LTO_MODES)}")
    ap.add_argument("--sizes", default=None, help=f"Comma-separated sizes to run (default: all). valid: {','.join(SIZES)}")
    ap.add_argument("--violin-html", action="store_true", help="Write an HTML gallery for variability violin plots")
    ap.add_argument("--violin", action="store_true",
                    help="After --run/--all, render a single violin PDF (instructions per allocate+free cycle) covering all selected sizes")
    ap.add_argument("--outdir", default=None)
    ap.add_argument("--rdpmc-counters", default=None,
                    help=f"Comma-separated rdpmc counters. Default: all. valid: {','.join(RDPMC_COUNTERS)}")
    ap.add_argument("--rdpmc-scenarios", default=None,
                    help=f"Comma-separated rdpmc scenarios. Default: all. valid: {','.join(RDPMC_SCENARIOS)}")
    ap.add_argument("--rdpmc-impls", default=None,
                    help=f"Comma-separated rdpmc impls. Default: all. valid: {','.join(RDPMC_IMPLS)}")

    args = ap.parse_args()

    env_checks()
    paths = make_outdir(args.outdir)
    selected_lto = parse_lto_arg(args.lto)
    # --paper accepts a comma-separated --task and resolves it inside the
    # branch; other modes still take a single task here.
    if args.paper:
        selected_task = None
        selected_sizes = None
    else:
        selected_task = parse_task_arg(args.task)
        selected_sizes = parse_sizes_arg(args.sizes, selected_task)

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
            write_violin_gallery_html(paths.fig_dir, paths.outdir / "variability_violin_gallery.html", paths.jitter_csv)
        run_main_measurement(args.NUM_ITER, args.runs, paths, selected_sizes, selected_task)
        if args.violin:
            plot_main_violin(
                paths.outdir / "main_summary.csv",
                paths.fig_dir / violin_pdf_name(selected_task, selected_sizes),
                selected_sizes, selected_task,
            )
        print(f"[*] Done. Results in {paths.outdir}/")
        return

    if args.jitter:
        setup_common()
        measure_jitter(args.NUM_ITER, args.runs, paths, selected_sizes, selected_task)
        if args.violin_html:
            write_violin_gallery_html(paths.fig_dir, paths.outdir / "variability_violin_gallery.html", paths.jitter_csv)
        print(f"[*] Done. Results in {paths.outdir}/")
        return

    if args.run:
        setup_common()
        run_main_measurement(args.NUM_ITER, args.runs, paths, selected_sizes, selected_task)
        if args.violin_html:
            write_violin_gallery_html(paths.fig_dir, paths.outdir / "variability_violin_gallery.html", paths.jitter_csv)
        if args.violin:
            plot_main_violin(
                paths.outdir / "main_summary.csv",
                paths.fig_dir / violin_pdf_name(selected_task, selected_sizes),
                selected_sizes, selected_task,
            )
        print(f"[*] Done. Results in {paths.outdir}/")
        return

    if args.rdpmc:
        setup_common()
        build_rdpmc_bench(selected_lto)
        counters = parse_csv_subset(args.rdpmc_counters, RDPMC_COUNTERS, "rdpmc-counters")
        scenarios = parse_csv_subset(args.rdpmc_scenarios, RDPMC_SCENARIOS, "rdpmc-scenarios")
        impls = parse_csv_subset(args.rdpmc_impls, RDPMC_IMPLS, "rdpmc-impls")
        run_rdpmc_sweep(args.NUM_ITER, paths, selected_sizes, scenarios, counters, impls)
        print(f"[*] Done. Results in {paths.outdir}/")
        return

    if args.paper:
        use_rt = _sudo_nopw_available()
        if not use_rt:
            print("[!] passwordless sudo not available; running without RT priority. "
                  "Configure NOPASSWD sudo for chrt to reduce jitter.")
        # Resolve task list. Default for --paper (when --task is omitted) is
        # the pair coalesce + exhaust. Otherwise honor --task (single or
        # comma-separated). --sizes is honored only when exactly one task is
        # selected; for multi-task runs we use each task's canonical sizes.
        if args.task is None:
            paper_tasks = ["coalesce", "exhaust"]
        else:
            paper_tasks = [t.strip() for t in args.task.split(",") if t.strip()]
            unknown = [t for t in paper_tasks if t not in TASKS]
            if unknown:
                raise SystemExit(f"ERROR: unknown task(s): {', '.join(unknown)}. "
                                 f"valid: {', '.join(TASKS)}")
        single_task = len(paper_tasks) == 1
        for t in paper_tasks:
            sizes_t = (parse_sizes_arg(args.sizes, t) if single_task
                       else list(TASK_SIZES[t]))
            df = measure_paper(args.NUM_ITER, args.runs, paths,
                               sizes_t, t, use_rt,
                               csv_name=f"paper_perf_{t}.csv")
            plot_paper_violin(df, paths.fig_dir, sizes_t, t, args.NUM_ITER)
            if t == "coalesce":
                plot_paper_grouped(df, paths.fig_dir, sizes_t, t, args.NUM_ITER)
        print(f"[*] Done. Results in {paths.outdir}/")
        return


if __name__ == "__main__":
    main()
