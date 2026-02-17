import pandas as pd
import numpy as np
import re
from pathlib import Path

DIR = Path("")

orig = DIR/"perf_original.csv"
ver  = DIR/"perf_verified.csv"
meta = DIR/"meta.log"

########################################
# load perf csv
########################################

def load_perf(path):
    rows = []
    with open(path) as f:
        for line in f:
            parts = line.strip().split(",")
            if len(parts) < 3:
                continue
            try:
                val = float(parts[0])
                ev  = parts[2]
                rows.append((val, ev))
            except:
                pass
    df = pd.DataFrame(rows, columns=["value","event"])
    return df

def reshape(df):
    out = {}
    for ev in df.event.unique():
        out[ev] = df[df.event==ev].value.values
    return out

orig = reshape(load_perf(orig))
ver  = reshape(load_perf(ver))

########################################
# ratio
########################################

def ratio(ev):
    a = orig[ev]
    b = ver[ev]
    n = min(len(a), len(b))
    r = b[:n] / a[:n]
    return r

instr_ratio = ratio("instructions")
cycle_ratio = ratio("cycles")

########################################
# IQR除去
########################################

def iqr_filter(x):
    q1 = np.percentile(x,25)
    q3 = np.percentile(x,75)
    iqr = q3-q1
    return x[(x>q1-1.5*iqr)&(x<q3+1.5*iqr)]

instr_ratio = iqr_filter(instr_ratio)
cycle_ratio = iqr_filter(cycle_ratio)

########################################
# 統計
########################################

def stats(x):
    med = np.median(x)
    lo  = np.percentile(x,2.5)
    hi  = np.percentile(x,97.5)
    return med, lo, hi

im, il, ih = stats(instr_ratio)
cm, cl, ch = stats(cycle_ratio)

########################################
# LaTeX table 出力
########################################

print(r"""
\begin{table}[t]
\centering
\begin{tabular}{lcc}
\hline
Metric & Median ratio & 95\% CI \\
\hline
Instructions & %.3f & [%.3f, %.3f] \\
Cycles & %.3f & [%.3f, %.3f] \\
\hline
\end{tabular}
\caption{Performance overhead of verified allocator relative to original rlsf.}
\end{table}
""" % (im, il, ih, cm, cl, ch))

########################################
# pgfplots 用データ
########################################

with open("instr_ratio.dat","w") as f:
    for x in instr_ratio:
        f.write(f"{x}\n")

with open("cycle_ratio.dat","w") as f:
    for x in cycle_ratio:
        f.write(f"{x}\n")
