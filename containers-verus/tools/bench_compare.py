#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""Compare Criterion baselines by the rule fixed in doc/tasks/final-performance-report.md.

Two modes:

  paired      verified-vs-legacy cases measured in the same binary; each case is
              a (group, verified id, legacy id) pair found by the pairing rules
              below, evaluated in every listed baseline (run A, run B, ...).
  checkpoint  the same benchmark id measured under two sets of baselines
              (final tree vs. checkpoint worktree), for cases without a legacy
              counterpart.

Ratio interval = [v_lo / l_hi, v_hi / l_lo] from Criterion's 95 % mean
confidence intervals.  Status: pass when every run's upper bound <= tau,
regression when every run's lower bound > tau, inconclusive otherwise.
"""
import argparse
import json
import os
import re
import sys

PAIR_RULES = [
    # (group regex, verified id regex, legacy id or callable(verified id) -> legacy id)
    (r".*", r"^verus$", "prod"),
    (r".*", r"^verified$", "legacy"),
    (r"^eclasses/", r"^verified$", "retained"),
    (r"^three_tier/write/", r"^(?!production$).*$", "production"),
    (r"^three_tier/mark$", r"^no_rollover_smt$", "no_rollover_production"),
    (r"^three_tier/restore$", r"^(trail|hot|cold)_one_frame$", "production_one_frame"),
    (r"^three_tier/end_to_end$", r"^(?!.*_production$).*$", lambda v: v + "_production"),
    (r"^three_tier_v1/", r"^(static_vecp|dyn_parallel)$", "production_vecp"),
    (r"^three_tier_v1/", r"^(dyn_inline|dyn_trail|static_veci|static_vect)$", "production_veci"),
]


def load_cases(root):
    """Return {full_id: {"group", "function", "value", "dir"}} for every benchmark."""
    cases = {}
    for dirpath, _dirs, files in os.walk(root):
        if "benchmark.json" not in files:
            continue
        # benchmark.json lives in each baseline directory; the case dir is its parent.
        with open(os.path.join(dirpath, "benchmark.json")) as fh:
            meta = json.load(fh)
        case_dir = os.path.dirname(dirpath)
        cases[meta["full_id"]] = {
            "group": meta["group_id"],
            "function": meta.get("function_id") or "",
            "value": meta.get("value_str") or "",
            "dir": case_dir,
        }
    return cases


def estimates(case, baseline):
    path = os.path.join(case["dir"], baseline, "estimates.json")
    if not os.path.exists(path):
        return None
    with open(path) as fh:
        est = json.load(fh)["mean"]
    return (
        est["confidence_interval"]["lower_bound"],
        est["point_estimate"],
        est["confidence_interval"]["upper_bound"],
    )


def ratio(v, l):
    return (v[0] / l[2], v[1] / l[1], v[2] / l[0])


def status(ratios, tau):
    if all(r[2] <= tau for r in ratios):
        return "pass"
    if all(r[0] > tau for r in ratios):
        return "regression"
    return "inconclusive"


def fmt_time(ns):
    for unit, div in (("s", 1e9), ("ms", 1e6), ("µs", 1e3)):
        if ns >= div:
            return f"{ns / div:.3f} {unit}"
    return f"{ns:.1f} ns"


def fmt_ratio(r):
    return f"{r[1]:.3f} [{r[0]:.3f}, {r[2]:.3f}]"


def pair_of(group, function, cases):
    for group_re, verified_re, legacy in PAIR_RULES:
        if re.match(group_re, group) and re.match(verified_re, function):
            legacy_id = legacy(function) if callable(legacy) else legacy
            if legacy_id == function:
                continue
            for full_id, c in cases.items():
                if c["group"] == group and c["function"] == legacy_id:
                    return full_id
    return None


def paired(args, cases):
    rows, unpaired = [], []
    for full_id in sorted(cases):
        c = cases[full_id]
        if args.filter and not re.search(args.filter, full_id):
            continue
        legacy_id = pair_of(c["group"], c["function"], cases)
        if legacy_id is None:
            unpaired.append(full_id)
            continue
        legacy_case = cases[legacy_id]
        if c["value"] and legacy_case["value"] != c["value"]:
            # value-parameterised groups: match the same parameter
            legacy_id = None
            for cand_id, cand in cases.items():
                if (
                    cand["group"] == c["group"]
                    and cand["function"] == legacy_case["function"]
                    and cand["value"] == c["value"]
                ):
                    legacy_id = cand_id
                    legacy_case = cand
            if legacy_id is None:
                unpaired.append(full_id)
                continue
        ratios, vs, ls, missing = [], [], [], False
        for b in args.runs:
            v, l = estimates(c, b), estimates(legacy_case, b)
            if v is None or l is None:
                missing = True
                break
            ratios.append(ratio(v, l))
            vs.append(v)
            ls.append(l)
        if missing:
            continue
        drift = max(ls[i][1] for i in range(len(ls))) / min(ls[i][1] for i in range(len(ls))) - 1.0
        rows.append(
            {
                "case": full_id,
                "legacy": legacy_id,
                "legacy_means": [l[1] for l in ls],
                "verified_means": [v[1] for v in vs],
                "ratios": ratios,
                "status": status(ratios, args.tau),
                "legacy_drift": drift,
            }
        )
    return rows, unpaired


def checkpoint(args, cases):
    rows = []
    for full_id in sorted(cases):
        c = cases[full_id]
        if args.filter and not re.search(args.filter, full_id):
            continue
        ratios, news, olds, missing = [], [], [], False
        for new_b, old_b in zip(args.runs, args.old):
            n, o = estimates(c, new_b), estimates(c, old_b)
            if n is None or o is None:
                missing = True
                break
            ratios.append(ratio(n, o))
            news.append(n)
            olds.append(o)
        if missing or not ratios:
            continue
        drift = max(o[1] for o in olds) / min(o[1] for o in olds) - 1.0
        rows.append(
            {
                "case": full_id,
                "legacy": "checkpoint",
                "legacy_means": [o[1] for o in olds],
                "verified_means": [n[1] for n in news],
                "ratios": ratios,
                "status": status(ratios, args.tau),
                "legacy_drift": drift,
            }
        )
    return rows


def fmt_speedup(legacy_mean, verified_mean):
    """Reference time over new time: above 1 the new side is faster."""
    return f"{legacy_mean / verified_mean:.2f}×"


def print_table(rows, runs, reference_label):
    # The convention for every number reported from this tool: the new side
    # against the reference, as a SPEEDUP (reference time ÷ new time, above 1 is
    # faster). The `Ratio` columns (new ÷ reference, with the interval the
    # verdict is taken from) stay because the pass/regression rule is stated on
    # them; read `Speedup` for direction and size.
    head = (
        f"| Case | {reference_label} mean ({'/'.join(runs)}) | Final mean ({'/'.join(runs)}) | Speedup "
        + " | Speedup ".join(runs)
        + " | Ratio "
        + " | Ratio ".join(runs)
        + " | Status |"
    )
    print(head)
    print("|" + "---|" * (4 + 2 * len(runs)))
    for r in rows:
        cells = [
            f"`{r['case']}`",
            " / ".join(fmt_time(m) for m in r["legacy_means"]),
            " / ".join(fmt_time(m) for m in r["verified_means"]),
        ]
        cells += [fmt_speedup(l, v) for l, v in zip(r["legacy_means"], r["verified_means"])]
        cells += [fmt_ratio(x) for x in r["ratios"]]
        cells.append(f"**{r['status']}**" if r["status"] != "pass" else "pass")
        print("| " + " | ".join(cells) + " |")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--criterion", default="target/criterion")
    ap.add_argument("--mode", choices=["paired", "checkpoint"], default="paired")
    ap.add_argument("--runs", nargs="+", required=True, help="baseline names (new side)")
    ap.add_argument("--old", nargs="*", default=[], help="checkpoint baseline names, one per run")
    ap.add_argument("--tau", type=float, default=1.08)
    ap.add_argument("--filter", default="", help="regex on the full benchmark id")
    ap.add_argument("--max-drift", type=float, default=0.08)
    args = ap.parse_args()
    cases = load_cases(args.criterion)
    if args.mode == "paired":
        rows, unpaired = paired(args, cases)
        print_table(rows, args.runs, "Legacy")
        if unpaired:
            print()
            print("Unpaired ids (no legacy counterpart in the same binary):")
            for u in unpaired:
                print(f"- `{u}`")
    else:
        if len(args.old) != len(args.runs):
            sys.exit("--old needs one checkpoint baseline per --runs entry")
        rows = checkpoint(args, cases)
        print_table(rows, args.runs, "Checkpoint")
    counts = {}
    for r in rows:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    noisy = [r["case"] for r in rows if r["legacy_drift"] > args.max_drift]
    print()
    print(f"Summary: {len(rows)} cases, " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    if len(args.runs) > 1:
        print(f"Reference-side same-code drift above {args.max_drift:.0%}: {len(noisy)} case(s)")
        for n in noisy:
            print(f"- `{n}`")


if __name__ == "__main__":
    main()
