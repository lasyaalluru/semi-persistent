# Conformance performance validation inventory

This inventories the 13 Criterion targets registered in
`containers-conformance/Cargo.toml` for the final performance acceptance gate in
[semi-persistence-completion-goal.md](semi-persistence-completion-goal.md).
It is a source review, not benchmark results or a claim of parity.

## Comparison coverage

| Target | Existing comparison | Role in final validation |
|---|---|---|
| `tracked_vec_bench` | `prod` / `verus` mark churn for inline and parallel stores | Required matched legacy comparison, including all registered sizes |
| `nested_mark_bench` | `prod` / `verus` deep retained histories and ancestor restores | Required matched legacy comparison, including registered depth/restore cases |
| `retained_containers_bench` | `legacy` / `verified` container workloads | Required matched legacy comparison; inspect each pair's equivalent logical work |
| `eclasses_bench` | Retained former-production versus verified EClasses | Required aggregate-level legacy comparison |
| `bplus_cursor_bitset_bench` | `prod` / `verus` B+ tree, cursor and bit-set workloads | Required matched legacy comparison for affected containers |
| `three_tier_bench` | Verified tier/store/policy matrix plus production workload controls | Use comparable logical workload controls where valid; tier-specific operations also require the specified `d191c4a` checkpoint comparison |
| `diff_compress_bench` | Verified encoding/decoding strategies | Supplementary encoder measurements; no paired legacy implementation in this target |
| `two_stack_bench` | Verified compressing versus noncompressing configurations | Supplementary configuration measurements; not a legacy parity comparison |
| `reorder_bench` | Verified write-order versus sorted run encoding | Supplementary transform measurements; not a legacy parity comparison |
| `scheme_comparison_bench` | Compression schemes and encoded size | Supplementary time/space evidence; not a legacy parity comparison |
| `parallel_frame_bench` | Sequential versus Rayon execution of verified compression | Supplementary parallelism evidence; not legacy-versus-verified group restore |
| `eager_write_bench` | Local plain-vector, hash-map and eager-run experiments | Algorithm experiment, not a call to either container implementation |
| `normalize_bench` | Local tuple and packed-key sorting candidates | Algorithm experiment, not an end-to-end container comparison |

These classifications follow the benchmark bodies and module comments, not just
their filenames. Recheck them on the final revision and record all selected
case IDs and exclusions. Do not count experimental or single-implementation
targets as evidence that the verified implementation matches legacy speed.

## Open coverage and measurement obligations

- The three-tier benchmark explicitly describes its production arms as workload
  controls: legacy does not implement the same explicit tier policies. Compare
  equivalent logical operations where possible, and label representation or
  configuration differences. Direct rollover and Cold-survivor cases need the
  checkpoint comparison required by the completion goal; that comparison alone
  cannot establish legacy parity for an operation absent from legacy.
- The parallel-frame target measures encoder fan-out, not actual group restore.
  Audit final supported parallel/group paths for a representative executable
  workload; add matched coverage when an equivalent legacy operation exists.
  Report missing counterparts explicitly.
- The eager-write target does not cover the actual Vec set path. Actual mutation
  coverage must come from matched container workloads (and the applicable
  three-tier controls), not the local vector/hash-map experiment.
- Establish the repeatability calibration, noise tolerance and decision rule
  before evaluating final comparison results. Retain raw Criterion artifacts,
  repeated runs, confidence intervals, environment, commands and revisions.
- Run timing measurements without concurrent verifier/test load. Require each
  applicable paired case to pass; neither aggregate speedups nor an inconclusive
  test establish parity. Fix reproducible regressions and rerun affected gates.

No timings have been collected for this inventory. Benchmark parity remains open.
