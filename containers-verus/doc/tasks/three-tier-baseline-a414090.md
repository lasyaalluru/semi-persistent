# Three-tier execution baseline — a414090

Recorded on 2026-09-13 before runtime changes for
`three-tier-frame-architecture-goal.md`.

## Environment

```text
commit: a414090e17df4e61622cafa83088e9377bcd1b81
host: Apple M4 Pro, 48 GiB
OS: Darwin 25.6.0 arm64
rustc: 1.97.1 (8bab26f4f 2026-07-14)
cargo: 1.97.1 (c980f4866 2026-06-30)
Verus: 0.2026.08.02.b677dd5
SEMPER_COMPRESS: unset
SEMPER_DIFF: unset
```

The only working-tree file before execution changes was the untracked controlling
goal document. Production `containers/` had no changes.

## Correctness baseline

All commands passed:

```bash
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo test -p semi-persistent-containers-verus
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo test -p semi-persistent-containers-verus --features "compat-all,literal-types"
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo test -p containers-conformance
PROPTEST_CASES=1024 env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo test -p containers-conformance --release
PROPTEST_CASES=1024 env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo test -p containers-conformance --release --test trail_semi_persistence
```

The previously recorded full Verus baseline also passed:

```text
verification results:: 2198 verified, 0 errors
```

## Saved Criterion baseline

Criterion data was saved under `pre_three_tier_a414090` with:

```bash
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench tracked_vec_bench -- --save-baseline pre_three_tier_a414090
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench retained_containers_bench -- --save-baseline pre_three_tier_a414090
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench two_stack_bench -- --save-baseline pre_three_tier_a414090
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench normalize_bench -- --save-baseline pre_three_tier_a414090
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench eclasses_bench -- --save-baseline pre_three_tier_a414090
```

### Shallow mark churn

Criterion point estimates (middle estimate):

| workload | production | verified |
|---|---:|---:|
| VecI, n=1,000 | 3.908 us | 4.166 us |
| VecI, n=100,000 | 4.474 us | 4.538 us |
| VecI, n=1,000,000 | 9.317 us | 10.253 us |
| VecP, n=1,000 | 4.548 us | 3.884 us |
| VecP, n=1,000,000 | 771.87 us | 815.96 us |

### End-to-end retained container controls

| workload | production (`legacy`) | verified |
|---|---:|---:|
| `vec/try_extend` | 127.03 us | 72.64 us |
| `vec/mark_set_restore` | 199.03 us | 135.80 us |
| `vec/restore_replay` | 209.40 us | 144.78 us |
| `vec/push_pop_untracked` | 134.53 us | 81.87 us |

### Current compression helpers

| workload | estimate |
|---|---:|
| two-stack mark churn, no compression | 11.00 us |
| two-stack mark churn, value dictionary | 120.99 us |
| two-stack mark churn, index runs | 75.58 us |
| packed unique normalize, 32 entries | 73.88 ns |
| packed unique normalize, 256 entries | 1.128 us |
| packed unique normalize, 4,096 entries | 24.08 us |
| packed unique normalize, 65,536 entries | 584.30 us |
| packed duplicate-heavy normalize, 32 entries | 78.41 ns |
| packed duplicate-heavy normalize, 256 entries | 972.15 ns |
| packed duplicate-heavy normalize, 4,096 entries | 23.49 us |
| packed duplicate-heavy normalize, 65,536 entries | 540.54 us |

The current two-stack 400-frame footprint report was:

| configuration | hot bytes | cold bytes | total bytes |
|---|---:|---:|---:|
| none | 65,536 | 0 | 65,536 |
| value dictionary | 32,768 | 63,168 | 95,936 |
| index runs | 32,768 | 46,912 | 79,680 |

### Equality-saturation aggregate control

| workload | production (`retained`) | verified |
|---|---:|---:|
| merge cascade | 83.58 us | 77.57 us |
| find sweep | 147.76 us | 155.24 us |
| mark/merge/restore | 9.110 us | 8.641 us |

## Comparison rule

Post-change measurements must use `--baseline pre_three_tier_a414090` on this
same host. Deltas inside the established 5–8 percent same-code noise band are
inconclusive. End-to-end profile rows and same-process production controls take
precedence over helper microbenchmarks.
