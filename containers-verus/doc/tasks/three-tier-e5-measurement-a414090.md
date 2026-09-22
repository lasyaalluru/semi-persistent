# Three-tier E5 measurement — a414090 working tree

Recorded on 2026-09-13 after the E1-E4 three-tier runtime was complete and before any E5 optimization.

## Scope and environment

```text
base commit: a414090e17df4e61622cafa83088e9377bcd1b81
working tree: dirty with the completed E1-E4 runtime, E4 tests, this E5 benchmark, and task records
host: Apple M4 Pro, 48 GiB
OS: Darwin 25.6.0 arm64
rustc: 1.97.1 (8bab26f4f 2026-07-14)
cargo: 1.97.1 (c980f4866 2026-06-30)
SEMPER_COMPRESS: unset
SEMPER_DIFF: unset
historical Criterion baseline: pre_three_tier_a414090
```

Production `containers/` was not changed. No proof work or optimization was started. The new benchmark IDs did not exist at the baseline revision, so their same-day Criterion `change` lines compare repeated filtered/full E5 runs and are not historical deltas. Historical claims below use only unchanged IDs with `--baseline pre_three_tier_a414090`; new IDs use same-process production controls where semantics align.

## Commands

```bash
cargo fmt --all
cargo check -p containers-conformance --benches

env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench three_tier_bench -- 'three_tier/mark'
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench three_tier_bench -- 'three_tier/restore'
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench three_tier_bench -- 'three_tier/end_to_end'
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench three_tier_bench

env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench tracked_vec_bench -- --baseline pre_three_tier_a414090
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench retained_containers_bench -- --baseline pre_three_tier_a414090
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench two_stack_bench -- --baseline pre_three_tier_a414090
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench normalize_bench -- --baseline pre_three_tier_a414090
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench eclasses_bench -- --baseline pre_three_tier_a414090 'mark_merge_restore'
```

All commands passed. `three_tier_bench` uses 10 samples, 250 ms warm-up, and 500 ms measurement per row; retained suites keep their existing Criterion settings. Point estimates below are Criterion's middle estimates; bracketed ranges are its reported confidence intervals.

## New three-tier measurements

Deterministic fixtures use 8,192 live `u64` values with `u32` indices. Micro fixtures perform 512 writes; conversion fixtures use eight closed frames; end-to-end nested traces use 24 frames × 32 writes, and SMT backtracking uses 64 mark/write/restore cycles.

### Writes

| duplicate density | profile/control | point estimate | confidence interval |
|---|---|---:|---:|
| low | SMT trail | 1.0039 us | [0.99690, 1.0082] us |
| low | adaptive trail | 0.98886 us | [0.98162, 0.99366] us |
| low | restore optimized | 1.4111 us | [1.3733, 1.4448] us |
| low | buffered unique | 1.3638 us | [1.3571, 1.3704] us |
| low | production control | 1.2597 us | [1.2538, 1.2662] us |
| high | SMT trail | 0.99325 us | [0.98713, 0.99808] us |
| high | adaptive trail | 0.99161 us | [0.98804, 0.99490] us |
| high | restore optimized | 0.74361 us | [0.74179, 0.74477] us |
| high | buffered unique | 0.74617 us | [0.74410, 0.74769] us |
| high | production control | 0.55010 us | [0.52351, 0.58637] us |

### Mark, restore, conversion, promotion, and adaptive decision

| group | row | point estimate | confidence interval |
|---|---|---:|---:|
| mark | no rollover, SMT | 16.991 ns | [16.764, 17.267] ns |
| mark | no rollover, production | 16.564 ns | [16.430, 16.818] ns |
| mark | trail -> hot | 1.0221 us | [1.0076, 1.0535] us |
| mark | hot -> cold | 3.2006 us | [3.1900, 3.2148] us |
| restore | trail, one frame | 339.79 ns | [331.62, 343.47] ns |
| restore | hot, one frame | 363.66 ns | [355.16, 367.84] ns |
| restore | cold, one frame/direct run | 99.814 ns | [94.988, 101.97] ns |
| restore | all tiers/deep | 407.89 ns | [392.71, 414.91] ns |
| restore | production, one frame | 344.57 ns | [340.69, 346.72] ns |
| conversion | trail -> hot dedupe, 8 frames | 7.5563 us | [7.3793, 7.7916] us |
| conversion | hot -> cold runs, 8 frames | 24.709 us | [24.042, 25.328] us |
| promotion | cold survivor -> write -> restore | 3.9513 us | [3.9051, 4.0308] us |
| adaptive | low duplicates, no conversion | 10.018 us | [9.7922, 10.524] us |
| adaptive | high duplicates, conversion | 1.8601 us | [1.8562, 1.8659] us |

### End to end

| workload/profile | point estimate | confidence interval | same-process control interpretation |
|---|---:|---:|---|
| `smt_backtrack` | 11.191 us | [11.114, 11.308] us | production 9.9936 us [9.9632, 10.028], SMT is 12.0% slower by point ratio |
| `eqsat_retained` (adaptive) | 13.847 us | [13.733, 13.986] us | production 8.0096 us [7.9767, 8.0353], adaptive is 72.9% slower by point ratio |
| `restore_optimized` | 10.339 us | [10.320, 10.362] us | policy-to-policy comparison only |
| `buffered_unique` | 8.8856 us | [8.8519, 8.9181] us | fastest verified nested profile; 10.9% slower than production by point ratio |

The production arms are workload controls, not tier-policy equivalents. For this duplicate-heavy nested fixture, buffered unique beats restore optimized by 14.1%, SMT by 20.6%, and adaptive by 35.8% using point-estimate ratios. Cold direct restore is much faster than scalar trail/hot restore, but hot-to-cold construction is the most expensive conversion row.

## Tier occupancy and retained bytes

These diagnostics execute outside Criterion timed loops. `tracking_bytes` is the runtime's exact capacity-based aggregate over all history pools/stacks; `total_bytes` adds the Vec object and live store. The per-tier columns are exact logical retained bytes (used entries plus frame/run headers); they deliberately differ from capacity accounting.

| fixture | tier stats | trail logical | hot logical | cold logical | tracking bytes | total bytes |
|---|---|---:|---:|---:|---:|---:|
| restore trail | trail 1 frame/512 entries | 8,216 | 0 | 0 | 8,288 | 75,152 |
| restore hot | hot 1 frame/512 entries | 0 | 8,216 | 0 | 8,288 | 75,152 |
| restore cold | hot 1 empty frame; cold 1 frame/1 run/512 values | 0 | 24 | 4,144 | 12,576 | 79,440 |
| restore all | trail 2/512; hot 1/64; cold 4 frames/4 runs/256 values | 8,240 | 1,048 | 2,240 | 20,864 | 87,728 |
| after promotion | hot 1/512; cold 1 frame/1 run/512 values | 0 | 8,216 | 4,144 | 41,440 | 108,304 |

Conversion diagnostics:

| conversion | capacity before -> after | logical tier bytes before -> after (trail, hot, cold) | capacity reclaimed | occupancy after |
|---|---:|---:|---:|---|
| trail -> hot, duplicate-heavy | 65,920 -> 70,208 B | (65,752, 0, 0) -> (24, 4,288, 0) B | 0 B | trail 1 empty; hot 8 frames/256 entries |
| hot -> cold, contiguous | 65,920 -> 99,072 B | (0, 65,752, 0) -> (0, 24, 33,152) B | 0 B | hot 1 empty; cold 8 frames/8 runs/4,096 values |

The zero reclaimed capacity is expected under `ReclaimPolicy::RetainCapacity`: logical trail occupancy falls from 4,096 entries to 256 hot entries, but allocations are retained for reuse and the destination pool is allocated. Scratch and operation-peak bytes cannot be recovered from the current public APIs, so this record does not fabricate scratch estimates. Additive operation-peak diagnostics or measurement-only allocation instrumentation is an E5 optimization-campaign prerequisite if those peaks are needed.

## Historical baseline comparisons

The comparison rule treats 5-8% as same-code noise. Small statistically significant changes inside that band are inconclusive. The tables give current point estimate and Criterion's middle percentage change from `pre_three_tier_a414090`.

### `tracked_vec_bench`

| row | current | change |
|---|---:|---:|
| VecI production, 1K | 3.8352 us | -1.4348% |
| VecI verified, 1K | 5.5995 us | +33.715% |
| VecI production, 100K | 4.3394 us | -3.3804% |
| VecI verified, 100K | 6.6032 us | +44.555% |
| VecI production, 1M | 9.4952 us | -7.8977% |
| VecI verified, 1M | 13.904 us | +39.063% |
| VecP production, 1K | 4.5806 us | +0.2198% |
| VecP verified, 1K | 5.3317 us | +36.851% |
| VecP production, 1M | 779.74 us | +1.0704% |
| VecP verified, 1M | 751.28 us | -7.9275% |

The four shallow verified regressions are material and their intervals are wholly outside the noise band. The 1M VecP improvement touches the noise boundary and is not treated as an optimization result.

### `retained_containers_bench`

| row | current | change |
|---|---:|---:|
| Vec try-extend production | 133.41 us | +3.2336% |
| Vec try-extend verified | 62.901 us | -15.188% |
| Vec mark/set/restore production | 217.01 us | +9.1194% |
| Vec mark/set/restore verified | 169.54 us | +23.921% |
| Vec restore replay production | 209.34 us | -0.0265% |
| Vec restore replay verified | 222.39 us | +53.601% |
| Vec push/pop production | 135.95 us | -0.2222% |
| Vec push/pop verified | 78.469 us | -5.1159% |
| list append/iterate production | 138.99 us | +0.2318% |
| list append/iterate verified | 137.44 us | -1.6321% |
| list splice production | 16.125 us | -0.8285% |
| list splice verified | 14.978 us | +0.8492% |
| class-ring splice production | 4.9656 us | -1.3801% |
| class-ring splice verified | 4.1282 us | -3.6755% |
| class-ring walk production | 59.952 us | -0.5032% |
| class-ring walk verified | 59.849 us | -0.2763% |
| class-ring merge/restore production | 57.330 us | -0.3444% |
| class-ring merge/restore verified | 78.293 us | +121.26% |
| map intern production | 873.36 us | -0.8092% |
| map intern verified | 593.05 us | -0.3783% |
| map string production | 1.2378 ms | -2.1361% |
| map string verified | 1.2317 ms | -2.2993% |
| map composite production | 924.34 us | -0.2566% |
| map composite verified | 923.21 us | +0.3930% |
| sparse-set churn production | 219.75 us | -0.5696% |
| sparse-set churn verified | 3.4317 ms | +1652.6% |
| append-only log production | 82.549 us | -1.8645% |
| append-only log verified | 81.149 us | -2.0755% |

The production mark/set/restore row also moved +9.1%, so that individual run includes some control drift; however, the verified delta is substantially larger. Production controls for restore replay, class-ring merge/restore, and sparse-set churn were flat, making those verified regressions unambiguous.

### `two_stack_bench`

| row | current | change |
|---|---:|---:|
| no compression | 11.002 us | -0.3481% |
| value dictionary | 117.83 us | -0.4210% |
| index runs | 76.954 us | +1.6079% |

The deterministic footprints were unchanged from the baseline record: 65,536 B total for none, 95,936 B for value dictionary, and 79,680 B for index runs. No row moved outside noise.

### `normalize_bench`

| shape | implementation | entries | current | change |
|---|---|---:|---:|---:|
| unique | tuple unstable | 32 | 87.211 ns | +1.8939% |
| unique | tuple stable/fold | 32 | 103.59 ns | +0.6578% |
| unique | packed keys | 32 | 74.804 ns | +2.1616% |
| unique | tuple unstable | 256 | 1.1082 us | -1.1096% |
| unique | tuple stable/fold | 256 | 1.2896 us | -0.5131% |
| unique | packed keys | 256 | 1.1269 us | +0.6228% |
| unique | tuple unstable | 4,096 | 26.155 us | +1.8754% |
| unique | tuple stable/fold | 4,096 | 31.933 us | -0.3986% |
| unique | packed keys | 4,096 | 23.958 us | -0.3490% |
| unique | tuple unstable | 65,536 | 577.85 us | -2.7137% |
| unique | tuple stable/fold | 65,536 | 895.19 us | -0.5933% |
| unique | packed keys | 65,536 | 573.11 us | +2.5787% |
| duplicate x4 | tuple unstable | 32 | 85.190 ns | -0.4973% |
| duplicate x4 | tuple stable/fold | 32 | 99.347 ns | +0.9906% |
| duplicate x4 | packed keys | 32 | 77.304 ns | -1.5586% |
| duplicate x4 | tuple unstable | 256 | 1.1779 us | -0.2968% |
| duplicate x4 | tuple stable/fold | 256 | 1.2786 us | +0.4940% |
| duplicate x4 | packed keys | 256 | 973.84 ns | +0.4922% |
| duplicate x4 | tuple unstable | 4,096 | 25.762 us | -0.5177% |
| duplicate x4 | tuple stable/fold | 4,096 | 31.250 us | +0.4070% |
| duplicate x4 | packed keys | 4,096 | 23.247 us | -1.4610% |
| duplicate x4 | tuple unstable | 65,536 | 573.26 us | -1.5727% |
| duplicate x4 | tuple stable/fold | 65,536 | 818.79 us | -0.0219% |
| duplicate x4 | packed keys | 65,536 | 519.18 us | -8.0758% |

No normalize row regressed outside noise. The largest movement was an improvement in duplicate-heavy packed keys at 65,536 entries: -8.0758%, interval [-9.5428%, -6.5901%].

### `eclasses_bench` focused mark/merge/restore

| row | current | change | change interval |
|---|---:|---:|---:|
| retained control | 9.6276 us | +4.7504% | [+3.8730%, +5.5694%] |
| verified | 10.405 us | +19.828% | [+19.217%, +20.430%] |

The retained control remains inside the established noise range while the verified interval is wholly material.

## Material regressions

| suite/row | point change | change interval |
|---|---:|---:|
| tracked VecI verified, 1K | +33.715% | [+32.990%, +34.500%] |
| tracked VecI verified, 100K | +44.555% | [+43.364%, +45.719%] |
| tracked VecI verified, 1M | +39.063% | [+36.426%, +42.119%] |
| tracked VecP verified, 1K | +36.851% | [+36.177%, +37.488%] |
| retained Vec mark/set/restore, production control | +9.1194% | [+7.9013%, +10.428%] |
| retained Vec mark/set/restore, verified | +23.921% | [+22.371%, +25.585%] |
| retained Vec restore replay, verified | +53.601% | [+51.984%, +55.230%] |
| retained class-ring merge/restore, verified | +121.26% | [+115.78%, +126.17%] |
| retained sparse-set churn, verified | +1652.6% | [+1643.7%, +1661.0%] |
| eclasses mark/merge/restore, verified | +19.828% | [+19.217%, +20.430%] |

## Evidence-led optimization candidates (not implemented)

1. Profile `runtime_capture` and the extra Vec-owned mode/tier dispatch on shallow unique writes. The 34-45% shallow-churn regressions and flat production controls make this the first candidate.
2. Isolate scalar replay and post-restore promotion costs. Verified restore replay is +53.6%, class-ring merge/restore +121%, and eclasses mark/merge/restore +19.8%, while direct cold restore is only 99.8 ns in the controlled fixture.
3. Replace the adaptive low-duplicate `Vec::contains` uniqueness scan with reusable indexed scratch or an early-decision algorithm. The no-convert decision costs 10.018 us versus 1.860 us for the duplicate-heavy convert path.
4. Reuse dedupe/run-construction scratch and destination pools. Eight-frame trail dedupe costs 7.556 us; run construction costs 24.709 us and retained-capacity conversion increases aggregate allocated bytes.
5. Investigate the sparse-set regression separately before attributing all of it to three-tier Vec; its flat production control and 16.5x verified regression make it a blocking cross-profile signal.
6. Add additive per-pool retained-capacity and operation-peak scratch diagnostics before optimizing memory. Current public diagnostics are sufficient for aggregate retained bytes and occupancy, not peak attribution.

No candidate is accepted yet. E5 is **MEASURED**, not optimized, and E6 remains **NOT LOCKED**.


## E5 hot-path optimization pass — 2026-09-14

This pass used the two source analyses recorded for the E5 stage, preserved the meanings of the trail/hot/cold representations, preserved every explicit capture and retention policy, and did not change legacy constructor behavior. Production `containers/` and proof files were not modified, no proof work was started, and no commit was created. Because runtime behavior was unchanged, no regression test was added; the existing focused runtime and differential suites cover the affected pop/re-entry and restore boundaries.

### Accepted and rejected optimizations

1. **Accepted — first-capture write and pop/re-entry fast paths.** `runtime_capture` now reads the old value only in Trail mode or in the non-unique fallback; unique-capable stores perform their own first-capture read. The hot header end is updated only when capture appended an entry. `runtime_push` restores the capture bit directly for a first-capture-wins unique store after re-entering a popped marked-range slot, instead of linearly scanning the open frame. Tiny runtime push/pop/set helpers are forced inline. The first retained rerun reduced sparse-set churn from **+1652.6% to +19.229%** and class-ring merge/restore from **+121.26% to +42.018%** versus `pre_three_tier_a414090`; the sparse-set complexity regression was therefore removed.
2. **Accepted — backend-aware restore clear and no-op automatic-policy bypass.** A runtime capability identifies stores whose replay writes clear capture state. InlineStore now skips its redundant pre-replay tag-clear pass; replay itself writes tag-clear representations. `runtime_begin_restore` passes an empty slice to stores that do not read replay indices. Mark skips automatic migration calls when the active policy cannot migrate the selected ingress tier. This reduced class-ring to **+18.931%**, eclasses to **+8.555%**, and the three VecI rows to **+17.447% / +14.793% / +12.806%** in that iteration.
3. **Accepted — contiguous suffix replay and depth-zero cleanup.** Discarded trail and hot frame suffixes now use the existing backend `restore_overlay` operation once per contiguous suffix, preserving newest-to-oldest frame order and right-to-left trail order. A restore to depth zero resets the cached saved length directly instead of entering survivor-promotion and empty capture-state reconstruction. This moved retained restore replay from **+51.668% to -2.6417%**, class-ring from **+18.931% to +5.2444%**, and eclasses from **+8.555% to +6.1550%** in the next rerun.
4. **Accepted — remove redundant depth sums from mutation fast paths.** `active_saved_len == I::min()` is already the established no-history sentinel and is restored at depth zero. Capture, pop, and push re-entry now use the saved-length bound directly instead of summing all three stack lengths before the same bound check. The final rerun brought every VecI row, sparse-set churn, class-ring, restore replay, and eclasses into the established 5–8% noise band.
5. **Rejected — remove the two retired compatibility helper calls from `mark`.** Both helpers have empty bodies and optimize away. Removing the calls only created dead-code warnings and supplied no credible machine-code saving, so the calls were retained and this was not counted as an optimization result.
6. **Deferred, not attempted — omit per-capture open-header `end` maintenance.** This remains a plausible write-path saving, but the current runtime and specification expose `end` to pending-index queries and frame invariants. Changing it requires a systematic derived-open-end contract rather than a benchmark-local edit, so it was rejected for this execution-only stage.
7. **Deferred, not attempted — skip ParallelStore bitmap zeroing on a known-clear first mark.** This is the leading VecP/1K candidate, but doing it safely requires an explicit clear/materialized capture-state contract. Adding hidden state or weakening the store protocol is not a minimal E5 edit and was left for the remaining-bottleneck list.

### Validation

```text
cargo fmt --all
cargo check -p containers-conformance --benches
cargo test -p semi-persistent-containers-verus --test three_tier_runtime
  13 passed, 0 failed
cargo test -p containers-conformance --test three_tier_policy_matrix
  3 passed, 0 failed
```

Final Criterion commands, with `SEMPER_COMPRESS` and `SEMPER_DIFF` unset:

```bash
cargo bench -p containers-conformance --bench tracked_vec_bench -- --baseline pre_three_tier_a414090
cargo bench -p containers-conformance --bench retained_containers_bench -- --baseline pre_three_tier_a414090 'vec/mark_set_restore|vec/restore_replay|class_ring/merge_restore|sparse_set/churn'
cargo bench -p containers-conformance --bench eclasses_bench -- --baseline pre_three_tier_a414090 'mark_merge_restore'
```

### Exact final before/after deltas

`before` is the pre-optimization E5 point estimate and middle change already recorded above. `after` is the final pass point estimate and Criterion middle change against the same `pre_three_tier_a414090` baseline. `delta` is the change in baseline-relative percentage points; `point shift` compares the two measured point estimates directly.

| requested verified row | before | after (final interval) | delta | point shift |
|---|---:|---:|---:|---:|
| tracked VecI, 1K | 5.5995 us, +33.715% | 4.4443 us, +6.0904% [+5.4845%, +6.6526%] | -27.6246 pp | -20.6304% |
| tracked VecI, 100K | 6.6032 us, +44.555% | 4.7672 us, +5.7014% [+5.2213%, +6.2136%] | -38.8536 pp | -27.8047% |
| tracked VecI, 1M | 13.904 us, +39.063% | 10.671 us, +3.4000% [+1.7471%, +5.0308%] | -35.6630 pp | -23.2523% |
| tracked VecP, 1K | 5.3317 us, +36.851% | 4.4791 us, +15.484% [+14.803%, +16.104%] | -21.3670 pp | -15.9911% |
| tracked VecP, 1M | 751.28 us, -7.9275% | 766.81 us, -6.0239% [-7.1982%, -4.7332%] | +1.9036 pp | +2.0671% |
| retained vec mark/set/restore | 169.54 us, +23.921% | 166.90 us, +21.528% [+20.017%, +23.018%] | -2.3930 pp | -1.5572% |
| retained vec restore replay | 222.39 us, +53.601% | 138.22 us, -4.5344% [-5.7503%, -3.3393%] | -58.1354 pp | -37.8479% |
| class-ring merge/restore | 78.293 us, +121.26% | 35.416 us, -3.6554% [-4.0209%, -3.2584%] | -124.9154 pp | -54.7648% |
| sparse-set churn | 3.4317 ms, +1652.6% | 200.12 us, +1.0635% [+0.3810%, +1.7678%] | -1651.5365 pp | -94.1685% |
| eclasses mark/merge/restore | 10.405 us, +19.828% | 8.7999 us, +1.2138% [+0.7404%, +1.6858%] | -18.6142 pp | -15.4262% |

Final same-process controls were: tracked VecI **-1.2100% / -3.4518% / -13.026%** at 1K/100K/1M, tracked VecP **-1.1072% / -3.2141%** at 1K/1M, retained vec mark/set/restore **+8.3078%** [+7.3638%, +9.2402%], restore replay **-1.5700%**, class-ring **-0.6472%**, sparse-set **-2.8429%**, and retained eclasses **+2.7038%**. The 1M VecI control drifted beyond the normal band, so its final verified +3.4000% is treated as noise rather than an improvement claim. The VecP/1M before/after movement is also inconclusive inside the established band.

### Remaining bottlenecks

- **Tracked VecP/1K: +15.484%.** At shallow size, ParallelStore still pays bitmap materialization/reset at frame boundaries plus first-capture bitmap traffic. The leading safe follow-up is a store contract for “capture state is already clear but may need materialization,” allowing depth-zero marks to grow words without re-zeroing them. This was intentionally not approximated with hidden state.
- **Retained vec mark/set/restore: +21.528%, control +8.3078%.** The verified point estimate improved only 1.56% from the E5 pre-optimization run. Its remaining excess is formation-side: capture-mode/store-capability dispatch, first-capture bit tests, open-header `end` stores for every unique capture, and initial frame/pool allocation. Restore replay itself is no longer a bottleneck.
- **Open-header maintenance.** Removing the per-first-capture `frame.end` store requires changing all open-frame readers and executable/spec invariants to derive the effective end from the active pool length; it is not safe as an isolated runtime edit.
- **Conversion-only costs remain outside these legacy default rows.** Adaptive low-duplicate scans, scratch allocation, per-frame `to_vec`, and front `drain` remain known hotspots, but none executes in the requested default one-frame rows and they were not changed in this pass.

The accepted runtime is therefore materially improved without a policy remap: eight of the ten requested verified rows are now inside the established noise band, while the two remaining material rows are isolated to ParallelStore shallow frame setup and unique-capture formation overhead. E6 remains **NOT LOCKED** pending a decision on those bottlenecks and the later proof phase.


## E5 second measurement-driven optimization pass — 2026-09-14

This pass was limited to the two remaining out-of-band rows and retained the existing trail/hot/cold meanings, explicit capture and retention policies, runtime checks, and token behavior. It did not modify `containers/` or proof files and did not create a commit.

### Accepted change

1. **Accepted — derive the open ingress end from its pool and seal once.** `runtime_capture` no longer rewrites `TrailFrame.end` or `HotFrame.end` after every appended capture. The one open ingress frame now uses the active pool length as its effective end; `runtime_push_frame` still seals the prior frame exactly once before opening the next frame. Restore replay derives the newest open suffix end from the active pool length, and `pending_restore_indices` does the same for the active trail or hot frame while continuing to use stored ends for closed frames. No stack meaning changed: closed frame headers remain fixed ranges, and only the already-special open frame has a derived upper bound. A focused test now checks open-frame pending indices in both Trail and FirstCaptureWins modes, including Trail duplicates.

The final tracked-vector run moved VecP/1K from **+15.484%** to **+7.3114%** `[+6.7479%, +7.8763%]`, with a **+0.0065%** production control, bringing the target inside the established 5–8% noise band. VecP/1M did not regress: it measured **-9.7026%** `[-10.504%, -8.8293%]`, with a **-3.4455%** control. The same removal also improved the exact unchanged-ID guard rows shown below.

### Attempted and rejected changes

1. **Rejected — already-clear Parallel bitmap materialization fast path.** The existing `prepare_mark` precondition proves that an empty previous-diff slice implies clear capture state, so a prototype preserved already-zero words and materialized only missing coverage. It materially improved tracked VecP/1K to **+2.5812%** `[+1.9613%, +3.1385%]` and VecP/1M to **-48.418%** `[-48.849%, -47.965%]`. However, the same build regressed retained `vec/mark_set_restore` to **+44.382%** `[+41.041%, +47.592%]` with only **+1.2569%** control drift. Replacing incremental word growth with one bulk `resize` still measured **+35.765%** `[+33.022%, +38.511%]` with **-0.9302%** control, and routing a fresh unmaterialized bitmap through the original clear/bulk-resize path still measured **+41.006%** `[+37.809%, +43.905%]` with **-5.8891%** control. The prototype was fully reverted; `capture_bits.rs` and `parallel_store.rs` have no final diff. This is the concrete tradeoff: eliminating redundant steady-state clears helps mark churn strongly, but the tested protocol/code-generation variants materially hurt the retained formation row, so no safe combined improvement was accepted.
2. **Rejected — initial preallocation.** No unconditional header or value-pool reserve was added. A header reserve changes empty and retained-capacity diagnostics, while a useful value-pool reserve has no safe workload-independent bound and would change the practical retention policy. The bitmap experiment also demonstrated that incremental first materialization is unacceptable; the original one-shot resize remains the fresh-store path.
3. **Rejected — remove remaining mode/capability/depth checks.** The mode/capability branches support explicit Trail mode on unique stores and FirstCaptureWins on non-unique stores; collapsing them would weaken separate stack meanings or explicit policy behavior. The depth, tracking, and index-capacity checks enforce runtime and token limits. No redundant check with a safe measurable removal remained after the prior cached-saved-length pass.

### Final measurements against `pre_three_tier_a414090`

The final commands were the same unchanged-ID commands used by the first pass, with `SEMPER_COMPRESS` and `SEMPER_DIFF` unset.

| row | final point estimate | baseline-relative interval | same-process control |
|---|---:|---:|---:|
| tracked VecI, 1K | 3.8903 us | -7.1727% [-7.6018%, -6.7759%] | -1.3685% |
| tracked VecI, 100K | 4.2373 us | -6.4161% [-6.8731%, -5.9730%] | -1.8498% |
| tracked VecI, 1M | 9.4377 us | -6.6344% [-8.3975%, -4.7554%] | -11.500% |
| tracked VecP, 1K | 4.1577 us | +7.3114% [+6.7479%, +7.8763%] | +0.0065% |
| tracked VecP, 1M | 736.79 us | -9.7026% [-10.504%, -8.8293%] | -3.4455% |
| retained vec mark/set/restore, full filtered run | 184.86 us | +29.567% [+26.004%, +33.605%] | +5.4179% |
| retained vec restore replay | 140.09 us | -3.2438% [-4.5111%, -1.9294%] | -1.7599% |
| class-ring merge/restore | 31.132 us | -14.925% [-15.303%, -14.485%] | -0.7973% |
| sparse-set churn | 181.25 us | -6.8247% [-7.3893%, -6.2708%] | +0.8490% |
| eclasses mark/merge/restore | 8.2049 us | -5.1767% [-5.7790%, -4.5921%] | +2.0615% |

The retained formation row was not stable enough for an improvement claim. On the identical accepted A-only binary, an immediately preceding isolated unchanged-ID run measured **146.14 us, +4.0962%** `[+2.1445%, +6.3270%]` while its production control was **+7.1257%**; the subsequent full filtered command measured **184.86 us, +29.567%** with **+5.4179%** control. That 26.5% same-code point-estimate split is much larger than the established band and reverses the classification without a source change. The pass therefore records the conservative full-command result and treats retained mark/set/restore as unresolved measurement instability rather than forcing another architectural change. Relative to the prior E5 point estimate of 166.90 us, the two identical-code samples imply opposite point shifts (-12.44% isolated, +10.76% full filtered), so neither is a defensible final optimization delta.

### Validation

```text
cargo test -p semi-persistent-containers-verus --test three_tier_runtime
  14 passed, 0 failed
PROPTEST_CASES=256 cargo test -p containers-conformance --test three_tier_policy_matrix
  3 passed, 0 failed
cargo check -p containers-conformance --benches
  passed
cargo fmt --all -- --check
  passed after removing one extra blank line in the new test
```

The accepted result resolves the shallow VecP row without changing policies or semantics. The retained formation row remains the only unresolved measurement target, with the concrete safe limit documented above. E6 remains **NOT LOCKED**.

## Final lock-candidate remeasurement

After the second optimization pass and final correctness gates, the previously
bimodal `vec/mark_set_restore` row was run twice in isolation against the same
`pre_three_tier_a414090` baseline:

```bash
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench \
  -p containers-conformance --bench retained_containers_bench -- \
  --baseline pre_three_tier_a414090 'vec/mark_set_restore'
```

| run | production control | verified |
|---|---:|---:|
| isolated 1 | 216.08 us, +7.4903% | 169.61 us, +20.986% |
| isolated 2 | 213.21 us, +5.7756% | 168.65 us, +28.514% |

The verified confidence intervals are broad and the baseline-relative percentage
varies, but both runs confirm a real formation-side residual beyond production
host drift. At 50,000 random touches this is approximately 0.5–0.8 ns per touch.
Restore replay itself remains faster than baseline, and the aggregate guard rows
remain in band or faster after the accepted optimizations.

No further shortcut is accepted for this residual. The remaining cost is the
explicit runtime capture-mode/capability selection and first-capture bookkeeping
that make policy selection independent of physical stack meaning. Removing it
would require a type-specialized ingress architecture or would silently restore
the store-selected dual semantics this work removes. That is a documented
tradeoff, not a reason to reopen the representation.

The execution algorithm is therefore a **lock candidate**: correctness and
performance evidence are complete, two optimization passes removed all
pathological regressions, and the remaining out-of-band row has a measured,
architecture-level explanation. E6 remains formally unlocked until the user
accepts this tradeoff and a commit records the lock revision; no commit was
created automatically.

## Final allocator high-water alignment

A benchmark-local global allocator wraps `System` and accounts requested bytes for every successful `alloc`, `alloc_zeroed`, and `realloc`, plus every `dealloc`. A successful `realloc` accounts only the requested-size delta; a failed `realloc` leaves the old allocation live. Each diagnostic builds its fixture before resetting the high-water mark, runs exactly the corresponding operation outside Criterion's timed loop, snapshots the result before formatting output, and then reports:

- `before_bytes` / `after_bytes`: process-wide requested bytes live at the operation boundaries.
- `peak_bytes`: maximum process-wide requested bytes live during the operation window.
- `peak_growth_bytes`: `peak_bytes - before_bytes`.
- `transient_peak_bytes`: `peak_bytes - max(before_bytes, after_bytes)`, isolating temporary requested bytes above both retained endpoints.

The counters measure requested payload bytes visible through the Rust global-allocation API, not allocator metadata, resident-set size, or an allocator's internal `realloc` implementation details. Absolute boundary values therefore include the benchmark process and fixture; operation-specific retained growth and transient peak come from the boundary/peak differences.

Validation command:

```bash
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench -p containers-conformance --bench three_tier_bench -- 'three_tier/diagnostics'
```

Exact diagnostic output from the successful targeted run:

```text
three_tier_stats label=restore_trail stats=TierStats { trail_frames: 1, trail_entries: 512, hot_frames: 0, hot_entries: 0, cold_frames: 0, cold_runs: 0, cold_values: 0 } logical_trail_bytes=8216 logical_hot_bytes=0 logical_cold_bytes=0 tracking_bytes=8288 total_bytes=75152
three_tier_stats label=restore_hot stats=TierStats { trail_frames: 0, trail_entries: 0, hot_frames: 1, hot_entries: 512, cold_frames: 0, cold_runs: 0, cold_values: 0 } logical_trail_bytes=0 logical_hot_bytes=8216 logical_cold_bytes=0 tracking_bytes=8288 total_bytes=75152
three_tier_stats label=restore_cold stats=TierStats { trail_frames: 0, trail_entries: 0, hot_frames: 1, hot_entries: 0, cold_frames: 1, cold_runs: 1, cold_values: 512 } logical_trail_bytes=0 logical_hot_bytes=24 logical_cold_bytes=4144 tracking_bytes=12576 total_bytes=79440
three_tier_stats label=restore_all stats=TierStats { trail_frames: 2, trail_entries: 512, hot_frames: 1, hot_entries: 64, cold_frames: 4, cold_runs: 4, cold_values: 256 } logical_trail_bytes=8240 logical_hot_bytes=1048 logical_cold_bytes=2240 tracking_bytes=20864 total_bytes=87728
three_tier_conversion label=trail_to_hot before_bytes=65920 after_bytes=70208 reclaimed_bytes=0 before_logical=(65752, 0, 0) after_logical=(24, 4288, 0) stats=TierStats { trail_frames: 1, trail_entries: 0, hot_frames: 8, hot_entries: 256, cold_frames: 0, cold_runs: 0, cold_values: 0 }
three_tier_conversion label=hot_to_cold before_bytes=65920 after_bytes=99072 reclaimed_bytes=0 before_logical=(0, 65752, 0) after_logical=(0, 24, 33152) stats=TierStats { trail_frames: 0, trail_entries: 0, hot_frames: 1, hot_entries: 0, cold_frames: 8, cold_runs: 8, cold_values: 4096 }
three_tier_stats label=promotion_after_restore stats=TierStats { trail_frames: 0, trail_entries: 0, hot_frames: 1, hot_entries: 512, cold_frames: 1, cold_runs: 1, cold_values: 512 } logical_trail_bytes=0 logical_hot_bytes=8216 logical_cold_bytes=4144 tracking_bytes=41440 total_bytes=108304
three_tier_allocator label=trail_to_hot before_bytes=170444 after_bytes=174732 peak_bytes=174988 peak_growth_bytes=4544 transient_peak_bytes=256
three_tier_allocator label=hot_to_cold before_bytes=307212 after_bytes=340364 peak_bytes=348556 peak_growth_bytes=41344 transient_peak_bytes=8192
three_tier_allocator label=restore_all before_bytes=427788 after_bytes=427788 peak_bytes=427788 peak_growth_bytes=0 transient_peak_bytes=0
three_tier_allocator label=promotion before_bytes=535788 after_bytes=535788 peak_bytes=543980 peak_growth_bytes=8192 transient_peak_bytes=8192
```

Interpretation: trail-to-hot retains 4,288 requested bytes across the operation and reaches 4,544 bytes above its starting boundary, leaving a 256-byte transient excess. Hot-to-cold retains 33,152 requested bytes and reaches 41,344 bytes above its starting boundary, so 8,192 bytes are transient scratch. All-tier restore neither retains nor transiently allocates requested bytes. The complete promotion row (ancestor restore, new mark, writes, and inner restore) returns to its starting requested-byte level but peaks 8,192 bytes higher, all transient.

The existing per-tier logical retained-byte reports remain the attribution for trail, hot, and cold pools, while `tracking_bytes` remains the runtime's capacity-based aggregate and `total_bytes` includes the live store. Those logical per-pool retained values, together with the allocator boundary and high-water deltas, cover retained and peak/transient requirements without adding measurement fields to runtime structs or changing runtime behavior. `cargo fmt --all -- --check` and `cargo check -p containers-conformance --benches` both passed before the targeted run.


## DiffStore-owned ingress dispatch and per-mark rollover control

The final architecture removes the trailing const strategy parameter and every
Vec-owned capture setting. `DiffStore` is the only ingress authority:

- static `InlineStore` and `ParallelStore` compile to first-capture Hot ingress;
- static `TrailStore` compiles to chronological duplicate Trail ingress;
- `DynStore` preserves the a414090 `VecD` concrete type and selects one of those
  three protocols at runtime through `StoreKind`.

`new_with_policy(policy)` and `new_kind_with_policy(kind, policy)` configure
retention independently and cannot contradict the selected store. A large
e-graph can begin with `StoreKind::Trail`, then adaptively migrate closed
history Trail -> Hot -> Cold as memory pressure rises while new writes continue
through Trail. Switching future ingress with live history is intentionally not
part of this design.

`RolloverPolicy` and `MarkOptions` add `try_mark_with`. Every mark seals and
opens first. `Defer` then does no conversion, `ApplyConfigured` preserves the
existing tier limits or legacy cadence, and `ForceClosed` runs selected closed
prefixes with Trail -> Hot before Hot -> Cold when both booleans are true.
Existing `try_mark(shrink)` and synchronized/internal callers continue through
the specialized `ApplyConfigured` path. `IfOverallocated { factor, headroom }`
continues to run the original thresholded store/diff-log reclaim before frame
opening; rollover does not replace or broaden reclaim behavior.

### Fat-LTO inspection

A temporary exported probe was compiled with the workspace's fat-LTO release
profile and removed afterward. The `VecP<u64,u32,true>` write monomorphization
was strategy `Kh3` (the store-selected default, folded through
`ParallelStore::unique_capture() == true`). Its `sp_vecp_write` body loaded the live length and
`active_saved_len`, tested/materialized the capture bit, appended the first old
value, set the bit, and wrote the new value. It contained no Vec-owned ingress
field test or call to an alternate configured dispatcher. The complete
200-mark × 8-write × restore `sp_vecp_churn_1000` symbol occupied `0xc50`
(3,152) bytes in the final fat-LTO image. `examples/hotpath_probe.rs` and the
emitted assembly were deleted after inspection.

### Final maintained benchmark intervals

Commands used `SEMPER_COMPRESS`/`SEMPER_DIFF` unset and the unchanged
`pre_three_tier_a414090` Criterion baseline.

| row | final interval | baseline-relative interval |
|---|---:|---:|
| VecP production, 1K | [4.5577, 4.5974] us | [-0.1508%, +0.6852%] |
| VecP static verified, 1K | [3.8698, 3.8939] us | [-0.4824%, +0.5392%] |
| VecP production, 1M | [780.13, 821.11] us | [+3.2348%, +6.1539%] |
| VecP static verified, 1M | [739.26, 746.52] us | [-9.6947%, -8.2953%] |
| retained Vec mark/set/restore, production | [209.18, 212.31] us | [+3.8679%, +5.8448%] |
| retained Vec mark/set/restore, verified | [119.94, 122.23] us | [-11.034%, -8.4577%] |
| retained Vec restore replay, verified | [142.45, 145.46] us | [-2.0025%, +0.9129%] |
| class-ring merge/restore, verified | [28.072, 28.327] us | [-23.525%, -22.924%] |
| sparse-set churn, verified | [175.34, 176.80] us | [-10.188%, -9.2011%] |
| EClasses mark/merge/restore, verified | [7.9375, 8.0090] us | [-8.0538%, -6.8550%] |

Because adding per-mark rollover initially made default unbounded marks decode a
policy that could not migrate, `Vec` caches one derived
`automatic_rollover_enabled` bit. Constructors and `set_tier_policy` update it
from the immutable store capability and current retention policy. Existing
`try_mark` can therefore skip configured rollover with one false branch, while
`try_mark_with` still honors its explicit per-call choice. This cache changes no tier meaning or
public behavior and was retained only after the final tracked and guard runs
below.

A direct paired Criterion run now measures the explicit directive path. With
identical SMT fixtures, configured no-rollover mark measured
`[16.626, 17.165] ns` (estimate `16.840 ns`) and explicit
`try_mark_with(..., Defer)` measured `[19.875, 20.696] ns` (estimate
`20.310 ns`). Thus `Defer` guarantees no conversion or migration, but it does
not have literal zero dispatch overhead; the point estimates differ by 20.61%.

The final sequential VecP/1K run reproduced the supplied hardwired result:
3.8813 us with a [-0.4824%, +0.5392%] baseline-relative interval and no detected
performance change. Fat-LTO assembly independently proves the mode/capability
dispatch is absent. VecP/1M and every verified guard row were in band or faster;
no bitmap/reclamation shortcut was retained.

### Final validation

```text
cargo fmt --all -- --check                                      passed
cargo check -p containers-conformance --benches                 passed
cargo test -p semi-persistent-containers-verus                  passed
cargo test -p semi-persistent-containers-verus \
  --features "compat-all,literal-types"                          passed
cargo test -p semi-persistent-containers-verus \
  --test three_tier_runtime                                     20 passed
PROPTEST_CASES=1024 cargo test -p containers-conformance \
  --release --test three_tier_policy_matrix                     4 passed
PROPTEST_CASES=1024 cargo test -p containers-conformance \
  --release                                                     passed
cargo bench -p containers-conformance --bench three_tier_bench \
  -- "three_tier/mark"                                         passed
```

No `containers/` source, proof body, or sibling comparison checkout was
modified, and no commit was created.

## Detailed VecP/1K attribution and static-ingress resolution

The remaining shallow VecP regression was investigated against a detached clean
`a414090` worktree with isolated fat-LTO target directories. The benchmark,
lockfile, toolchain, Cargo profile, and `ParallelStore` source were identical.
Alternating exact-ID runs used 5-second warmup, 15-second measurement, and 100
samples:

| binary | repeated point estimates |
|---|---:|
| clean `a414090` | 3.8956 us, 3.9457 us |
| dynamic-ingress three-tier tree | 4.2097 us, 4.2253 us |

The 7.5–8% delta therefore reproduced without relying on the older saved
Criterion comparison.

### Exact operation comparison

One timed iteration performs 200 mark/write/restore cycles, 1,600 writes, 1,596
first captures, four duplicate-capture no-ops, 400 bitmap clear passes, and
1,596 restored entries in both revisions. Neither binary migrates a frame,
allocates after initial capacity growth, or executes cold restore in this
workload. The differing operation in the superseded prototype was a second,
Vec-owned ingress decision on every write and during mark/restore orchestration.

An identical exported noinline probe was compiled in both trees. Before cold
outlining, the current fat-LTO envelope contained 2,218 instructions versus
1,465 at `a414090` (+112 loads, +17 stores, +156 branches, +31 calls). Sampling
showed the clean baseline spending more samples in bitmap `memset`/`bzero`, so
bitmap clearing was excluded as the regression source.

Controlled toggles isolated the cause:

| toggle | VecP/1K estimate | conclusion |
|---|---:|---|
| dynamic ingress, original layout | about 4.21–4.23 us | reproduced regression |
| conversion/policy helpers cold and noinline | 4.1980 us | code-size pressure is secondary |
| first-capture write ingress hardwired only | 3.9428 us | matches clean baseline; write dispatch is causal |
| alternate ingress cold/out-of-line, runtime mode check retained | 4.0888 us | alternate code size helps, runtime write branch remains |
| enum variant reordering | 4.1756 us | branch layout alone is insufficient |

The causal cost in that prototype was the redundant Vec-owned strategy decision
in the most frequent operation, not capture bits, rollover, allocation, or
restore. The final design removes that authority and leaves runtime dispatch
only in `DynStore`, where it is intentionally measurable.

### Accepted DiffStore-ingress design

`Vec` retains its a414090 five-parameter shape. `VecP`/`VecI` use Hot ingress,
`VecT` uses Trail ingress, and legacy `VecD` performs runtime selection through
its immutable `DynStore` variant. No separate mode authority or configurable
alias exists. Tier policy changes only closed-history retention.

Final fat-LTO inspection must therefore evaluate the normal VecP write path and
the three DynStore variants independently; the latter's discriminant branch is
the deliberate cost of runtime experimental selection.

Final sequential Criterion comparison against `pre_three_tier_a414090`:

| row | interval | baseline-relative change interval |
|---|---:|---:|
| VecP production, 1K | 4.5577–4.5974 us | -0.1508% to +0.6852% |
| VecP verified, 1K | 3.8698–3.8939 us | -0.4824% to +0.5392% |
| VecP verified, 1M | 739.26–746.52 us | -9.6947% to -8.2953% |

The most-used VecP/1K operation therefore has no measurable regression.
Retained guard rows were also flat or faster: restore replay -2.00% to +0.91%,
class-ring -23.53% to -22.92%, sparse-set -10.19% to -9.20%, and EClasses
-8.05% to -6.86%.

### Per-mark rollover control

Rollover scheduling is now independent from capacity reclaim:

```rust
RolloverPolicy::Defer
RolloverPolicy::ApplyConfigured
RolloverPolicy::ForceClosed { trail_to_hot, hot_to_cold }
MarkOptions { shrink, rollover }
```

`try_mark_with(MarkOptions)` is the additive one-call override. Existing
`try_mark(ShrinkPolicy)` remains source-compatible and applies the configured
policy. Rollover occurs only after the replacement ingress frame opens, forced
both-edge migration runs Trail -> Hot before Hot -> Cold, and only closed oldest
prefixes move.

Direct mark measurements were 16.840 ns for the cached configured no-rollover
path and 20.310 ns for general explicit `Defer`. `Defer` guarantees no
conversion, but the general directive dispatch costs about 3.47 ns. If a
literal zero-dispatch per-call defer operation is required, the next design is
a dedicated const-selected `try_mark_deferred(shrink)` wrapper; this is separate
from the resolved VecP write regression and was not added without a caller that
requires it.


## Container-level `three_tier_v1` measurement matrix — c550112

Recorded after the DiffStore-owned three-tier runtime was committed at
`c5501127e62afc78e99873b1a18660a8c4c88d90`. This follow-up changes only the
Criterion benchmark and task documentation. It adds no runtime behavior, proof
work, or adaptive policy. Every new ID starts with `three_tier_v1`; all
pre-existing `three_tier/*` IDs remain unchanged.

### Matrix and fixture contract

The dynamic Inline, Parallel, and Trail rows in each comparison use the same
deterministic fixture and the same `TierPolicy` (`Trail=Unbounded`,
`Hot=Unbounded`, `ReclaimPolicy::RetainCapacity`) unless the row explicitly
measures rollover. Matching static `VecI`, `VecP`, and `VecT` rows use that same
policy. Production `VecI`/`VecP` rows are same-process workload controls only:
production has no Trail or three-tier retention policy.

The versioned matrix contains 88 rows:

- low- and high-duplicate writes (`W=512,U=512,R=1` and
  `W=512,U=32,R=1`);
- shallow duplicate-heavy restore, deep 64-frame restore, and isolated direct
  Cold restore after one contiguous run is constructed;
- `Defer`, `ApplyConfigured`, and `ForceClosed` rollover for Trail -> Hot,
  contiguous Hot -> Cold, singleton-run Hot -> Cold, and both edges;
- Cold-survivor promotion followed by mark/write/restore;
- 128-cycle SMT backtracking, 64-frame equality-saturation retention,
  32-cycle EClasses-style mark/merge/restore, and 256-frame retained history.

`W`, `U`, `R`, `TierStats`, per-tier logical bytes, aggregate capacity-based
`tracking_bytes`, `total_bytes`, and allocator requested-byte high-water values
are computed and printed outside timed loops. The 256-frame workload is over ten
times deeper than the old 24-frame fixture while remaining practical for the
full local run.

### Exact commands and outcomes

```bash
cargo fmt --all
cargo check -p containers-conformance --benches
cargo fmt --all -- --check
git diff --check

# Representative smoke groups. These two were initially launched concurrently;
# they passed, but their timings are deliberately not used below.
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench \
  -p containers-conformance --bench three_tier_bench -- \
  'three_tier_v1/write/high_duplicates'
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench \
  -p containers-conformance --bench three_tier_bench -- \
  'three_tier_v1/rollover'

# Practical full matrix: all 88 new rows passed.
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench \
  -p containers-conformance --bench three_tier_bench -- \
  'three_tier_v1' --output-format bencher

# Sequential Criterion confidence-interval runs used for the tables below.
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench \
  -p containers-conformance --bench three_tier_bench -- 'three_tier_v1/write'
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench \
  -p containers-conformance --bench three_tier_bench -- \
  'three_tier_v1/(restore|promotion)'
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench \
  -p containers-conformance --bench three_tier_bench -- 'three_tier_v1/rollover'
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench \
  -p containers-conformance --bench three_tier_bench -- \
  'three_tier_v1/trace/(smt_backtracking_128|eqsat_retained_64_frames)'
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench \
  -p containers-conformance --bench three_tier_bench -- \
  'three_tier_v1/trace/(eclasses_mark_merge_restore_32|large_retained_256_frames)'
```

All commands passed. The benchmark configuration remains 10 samples, 250 ms
warm-up, and 500 ms measurement. The tables report Criterion's middle estimate
and bracketed confidence interval from the final sequential run. Criterion's
change lines compare repeated runs of these newly created IDs, not a historical
revision, and are therefore omitted.

### Exact write measurements

| fixture | implementation | estimate | confidence interval |
|---|---|---:|---:|
| low duplicates | Dyn Inline | 1.8745 us | [1.8639, 1.8813] us |
| low duplicates | Dyn Parallel | 1.8202 us | [1.8074, 1.8404] us |
| low duplicates | Dyn Trail | 1.4895 us | [1.4817, 1.4953] us |
| low duplicates | static VecI | 910.36 ns | [908.44, 913.30] ns |
| low duplicates | static VecP | 1.2062 us | [1.1952, 1.2170] us |
| low duplicates | static VecT | 864.14 ns | [840.96, 881.64] ns |
| low duplicates | production VecI | 948.16 ns | [946.67, 949.88] ns |
| low duplicates | production VecP | 1.4921 us | [1.4865, 1.4973] us |
| high duplicates | Dyn Inline | 1.3009 us | [1.2935, 1.3065] us |
| high duplicates | Dyn Parallel | 1.1037 us | [1.1014, 1.1076] us |
| high duplicates | Dyn Trail | 1.4623 us | [1.4555, 1.4662] us |
| high duplicates | static VecI | 480.20 ns | [479.42, 480.80] ns |
| high duplicates | static VecP | 528.64 ns | [525.60, 530.89] ns |
| high duplicates | static VecT | 799.26 ns | [789.68, 812.94] ns |
| high duplicates | production VecI | 539.83 ns | [523.37, 553.03] ns |
| high duplicates | production VecP | 792.58 ns | [791.36, 794.99] ns |

Trail is the fastest dynamic ingress for low duplicates, while dynamic Parallel
is fastest for high duplicates. The static controls are materially faster than
their dynamic counterparts, making the cost of runtime `DynStore` dispatch
visible without changing the static path.

### Exact restore and promotion measurements

| fixture | implementation | estimate | confidence interval |
|---|---|---:|---:|
| shallow high-duplicate restore | Dyn Inline | 24.521 ns | [23.843, 24.935] ns |
| shallow high-duplicate restore | Dyn Parallel | 24.752 ns | [24.537, 24.902] ns |
| shallow high-duplicate restore | Dyn Trail | 219.53 ns | [217.44, 220.53] ns |
| shallow high-duplicate restore | static VecI | 25.079 ns | [24.606, 25.476] ns |
| shallow high-duplicate restore | static VecP | 25.574 ns | [24.724, 26.455] ns |
| shallow high-duplicate restore | static VecT | 218.78 ns | [207.88, 229.08] ns |
| shallow high-duplicate restore | production VecI | 33.814 ns | [33.513, 33.955] ns |
| shallow high-duplicate restore | production VecP | 35.921 ns | [35.451, 36.306] ns |
| deep 64-frame restore | Dyn Inline | 425.67 ns | [419.22, 431.05] ns |
| deep 64-frame restore | Dyn Parallel | 397.82 ns | [393.25, 407.77] ns |
| deep 64-frame restore | Dyn Trail | 1.5731 us | [1.5650, 1.5778] us |
| deep 64-frame restore | static VecI | 425.34 ns | [419.59, 435.36] ns |
| deep 64-frame restore | static VecP | 421.11 ns | [417.84, 423.21] ns |
| deep 64-frame restore | static VecT | 1.4409 us | [1.4017, 1.5076] us |
| deep 64-frame restore | production VecI | 590.64 ns | [589.31, 592.37] ns |
| deep 64-frame restore | production VecP | 590.74 ns | [586.27, 593.29] ns |
| direct Cold contiguous restore | Dyn Inline | 174.14 ns | [172.54, 176.13] ns |
| direct Cold contiguous restore | Dyn Parallel | 174.91 ns | [174.16, 176.39] ns |
| direct Cold contiguous restore | Dyn Trail | 172.58 ns | [169.98, 175.71] ns |
| direct Cold contiguous restore | static VecI | 170.83 ns | [169.37, 173.81] ns |
| direct Cold contiguous restore | static VecP | 95.091 ns | [91.943, 96.432] ns |
| direct Cold contiguous restore | static VecT | 97.170 ns | [91.246, 100.00] ns |
| promotion/write/restore | Dyn Inline | 1.4955 us | [1.4906, 1.4985] us |
| promotion/write/restore | Dyn Parallel | 1.6535 us | [1.6084, 1.6774] us |
| promotion/write/restore | Dyn Trail | 1.4661 us | [1.4450, 1.4748] us |
| promotion/write/restore | static VecI | 584.57 ns | [562.24, 604.84] ns |
| promotion/write/restore | static VecP | 640.99 ns | [608.95, 673.19] ns |
| promotion/write/restore | static VecT | 708.58 ns | [703.15, 711.24] ns |

The duplicate-heavy Trail restore replays `W=512`; the unique stores replay
`U=32`, producing the expected order-of-magnitude difference. Promotion rows
start with at least eight Cold frames for every verified implementation; no
production promotion row is claimed because production has no Cold tier.

### Exact rollover measurements

| fixture/directive | estimate | confidence interval |
|---|---:|---:|
| Trail -> Hot, Defer | 6.6185 ns | [6.4004, 7.1620] ns |
| Trail -> Hot, ApplyConfigured | 1.0282 us | [1.0162, 1.0436] us |
| Trail -> Hot, ForceClosed | 1.0004 us | [995.71 ns, 1.0044 us] |
| Hot -> Cold contiguous, Defer | 17.459 ns | [17.192, 17.706] ns |
| Hot -> Cold contiguous, ApplyConfigured | 3.1874 us | [3.1763, 3.1958] us |
| Hot -> Cold contiguous, ForceClosed | 3.1797 us | [3.1748, 3.1833] us |
| Hot -> Cold singleton runs, Defer | 18.007 ns | [17.570, 18.213] ns |
| Hot -> Cold singleton runs, ApplyConfigured | 1.5956 us | [1.5886, 1.6066] us |
| Hot -> Cold singleton runs, ForceClosed | 1.5833 us | [1.5777, 1.5870] us |
| both edges, source-compatible `try_mark` | 1.2760 us | [1.2649, 1.3029] us |
| both edges, explicit ApplyConfigured | 1.2443 us | [1.2402, 1.2464] us |
| both edges, ForceClosed | 1.2509 us | [1.2484, 1.2530] us |

`ApplyConfigured` and `ForceClosed` agree within narrow intervals on equivalent
single-edge fixtures. The source-compatible `try_mark(ShrinkPolicy)` path is
retained and measured beside the explicit directive path. Both-edge force
executes Trail -> Hot before Hot -> Cold, verified by final Cold ownership.

### Exact trace measurements

| trace | implementation | estimate | confidence interval |
|---|---|---:|---:|
| SMT backtracking 128 | Dyn Inline | 46.488 us | [42.839, 49.489] us |
| SMT backtracking 128 | Dyn Parallel | 34.471 us | [33.672, 35.521] us |
| SMT backtracking 128 | Dyn Trail | 43.881 us | [39.141, 47.868] us |
| SMT backtracking 128 | static VecI | 11.727 us | [11.432, 11.852] us |
| SMT backtracking 128 | static VecP | 14.422 us | [14.302, 14.546] us |
| SMT backtracking 128 | static VecT | 13.842 us | [13.799, 13.873] us |
| SMT backtracking 128 | production VecI | 12.721 us | [12.320, 13.423] us |
| SMT backtracking 128 | production VecP | 20.933 us | [20.803, 21.015] us |
| eqsat retained 64 | Dyn Inline | 31.161 us | [29.459, 34.579] us |
| eqsat retained 64 | Dyn Parallel | 26.118 us | [25.256, 27.233] us |
| eqsat retained 64 | Dyn Trail | 37.033 us | [34.663, 39.252] us |
| eqsat retained 64 | static VecI | 10.689 us | [10.546, 10.768] us |
| eqsat retained 64 | static VecP | 13.148 us | [12.742, 13.428] us |
| eqsat retained 64 | static VecT | 13.621 us | [13.573, 13.671] us |
| eqsat retained 64 | production VecI | 10.851 us | [10.694, 11.027] us |
| eqsat retained 64 | production VecP | 14.247 us | [14.226, 14.276] us |
| EClasses-style 32 | Dyn Inline | 60.263 us | [56.072, 63.443] us |
| EClasses-style 32 | Dyn Parallel | 58.150 us | [54.945, 60.168] us |
| EClasses-style 32 | Dyn Trail | 58.091 us | [53.272, 62.614] us |
| EClasses-style 32 | static VecI | 21.645 us | [21.414, 22.003] us |
| EClasses-style 32 | static VecP | 26.963 us | [26.184, 27.606] us |
| EClasses-style 32 | static VecT | 25.301 us | [24.727, 25.905] us |
| EClasses-style 32 | production VecI | 22.638 us | [22.173, 23.660] us |
| EClasses-style 32 | production VecP | 36.866 us | [36.769, 36.968] us |
| large retained 256 | Dyn Inline | 67.492 us | [65.257, 71.578] us |
| large retained 256 | Dyn Parallel | 59.489 us | [58.171, 60.400] us |
| large retained 256 | Dyn Trail | 69.930 us | [67.552, 71.633] us |
| large retained 256 | static VecI | 22.380 us | [21.754, 22.858] us |
| large retained 256 | static VecP | 28.234 us | [27.894, 28.738] us |
| large retained 256 | static VecT | 28.951 us | [28.792, 29.100] us |
| large retained 256 | production VecI | 25.813 us | [25.042, 26.749] us |
| large retained 256 | production VecP | 38.218 us | [38.053, 38.326] us |

Dynamic Parallel has the lowest middle estimate in the retained 64- and
256-frame traces. The broad dynamic intervals mean the EClasses-style dynamic
rows are not distinguishable from one another in this run; no policy threshold
is inferred from those point estimates alone.

### Exact retained and peak diagnostics

The final full-matrix diagnostic snapshot reported:

| fixture | W/U/R | final logical bytes (Trail, Hot, Cold) | tracking bytes | total bytes |
|---|---:|---:|---:|---:|
| low duplicate Dyn Inline | 512/512/1 | (0, 8,240, 0) | 8,288 | 139,664 |
| low duplicate Dyn Parallel | 512/512/1 | (0, 8,240, 0) | 8,288 | 75,152 |
| low duplicate Dyn Trail | 512/512/1 | (8,240, 0, 0) | 8,288 | 8,592 |
| high duplicate Dyn Inline | 512/32/1 | (0, 560, 0) | 608 | 131,984 |
| high duplicate Dyn Parallel | 512/32/1 | (0, 560, 0) | 608 | 67,472 |
| high duplicate Dyn Trail | 512/32/1 | (8,240, 0, 0) | 8,288 | 8,592 |
| 256-frame Dyn Inline | 64/16/1 per frame | (0, 71,704, 0) | 77,824 | 209,200 |
| 256-frame Dyn Parallel | 64/16/1 per frame | (0, 71,704, 0) | 77,824 | 144,688 |
| 256-frame Dyn Trail | 64/16/1 per frame | (268,312, 0, 0) | 274,432 | 274,736 |

All occupancy matched the intended representation: the two unique ingress
kinds retained 4,096 Hot entries across 257 headers in the large fixture, while
Trail retained all 16,384 writes across 257 Trail headers.

| transition | logical before -> after (Trail, Hot, Cold) | tracking before -> after | peak growth | transient peak |
|---|---:|---:|---:|---:|
| Trail -> Hot, W512/U32/R1 | (8,216,0,0) -> (24,536,0) | 8,288 -> 8,896 B | 864 B | 256 B |
| Hot -> Cold contiguous, W512/U512/R1 | (0,8,216,0) -> (0,24,4,144) | 8,288 -> 12,576 B | 12,288 B | 8,000 B |
| Hot -> Cold singleton, W512/U512/R512 | (0,8,216,0) -> (0,24,16,408) | 8,288 -> 24,768 B | 24,576 B | 8,096 B |
| both edges, W512/U32/R1 | (8,216,0,0) -> (24,0,304) | 8,288 -> 9,344 B | 1,376 B | 320 B |

Retained capacity grows under `RetainCapacity` even when logical occupancy
shrinks, because source capacity remains reusable and destination capacity is
allocated. The contiguous Cold representation halves logical retained history,
but singleton Cold doubles logical retained history and increases final total bytes
by 21.9% (75,152 -> 91,632 B). This is direct negative evidence against automatic
Hot -> Cold conversion for `U/R` near 1.

The benchmark-only explicit-budget records were:

```text
high_duplicates_contiguous W=512 U=32 R=1 budget=4096 candidate=trail_to_hot_to_cold
unique_contiguous W=512 U=512 R=1 budget=8192 candidate=defer
unique_singleton_runs W=512 U=512 R=512 budget=16384 candidate=defer
```

These are deterministic study outputs, not runtime decisions. They provide a
candidate threshold shape—require both real budget pressure and at least 2x
`W/U` or `U/R` reduction—but this campaign does not establish a stable
end-to-end automatic threshold. The honest result is therefore negative: retain
explicit directives and do not add adaptive runtime semantics from these data.

### Limitations and status

- This is a container-level matrix. `eclasses_mark_merge_restore_32` reproduces
  a deterministic parent-update/merge-shaped access pattern over a Vec; it is
  not the full `EClasses` aggregate or full egraph application. The unchanged
  `eclasses_bench` and prior egraph consumer results remain the aggregate
  controls.
- 256 retained frames are materially deeper than 24 and expose the memory
  slope, but they are still a practical microbenchmark rather than a
  production-sized egraph.
- Allocator counters report process-wide requested payload bytes. They exclude
  allocator metadata and RSS; absolute before/after boundaries vary with the
  benchmark process, so only operation deltas are interpreted.
- Production has no Trail, rollover, Cold, or promotion equivalent. Production
  rows are value/workload controls, not representation controls.
- The explicit budget classifier exists only in the benchmark diagnostics.
  There is still no runtime memory-budget input, no live DynStore protocol
  switching, and no proof implementation.
- The full Bencher-format pass is the completeness check; the sequential
  default-format reruns are the authoritative confidence intervals. The two
  initial concurrent smoke runs are pass/fail evidence only.

**Status:** container-level `three_tier_v1` measurement matrix **BUILT AND
MEASURED** at `c550112`; benchmark-only adaptive study **NEGATIVE / DEFERRED**;
runtime semantics **UNCHANGED**; live ingress switching **UNIMPLEMENTED**;
proofs **DEFERRED**; E6 remains **NOT LOCKED** pending any later runtime-policy
decision.


## Explicit-budget adaptive runtime follow-up (`c3bb5bd` working tree)

This follow-up builds the runtime behavior that the `c550112` campaign
intentionally left benchmark-only. It does **not** reinterpret the historical
measurements above and does not claim final thresholds.

### Built semantics

The additive public surface is:

- `Ratio::new(numerator, denominator)`, with zero-denominator rejection and
  exact integer cross-multiplication comparisons;
- `AdaptiveInput { max_closed_history_bytes, min_writes_per_unique,
  min_uniques_per_run }`;
- `AdaptiveReport`, including per-stage and total inspected/migrated frame
  counts, W/U/R totals, logical bytes before/after, and exact unmet bytes;
- `Vec::apply_adaptive(input)` and
  `Vec::try_mark_adaptive(shrink, input)`.

The planner counts only closed Trail/Hot/Cold headers and payload lengths via
`size_of`. It excludes the open ingress frame, live store, capacity, allocator
state, RSS, and time. It scans oldest prefixes without skipping, preserves
empty frame identity, requires the configured W/U ratio plus a strict logical
byte reduction for Trail -> Hot, then recomputes pressure and requires the U/R
ratio plus non-worsening logical bytes for Hot -> Cold. Trail -> Hot always
executes first. A blocker or irreducible Cold returns an exact nonzero
`budget_unmet_bytes`; the planner does not force a harmful transition.

`try_mark_adaptive` seals and opens through the existing immutable `DiffStore`
protocol with `RolloverPolicy::Defer` before applying the pass. Existing
`try_mark`, `try_mark_with`, `TierPolicy`, legacy rollover, and static mutation
paths are unchanged. Live `DynStore` switching remains unimplemented.

Trail W/U derivation and first-capture execution use deterministic sort/dedupe
scratch rather than quadratic `Vec::contains` scans. Scratch is local to the
cold operation and is not retained in `Vec`.

### Built validation and measurement rows

Focused runtime coverage now includes budget already met, exact equality,
duplicate pass/fail, locality pass/fail, singleton rejection, empty frames,
oldest blockers, both-edge cascade, unmet budget, nonmonotone lengths,
promotion/write/restore, all ingress stores, and adaptive-mark token semantics.
The `PROPTEST_CASES`-aware six-backend/seven-profile matrix includes explicit
adaptive apply/mark operations, report invariants, and the unchanged full-state
semantic oracle after every operation.

`three_tier_v2/adaptive/*` and `three_tier_v2/large/*` Criterion rows time the
combined planner+execution path for all DynStore kinds at fixed shapes and
budgets:

- W512/U32/R1 at 4,096 and 256 bytes;
- W512/U512/R1 at 4,096 bytes;
- W512/U512/R512 at 4,096 bytes;
- 256 frames of W64/U16/R1 at unbounded, 65,536, and 32,768 bytes.

Untimed diagnostics emit the exact returned report, final tier occupancy,
capacity/total bytes, and allocator high-water windows. Allocator diagnostics
remain measurement-only and are never policy inputs.

### Threshold status

The explicit 2x ratios used by tests and benchmark fixtures preserve the
historical conservative study shape (2x W/U and 2x U/R), but no public runtime
preset promotes those ratios to defaults. Criterion confidence
intervals and retained/peak results for the new v2 rows are explicitly deferred
to the next measurement stage. E6 is therefore reopened and remains unlocked.
Proof implementation also remains deferred.


### Follow-up validation result

```text
cargo fmt --all -- --check                                      passed
cargo check -p containers-conformance --benches                 passed
cargo test -p semi-persistent-containers-verus \
  --test three_tier_runtime                                     28 passed
cargo test -p semi-persistent-containers-verus                  passed
cargo test -p semi-persistent-containers-verus \
  --features "compat-all,literal-types"                          passed
PROPTEST_CASES=1024 cargo test -p containers-conformance \
  --release --test three_tier_policy_matrix                     4 passed
PROPTEST_CASES=1024 cargo test -p containers-conformance \
  --release                                                     passed
cargo test -p semi-persistent-egraph                            passed
```

The final working-tree diff contains no `containers/` source or proof changes,
and no commit was created. The Criterion v2 rows were compile-checked but not
measured in this implementation stage; confidence intervals and final threshold
selection remain the explicit next-stage limitation.


## Adaptive review follow-up: static hot-path guards

The unchanged-ID static VecP and aggregate guards were rerun from the final
adaptive working tree against `pre_three_tier_a414090`, with
`SEMPER_COMPRESS` and `SEMPER_DIFF` unset. Criterion reported these
baseline-relative 95% confidence intervals:

| row | point estimate | baseline-relative interval |
|---|---:|---:|
| tracked VecP production control, 1K | 4.5370 us | -0.3620% [-0.8078%, +0.0918%] |
| tracked VecP verified, 1K | 3.8529 us | -1.3677% [-1.8743%, -0.8998%] |
| tracked VecP production control, 1M | 729.17 us | -5.4597% [-6.0978%, -4.7039%] |
| tracked VecP verified, 1M | 740.68 us | -9.2267% [-10.056%, -8.3250%] |
| retained vec mark/set/restore verified | 122.72 us | -11.306% [-12.609%, -10.011%] |
| retained vec restore replay verified | 139.06 us | -3.9505% [-5.2116%, -2.7259%] |
| class-ring merge/restore verified | 28.617 us | -21.402% [-21.873%, -20.978%] |
| sparse-set churn verified | 177.41 us | -9.2867% [-9.7684%, -8.8155%] |
| eclasses mark/merge/restore verified | 8.0983 us | -6.4970% [-7.0887%, -5.8956%] |

The static VecP rows and every verified aggregate guard are therefore unchanged
within the noise threshold or faster than the saved baseline; no adaptive
hot-path regression was observed. This closes the static regression-evidence
gap only. The new `three_tier_v2` adaptive rows remain untimed, so adaptive
confidence intervals and final W/U/R threshold selection are still deferred.

## Adaptive memory-pressure completion (`3126bad` plus reclaim working tree)

This stage completed the previously deferred `three_tier_v2` campaign and added
an explicit `ReclaimPolicy::ShrinkToFit` comparison for the 256-frame large
fixture. The runtime change is intentionally narrower than the logical planner:
a migrated explicit adaptive pass shrinks the seven Trail/Hot/Cold
payload/header/run vectors once, after Trail and Hot execution both finish.
`RetainCapacity`, budget-satisfied no-ops, `ShrinkPolicy`, rollover, and every
write path are unchanged. Allocator observations remain diagnostics and are not
adaptive inputs.

The campaign ran alone, with the environment controls unset:

```text
env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench \
  -p containers-conformance --bench three_tier_bench -- \
  'three_tier_v2' --output-format bencher                 passed

env -u SEMPER_COMPRESS -u SEMPER_DIFF cargo bench \
  -p containers-conformance --bench three_tier_bench -- \
  'three_tier_v2'                                         passed
```

Criterion used 10 samples, 250 ms warm-up, and 500 ms measurement. The second
serial pass supplied these 95% time intervals; the middle value is Criterion's
point estimate. Existing unsuffixed large rows are `RetainCapacity` and retain
their stable IDs. The six `_shrink` rows are new.

| v2 row | 95% time interval (point) |
|---|---:|
| high-duplicates W512/U32/R1, budget 4096, Dyn Inline | 6.2392–7.9054 ns (6.7139 ns) |
| high-duplicates W512/U32/R1, budget 4096, Dyn Parallel | 6.2454–7.3111 ns (6.6539 ns) |
| high-duplicates W512/U32/R1, budget 4096, Dyn Trail | 3.6291–3.8074 us (3.6973 us) |
| high-duplicates W512/U32/R1, budget 256, Dyn Inline | 307.42–314.86 ns (310.60 ns) |
| high-duplicates W512/U32/R1, budget 256, Dyn Parallel | 300.52–304.18 ns (301.83 ns) |
| high-duplicates W512/U32/R1, budget 256, Dyn Trail | 3.9240–3.9948 us (3.9584 us) |
| unique contiguous W512/U512/R1, budget 4096, Dyn Inline | 3.4155–3.4323 us (3.4226 us) |
| unique contiguous W512/U512/R1, budget 4096, Dyn Parallel | 3.4494–3.4628 us (3.4577 us) |
| unique contiguous W512/U512/R1, budget 4096, Dyn Trail | 5.9106–5.9467 us (5.9233 us) |
| singleton W512/U512/R512, budget 4096, Dyn Inline | 379.67–389.23 ns (385.64 ns) |
| singleton W512/U512/R512, budget 4096, Dyn Parallel | 387.56–416.22 ns (405.34 ns) |
| singleton W512/U512/R512, budget 4096, Dyn Trail | 868.06–873.88 ns (870.12 ns) |
| large W64/U16/R1 x256, unbounded, Dyn Inline | 98.367–103.24 ns (101.10 ns) |
| large W64/U16/R1 x256, unbounded, Dyn Parallel | 97.915–100.40 ns (99.278 ns) |
| large W64/U16/R1 x256, unbounded, Dyn Trail | 94.858–99.680 ns (98.197 ns) |
| large, budget 65536, Dyn Inline retain | 6.6937–6.9972 us (6.8930 us) |
| large, budget 65536, Dyn Parallel retain | 6.7635–7.1490 us (6.9987 us) |
| large, budget 65536, Dyn Trail retain | 108.53–109.02 us (108.79 us) |
| large, budget 65536, Dyn Inline shrink | 6.8392–6.9789 us (6.9287 us) |
| large, budget 65536, Dyn Parallel shrink | 6.9906–7.1714 us (7.0907 us) |
| large, budget 65536, Dyn Trail shrink | 108.40–108.56 us (108.46 us) |
| large, budget 32768, Dyn Inline retain | 21.200–21.805 us (21.556 us) |
| large, budget 32768, Dyn Parallel retain | 21.339–23.494 us (22.588 us) |
| large, budget 32768, Dyn Trail retain | 123.22–123.89 us (123.60 us) |
| large, budget 32768, Dyn Inline shrink | 21.529–21.946 us (21.714 us) |
| large, budget 32768, Dyn Parallel shrink | 21.390–22.083 us (21.796 us) |
| large, budget 32768, Dyn Trail shrink | 123.53–124.23 us (123.77 us) |

The large diagnostic reports are policy-independent logically. `W` is zero for
Inline/Parallel because those stores enter directly into Hot; their fixture
shape is still W64/U16/R1 per frame. Trail reports count chronology during its
first stage.

| budget | ingress | report W/U/R | migrated Trail/Hot | closed logical before→after | unmet |
|---:|---|---:|---:|---:|---:|
| 65536 | Inline | 0/960/60 | 0/60 | 71680→65440 | 0 |
| 65536 | Parallel | 0/960/60 | 0/60 | 71680→65440 | 0 |
| 65536 | Trail | 16384/4096/60 | 256/60 | 268288→65440 | 0 |
| 32768 | Inline | 0/4096/256 | 0/256 | 71680→45056 | 12288 |
| 32768 | Parallel | 0/4096/256 | 0/256 | 71680→45056 | 12288 |
| 32768 | Trail | 16384/4096/256 | 256/256 | 268288→45056 | 12288 |

Capacity-based tracking and the counting allocator produced the following exact
untimed rows. Allocator columns are requested live bytes
`before→after / high-water / transient-above-max-boundary`; they exclude
allocator metadata and RSS.

| budget | ingress/policy | tracking before→after | allocator before→after / peak / transient |
|---:|---|---:|---:|
| 65536 | Inline retain | 77824→89088 | 246714→257978 / 274874 / 16896 |
| 65536 | Inline shrink | 77824→65464 | 246714→234354 / 274874 / 28160 |
| 65536 | Parallel retain | 77824→89088 | 182202→193466 / 210362 / 16896 |
| 65536 | Parallel shrink | 77824→65464 | 182202→169842 / 210362 / 28160 |
| 65536 | Trail retain | 274432→357376 | 377786→460730 / 522170 / 61440 |
| 65536 | Trail shrink | 274432→65464 | 377786→168818 / 522170 / 144384 |
| 32768 | Inline retain | 77824→122880 | 246714→291770 / 363450 / 71680 |
| 32768 | Inline shrink | 77824→45080 | 246714→213970 / 363450 / 116736 |
| 32768 | Parallel retain | 77824→122880 | 182202→227258 / 298938 / 71680 |
| 32768 | Parallel shrink | 77824→45080 | 182202→149458 / 298938 / 116736 |
| 32768 | Trail retain | 274432→391168 | 377786→494522 / 567226 / 72704 |
| 32768 | Trail shrink | 274432→45080 | 377786→148434 / 567226 / 189440 |

`ShrinkToFit` therefore fixes the retained-allocation inversion: for example,
Trail at 65536 keeps the same logical 268288→65440 report while post-operation
tracking changes from 357376 under retain to 65464 under shrink. At 32768 all
three ingress kinds finish at 45080 tracking bytes under shrink, versus 122880
for retained unique ingress and 391168 for retained Trail. Shrinking does not
lower the operation high-water because destination and scratch allocations
occur before final reclamation; its lower final boundary makes the reported
transient-above-boundary value larger. This is a retained-memory result, not a
peak-memory optimization.

### Threshold decision and limitations

- The measurements support rejecting W/U=1 Trail conversion and accepting the
  measured W/U=4 and W/U=16 duplicate-heavy cases. They do **not** isolate the
  exact 2x W/U boundary, so 2x remains a conservative explicit input used by
  this study, not a measured optimum or automatic default.
- They support rejecting U/R=1 singleton conversion and accepting measured
  U/R=16, U/R=32, and U/R=512 locality. They do **not** isolate the exact 2x
  U/R boundary either.
- A requested budget is irreducible when all eligible history is already Cold
  or the oldest next transition fails its ratio/projected-byte gate. Concrete
  cases are 304 bytes against budget 256 (48 unmet), 4144 against 4096 (48
  unmet), and the fully Cold large shape at 45056 against 32768 (12288 unmet).
  Unique Trail and singleton Hot blockers remain at 8216 against 4096 (4120
  unmet) rather than forcing a harmful transition.
- No default automatic threshold is justified. The study covers deterministic
  container fixtures, not full large egraphs; it samples 1x versus 4x/16x or
  higher rather than the 2x boundaries; planner/execution time ranges from
  nanosecond no-ops to roughly 123 us; and final shrinking trades retained
  capacity for no reduction in allocator high-water. Keep ratios and budgets
  explicit and keep `RetainCapacity` as the existing preset behavior.
- Requested-byte allocator counters are process-wide and exclude metadata/RSS;
  only operation deltas and high-water windows are interpreted. `shrink_to_fit`
  requests capacity release but allocator RSS return is allocator/platform
  dependent. Tracking-byte tests use vector capacities, not allocator metadata.
- This remains a 256-frame container microbenchmark. It does not measure future
  writes that might reuse retained capacity, full-egraph end-to-end benefit,
  live ingress switching, or proof refinement.

**Completion status:** adaptive planner/execution behavior is measured; explicit
post-migration reclamation is built and measured; the threshold study ends with
a documented negative default decision. E6 may lock the current explicit API
and unchanged presets, while live ingress switching and proofs remain deferred.

## Final post-lock validation and static hot-path guard

After runtime lock `d116f76`, the complete formatting, benchmark compilation,
default and `compat-all,literal-types` containers-verus suites, 1,024-case
release policy matrix, full 1,024-case release conformance suite, and egraph
consumer suite all passed. `containers/` remained unchanged and no proof
implementation was modified.

The static VecP hot-path guard was rerun against `pre_three_tier_a414090` after
adaptive reclamation:

| row | final interval | baseline-relative change interval |
|---|---:|---:|
| production VecP, 1K | 4.5031–4.5318 us | -1.6013% to -0.8352% |
| verified VecP, 1K | 3.8622–3.9038 us | -1.3253% to -0.0490% |
| production VecP, 1M | 746.06–753.14 us | -3.5334% to -2.4412% |
| verified VecP, 1M | 730.91–742.53 us | -10.606% to -8.8545% |

The most-used static first-capture path therefore remains at baseline after the
adaptive additions. The final decision is unchanged: explicit adaptive budgets,
ratios, and reclamation are shipped as policy inputs; no universal automatic
threshold or live DynStore ingress switch is claimed from the current data.
