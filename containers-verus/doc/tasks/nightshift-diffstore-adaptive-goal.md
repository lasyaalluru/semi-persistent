# Nightshift goal: DiffStore-owned three-tier protocol and adaptive large-egraph study

**Completed at runtime lock `d116f76`: the DiffStore-owned three-tier protocol,
88-row DynStore comparison, deterministic explicit-budget adaptive semantics,
post-migration `ShrinkToFit` reclamation, focused runtime coverage, and the
1,024-case differential matrix are BUILT, VALIDATED, and MEASURED. Static VecP
and aggregate baseline guards have no verified regression. The measured data
supports explicit pressure plus ratio/size gates, but does not establish 2x as
an optimal universal threshold, so presets remain unchanged and callers supply
budgets and ratios explicitly. Live ingress switching was evaluated and remains
UNIMPLEMENTED; proofs remain DEFERRED.**

The additive runtime API provides validated integer ratios, `AdaptiveInput`,
`AdaptiveReport`, `Vec::apply_adaptive`, and `Vec::try_mark_adaptive`. It keeps
DiffStore ingress immutable and performs only closed oldest-prefix Trail → Hot
→ Cold conversion after the replacement frame opens. The `three_tier_v1` and
`three_tier_v2` timing, logical-memory, allocated-capacity, and high-water
results are recorded in `three-tier-e5-measurement-a414090.md`. Allocator data
remains measurement-only and never drives policy.

Execution began from `a414090` on `d21-exec`; milestone commits `c550112`,
`c3bb5bd`, `3126bad`, and `d116f76` preserve the implementation, measurements,
adaptive policy, and reclamation work. Use
`containers-verus/doc/tasks/three-tier-frame-architecture-goal.md` and
`containers-verus/doc/tasks/three-tier-e5-measurement-a414090.md` as the source
of truth.

Complete and validate the DiffStore-owned three-tier architecture. `DiffStore`
must be the only ingress-protocol abstraction: `InlineStore` and
`ParallelStore` statically implement first-capture-wins and write directly to
Hot; `TrailStore` appends duplicate-preserving chronological writes to Trail;
`DynStore` selects Inline, Parallel, or Trail at runtime so identical workloads
can measure all protocols without recompilation. `Vec` must not contain a
second `CaptureMode` field, const strategy, or conflicting dispatch abstraction.
Rollover policy remains independent of `DiffStore` and controls only when closed
history transitions Trail → Hot → Cold.

First finish the current refactor and run all required checks: formatting,
focused three-tier tests, default and `compat-all,literal-types`
containers-verus suites, the 1,024-case release policy matrix, full release
containers-conformance, and the egraph consumer suite. Preserve all APIs that
existed at `a414090`, preserve `VecD`'s historical concrete type, keep
`containers/` unchanged as the independent oracle, do not create a commit, and
do not begin proof implementation. Fix any failures before proceeding.

Then rerun the exact VecP 1K/1M and aggregate guard benchmarks against
`pre_three_tier_a414090`. Confirm that deriving ingress from the concrete
`DiffStore` preserves the recovered zero-regression VecP hot path: static
VecP/VecI writes must compile directly to first-capture capture with no runtime
mode branch, VecT writes directly to Trail, and only `DynStore` performs runtime
protocol dispatch. Retain same-process production controls and report confidence
intervals, not point estimates alone.

Extend the benchmark campaign to compare `DynStore` `StoreKind::Inline`,
`StoreKind::Parallel`, and `StoreKind::Trail` on identical deterministic
workloads. Measure at minimum:

- write throughput at low and high duplicate density;
- shallow mark/restore and deep backtracking;
- Trail restore before rollover;
- Trail → Hot dedupe formation cost and memory reduction;
- Hot restore versus Trail restore;
- Hot → Cold sort/run-construction cost and retained-memory reduction;
- direct Cold run restore;
- promotion followed by additional writes and another restore;
- complete SMT-style backtracking traces;
- equality-saturation and EClasses mark/merge/restore traces;
- large retained-history traces representative of very large egraphs;
- logical bytes per tier, allocated capacity, and transient peak scratch.

Study an adaptive large-egraph policy using the cost model `W` writes → `U`
unique cells → `R` contiguous runs:

- Trail has negligible frame-formation work but restores `W` entries.
- Hot pays dedupe once and restores `U` unique entries.
- Cold pays sorting/run construction and restores `R` vectorized slices.
- Trail → Hot should be considered when duplicate or retained-byte overhead
  makes `W/U` sufficiently large.
- Hot → Cold should be considered when memory pressure is real and `U/R`
  indicates enough locality for run copies; singleton-heavy frames must remain
  Hot unless an explicit memory budget accepts the restore tradeoff.
- All automatic decisions must use deterministic recorded statistics and
  explicit memory-budget inputs, not ambient allocator state.
- Rollover operates only on closed oldest prefixes and never migrates the newly
  opened frame.

Use the existing per-mark control:

- `RolloverPolicy::Defer` seals/opens without conversion.
- `RolloverPolicy::ApplyConfigured` enforces retained tier limits.
- `RolloverPolicy::ForceClosed` independently forces Trail → Hot, Hot → Cold,
  or both, with Trail → Hot executed first.
- `ShrinkPolicy` remains capacity reclamation and must not be overloaded with
  representation migration.

Measure the explicit directive overhead and preserve the source-compatible
`try_mark(ShrinkPolicy)` path.

Distinguish two adaptive questions:

1. **Required first target:** continue using `TrailStore` for new writes while
   adaptively converting closed Trail frames to Hot and Cold. This changes
   historical representation without changing the live `DiffStore` protocol.
2. **Optional research target:** determine whether a live `DynStore` can safely
   switch future ingress from Trail to first-capture-wins at a mark boundary.
   Do not implement this casually. A safe switch would require closing the
   Trail frame, migrating or preserving all older representations, converting
   the live backend and capture state without changing values, opening a fresh
   unique frame, and proving through differential runtime tests that token,
   restore, and failure semantics remain unchanged. If those requirements or
   measurements do not justify it, document the design and leave live protocol
   switching unimplemented.

Add focused deterministic regressions and a `PROPTEST_CASES`-aware differential
matrix for every implemented adaptive transition. Include empty frames,
duplicate-heavy frames, finite and unbounded retention, nonmonotone saved
lengths, restore targets in every populated tier, forced/deferred rollover,
memory-pressure transitions, write-after-promotion, and deep unwind. Compare
values, length, depth, token liveness, rejected operations, and tier ownership
after every operation.

Optimize only from measured end-to-end evidence. Do not reintroduce dual stack
meanings, runtime dispatch into static VecP/VecI/VecT writes, pair decoding on
the Cold restore path, or orphan payloads. Revert experiments that improve one
microbenchmark while materially regressing another required workload. Record
accepted and rejected experiments with exact commands and confidence intervals.

Stop only when:

- all runtime and differential gates are green;
- static VecP/VecI/VecT paths retain their intended zero-overhead `DiffStore`
  dispatch;
- DynStore Inline/Parallel/Trail comparisons are recorded;
- the adaptive large-egraph policy has measured thresholds or a documented
  negative result;
- peak and retained memory evidence is recorded;
- the final diff contains no `containers/` or proof changes;
- the architecture and measurement documents accurately distinguish built
  behavior, measured behavior, optional research, and deferred proof work.

If blocked, preserve the smallest failing trace, exact command/output, and a
precise architectural explanation rather than weakening the representation
boundaries or silently changing compatibility behavior.


## `c3bb5bd` explicit-budget implementation checkpoint

The required first target is now built as an additive cold-path API. Explicit
budgets apply only to closed logical history; the planner scans oldest prefixes,
executes exact Trail -> Hot first-capture migration before any Hot -> Cold run
formation, preserves empty frame boundaries, and reports exact residual
pressure. Ratio and projected-byte blockers stop a prefix rather than allowing
a newer frame to leapfrog. No adaptive input is stored in `Vec`, no allocator
measurement is consulted, and no write path or existing rollover API gained an
adaptive branch.

The optional live-protocol research target remains deliberately unimplemented:
`DynStore` continues to select one immutable ingress protocol at construction.
The new v2 benchmark matrix is present for next-stage measurement, but final
W/U and U/R thresholds are not claimed until those confidence intervals and
memory diagnostics are recorded.

## `3126bad` adaptive memory-pressure completion

The final implementation adds only post-operation reclamation. If an explicit
adaptive pass migrates at least one frame and the vector's existing policy is
`ShrinkToFit`, it calls `shrink_to_fit` on all seven Trail/Hot/Cold
payload/header/run vectors once after both plans execute. A no-op pass does not
shrink. `RetainCapacity`, `ShrinkPolicy`, rollover, immutable ingress, and write
cost are unchanged; allocator state is never a policy input.

Validation completed from the working tree based on `3126bad`:

```text
cargo fmt --all -- --check                                  passed
cargo check -p containers-conformance --benches             passed
cargo test -p semi-persistent-containers-verus \
  --test three_tier_runtime                                 29 passed
PROPTEST_CASES=1024 cargo test -p containers-conformance \
  --release --test three_tier_policy_matrix                  4 passed
```

Both complete v2 output passes ran alone with `SEMPER_COMPRESS` and
`SEMPER_DIFF` unset. The 256-frame W64/U16/R1 retain-versus-shrink rows had
these exact Criterion 95% intervals (point estimate in parentheses):

| budget | ingress | retain | shrink |
|---:|---|---:|---:|
| 65536 | Inline | 6.6937–6.9972 us (6.8930) | 6.8392–6.9789 us (6.9287) |
| 65536 | Parallel | 6.7635–7.1490 us (6.9987) | 6.9906–7.1714 us (7.0907) |
| 65536 | Trail | 108.53–109.02 us (108.79) | 108.40–108.56 us (108.46) |
| 32768 | Inline | 21.200–21.805 us (21.556) | 21.529–21.946 us (21.714) |
| 32768 | Parallel | 21.339–23.494 us (22.588) | 21.390–22.083 us (21.796) |
| 32768 | Trail | 123.22–123.89 us (123.60) | 123.53–124.23 us (123.77) |

Logical reports were identical across reclaim policies. At budget 65536,
Inline/Parallel reported W/U/R=0/960/60 and 71680→65440 bytes; Trail reported
16384/4096/60 and 268288→65440. All met the budget. At 32768,
Inline/Parallel reported 0/4096/256 and Trail 16384/4096/256; all reached the
fully Cold 45056-byte floor and reported 12288 unmet.

Exact post-operation tracking results were:

| budget | ingress | retain tracking | shrink tracking |
|---:|---|---:|---:|
| 65536 | Inline | 77824→89088 | 77824→65464 |
| 65536 | Parallel | 77824→89088 | 77824→65464 |
| 65536 | Trail | 274432→357376 | 274432→65464 |
| 32768 | Inline | 77824→122880 | 77824→45080 |
| 32768 | Parallel | 77824→122880 | 77824→45080 |
| 32768 | Trail | 274432→391168 | 274432→45080 |

Requested-byte allocator `before→after / high-water / transient` was,
respectively: 65536 Inline retain
246714→257978/274874/16896 and shrink
246714→234354/274874/28160; Parallel retain
182202→193466/210362/16896 and shrink
182202→169842/210362/28160; Trail retain
377786→460730/522170/61440 and shrink
377786→168818/522170/144384. At 32768: Inline retain
246714→291770/363450/71680 and shrink
246714→213970/363450/116736; Parallel retain
182202→227258/298938/71680 and shrink
182202→149458/298938/116736; Trail retain
377786→494522/567226/72704 and shrink
377786→148434/567226/189440. Shrinking fixes retained allocation but does not
reduce high-water because it occurs after destination/scratch allocation.

The threshold result is deliberately negative. The campaign supports rejecting
W/U=1 while accepting measured W/U=4 and 16, and rejecting U/R=1 while
accepting 16, 32, and 512. It did not measure the exact 2x boundaries, so
neither 2x W/U nor 2x U/R is established as an optimal automatic threshold.
Budgets are irreducible at a Cold floor or oldest-prefix blocker: measured
examples are 304 against 256 (48 unmet), 4144 against 4096 (48 unmet), 45056
against 32768 (12288 unmet), and blocked unique/singleton shapes at 8216 against
4096 (4120 unmet). No default automatic policy or preset change is justified;
keep ratios/budgets and reclamation explicit.

Limitations: allocator counters exclude allocator metadata and RSS;
`shrink_to_fit` does not guarantee immediate RSS return; the 256-frame fixture
is container-level rather than a full large egraph; future reuse of retained
capacity is not timed; and live ingress switching and proof refinement remain
deferred. The full 27-row confidence table and exact diagnostic table are in
`three-tier-e5-measurement-a414090.md`.
