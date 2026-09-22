# Task: multi-threaded concurrent run write-back (measurement-gated)

## One-line outcome (BUILT, but gated — may end DISABLED by measurement)
A parallel restore path that writes disjoint runs of one frame concurrently across
threads into the same base array, conformance-checked equal to the scalar
reference, and a MEASURED decision on whether it ever beats single-threaded — with
the default set by that measurement, not shipped on faith.

## Precondition
Tasks 01 (verified run-slice write-back) and 04 (SIMD) discharged first. This is
the last-resort parallelism and is expected to LOSE on typical (small) restore
strata; the task's real deliverable is the measured crossover, not a shipped
default-on parallel path.

## Why safe, why probably a loss
Runs are disjoint (unique indices per frame ⇒ no aliasing), so threads writing
different runs never race — no synchronization on the writes. But restore-heavy =
SMT backtracking with small strata; thread spawn/join + base-array cache-line
contention dominate for small frames, and the write is memory-bandwidth-bound.

## Acceptance — runnable checks (all must pass)
1. A parallel run write-back exists with a scalar-equivalent contract and scalar
   fallback; `cargo verus verify -p semi-persistent-containers-verus` GREEN
   (external_body allowed for the threading; the disjointness that makes it
   race-free is stated).
2. `cargo test -p containers-conformance --test parallel_restore_matches_scalar`
   PASSED (2000+ cases): parallel and scalar write-back produce byte-for-byte
   equal arrays across frame sizes and thread counts.
3. A criterion bench sweeps frame size (small SMT strata → large batch frames) and
   thread count, with COMMITTED numbers, and a recorded crossover frame-size above
   which parallel wins (or "never wins on this host", a first-class result). The
   default is set from this number.
4. `cargo build -p semi-persistent-egraph` builds; tests pass single-threaded.

## Forbidden proxies
- Shipping parallel-by-default without check 3's crossover measurement.
- A bench that only tests large frames (must include the small-stratum case that
  is the actual SMT workload, where it is expected to lose).
- external_body threading with no conformance proptest (check 2).
- Reporting "parallel restore works" without the measured decision — correctness
  is necessary but the DELIVERABLE is the crossover number and the default it sets.

## Optimal-first
State the parallelization unit (one run per task vs chunked run ranges) and the
thread pool (reuse, not spawn-per-restore) before coding; spawn-per-restore is a
downgrade that must be justified.

## Hard-part-first ordering
1. FIRST: the conformance differential harness (check 2) across sizes/thread
   counts.
2. Then: the parallel write-back with disjointness argument + scalar fallback.
3. Then: the size×threads sweep and the crossover decision (check 3).

## No lateral motion
This is the last task in the set; do not expand scope beyond the crossover
measurement.

## Partial = not done
"Parallel path written, no crossover measured" is NOT DONE — the measured decision
IS the deliverable.

## Status format
Each check BUILT/MEASURED/DESIGNED with: verify line, conformance test-result line,
the size×threads bench table, the crossover frame-size (or "never on host X"), and
the resulting default.
