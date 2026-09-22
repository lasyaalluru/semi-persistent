# Task: SIMD write-back on restore (contiguous memcpy + scattered scatter)

## One-line outcome (BUILT)
A SIMD restore path — vectorized bulk copy for contiguous runs and SIMD scatter
for un-reordered scattered frames — that is conformance-checked byte-for-byte
equal to the verified scalar `overlay`/run-slice reference, gated behind runtime
CPU-feature detection with a scalar fallback.

## Precondition
Task 01 (run-major slice write-back, verified) is discharged first — it is the
scalar reference this SIMD path is checked against, and its `copy_from_slice`
already vectorizes the contiguous case for free. This task adds SIMD only where
that does not apply: scattered frames (value-major, un-reordered).

## Acceptance — runnable checks (all must pass)
1. A SIMD scatter write-back exists (`#[verifier::external_body]` is EXPECTED and
   allowed here — Verus cannot model intrinsics) with an `ensures` equal to the
   scalar overlay postcondition (the trusted contract), and a scalar fallback when
   the CPU feature is absent. `cargo verus verify -p semi-persistent-containers-verus`
   stays GREEN (the external_body contract typechecks; callers verified against it).
2. `cargo test -p containers-conformance --test simd_restore_matches_scalar`
   PASSED (2000+ cases, run on the current host): for random frames, SIMD
   write-back and the verified scalar path produce byte-for-byte equal arrays.
   This proptest IS the trust for the external_body — it must be present and
   passing, not "to be added".
3. A criterion bench shows the SIMD scatter path vs scalar on scattered frames,
   with a committed real speedup number; if SIMD does NOT beat scalar on the test
   host, that negative result is recorded and the SIMD path is left disabled by
   default (a measured decision, not shipped-on-faith).
4. `cargo build -p semi-persistent-egraph` builds; tests pass on hosts without the
   CPU feature (fallback exercised).

## Forbidden proxies
- SIMD path with NO conformance proptest (check 2) — external_body without its
  differential test is an unbacked trusted claim; not discharged.
- A bench without the conformance test, or a conformance test without the bench.
- Claiming a speedup from theory; check 3 needs the measured number on a stated
  host.
- Shipping the SIMD path enabled by default when check 3 shows no win.

## Optimal-first
Use the widest available scatter/gather (AVX-512 `vpscatter`/`vpgather` where
present, else AVX2 fallback) behind feature detection. State the target ISA before
coding. The contiguous case must use the scalar task-01 slice write (already
vectorized) — do NOT reimplement it in intrinsics.

## Hard-part-first ordering
1. FIRST: the conformance differential harness (check 2) driving BOTH paths — this
   is what makes any SIMD code trustworthy; write it before the intrinsics.
2. Then: the SIMD scatter behind feature detection + scalar fallback.
3. Then: the bench and the enable/disable decision.

## No lateral motion
Do not begin threads (task 05) until 1–4 discharged.

## Partial = not done
"Intrinsics written, no conformance test", "conformance passes, no bench",
"benched but shipped enabled despite no win" are each NOT DONE.

## Status format
Each check BUILT/MEASURED/DESIGNED with: verify line, `simd_restore_matches_scalar`
test-result line + host CPU, bench numbers + host, default-enabled/disabled
decision with its number.
