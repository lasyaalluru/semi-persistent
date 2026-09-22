# Task: run-major slice write-back on restore

## One-line outcome (BUILT)
A verified restore path that reconstructs a finalized frame by copying each
coalesced run into the base as a contiguous slice (`base[start..start+len]
.copy_from_slice(run)`), one `memcpy` per run, instead of the per-entry indexed
scatter used today — with `view()`/restore semantics unchanged.

## Why this is soundly a slice write
A finalized frame has at most one write per cell (first-write-wins ⇒ unique
indices), so within a frame the write order is irrelevant to the restored state
(`vec::lemma_overlay_same_map` / `lemma_multiset_eq_overlay`). A run frame
(`RunFrame { starts, vals }`) stores, per run `r`, a start index `starts[r]` and a
contiguous value block `vals[r]`; the run's length is `vals[r].len()`. So the
cells `[starts[r], starts[r]+vals[r].len())` are exactly the run and may be written
in one bulk copy.

## Acceptance — runnable checks (all must pass)
1. `cargo verus verify -p semi-persistent-containers-verus` is GREEN with the new
   run-slice write-back function present and its `ensures` proved. The function
   signature is `restore_runs(&mut base: Vec<T>, frame: &RunFrame<T>, saved_len)`
   (or a method), and its `ensures` states the resulting base equals the scalar
   overlay of the frame's decoded diffs: for every cell `j`,
   `final(base)[j] == overlay(old(base), frame.decode_i(), 0, len)[j]`. A prose
   claim of equivalence does NOT count; the postcondition must be the overlay
   equality (or a lemma discharging it) and must verify.
2. A conformance proptest in `containers-conformance` (e.g.
   `run_slice_writeback_matches_scalar`) constructs random finalized frames
   (unique indices, mixed run lengths), runs BOTH the new slice write-back and the
   existing entry-by-entry `overlay`/`restore_entry` path into two copies of the
   same base, and asserts the two resulting arrays are byte-for-byte equal.
   `cargo test -p containers-conformance --test run_slice_writeback` shows the
   test PASSED (2000+ cases).
3. A criterion bench (`reorder_bench` or a new `restore_bench`) reports the new
   run-slice path vs the entry-by-entry path on the same sorted frames, and the
   committed bench output shows the slice path is faster at run_len ≥ 16 (a real
   number in the commit message, not "should be faster").
4. `cargo build -p semi-persistent-egraph` builds; all existing tests still pass.

## Forbidden proxies (report of any of these = not discharged)
- `#[verifier::external_body]` on the write-back function itself. The overlay
  equality must be PROVED, not trusted. (external_body is allowed only for a
  separately-benched SIMD variant, see task 04 — not for the scalar slice path.)
- A bench standing in for the verified function. The bench is check 3, additional
  to the verified function of check 1, not a replacement.
- Claiming the win from `copy_from_slice` lowering to `memcpy` without check 3's
  measured number.
- Leaving the entry-by-entry path as the only verified one and calling the slice
  path "wired".

## Optimal-first
The optimal write pattern for contiguous runs is a single `copy_from_slice`
(vectorized `memcpy`) per run — use it. Do not hand-roll a per-element loop "for
simplicity"; if `copy_from_slice`'s Verus spec is insufficient, state that as the
one-line blocker and stop, do not downgrade to a scalar loop silently.

## Hard-part-first ordering
1. FIRST: the overlay-equality `ensures` for one run-slice write (prove
   `copy_from_slice` over `[start,start+len)` equals the overlay of that run's
   diffs, using the run's unique-index disjointness). This is the proof that
   breaks; nothing else is reported until it verifies.
2. Then: fold over all runs (runs are disjoint, so each slice write commutes with
   the others — extend the single-run lemma across the run list).
3. Then: the conformance proptest (check 2).
4. Then: the bench (check 3).

## No lateral motion
Do not start delta-bitpack (task 02), Elias-Fano (03), SIMD (04), or threads (05)
until checks 1–4 here are discharged. If check 1 is blocked on a missing
`copy_from_slice` spec, stop and report the exact obligation.

## Partial = not done
"Slice function written but overlay-equality not proved", "verifies but no
conformance test", "conformance passes but no bench number" are each NOT DONE.
Report the specific remaining check and when it closes.

## Status format
Report each of checks 1–4 as BUILT / MEASURED / DESIGNED with the command output
(verify result line, test-result line with case count, bench time numbers, diff
of the new `ensures`). No narrative.
