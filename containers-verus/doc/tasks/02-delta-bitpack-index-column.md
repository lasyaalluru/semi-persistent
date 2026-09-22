# Task: delta + bit-pack the value-major index column

## One-line outcome (BUILT)
A verified value-major encoder variant whose index column is stored as
first-differences of the sorted indices, bit-packed to `ceil(log2(max_gap+1))`
bits, behind the existing code-column-style `view: Seq<nat>` contract — so
`DictFrame`'s decode bijection is unchanged and the index column shrinks from
`N·|I|` toward the set's entropy.

## Why
The measurements showed value-major's residue was the explicitly-stored index
column (`N·4` bytes on u32), which dominated after codes were narrowed. Sorting
the frame's unique indices makes them strictly ascending; first-differences are
small positive gaps; bit-packing them to the max-gap width is O(N), model-free.

## Acceptance — runnable checks (all must pass)
1. `cargo verus verify -p semi-persistent-containers-verus` GREEN with an
   `IndexColumn` (or extended `Codes`-style) type whose `view() -> Seq<nat>`
   reproduces the original index sequence, and a `DictFrame` variant using it whose
   `decode() == diffs@` bijection is PROVED (same contract as today's `DictFrame`).
2. `cargo test -p containers-conformance --test dict_delta_roundtrip` PASSED
   (2000+ cases): `decode(compress_delta(d)) == d` exactly for random
   unique-index frames including adversarial gap distributions.
3. `scheme_comparison_bench` reports the REAL encoded size of the delta-bitpacked
   value-major (from the shipped encoder, via a `byte_len`-style accessor — not a
   computed formula) and the committed output shows it beats the byte-granular
   value-major on the union-find shapes (a real ratio, e.g. < 0.63x).
4. `cargo build -p semi-persistent-egraph` builds; existing tests pass.

## Forbidden proxies
- A COMPUTED size row standing for the encoder (the bench must call the real
  encoder and measure its output, as `scheme_comparison_bench`'s `val-major REAL`
  row does — not a `ceil_div(...)` formula).
- `external_body` on the bit-pack/unpack where the `view()` bijection is wanted;
  the pack/unpack must be verified (bit arithmetic) OR, if bit-level proofs are out
  of scope, that downgrade is stated one-line and approved first, with an
  external_body pack backed by a conformance proptest — never silently.
- Byte-granular codes reported as satisfying this task (that is task-done already;
  this task is specifically the delta+bitpack of the INDEX column).

## Optimal-first
Optimal index-column size here is bit-packed deltas at `ceil(log2(max_gap+1))`
bits. State whether you pack to a global width (simplest) or per-block widths
(smaller, more complex) before coding; use global width unless a measured gain
justifies per-block, approved first.

## Hard-part-first ordering
1. FIRST: the bit-pack/unpack `view()` bijection (the bit arithmetic is the
   proof that breaks). Nothing reported until it verifies OR the external_body +
   conformance downgrade is explicitly approved.
2. Then: wire into `DictFrame`/`compress`, prove `decode() == diffs@`.
3. Then: conformance proptest (check 2).
4. Then: the REAL-size bench (check 3).

## No lateral motion
Do not touch Elias-Fano (03) or SIMD (04) until checks 1–4 discharged.

## Partial = not done
"Packs but bijection unproven", "verifies but bench uses computed size" are NOT
DONE.

## Status format
Label each check BUILT/MEASURED/DESIGNED with command output (verify line,
test-result line, bench ratio from the real encoder, `ensures` diff).
