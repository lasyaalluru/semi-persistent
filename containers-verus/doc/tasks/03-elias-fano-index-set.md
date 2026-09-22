# Task: Elias-Fano / bitset index-set encoding

## One-line outcome (BUILT)
A verified index-set codec for a finalized frame's touched indices over
`[0, saved_len)` — Elias-Fano when sparse, plain bitset when dense — behind the
`view: Seq<nat>` index-column contract, selected by exact-size costing against the
delta-bitpack variant (task 02).

## Why
A frame's indices are a SET over a known universe `U = saved_len`. Elias-Fano is
near information-theoretic (`~N·(2+log2(U/N))` bits), O(N) sequential decode, O(1)
access, model-free. A bitset (`U/8` bytes) is cheaper to write and wins when dense.
This is the strongest linear-time, model-free ceiling for the index axis.

## Acceptance — runnable checks (all must pass)
1. `cargo verus verify -p semi-persistent-containers-verus` GREEN: an `IndexSet`
   codec with `view() -> Seq<nat>` (the sorted index sequence) proved to reproduce
   the input set, for BOTH the Elias-Fano and bitset representations, and the
   `DictFrame`/index-column bijection `decode() == diffs@` proved on top.
2. `cargo test -p containers-conformance --test index_set_roundtrip` PASSED
   (2000+ cases): round-trip is exact across sparse and dense frames; the
   dense/sparse selector picks the smaller representation on adversarial inputs.
3. `scheme_comparison_bench` reports REAL encoded sizes (from the shipped codec)
   for elias-fano and bitset alongside delta-bitpack and plain; committed output
   shows which wins per shape (union-find sparse vs contiguous dense).
4. `cargo build -p semi-persistent-egraph` builds; tests pass.

## Forbidden proxies
- Computed `~N·(2+log2(U/N))` figures standing for the real encoder — measure the
  shipped codec's output.
- `external_body` on the Elias-Fano low/high-bits split where the `view()`
  bijection is wanted, unless the bit-proof downgrade is approved one-line and
  backed by the conformance proptest.
- Shipping only the bitset and calling Elias-Fano "designed".

## Optimal-first
State the sparse/dense crossover (where bitset `U/8` beats Elias-Fano) before
coding and make the selector use exact-size costing, not a fixed threshold.

## Hard-part-first ordering
1. FIRST: Elias-Fano's high-bits unary + low-bits fixed-width `view()` bijection
   (the hardest bit-proof). Report nothing until it verifies or the downgrade is
   approved.
2. Then: bitset codec (simpler) and the exact-size selector between them.
3. Then: `decode() == diffs@` wiring, conformance proptest, REAL-size bench.

## No lateral motion
Do not start SIMD (04) or threads (05) until 1–4 discharged. If Elias-Fano's
bit-proof is out of budget, stop and report it as the blocker — do not fall back to
bitset-only and report the task done.

## Partial = not done
"Bitset done, Elias-Fano deferred" is NOT this task done (it is bitset-only done);
name the remaining obligation.

## Status format
Each check BUILT/MEASURED/DESIGNED with command output and the per-shape winner
from the real encoder.
