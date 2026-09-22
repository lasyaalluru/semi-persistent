# Compression / restore task contracts

Task-contract files (acceptance = runnable checks, not prose; every deliverable
labeled BUILT / MEASURED / DESIGNED; forbidden proxies named; hard-part-first;
no lateral motion; partial = not done). Authored per `~/.claude/skills/task-contract`.

Priority order (each gated on the previous; do not start N+1 until N is discharged):

1. **01-run-major-slice-writeback** — biggest restore speedup, uses the run
   structure already produced; the `copy_from_slice`-per-run write-back, verified
   equal to the scalar overlay. START HERE.
2. **02-delta-bitpack-index-column** — biggest size-per-cycle win on value-major;
   delta + bit-pack the explicitly-stored index column.
3. **03-elias-fano-index-set** — the linear-time model-free size ceiling for the
   index axis (Elias-Fano sparse / bitset dense), size-costed against 02.
4. **04-simd-scatter-restore** — SIMD only where task-01 slice writes do not
   already vectorize (scattered frames); external_body + conformance-checked.
5. **05-multithread-run-writes** — last resort, measurement-gated; the deliverable
   is the crossover number and the default it sets, not a shipped parallel path.

Cross-cutting rules for all five:
- Verus cannot model SIMD/threads: the verified scalar `overlay`/run-slice path is
  the reference; any external_body fast path is proptest-checked byte-for-byte
  equal via `containers-conformance`, never proved.
- Reordering within a frame is sound (unique indices per frame; first-write-wins)
  by `vec::lemma_overlay_same_map` / `lemma_multiset_eq_overlay`.
- Benches report REAL shipped-encoder output, never computed size formulas.
