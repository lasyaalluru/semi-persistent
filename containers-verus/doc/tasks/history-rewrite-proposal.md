# Proposal: rewriting `spvec-compression` into a bisectable history

The branch is 200 commits and 37,594 insertions over 109 files against
`main`. That history is a NARRATIVE: it records discovery order, including
hypotheses that were later refuted, measurements that were later corrected,
and designs that were superseded mid-flight. That is the right shape while
work is in progress and the wrong shape for review or `git bisect`.

This proposes the replacement shape. It is not a squash: the branch contains
five distinct campaigns and roughly fifteen independently valuable changes,
and collapsing them would destroy exactly the bisection points a future
regression hunt needs.

## Rules each rewritten commit obeys

1. **Green at every commit.** `cargo verus verify` reports 0 errors, the
   containers suite, the conformance suite and the e-graph suite pass. This
   is what makes `git bisect run` usable: a bisect script can build, verify
   and test at any point in the history.
2. **One theme.** A commit adds one capability, fixes one defect, or
   discharges one obligation. Never two.
3. **Doc plus code plus tests, together.** The design note, the
   implementation and its test/differential land in the same commit. A
   reviewer reading one commit sees why, what and the evidence.
4. **Measurements in the message, not in a later commit.** Every performance
   claim states its number and the benchmark that regenerates it.
5. **Negative results survive.** A refuted hypothesis stays recorded in the
   findings doc of the commit that refuted it. These are the most expensive
   knowledge on the branch and the easiest to lose in a rewrite.

## The proposed sequence

Ordered by dependency. Each entry lists the theme, the principal files, and
the gate that must pass before moving on.

### Layer 1: the verified compression substrate (containers-verus)

**1. Design: diff-stack compression and shared fork history.**
The two design docs, stating the problem, the axes (value-major,
index-major, sorted), and the codec contract as a multiset round-trip. No
code. Gate: docs build.

**2. `DiffLog` behind an abstract `Seq<(T, I)>` view, with the
value-dictionary codec.** `diff_log.rs`, `diff_compress.rs` (`DictFrame`,
`ValFrame`, `Codes`), plus the bit-packed narrow codes. Carries
`lemma_multiset_eq_overlay`: two frames with the same write multiset restore
identically, which is the obligation every later codec discharges. Tests:
codec round-trip conformance. Gate: verify + conformance.

**3. Index-major run coalescing (`RunCol`).** The write-order encoder,
`decode_at`, the index projection, and the frame-wise restore. Includes the
`IndexFromNat` negative result: unimplementable for opaque id types, which
is why `RunCol` reconstructs indices with `checked_add` instead. Gate:
verify + `run_col_index_major`.

**4. Sorted index-major and the multiset frame rule.** `compress_runs_sorted`
plus `lemma_frame_inv_range_multiset` and
`lemma_diff_log_rep_change_preserves_wf_multiset` - the theorem that lets a
reordering fold preserve `Vec::wf`. This is the deepest proof on the branch
and deserves to be bisectable alone. Gate: verify.

**5. Per-frame adaptive cold tier.** `ColdFrame`, the `Cols | Adaptive`
`DiffLog` split, `compact_adaptive`, `Auto` mode selection by exact-size
costing, `FrameStats`. Gate: verify + adaptive_compaction test.

**6. The `ValueCompressor` strategy and the layered frame.** The trait, its
four impls, `LayeredFrame` (index layer x value layer), and the per-frame
selector. Includes the F2.4 negative: struct-column RLE refuted at both SMT
and EqSat scale with the measured byte counts. Gate: verify + selector
differential.

### Layer 2: sharing and parallelism (containers-verus)

**7. `GenStamps` fork-history reclamation.** The O(max-depth) stamp array
replacing the O(restores) branch model, `lemma_bump_invalidates` (both
directions), and the measured 80 MB -> 9 KB reclamation. Gate: verify +
reclamation measurement.

**8. `History`, `Solo`, `SyncPair`, `ForkHistory`, `SyncMember`.** One
genealogy over many typed members; the group invariant and the composition
theorem. Gate: verify + heterogeneous differential.

**9. Parallel mark/restore over disjoint members.** The rayon fan-out with
its differential test and spawn witness, and the two `external_body`
dispatch sites stated honestly as a concurrency claim. Gate: verify +
`parallel_twins_match_sequential_and_spawn`.

**10. The memcpy restore path.** `restore_overlay`, forward/backward
equivalence under unique indices (`lemma_apply_all_eq_overlay`), frame-wise
`restore_range_into`, and the replayed-index skip for wholesale-clearing
stores. Includes the F1 negative about index materialization dominating.
Gate: verify + F1 measurement.

### Layer 3: the discipline axis (containers-verus)

**11. `TrailStore` and the first-hitter reconstruction invariant.** The
chronological-capture store, and the generalization of `frame_cell_inv` to
first-hitter form with `stratum_unique` relocated to a
discipline-conditional `wf` clause. Pure prerequisite for 12. Gate: verify +
`trail_vec` differential.

**12. Runtime store selection.** Instance-level `unique_capture_spec` with
the constancy contract on all 14 mutating methods, the definitional
broadcasts, `DynStore`, `VecD`, `SEMPER_DIFF`. Gate: verify + three-kind
`VecD` differential.

**13. `HintedArena`: the verified arena plus hint index.** The
cannot-miss-a-collision theorem and its zero-maintenance restore proof, with
the three-store differential driving the oscillation pattern and deep
restores. Gate: verify + `hinted_arena` differential.

### Layer 4: trust surface (containers-verus)

**14. Discharge the critical trusted surface.** Ten `external_body` markers
become proofs (`bump_from`, `adaptive_len_exec`, `decode_exec_i`,
`pack_codes`, `packed_get`, `sort_frame_by_index`, `is_unique_idx`,
`RunCol::restore_to`, `assign_codes`, plus one dead function deleted), and
the byte-counter family via verified `sat_mul`/`sat_add`. Ships with the
audit doc and the re-pinned CI gate count. Gate: verify + conformance +
the trust-surface count check.

### Layer 5: the e-graph (egraph)

**15. Corpus correctness: restore re-inserts only surviving dirty ids.**
The C1 crash class and the unsound tf-collision clauses, with the corpus
evidence (26 incorrect -> 0). This is a bug fix and belongs early in the
e-graph sequence so a bisect over later performance work never lands on a
broken corpus. Gate: e-graph suite + corpus sweep.

**16. Adopt the verified substrate.** One `History` per e-graph,
`EGraphToken` collapsed to a `GroupToken`, H2 (containers lose per-container
genealogy), columns on `VecD` with the `SEMPER_DIFF` lever, `--diff-mode` on
both CLIs. Gate: e-graph suite in every diff mode + corpus sweep.

**17. `explain_deep` memoizes congruence expansion.** The unbounded-growth
defect (2M steps, 16 GB) and its fix. Independent of everything around it
and a genuine correctness fix, so it must be its own bisection point. Gate:
e-graph suite + the `boolean_backtracking` instance answering unsat.

**18. The hashcons hint index.** The index becomes a probe-validated hint
cache so restore does no index work: the packed 8-byte `HintSlot`, the
completeness oracle replacing the exact-table invariant, and the
dead-single fix. Carries the diagnosis (14 distinct fingerprints across
11,678 nodes; rebuild cost O(sum of cluster squares)) and the measurement
(restore 949ms -> 25ms). Gate: e-graph suite both compression modes +
corpus sweep + the SMT envelope.

**19. O(1) group-machinery prechecks.** The two per-event registry scans
replaced by map-population reads. Gate: e-graph suite + wall measurement.

**20. Hint-index economics.** Fingerprint threading (recanonize 3 hashes ->
1), dedup on push, move-to-front, lazy bounds-dead reclamation. Carries two
recorded negatives: the 24-bit node tag (measured flat, removed) and the
unsound "drop on query mismatch" GC rule (broke completeness, 39 phantom
nodes). Gate: e-graph suite + node-count identity on every benchmark.

**21. Versioning benchmarks.** `gen_search_bench.py` and its three
families, with the finding that motivated them (the shipped corpus versions
too shallowly to measure the discipline) and the degeneration they exposed.
Gate: programs run, node counts stable.

### Layer 6: performance on the verified side (containers-verus)

**22. Path halving in `UnionFind::find`.** Half the writes, same
inverse-Ackermann bound, same observational-neutrality theorem. Measured
16.7% -> 4.7% of EqSat self time. Gate: verify + containers suite + EqSat
profile.

**23. Zero-copy mark and restore.** `DiffLog::index_slice` and its three
call sites; the abstraction cost where materializing the index column taxed
every mark and restore. Measured: mark 350ms -> 83ms, restore 1.37s ->
0.82s. Gate: verify + containers suite + SMT envelope.

### Layer 7: the record

**24. Findings and inspection docs.** The theorem inventory, the trust
audit, the profiles for both regimes, the mode sweeps, the open questions
(semper-arithmetic defect, the EqSat deep-state premise still unmeasured).
Docs only. Gate: none.

## Entanglement warnings

Three files carry changes from several themes and cannot be split by path
alone; they need hunk-level staging:

- `vec.rs` - first-hitter generalization (11), discipline instance move
  (12), zero-copy mark/restore (23).
- `caches.rs` - hint index (18), fingerprint threading and bucket
  economics (20).
- `egraph.rs` - one-History adoption (16), `explain_deep` fix (17),
  prechecks (19).

Two ordering constraints are hard: 11 must precede 12 (the first-hitter
invariant is what makes the discipline conditional expressible), and 15
must precede 16 (never bisect a performance change onto a corpus that
answers incorrectly).

## Mechanics

`git reset --soft main` onto a scratch branch, then rebuild the sequence by
staging file subsets and hunks, verifying after each commit. Budget the
gates honestly: `cargo verus verify` is about 50 seconds warm, the e-graph
suite about 3 minutes, and a full corpus sweep about 25 minutes, so the
per-commit gate is roughly 4 minutes and the corpus sweep runs at the layer
boundaries rather than at every commit. Expect the rewrite to take a working
day, most of it waiting on gates rather than editing.

Keep the original branch as `spvec-compression-narrative` until the rewrite
is reviewed. The narrative is the only place where the discovery order is
legible, and twice on this branch a "superseded" result turned out to be the
one that explained a later measurement.
