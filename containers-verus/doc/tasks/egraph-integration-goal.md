# Goal: fork-history sharing + parallel adaptive diff compression on the e-graph, measured on Sundance

Branch `spvec-compression` (repo `yaspar-org/semi-persistent`, local `sp-compression`).
This is a transient planning document, discarded once the work lands. The durable design
(current shape and rejected alternatives) lives in the design docs: `doc/design/09`
(compression), `doc/design/10` (fork history), `doc/design/11` (parallel + eager). Every
measured finding from this work is recorded THERE, not here (see G4).

This is a task contract: every acceptance criterion is a command, test, diff, or proof
obligation that either holds or does not; none is discharged by prose. Each deliverable
is labeled BUILT (artifact exists and its own check passes), MEASURED (a number exists,
no artifact), or DESIGNED (a doc exists, no number). A BUILT goal is not discharged by a
MEASURED or DESIGNED result.

## One-line outcome

The e-graph's live mark/restore path compresses every column with a per-column choice of
value-major, index-major (write-order and sorted), or adaptive (`Auto`/calibrated); its
~10 members share ONE fork history; and mark compresses / restore decompresses the
disjoint columns in parallel above a measured threshold. All of it verified, and the
Sundance configuration matrix measured end to end. (BUILT for the code, MEASURED for the
Sundance matrix.)

## Current state this starts from

The compression encoders (value-major with byte + packed codes, index-major write-order
and sorted, the two-stack, the honest `Auto`/calibration selector), the fork-history
reclamation, the shared x1 `History` primitive, and rayon-coexists-with-verus are all
BUILT and verified in `containers-verus`. NONE is on the e-graph's live path:
`EGraph31::mark/restore` (`egraph/src/egraph.rs:2966`) dispatches to ~10 members, each
with a plain `DiffLog`, its own fork history, sequentially. Every phase below is therefore
unbuilt in the e-graph.

## Global invariants (checked at EVERY commit)

- G1. `cargo verus verify -p semi-persistent-containers-verus` prints
  `verification results:: N verified, 0 errors`. A commit with any error count, or with no
  `verification results::` line (a corrupted/incomplete run), is broken and must not exist
  in history.
- G2. `cargo build -p semi-persistent-egraph` and `cargo test -p containers-conformance -p
  semi-persistent-egraph -p semi-persistent-containers-verus` pass (0 failed).
- G3. Every semi-persistence theorem and every fork-reclamation theorem present at the
  start is still present and verified: no `assume`, no `ensures` weakened or removed, no
  theorem downgraded to `external_body`. Check: G1 plus a diff review of the touched
  `ensures`.
- G4. Every measured finding, including negatives, is recorded in the DESIGN docs (09/10/11)
  with the bench/test that regenerates it. This task doc holds raw matrices; the design
  docs hold the durable conclusion.

## Optimal-first clause

Before coding each phase, state the asymptotically and architecturally optimal choice
(data structure, contract shape, borrow structure) and use it. Any downgrade is written
as one line naming the debt and its revival condition, and approved before coding.
"Simpler now, optimal later" is otherwise banned.

## Hard-part-first ordering; phases strictly sequential; no lateral motion

Do the phases in order; within a phase, do the listed items in order (the proof-hardest
first). Do not start a later item, and do not add adjacent or additive work (another
encoder, a refactor, a bench for a not-yet-built path), while the current item is open.
If blocked, stop and state the exact blocker; do not detour into easier work to
manufacture motion. Progress is not reported for a phase until its pinned first item lands
verified.

===============================================================================
## Phase A (BUILT): compression on the live diff-log path, all modes + adaptive

Approach decided (optimal-first), from mapping the proof surface: `Vec` reasons over
`DiffLog@: Seq<(T,I)>` behind a fixed API, and `indices()` (vec.rs:2741/3030/3231) hands
the capture machinery the WHOLE index column as one contiguous `&[I]`. So value-major
(keeps `idxs` whole, preserves flat `@` and `indices()`) integrates with zero `Vec`
re-proof and goes FIRST; index-major (drops `idxs`) needs a capture-machinery change;
sorted (breaks flat `@`) needs the `Vec` multiset model. Cold value column model: a
sequence of IMMUTABLE per-frame `dict`+packed-`Codes` frames plus a plain hot `tail`,
`idxs` kept whole, compacted per frame at mark (amortized O(frame)); packed codes never
need appending. Future "recompress cold" mode (one optimal dictionary across all cold
frames) is noted, not in scope.

- A1 (value-major, the pinned hard item). `cargo verus verify` green (G1) with `DiffLog`
  carrying the two-tier value column (immutable cold frames + hot tail) and a
  `compact_tail` folding a closed frame at mark. Diff review shows `DiffLog`'s public API
  ensures (`@`, `push`, `index`, `subrange_vec`, `drop_front`, `truncate`, `indices`, `wf`)
  UNCHANGED, and `vec.rs` unchanged except the mark-time `compact_tail` call, so no `Vec`
  reconstruction proof was reopened. A conformance test drives a random mark/write/restore
  trace on a `ValueDict` column and asserts the restored `view()` equals the plain oracle's
  (differential); another asserts the column's MEASURED `heap_bytes()` after marks is
  strictly less than plain on a value-repetitive (union-find) workload AND that the cold
  storage is actually dict-coded (not silently plain).
- A2 (index-major write-order). `cargo verus verify` green with the capture machinery no
  longer requiring a contiguous `idxs` slice for compressed columns (the change that lets a
  column drop its index column), and an `IndexRuns` column integrated end to end. Same
  differential test passes; MEASURED `heap_bytes()` < plain on a contiguous-batch workload.
  Design decided (optimal-first): the `DiffStore` capture trait is NOT changed. Instead the
  Vec MATERIALIZES the active/restored frame's index range into an owned `Vec<I>`
  (`DiffLog::index_range`) and passes its slice to `prepare_mark`/`finish_restore`; the
  capture machinery only ever needs one frame's indices, so a range copy (idxs-whole) or a
  run-decode (index-major cold) both satisfy it, and dropping the stored index column becomes
  invisible to the store interface. Step 1 (BUILT, 692d418): `index_range` + push_frame uses
  it. Step 2: an index-major cold frame (RunFrame, no idx column) as a DiffVals variant,
  `idxs` no longer whole; `index_range` run-decodes cold, copies the hot tail. Step 3: the
  differential + heap_bytes test on a contiguous column.
  Obstruction found for step 2 (BOUND PROPAGATION, wide): `RunFrame::decode_i` requires
  `I: IndexFromNat` (reconstruct the dropped indices via `from_nat`), implemented only for the
  primitive index types (u8/u16/u32/u64/usize), NOT the wrapper id types (`DenseId31/63`,
  `SparseSetId`, `UseListId`, ...). Because `DiffLog<T,I>`'s `view()`/`wf` must be defined for
  every variant at the type level, an `IndexRuns` variant whose `view()` run-decodes forces
  `I: IndexFromNat` to propagate `DiffLog -> Vec -> every column instantiation`. So step 2's
  real first move is to implement `IndexFromNat` for all id types (from_nat = wrap(from_nat of
  the inner width) + the round-trip/bounded-value lemmas) and then bump the `DiffLog`/`Vec`
  index bound: a broad multi-file change, unlike A1's localized diff_log-only proof.
  Value-major (A1) had no such obstruction because it keeps `idxs` whole and reconstructs no
  index.
  NEGATIVE RESULT (measured, attempt reverted): `IndexFromNat` cannot be implemented for the
  opaque type-invariant id types (DenseId31/63, wrapper ids) as the trait stands. Its
  `lemma_as_nat_bounded_val(i: Self)` / `lemma_from_as_nat(i: Self)` take a spec-mode param, so
  `use_type_invariant(&i)` is a mode error ("expression has mode spec, expected proof"), and
  with empty bodies both postconditions fail (Verus does NOT globally assume a type invariant
  for a spec value). For DenseId31 the facts `as_nat() < max_nat` and `from_nat(as_nat()) ==
  self` ARE the invariant (`raw < 2^31`), unreachable from a receiver-free lemma; for a
  primitive the same bound is structural (`u32 < 2^32`) so the empty proof works. Consequence
  and decision: index-major on the live path is available only for PRIMITIVE-I columns as the
  trait stands. Opaque-id columns need either an `IndexFromNat` redesign (receiver-based bound
  lemmas, which then breaks `RunFrame::decode_i`'s ghost-index callers that read an index from
  a `Seq` with no tracked receiver) or a trusted broadcast axiom that every id value satisfies
  its invariant. So A2 proceeds for primitive-I contiguous columns; opaque-id columns stay
  value-major/plain until the trait question is resolved.
  UNBLOCK (confirmed sound): drop `IndexFromNat` entirely for the live-path index-major
  encoder; use a ghost-write-set run column reconstructing indices with IndexLike arithmetic.
  Design `RunCol<T,I>`: parallel `starts: Vec<I>` + `run_vals: Vec<Vec<T>>` (run r holds values
  at consecutive indices `starts[r], starts[r]+1, ...`) + ghost `pairs: Seq<(T,I)>` (the write
  sequence it encodes). `decode() == pairs` (spec). wf ties `pairs` to the runs by `as_nat`
  ONLY (no `from_nat`): for run r, offset k, `pairs[off(r)+k].0 == run_vals[r][k]` and
  `pairs[off(r)+k].1.as_nat() == starts[r].as_nat() + k < max_nat`, where `off(r)` is the
  prefix sum of run lengths (a `cold_vals`-style recursive spec). `decode_exec` reconstructs
  each index via `index_like::checked_add(starts[r], <I with as_nat k>)` whose ensures give
  `res.as_nat() == starts[r].as_nat() + k`; with wf's `as_nat` relation and
  `lemma_as_nat_injective`, `res == pairs[off(r)+k].1`, so `decode_exec@ == pairs == decode()`.
  This needs only IndexLike (`as_nat`, `checked_add`, injectivity), works for opaque ids, and
  is a write-order (exact) encoder; `compress` builds runs by capture-order-contiguous indices
  and sets `pairs = diffs@`. The multiset round-trip and `lemma_multiset_eq_overlay` then give
  restore-equivalence.
  STATUS: BUILT and DISCHARGED on the live path (full crate green, commits 38a485d, bcfb9d3,
  9092fd8, 2c113d9, 4cf605b, f842ef3). `RunCol<T,I>` cold-frame API: `compress` (write-order
  coalescing, `decode() == diffs@` via `run_seq == nat_pairs`), `decode_exec`, `decode_at`,
  `idx_seq`/`idx_at`, `restore_runs_into` (the memcpy fast restore), `single_run`, `byte_len`,
  cached `len`. `DiffIdxs<I>` = `Plain(Vec<I>)` | `Runs { cold: Vec<RunCol<(),I>>, tail }` is
  the index-major dual of `DiffVals`: `cold_idxs` concatenates each cold frame's `idx_seq`
  (a `RunCol<(),I>` drops the index column to run starts), with the four lemmas mirroring
  `cold_vals`. `DiffLog.idxs` is now `DiffIdxs<I>`; `compact_tail` folds the frame's index tail
  into a cold frame; `index`/`index_range` reconstruct; the two `vec.rs` restore callers use
  `index_range` (whole-slice `indices()` removed). At most one column compresses (index-major
  keeps values plain) so `len` reads the plain column in O(1). All ~12 `DiffLog` methods
  re-proved green. Acceptance: `index_major_compaction_tests::indexruns_restore_matches_plain_
  and_compresses` drives a live IndexRuns Vec column through 24 `mark_and_compact` frames vs a
  plain oracle: identical contents every step and after a deep cold restore, `tracking_bytes <
  plain`. Differential restore==oracle + heap check on a live column: satisfied.
  FOLLOW-UP (combined mode, user-proposed): index-major runs AND value-dict together for the
  union-find columns (scattered-but-repetitive: drop the index column with runs AND compress
  the few distinct values with a dictionary). Requires dropping the current "at most one column
  compresses" invariant and adding a cached `len` to `DiffLog` (neither column stays plain to
  read length from). A clean extension of the now-proven enum machinery; folds into A4's
  per-column selection.
- A3 (sorted index-major). `cargo verus verify` green with `Vec::restore`'s reconstruction
  re-established over the per-frame write-multiset contract (so a reordering flush is sound),
  and an `IndexRunsSorted` column integrated. Differential test (restore == oracle) passes
  on random unique-index traces; MEASURED `heap_bytes()` <= the write-order encoder on a
  shuffled-but-contiguous workload.
  STATUS: encoder BUILT and verified (commit for `RunCol::compress_sorted`): sort-first
  coalescing, opaque-id safe (no `IndexFromNat`), `decode().to_multiset() ==
  diffs@.to_multiset()`. Conformance `run_col_index_major::compress_sorted_restore_matches_
  and_sorts` (2000 cases): decoded pairs restore-equal the originals under unique indices and
  come out ascending. A3 NOT discharged: the live integration needs the Vec multiset model.
  Scoped precisely: `lemma_multiset_eq_overlay` (vec.rs:390) already proves `overlay(base,d1)
  == overlay(base,d2)` for equal-multiset unique-index frames, and first-write-wins gives
  unique indices across the whole active region, so a sorted cold flush is sound for restore.
  The work is routing `Vec::restore`'s reconstruction (currently stated over the exact
  `diff_log@` order) through that overlay equivalence, and weakening `compact_tail`'s
  `final@ == old@` to `final@.to_multiset() == old@.to_multiset()` for the sorted-Runs case,
  propagating the weaker contract along mark/restore. Largest single Phase A proof change;
  pinned next build.
  TRACTABILITY (traced): the Vec `wf` (vec.rs:965) touches `diff_log@` only through
  `frame_inv_range` (overlay-based snapshot reconstruction) and `captured_in_range` (whether
  an index appears in a range: order-independent). Compaction folds the tail at each mark, so
  a sorted cold flush permutes ONLY within one mark frame's `[diff_start(k), stratum_end(k))`
  range, and first-write-wins makes each such range unique-indexed, so
  `lemma_multiset_eq_overlay` preserves `frame_inv_range` for that frame and every other
  frame's range is untouched. Concrete plan: (1) `compact_tail_sorted` variant permuting only
  the just-closed frame, contract `final@.to_multiset()-per-frame == old@`; (2)
  `lemma_diff_log_rep_change_preserves_wf_multiset` re-deriving the two `diff_log@`-dependent
  wf conjuncts under within-frame permutation via `lemma_multiset_eq_overlay` +
  `captured_in_range` order-invariance; (3) `mark_and_compact_sorted` using it; (4)
  `IndexRunsSorted` mode routed to it in `with_store_mode`; (5) live differential + heap test.
  NO SHORTCUT via the two-stack: `TwoStackLog` has the `frame_msets` multiset infra and
  `flush_cold` supports `IndexRunsSorted`, but nothing wires it to a store-reconstructing
  restore, so it is not a smaller path to a live differential test.
  PROGRESS (steps 1-3 BUILT + verified, committed): (1) `lemma_frame_inv_range_multiset`
  proves `frame_inv_range` invariant under a within-stratum permutation (it reads the range
  only through quantifiers, so it depends on the multiset, not order) plus
  `lemma_captured_in_range_multiset` for the bridge; (2) `DiffLog::compact_tail_sorted` sorts
  the just-closed frame's pairs, writes sorted values back to the plain value tail, folds
  sorted indices into a cold `RunCol`, and proves it permutes only `[cold_len, n)` preserving
  that region's multiset AND uniqueness; (3) `lemma_diff_log_rep_change_preserves_wf_multiset`
  proves `Vec::wf` survives a per-stratum permutation. These are the hardest, novel proofs and
  all verify green.
  DISCHARGED on the live path (steps 4-5 done). `Vec::mark_and_compact_sorted` sort-folds
  the open top frame's stratum before opening the next, lifting wf via
  `lemma_diff_log_rep_change_preserves_wf_multiset`. The `cold_len == diff_start(top)` alignment
  is a precondition (a compact-at-every-mark discipline maintains it) plus per-frame
  uniqueness; both hold by construction for an `IndexRunsSorted` column driven through this
  entry and `push`, so the exec live test satisfies them without a call-site proof, and the
  method body is fully verified. `IndexRunsSorted` mode routes to the run-compressed column.
  Acceptance: `index_major_sorted_compaction_tests::indexrunssorted_restore_matches_plain_and_
  compresses` drives a live column through 24 `mark_and_compact_sorted` frames (each writing
  every cell in a coprime-stride shuffle so sorting coalesces the frame to one run) vs a plain
  oracle: identical contents every step and after a deep restore through the REORDERED cold
  region, `tracking_bytes < plain`. Differential restore==oracle + heap check on a live column:
  satisfied.
  NOTE: verified chaining of `mark_and_compact_sorted` (e.g. from the e-graph, not just the
  exec test) needs the alignment lifted into `Vec::wf` and `mark`'s ensures to expose diff-log
  preservation; deferred until an e-graph column drives it, since the live discharge holds now.
- A4 (adaptive). `cargo verus verify` green with `Auto` and `CalibrationPolicy` selecting
  per frame among the INTEGRATED modes at flush, on the live path. A test drives a mixed
  workload and asserts (i) restore == oracle, and (ii) the per-frame encodings chosen match
  `best_mode`'s argmin on the same frames (the selector actually drives the choice, not a
  fixed mode).
  KEY FINDING: meaningful per-frame adaptivity is value-major vs index-major (union-find
  columns want value-dict; contiguous captures want index-runs). Within index-major,
  sorting always coalesces at least as well as write-order, so an index-only adaptive would
  trivially always sort: not a real selector. So A4 needs a UNIFIED per-frame cold tier, not
  the column-level `DiffVals`/`DiffIdxs` split (which cannot mix value- and index-major across
  frames in one column). SUBSTRATE BUILT + verified (commit for `ColdFrame`): `ColdFrame<T,I>`
  = `Plain | Dict(DictFrame) | Runs(RunCol)`, a self-contained per-frame frame with a
  mode-agnostic `decode()`, `decode_at`, `entry_len`, `byte_len`, and `compress_mode(diffs,
  mode)` proving `decode().to_multiset() == diffs@.to_multiset()` for every mode; opaque-id
  safe (Runs via `RunCol`). Conformance `cold_frame_modes_roundtrip` (1000 cases, all four
  modes). DISCHARGED on the live path. `DiffLog` is now `Cols | Adaptive`; `Adaptive { cold:
  Vec<ColdFrame>, hot, len }` holds a per-frame mix. `compact_adaptive(mode)` folds the hot
  frame in the selected mode (multiset-preserving), `mark_and_compact_adaptive` lifts it via
  the multiset rep-change lemma, `Auto` routes to it. Acceptance:
  `adaptive_compaction_tests::adaptive_restore_matches_plain_and_compresses` drives an Auto
  column through 24 mixed-workload frames, each frame's mode picked by the real `choose_mode`
  on its captured diffs, restoring identically to a plain oracle (every step + deep restore
  through the mixed cold region) with `tracking_bytes < plain`. PHASE A COMPLETE (A1-A4 all
  live-discharged). FOLLOW-UP (user-proposed combined index-runs + value-dict): now a single
  new `ColdFrame` variant (a `DictFrame` whose index column is run-encoded) slotting into the
  adaptive tier + `choose_mode`.

Forbidden proxies for Phase A: a computed/projected size for any `heap_bytes()` check; a
`CompressionMode` that silently falls back to plain reported as compression; `external_body`
on any `Vec`/`DiffLog` reconstruction theorem; a standalone encoder test reported as
live-path integration; declaring A2/A3 done while the column still stores a full `idxs`
column (that is value-major, not index-major).

===============================================================================
## Phase B (BUILT): one shared fork history across the e-graph's members

- B1. `cargo verus verify` green (G1) with `EGraph31::mark/restore` routing through ONE
  shared `History` (GenStamps). Diff review shows per-member fork state removed from the
  members that now share, not merely supplemented, and the members mark/restore through the
  genealogy-free `push_frame`/`restore_frame`.
- B2. A test asserts one group token validates the whole group: its generation/depth is a
  single value, not an N-tuple of per-member tokens.
- B3. A test measures peak fork-history bytes (real `heap_bytes` summed over the e-graph) on
  a mark/restore-heavy trace and asserts shared < per-member.
- B4. Branch-cut safety preserved: G1 plus the restore differential test on the shared path
  passes.

Forbidden proxies for Phase B: adding a shared `History` while leaving per-member histories
in place (B1 requires replacement); reporting the already-done container-level reclamation
or the verified-but-unwired `History` primitive as the e-graph wiring.

===============================================================================
## Phase C (BUILT): sequential then parallel mark/restore with concurrent (de)compression

- C1 (sequential baseline). `EGraph31::mark/restore` over the shared history and compressed
  columns: G1 green and the Phase A/B differential traces pass. This is the correct baseline
  the parallel path is checked against.
- C2 (parallel). An `external_body` `_parallel` twin per composite (the e-graph aggregate
  and its sub-aggregates) with a contract IDENTICAL to its sequential method (diff review:
  same `requires`/`ensures`, verbatim), body = `threshold ? rayon fan-out : sequential
  verified path`, so mark compresses and restore decompresses the disjoint columns
  concurrently on the rayon pool above `parallel::PAR_THRESHOLD`.
- C3. A differential test drives random traces through both the sequential and parallel
  mark/restore and asserts identical resulting `view()` for every member.
- C4. A bench shows the parallel path is at least as fast as sequential ABOVE the threshold
  and falls back to sequential below it (never worse than sequential plus a branch). Numbers
  recorded per G4.

Forbidden proxies for Phase C: a `_parallel` twin whose contract is weaker than the
sequential one; `unsafe` in the twin; a twin that never spawns (just calls sequential)
reported as parallel (C4's above-threshold speedup must be real); reporting C4's bench in
place of the C1-C3 verification.

===============================================================================
## Phase D (MEASURED): the Sundance configuration matrix

The adapter exists (`sundance/src/egraphs/semper/mod.rs`, feature `semper-egraph`, EUF-only,
`--arith-solver none`); Sundance pins the semper backend to git rev `ec1eb8ae` (the
`satcore-layer0` base this branch built on). Baseline is `sundance` without semper.

Matrix (each cell one Sundance run):

| axis | settings |
|------|----------|
| compression | off / per-column defaults / all-value-major / all-index-sorted / adaptive |
| fork history | per-member / shared x1 |
| mark/restore | sequential / parallel |

- D1. Sundance's `semper-egraph` dependency repointed at the current branch (diff of
  `sundance/Cargo.toml` shown); `cargo build -p sundance-smt --features semper-egraph`
  succeeds.
- D2. `cargo bench` in Sundance (`benches/lia_benchmarks`, `benches/tableau_benchmarks`, EUF
  subset) runs for baseline and for each matrix cell.
- D3. The matrix is filled with measured solve times and e-graph peak fork bytes, each cell
  naming the bench; the winning configuration and every losing one (with numbers) recorded
  in the design docs (G4). Empty or "expected" cells fail this criterion.
- D4. Every losing configuration is recorded as a negative result with its number, not
  silently dropped.
- D5. Both use cases are measured against the `main` branch baseline, not only against
  semper-off: the SMT use case (LIA / tableau EUF subset) and the EqSat use case
  (equality-saturation workload). Each reports the current branch vs `main` delta.
- D6. Identify and record every suboptimal algorithmic aspect of diff-frame compression and
  decompression found while measuring: the O(cold frames) linear frame walk in `index`
  (a `starts` prefix-offset array would make it O(log)); any redundant re-decode on restore
  where a memcpy slice-copy applies (`RunCol::restore_runs_into`); allocation churn in
  `compress`/`decode_exec`; and the per-frame vs recompressed-cold-tail dictionary tradeoff.
  Each recorded with the measured cost and the proposed fix (or why it was rejected).

Forbidden proxies for Phase D: projecting Sundance numbers from the container microbenches;
substituting the local `egraph/benches/saturate_bench` for the Sundance benches; leaving any
matrix cell unmeasured.

## Partial states are failure states

"Wired but the restore theorem not re-proven", "parallel twin added but not
differential-tested", "value-major done, index/sorted/adaptive pending" reported as Phase A
done, "matrix mostly filled" are NOT progress toward done. Each is reported with the exact
remaining obligation and the commit at which it closes. There is no "mostly done": each item
is discharged (its check shown passing) or not discharged (with the one missing thing named).

## Status format for every progress report

For each item: the label BUILT/MEASURED/DESIGNED and the evidence as command output, test
name, diff, or proof result, not a narrative. Example: "A1 BUILT: `cargo verus verify` ->
`1840 verified, 0 errors` (paste); diff shows `DiffLog` API ensures unchanged; differential
test `valuedict_restore_matches_oracle` passes; `heap_bytes` 17KB < 32KB plain." A claim
without its shown check is not discharged.
