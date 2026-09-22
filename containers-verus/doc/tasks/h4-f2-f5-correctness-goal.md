# Goal: corpus correctness, full H4, F2-full, F5-EqSat

Task contract, successor to `forkhistory-and-frame-compression-goal.md`. Acceptance
is a runnable check per item. Every deliverable is labeled BUILT / MEASURED /
DESIGNED from evidence, not intent; a goal that asks for BUILT is not discharged by
MEASURED or DESIGNED. Partial states ("wired but not proven", "parallel but not
differential-checked", "fewer incorrects") are failure states reported with the
exact remaining obligation.

## One-line outcome

The Sundance regression corpus answers correctly on every non-timeout instance with
the semper e-graph; the e-graph's mark and restore run the verified parallel
compression/decompression fan-out; every column's value layer is a
`ValueCompressor` strategy so struct columns compress too; and the per-column mode
table is decided from measured EqSat-scale frames, both axes.

## Starting state (verified green at HEAD)

- Compression live on every column via `SEMPER_COMPRESS=auto`; corpus
  behavior-identical (438 total / 403 correct / 26 incorrect / 9 timeout) with and
  without, activation proved (`env_lever`).
- The 26 incorrect are PRE-EXISTING on this branch (identical in the uncompressed
  baseline): divergence from the satcore-layer0 pin (rev `ec1eb8ae`), which the
  Sundance adapter was built against. The `Assumption` justification is already
  restored; whatever else diverged is unidentified.
- Memcpy restore on the live path (27.1x measured). `ForkHistory` with
  `mark_parallel`/`restore_parallel` verified and measured (7.45x / 6.66x on 10
  members) but NOT reached by the e-graph: `EGraph::mark`/`restore` walk ~10
  composite members sequentially, each minting its own token into `EGraphToken`.
- `Vec` still owns `forks: GenStamps` and `id: ContainerId` (H2 open).
- Value layer: dict/delta only for `T: IndexLike`; struct columns (node caches
  2.7 MB, ClassData 2.4 MB plain in the corpus — the largest byte pools) can only
  index-compress. The `ValueCompressor` design is specified in the predecessor
  goal's appendix; only the F2.1b demotion slice is built.
- F5 is MEASURED for SMT only: sorted runs 0.77–0.94x everywhere, dict on UF parent
  REFUTED at SMT frame sizes (1.12x, ~6-entry frames). The EqSat-scale regime is
  unmeasured.

## Global invariants (checked at EVERY commit)

- `cargo verus verify -p semi-persistent-containers-verus`: 0 errors. Never commit
  a failing proof.
- All semi-persistence and fork-reclamation theorems preserved.
- The e-graph and containers test suites stay green (the `au_exact_anytime`
  machine-speed flake is the single recorded exception).
- Findings, including negatives, recorded in the design docs with the number and
  the command that regenerates it.

## Hard-part-first ordering (strict; no lateral motion)

C1 (correctness) is pinned FIRST: it has the most unknowns and gates every
benchmark claim. Then H4 (the unclaimed parallel gains), then F2-full, then F5
(which needs F2's full candidate set to decide columns). Do not start an adjacent
item while the current one is incomplete; if blocked, stop and state the blocker.

===============================================================================
## Phase C1 (BUILT + MEASURED, PINNED FIRST): the 26 incorrect corpus results

The divergence is between this branch's e-graph and the satcore-layer0 pin the
adapter was written for. The fix is identified from evidence, not guessed.

- C1.1. DIAGNOSE: list the 26 failing instances (the harness prints per-file
  results); bisect the behavior difference by diffing this branch's `egraph/src`
  against `git show ec1eb8ae` for the modules the EUF path exercises (union_find,
  eclasses/classes, egraph merge/explain, node canonicalization), and by running
  one failing instance under both `--features semper-egraph` builds if the pin
  still builds. The diagnosis is written down: which commit/behavior diverged and
  why it changes sat/unsat answers.
- C1.2. FIX: port or repair the diverging behavior on THIS branch (the same
  faithful-port discipline as the `Assumption` restoration; each port cites the
  pin's code). No fix that special-cases test files; no weakening of the harness.
- C1.3. MEASURED: the corpus reports **Incorrect: 0** with `semper-egraph`, both
  with and without `SEMPER_COMPRESS=auto`, and the correct/timeout split is
  recorded. If any instance is found to be mislabeled in the corpus itself, that
  claim needs the instance's expected-answer provenance shown, not asserted.
- C1.4. The e-graph and containers suites still pass after the ports.

Forbidden proxies: skipping or allowlisting the 26 files; calling them "expected
failures"; fixing by pinning Sundance back to `ec1eb8ae` (the whole point is this
branch); reporting "fewer than 26" as done.

===============================================================================
## Phase H4 (BUILT + MEASURED): the e-graph runs the parallel fan-out

Two stages; the shortcut delivers the measured gain, the full adoption cleans the
architecture. The shortcut is not a substitute for the full adoption — both are in
scope, in this order.

### H4a (shortcut): parallel mark/restore inside `EGraph`

- H4a.1. `EGraph::mark` and `EGraph::restore` fan their member composites out over
  a `rayon::scope` on disjoint `&mut` borrows (same soundness argument as
  `ForkHistory`'s twins: each member owns its stores/logs/frames; any shared
  bookkeeping runs strictly outside the fan-out). `EGraphToken` unchanged.
  external_body only on the scope dispatch; threshold-gated like PAR_MEMBER_MIN.
- H4a.2. Differential test: a saturation+backtrack workload driven through the
  sequential and parallel paths yields identical e-graph observables (canonical
  forms, class counts, extractable terms) and identical member depths.
- H4a.3. The parallel fan-out is observed spawning (thread witness), and the full
  e-graph suite passes with it enabled.
- H4a.4. MEASURED: wall-clock for mark and for restore, sequential vs parallel,
  reported separately, on (i) a synthetic backtrack-heavy driver and (ii) at least
  three restore-heavy Sundance instances (chosen by profiling, see H4a.5).
- H4a.5. MEASURED (the profile that directs everything): time-in-mark and
  time-in-restore as a fraction of solve time on at least five backtrack-heavy
  corpus instances, before and after. If mark/restore is a small fraction, that
  finding is recorded and the projected ceiling for parallel gains stated — a
  neutral corpus wall is a finding, not a failure, but it must be explained by the
  profile, not asserted.

### H4b (full adoption): one `ForkHistory`, H2 included

- H4b.1. The e-graph's synchronized members register with one `ForkHistory`;
  `EGraph::mark`/`restore` delegate to it; the token tree collapses to one
  `GroupToken` (the member token structs disappear from `EGraphToken`).
- H4b.2. H2 lands with it: `grep -n "forks\|id: ContainerId"` on `struct Vec`
  shows the fields gone; standalone `Vec` use is a group of one; token validation
  and forgery rejection live on the history. All existing tests pass with at most
  mechanical call-site changes.
- H4b.3. MEASURED: peak fork-history bytes, shared vs the current per-member
  duplication, ten-member group and the real e-graph.
- H4b.4. The e-graph suite and the corpus (C1.3 state: Incorrect 0) still pass.

Forbidden proxies: a scope fan-out that spawns nothing; a differential test that
only checks depths and not contents; H4b reported done while `Vec` still owns
`forks` or `id`; one combined mark+restore timing number.

===============================================================================
## Phase F2-full (BUILT): the `ValueCompressor` strategy and the layered modes

Per the predecessor goal's interface appendix, unchanged in substance:

- F2.1. `ValueCompressor<T>` trait (spec `decode`, exec `compress` with exact-decode
  ensures, `decode_at`, `byte_len`) with the four impls carrying their own bounds:
  `NoValueCompression` (any `T: Copy`), `ValueRle` (`T: Copy + PartialEq`),
  `ValueDictC` (`T: IndexLike`), `ValueDelta` (`T: IndexLike`). `cargo verus
  verify` green with each.
- F2.2. The layered frame: index layer {none, runs, sorted runs} composes with the
  value layer on ONE frame (an index-run frame whose run values are value-layer
  coded). The seven composed modes from the predecessor goal round-trip under a
  conformance proptest (>= 1000 cases each) with the multiset contract, exact
  sequence for non-sorting modes, and every mode's `restore_to` matching the
  reference application.
- F2.3. `Vec`/`DiffLog` take the strategy parameter (defaulting to
  `NoValueCompression`); an illegal column/codec pairing fails to typecheck
  (compile-fail evidence). The `DiffStore` trait is untouched.
- F2.4. Struct columns compress: the node-cache and ClassData column types
  instantiate with `ValueRle` (or stay `NoValueCompression` where RLE loses), and
  the shadow harness logs their value-layer candidates. MEASURED: their encoded
  sizes on the corpus, table recorded.
- F2.5. The per-frame selector ranges over index layer x value layer within the
  column's family, still self-demoting to plain. Existing live-column differential
  tests still pass; the A4 adaptive test extends to a layered mode.

Forbidden proxies: a runtime fallback where the type system should reject; a
layered mode that exists but is never selectable by the live selector; RLE claimed
for struct columns without the corpus measurement.

===============================================================================
## Phase F5-EqSat (MEASURED): the per-column decision, big-frame regime

- F5.1. An equality-saturation workload (the e-graph's own saturation driver on a
  rewrite corpus, mark per rewrite round so frames are per-round scale) runs with
  `SEMPER_SHADOW=<file>`; at least 1000 frames per hot column are logged with the
  FULL candidate set (post-F2: plain / runs / sorted / rle / dict / delta and the
  composed modes).
- F5.2. The per-column table: for every e-graph column, frames, entries,
  distinct-count, run counts, and every mode's REAL encoded bytes vs plain — plus
  the restore-time axis: per-mode restore wall on representative frames (the
  memcpy path vs scattered vs decode-heavy modes), not size alone.
- F5.3. Verdicts: the dict-wins-at-EqSat-scale hypothesis (synthetic 0.30x)
  confirmed or refuted with the number; every other predecessor hypothesis
  revisited in the big-frame regime; refuted ones recorded as negatives.
- F5.4. The outcome is an actual per-column configuration (the modes each column
  ships with under the eq-sat profile), applied and shown active, with the
  end-to-end saturation peak-bytes and wall-clock before/after.

Forbidden proxies: reusing the SMT sweep as the EqSat answer; a size-only table;
a recommended configuration that is never applied and re-measured.

===============================================================================
## Status format

Every progress report labels each item BUILT / MEASURED / DESIGNED with the command
output, test name, or diff that proves it, and names the exact remaining obligation
for anything open. "It should pass" fails the audit.
