# Nightshift goal: one external history manager, and close the open gaps

Work autonomously on branch `d21-exec` in `/Users/remidelmas/projects/sp-d21-exec`
(local signed commits only; **never push**) until every required outcome below
meets its acceptance criterion. This goal follows the wave of 2026-09-17
(commits `71f8358`, `2425233`, `60b34a1`, `6c96c24`, `33b565c` and the docs
commit after them; progress doc section "Stratified reporters, literal store
on SpMap, Trail fast path, token provenance, grouped-history tests") and the
architecture the user settled that evening: **the history manager is always
external, there is no standalone container that "just works" on its own, and
the setup is manual.** Design doc 10, "Next: one external manager", records
the shape; the token rule is outcome 2 below (semantics B, decided later the
same evening: a restored token stays valid, every token minted after it dies,
foreign tokens are refused).

## Required outcomes

1. **One external history manager (the typed group).**
   - Columns (`Vec`, `AppendOnlyVec`) carry no manager and no tokens. Their
     whole versioning surface is the member protocol: `push_frame`,
     `restore_frame(depth)`, `depth`, all total (`restore_frame` refuses a
     depth at or above the current one). `mark`, `restore`, `is_valid_token`,
     `try_mark`, `try_restore` and the embedded `Genealogy` leave the columns.
   - Composites (`SpMap`, `ListArena`, `CircularList`, `SparseSet`,
     `UnionFind`, `BPlusTreeSet`, `EClasses`) implement the same protocol by
     fanning out to their columns and doing their own restore work (index
     unwinding, header-archive truncation, ring bookkeeping). Their private
     token types and bundled-token invariants go; the lockstep of their
     columns stays part of their `wf`.
   - `ForkHistory<M: SyncMember>` owns the `History` (genealogy plus depth)
     and exactly one typed member `M`. `mark()` pushes a frame on `M` and
     mints; `restore(t)` validates, cuts from `t.depth + 1` (semantics B,
     outcome 2) and resets `M` to the checkpoint `t`, keeping frame `t.depth`
     open and empty; `pop()` drops the empty top frame; `is_valid(t)` is the
     manager's answer. Typed
     access is `group.member.<field>`. A consumer with several columns writes
     one forwarding struct implementing `SyncMember` (or a small macro does);
     a standalone container is `ForkHistory::new(Vec::new())`.
   - Misuse is refused, not undefined: `push_frame` called on a member behind
     the group's back drifts its depth, and the next group `mark`/`restore`
     refuses because member depth and history depth disagree. State and prove
     that check.
   - The lockstep theorem is stated once, on `ForkHistory<M>`: after `mark`
     every member depth equals the history depth; after `restore(t)` the
     member is at `t.depth` and its view is its snapshot at `t.depth`. The
     forwarding impls discharge it through `SyncMember`'s contract.
   - Consumers migrate: the e-graph owns one `ForkHistory<EGraphColumns>`
     and its `mark`/`restore` go through it (the per-column token bundling in
     `EGraph::mark`/`restore` goes away; `EGraph::mark` still rebuilds first);
     the SAT core likewise. The conformance harnesses (`three_tier_policy_
     matrix`, `proptest_oracle`, `differential`, `misuse`, the retained and
     three-tier benches) wrap the verified side in a group of one so the
     legacy pairing keeps measuring the same operations.
   - Acceptance: every gate in "Gates" green on the final source; no public
     partial function; design docs 08 and 10 rewritten for the shipped shape;
     the grouped-history property tests (`grouped_history_random_sequences_
     land_in_lockstep`, `egraph/tests/group_history_props.rs`) pass against
     the new API; the paired benchmarks against legacy stay within τ on every
     required case (the group-of-one wrapper must not cost a measurable
     per-operation overhead on `vec/`, `aov/`, `map/`, `class_ring/`,
     `eclasses/`, `bplus/`).

2. **Restore semantics B — DONE in the wave of 2026-09-17 (commit
   `2743e17`), kept here as the specification the typed group must
   preserve.** `restore(t)` reconstructs the
   state at mark `t`, keeps frame `t.depth` open and empty, cuts the
   genealogy at `t.depth + 1` (so `t` stays valid and every later token dies),
   and never reopens the parent frame; a separate `pop()` drops the empty top
   frame and reopens the parent (the only place the survivor-reopening paths
   of the tiered Vec remain). SMT-LIB `(pop)` in the interpreter becomes
   `restore(t); pop()`; the SAT core's backjump is `restore(t)` alone; retry
   loops reuse one token. Consequences: the validity rule coincides with the
   legacy inclusive rule (`depth <= fork depth`), so the harness models drop
   the one-sided "verified ⟹ production" relation and assert agreement again;
   affine tokens are off the table (a token is valid exactly while its frame
   exists, which the stamp table tracks); the `GenStamps` of `W5B` already
   supports it (`cut_from(t.depth + 1)`); design docs 08 §1/§3/§6 and 10 are
   rewritten for B. Shipped on the standalone path with the tiered `Vec`'s
   B restore composed as pop core + structural push (so it still reopens
   and re-seals the parent once); the typed group's restore must keep the
   same contract and may implement the native reset (truncate to
   `t.depth + 1`, empty the open stratum) to drop that reopen.
   Memory of the stamp table: 8 bytes per depth of the deepest nesting ever
   reached, kept as capacity (like every column's frame stack); reclaim only
   if a workload shows a reason (shrink when the live length is below a
   quarter of the capacity).

2b. **A restore that never reopens the parent (optional, measured
   first).** Today `Vec::reset_frame` is the pop core plus a deferred
   header push: the parent stratum is promoted into the trail and its
   capture tags recomputed, then sealed again. A true semantics-B core
   would undo the strata above the checkpoint and rewind the open stratum
   in place, leaving the parent sealed where it is — strictly less work
   than the legacy restore, and `pop_scope` alone would pay the reopen.
   Worth doing only if the keep-open cases (`three_tier/restore/*_keep_open`,
   the SAT core's backjump) show a cost the fused `restore_and_pop` does
   not cover; it is a new checked core in the tiered `Vec` (frame
   partition, tier representations and capture tags all touched), so budget
   it as a milestone, not a fix.

3. **CLOSED 2026-09-20** — see the performance report's section "The two
   open benchmark gaps": `aov/log` has a root cause (allocation placement;
   every phase at parity or better, no code change), and the dyn-store family
   is fixed (`VecD` as an enum of the static columns, plus a harness call
   boundary the bench wrapper was adding), within 1.02–1.19 of static on
   writes and level on restores. Original text follows.

   **Close the append-only log gap** (`aov/log/verified` 0.92× of legacy,
   200 µs vs 183 µs for 100 000 pushes, 0.16 ns per push, pre-existing since
   before `aa01a08`). Bounded experiments, in this order, each measured at the
   protocol settings with both orders: (a) after outcome 1 the push path is
   different code — re-measure first; (b) layout: move the two benchmark
   bodies into `#[inline(never)]` functions and swap their order in the
   source, to confirm or refute the placement hypothesis the report records
   for `eclasses/find_sweep`; (c) the verified bench calls `try_push` +
   `expect` per iteration where legacy calls a panicking `push`: measure a
   verified body that hoists the bound check out of the loop. Acceptance:
   parity (≤ 1.08 in both runs and the rerun) **or** a root cause written in
   the performance report. Add no public partial function to get it. Give
   the same treatment to the two residuals of the 2026-09-18 pair
   (`073e38a` against `60b34a1`): the dyn-store family — `three_tier_v1/
   write/*/dyn_{inline,trail}` 1.09–1.25, `promotion/*/dyn_trail` 1.13,
   `large_retained_256_frames/dyn_inline` 1.13, a dozen `dyn_*` traces
   1.02–1.11 (every static store at parity on the same loops; no code on
   those paths changed, so inlining/layout under fat LTO is the first
   suspect), and
   `store/sp-t880.empty20k/*` 1.23–1.30 (20 000 empty push/pop pairs: the
   per-column provenance constant, ≈ 8 ns per column per pair over the
   e-graph's ~30 columns; every other store trace is at 0.94–0.99). The
   second is what outcome 1 removes — one stamp per group per mark instead
   of one per column — so re-measure it after outcome 1 before anything
   else.

4. **Close the Trail-first literal-store cost** (`store/sp-t880.*/smt32`
   1.06–1.08 against `2425233`, the SpMap literal store; `eqsat32` at
   1.00–1.02). The store's own operations are configuration-independent, so
   the working hypothesis is footprint: the map's log holds `(key, value)`
   pairs plus the previous-occurrence column, about 2.4× the bytes per
   literal of the old log, competing with the Trail-first columns for cache.
   Confirm or refute with the reruns and one experiment (a key-only
   `SpMap<L::Key, (), I>` beside a plain value column for identity-keyed
   literal types, or a generic value-only log with keys derived on unwind —
   the latter is a verified change to `SpMap` and must keep `obeys_key_model`
   as the only assumption). Acceptance: ≤ τ on both configurations of
   `store_bench` and `saturate_bench`, or a documented cost the user accepts.

5. **Verify the two-step id-mint protocol** of the node store
   (`doc/future/node-store-plan.md`: `TypedRouting` reserve/finalize and entry
   agreement), the item the user deferred to "a next wave" on 2026-09-17.
   Acceptance: the protocol's invariant is a `wf` clause with verified
   transitions; no new trust.

6. **Node caches on SpMap** — only after outcome 4 is understood, and ask
   the user before starting: the user said "keep the node caches intact for
   now". If authorised, the caches lose `REBUILD_RATIO`/`restore_incrementally`
   and their hand-rolled hashbrown index, with the paired `eclasses/` and
   `saturate/` benchmarks as the acceptance test.

7. **Lean per-commit gate** (user, 2026-09-17 22:15: "not all these tests
   are necessary"; the split below was confirmed by the user at 22:20 —
   adopt it from the external-manager commits on). Where the consumer time
   goes: eight anti-unification binaries (`au_delegation` 90 s for 3 tests,
   `egg_tests` 45 s/190, `au_hardness` 34 s, `au_deep_term_stress` 22 s,
   `au_differential` 21 s, `au_corpus_bench` 16 s, `au_hybrid_exact` 13 s,
   `au_closed_bit` 9 s) = 210 of 265 s, unoptimized search loops run one
   binary after another. Two fixes, both approved: `[profile.test]
   opt-level = 2` (debug assertions kept) and `cargo-nextest` (one process
   per test across all cores, per-test timings; install with `cargo install
   cargo-nextest --locked` on an idle machine, then `cargo nextest run` in
   place of `cargo test` for the consumer and conformance suites — the
   proptest suites keep their `PROPTEST_CASES`). Measured battery: 11 min, of
   which consumer suites 340 s
   (18 s compile, 265 s running 66 unoptimized test binaries) and the
   literal-types verify 86 s (a full second verify of 2655 functions for one
   gated module block). Per commit: default verify (90 s), composition,
   feature suite (47 s), policy matrix (14 s), conformance (22 s), canary,
   au-verus, partial-API, fmt, diff, legacy check, plus (a) the gated modules
   only under `--features literal-types` (`--verify-only-module`, ~10 s) and
   (b) the consumer suites only when `egraph/`, `satcore/` or the container
   crate's public surface changed, under an optimized test profile
   (opt-level 2, debug assertions on); otherwise `cargo check --tests` of
   the consumers (~20 s). Target: ~3.5 min per commit. The full battery as
   listed under "Gates" runs once per wave on the final commit, before the
   benchmarks. Never trade away the default verify or the policy matrix.

8. **Records and merge.** Progress doc section with per-commit gate evidence;
   performance report section per measured commit (protocol tables, reruns,
   verdicts); trust ledger, verification report and handoff counts; design
   docs; CHANGELOG. Then a local merge of `d21-exec` into `main` (never push).

## Design detail settled by the code reading of 2026-09-17 evening

- The member protocol already exists and is verified: `sync_group::SyncMember`
  (`seal_frame` = push a frame, `restore_frame(depth)`, `depth_spec`,
  `can_seal`/`can_seal_now`, abstract `model`/`archive`, `lemma_archive_depth`),
  with `ForkHistory { members: Vec<Box<dyn SyncMember>>, history }` proving
  lockstep over the boxed members. The typed group is that theorem restated
  over one generic member: `ForkHistory<M: Member>` where `Member` is the
  same protocol with an **associated `Model` type** instead of the
  `Seq<nat>` projection the dyn-compatible trait needs (associated types in
  verified traits are already in use: `StorePolicy::Store`, `Tagged::Repr`).
  Keep the dyn group until the last commit removes it, or retire it when the
  typed one is verified; do not maintain two theorems longer than needed.
- Forwarding structs: `impl Member for EGraphColumns { fn push_frame(..) {
  self.classes.push_frame(..); self.nodes.push_frame(..); ... } ... }`; the
  parallel fan-out the e-graph does today with `rayon::scope` moves into that
  impl (the dyn group's `mark_parallel`/`restore_parallel` are the template),
  behind the same `fanout_enabled` threshold.
- The composites already have token-free cores: `SparseSet::restore_frames`,
  `CircularList::restore_frames`, `ListArena::restore_frames`,
  `UnionFind::restore_frames`; `SpMap::restore`, `BPlusTreeSet::restore` and
  `EClasses::restore` read only `token.<column>.depth` and split the same way.
  Their `push_frame` is today's `mark` minus the token bundling.
- The e-graph is closer than it looks: `EGraphToken { group: GroupToken,
  completion_outcome }` already names one version, `EGraph::history` is
  already a `History`, and `restore_with` already validates against it. What
  goes: the nine per-member token stacks (`classes_marks`, `nodes_marks`,
  `sorts_marks`, `ops_marks`, `rules_marks`, `axioms_marks`, `lits_marks`,
  `unit_node_marks`, `inverse_op_marks`) and every member `mark()`/
  `restore(token)` call, replaced by the group's structural `push_frame`/
  `restore_frame(depth)` on a forwarding struct of those nine members.
- Call-site inventory at the start (grep, 2026-09-17): e-graph 164 `mark`,
  177 `restore`, 85 `is_valid_token`, 109 token-type mentions (most are
  tests of per-component token semantics and collapse to group tests); SAT
  core 6/4; conformance 123/128; in-crate tests 134/101. Commit order that
  keeps every commit green: (A) typed group + `Member` impls for every
  column and composite, additive; (B) e-graph and SAT core on the typed
  group; (C) conformance harnesses and benches on groups of one; (D) the
  deletion — tokens, `mark`/`restore`, the embedded `Genealogy` — with the
  in-crate tests; docs last.

## Non-negotiable constraints

- No `admit`, `assume`, axioms, trusted semantic wrappers, new `external_body`
  or raised solver limits (`rlimit`). Decompose and hide instead; lowering a
  limit is allowed when the proof no longer needs it.
- `containers/` stays byte-identical (`git diff --quiet aa01a08 -- containers`).
- Every public function is total: the partial-API gate must report 0/0/0/0
  with an empty allowlist. Internal primitives with preconditions are
  `pub(crate)`.
- One battery per commit, in an isolated worktree holding exactly that
  commit's files, plus the affected benchmarks against the previous commit;
  commit messages end with the session's attribution trailers; signing key
  `0A4440702F23E58F`.
- No subagents unless the user authorises delegation. Report the partial-API
  and benchmark results honestly; inconclusive stays inconclusive.
- Docs are the last commit of the wave.

## Gates (recreate the battery script from this list; the scratchpad copy is ephemeral)

From the repo root, worktree `<W>` holding the candidate files, `touch` a
source before every Verus run:

```
(cd containers-verus && cargo verus verify)                                  # default, expect "N verified, 0 errors"
(cd containers-verus && cargo verus verify --features literal-types)
verus --crate-type lib containers-verus/proofs/top_down/composition.rs       # 80 verified
cargo test -p semi-persistent-containers-verus --features 'compat-all,literal-types'
PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test three_tier_policy_matrix
cargo test -p containers-conformance --release --test proptest_oracle --test differential --test egraph_reference_differential
cargo test -p semi-persistent-satcore -p semi-persistent-egraph              # debug build: au_exact_anytime's 5 ms deadline fails in --release
cargo test -p containers-verus-canary --features compat-all
(cd au-verus && touch src/lib.rs && cargo verus verify)                      # 29 verified
python3 containers-verus/tools/check_partial_api.py containers-verus/src containers-verus/partial-api-allowlist.txt
cargo fmt --all -- --check; git diff --check; git diff --quiet aa01a08 -- containers
grep -rh '#[verifier::external_body]' containers-verus/src --include='*.rs' | wc -l   # 42 = 37 default + 5 gated; CI pins 37
```

Benchmarks: τ = 1.08, two interleaved runs per tree into one
`CRITERION_HOME` (`--save-baseline <tag>_cand_A`, `_prev_A`, `_cand_B`,
`_prev_B`), evaluated by `containers-verus/tools/bench_compare.py --mode
checkpoint --runs <tag>_cand_A <tag>_cand_B --old <tag>_prev_A <tag>_prev_B`
(paired mode for verified-vs-legacy); inconclusive cases rerun once per side
at `--sample-size 100 --warm-up-time 3 --measurement-time 10`. Benchmarks
only on an idle machine, never concurrently with a battery.

## Operational notes (hard-won on 2026-09-17; read before starting)

- A healthy full default verify of the crate takes about ninety seconds
  (2655 functions). A run that takes an hour or ends in a Z3 worker panic
  ("expected rlimit-count in smt statistics") is a runaway quantifier in one
  function: find it from the panic location, read the predicates it unfolds,
  and decompose. The pattern that fixed `ListArena::splice_raw`: `hide(...)`
  for the self-feeding predicates as the **first statements of the exec
  body** (not inside a `proof {}` block), small accessor lemmas for the facts
  the body needs, delegated lemmas that re-establish each predicate for the
  new state in their own context. Do not bisect by whole runs; read the diff.
- A new field on `Vec` perturbs unrelated proofs near their budget (this wave:
  `lemma_hot_frame_strict`, `lemma_ingress_capture_preserves`); fix by
  splitting, never by raising. Changes confined to a non-physical field go
  through a framing lemma (`lemma_genealogy_framing` is the template: a
  ghost snapshot before the change, the lemma after it).
- `&mut self` calls havoc unstated fields: mutate a new field **last** in a
  function whose ensures must state facts about it. Public `ensures` may not
  read `pub(crate)` fields of opaque types: add `pub open(crate) spec fn`
  accessors. `gen` is a reserved word (edition 2024). `x as usize < y` parses
  as generics: parenthesise.
- Never edit the tree a verify or battery is compiling. Never `cargo check`
  as evidence: it erases proof code.
- Commit procedure: keep the main tree at the final content and build the
  per-commit file sets relative to the current `HEAD`; commit a set by
  staging exactly its files. Do **not** lay an intermediate set over the
  main tree (this wave lost the working copies of three files that way and
  recovered them from the battery worktree), and never delete a validated
  state directory before its replacement exists.
- Pre-existing, unrelated: `egraph/tests/au_exact_anytime.rs`
  (`exact_deadline_returns_anytime_incumbent`) fails in `--release` on a fast
  machine; the gate runs the consumer suites in debug.
- Worktrees at the end of 2026-09-17: `sp-d21-b` (battery), `sp-d21-prev`,
  `sp-d21-bench`, `sp-d21-bench2`, `sp-d21-bench3` (benchmark trees, one per
  wave state), plus the legacy checkpoints `sp-d21-aa01a08`,
  `sp-d21-before-tiers-0eaec9e`, `sp-d21-pre-topdown-3598ebd`. Reuse or
  remove them (`git worktree remove`), do not create more than needed.

## Completion and handoff

Record, for each outcome, the commit, the gate evidence with log paths, the
benchmark verdicts and the exact remaining dependency if any, in the progress
doc and the handoff's "Next actions". Do not label an outcome complete
because the night ends: an outcome without its evidence is open, and an
inconclusive benchmark is not a pass.

## Status at the wave's close (2026-09-18, wrapped up at the user's request)

**Outcome 1 — the typed external manager: shipped, with two token surfaces
left standing for a named reason.** Six commits, `5fc8b29` through `67900d4`
(rebuilt from the twelve that were actually built and gated, which stay on the
local branch `d21-exec-wave-full`; logs `scratchpad/lean_*.log`, and the
progress doc carries the table plus the tree-by-tree mapping).
`ForkHistory<M: Member>` owns one `History` and one typed member; every
container in the crate is a `Member`; `Pair<A, B>` nests; the e-graph's nine
members run on one `History` through `EGraphMembers` (store traces
0.97–1.00×, `empty20k` 0.79–0.80×, saturation parity); the harnesses, the
benches and all 22 in-crate test files drive groups of one;
`tests/typed_group.rs` is the acceptance suite, including a randomized
lockstep proptest over a nested `Pair` of three columns. The deletion took
the seven composites' token API and token types, the token-only predicates,
`sync_group`, `Solo`/`SyncPair` and the e-graph wrappers' token layer: about
5,500 lines, verification **2726 verified, 0 errors**.
**Closed (2026-09-18, two further commits).** `92dab5b` put the
anti-unification search layer on one history (`AuMembers`; 62 tokens per
checkpoint became one, and its action cache's plain `Vec` became an
`AppendOnlyVec`), which unblocked `34b5a92`: the token API of `SpMap`, `Vec`
and `AppendOnlyVec` is deleted, along with the columns' embedded `Genealogy`,
its three framing lemmas and the cuts inside `restore_frame`/`reset_frame`.
Nothing in the workspace mints or validates a token outside a `History`.
Verification **2688 verified, 0 errors**; both commits lean-gated
(`scratchpad/lean_au.log`, `scratchpad/lean_cols.log`). The one piece of
hand-maintained derived state left is the exact memo's hash index, which an
`SpMap` would absorb.

**Outcome 2 — restore semantics B: done** (`2743e17`, `c23eb12`, `073e38a`;
the fused `restore_and_pop` is the SMT-LIB `pop`). Outcome 2b (a true
in-place B core) stays a milestone, not started.

**Outcome 7 — the lean per-commit gate: done and used for all ten commits**
(literal verify, the four suites, consumers under cargo-nextest, the source
checks); the full battery ran once on the final source.

**Outcomes 3, 4, 5, 6: open**, in that order, as recorded in the handoff's
"Next actions" item 8. Outcome 3's `empty20k` provenance constant was
removed by the e-graph commit as a side effect; the `aov/log` 0.92× gap and the
dyn-store residuals are untouched.
