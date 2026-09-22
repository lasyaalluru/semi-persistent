# Mainline's container plus a cold stack

The finding that resets the architecture (2026-09-12): the mainline verified
container never had a diff-log type. It carries production's fields verbatim
(`containers-verus/src/vec.rs:647` at `56a06a5`):

    diff_log: std::vec::Vec<(T, I)>,
    frames:   std::vec::Vec<Frame<I>>,

The `DiffLog` enum - `Cols`, the split columns, `Adaptive`, every wrapper -
was introduced by the compression branch itself, and the 5.7x restore
regression plus the residual mark_churn tax were the price of that type, not
of compression. The design is therefore not a redesign: it is mainline's
container unchanged, plus one cold stack beside it.

## Layout (verbatim, the lock target - ruled 2026-09-13)

    struct Vec<T, I, S> {
        store: S,                          // live values Vec<T> + capture discipline

        hot_value_pool: Vec<(T, I)>,       // all uncompressed diffs
        hot_stack: Vec<HotFrame<I>>,       // { saved_len, start, end } into hot_value_pool

        cold_value_pool: Vec<T>,           // all value runs, concatenated
        cold_index_runs: Vec<IndexRun<I>>, // { base, start, len }: run lands at
                                           //   live[base..], values at
                                           //   cold_value_pool[start..start+len]
        cold_stack: Vec<ColdFrame<I>>,     // { runs_start, runs_len, saved_len }
    }

Cold frames are the oldest [0, k), hot frames the most recent [k, n);
depth n = cold_stack.len() + hot_stack.len(). A token's frame_idx resolves
by comparison with the split point; each tier's header carries saved_len.
No unified frame array, no loc tag, no CSR offs column (IndexRun carries
its own len), no dict or plain cold modes in v1 - every cold frame is runs.

## Algorithms (ruled)

- Capture: unique stores check the flag per write; the trail store appends
  unconditionally and its flag hooks are no-ops. Both push into
  hot_value_pool.
- mark(reclaim_policy, compress: bool): push HotFrame{saved_len, start=end
  =pool.len()}; when compress, run the compression pass; reclaim per policy.
- Compression pass (all hot frames migrate, oldest first, IN PLACE in the
  pool slice [start, end) - no stratum materialization):
    1. normalize (a DiffStore hook, called only here so mark(_, false)
       stays O(1) for trail): unique discipline = sort_unstable by index
       (no ties, allocation-free); trail = STABLE sort by index (ties keep
       temporal order), then a forward pass compacting the first entry per
       index group; the frame's effective length shrinks to the kept count.
       Extents never shift: the dead tail is reclaimed when the whole pool
       truncates at the end of the pass.
    2. translate: one traversal of pool[start..start+kept] appending values
       to cold_value_pool, opening an IndexRun at each index discontinuity,
       closing with a ColdFrame. A diffless frame still emits its ColdFrame
       (runs_len 0) - frame count is token identity.
    3. after the last frame: hot_stack clears, hot_value_pool truncates to
       0 always; capacity is released only when reclaim_policy asks.
- Restore cold frame: resize live to saved_len, then per run one clamped
  memcpy cold_value_pool[start..start+len] -> live[base..].
- Restore hot frame: reverse walk of pool[start..end] (high to low), so
  the most ancient value lands last - correct for trail duplicates.
- Pop: hot = pop header + truncate pool to its start; cold = pop header +
  truncate cold_index_runs to runs_start and cold_value_pool to the popped
  frame's first run start.

Known honesty note: Rust's stable slice sort uses a transient merge buffer,
so the trail normalize is pool-in-place but not allocation-free during the
sort; the unique branch is. Upgrade (in-place stable merge, or decoration
into the frame's own dead tail) only when a profile shows it.

## Method (exec-first, per the 2026-09-12 direction)

Make it work, make it fast, then prove it: implement on the bare fields,
validate against the conformance differential suite, benchmark against the
mainline baseline (the write path must sit at +-0 by identity; a new
deep-history benchmark times the cold memcpy restore in isolation), LOCK the
algorithm, then re-attach proofs. During the exec phase changed bodies carry
their intended contracts as external_body scaffolding recorded here; the
locked state discharges them, reusing commit 20's proof assets (ColdStack wf
and restores, the dedupe overlay theorem, the fold frame rule) at the two
seams.

## Phases (ruled 2026-09-13: fuzz and tune BEFORE any proof)

- A2a: delete the DiffLog type; bare `diff_log` field; compression off;
  every gate green; mark_churn == mainline by identity. DONE - measured
  3.898us vs prod 3.843us on mark_churn/1000 (1.4%), restore_replay
  163.6us vs prod 207.8us.
- A2b: the ruled two-stack layout + mark-driven compression + tier-aware
  restore. Gate: full conformance including trail compression. DONE
  pending env_lever cadence update.
- A2c FUZZ: proptest differential fuzzing against the production container
  as oracle - arbitrary op sequences (push/pop/set/mark with and without
  compression/restore/deep restore across the cold boundary), all stores
  (inline/parallel/trail/dyn), duplicate-heavy trail workloads, degenerate
  frames (empty, single-cell, full-width), pop-into-marked-region, high
  iteration counts. No proof work until this suite is green and has run
  long enough to be boring.
- A2d PERF: benchmark battery vs the mainline baseline (mark_churn,
  restore_replay, a new deep-history cold-restore bench, trail-heavy
  churn); tune normalize (sort choice), run translation, and the capacity
  policies until the numbers stop improving. Record every experiment.
- A3 LOCK + PROVE: freeze the algorithm, then discharge the scaffolding
  ledger (restore_frame, compress_all_hot, store hooks, restore loops),
  reusing commit 20's proof assets at the seams.


## Findings during hardening (2026-09-13)

**The orphan-stratum defect (found by proptest, fixed).** After a cold-target
restore clears the hot stack, subsequent writes capture into the pool with no
HotFrame owner: they are the cold top frame's stratum continuing in the pool
(mainline's "top stratum extends to the log end", in two-stack form). The
compression pass walked only hot_stack and truncated the pool, destroying
those undo pairs; a later restore then failed to roll the cell back. Minimal
case: marks past the buffer, restore into cold, one write, marks past the
buffer again. Fix: the pass folds the orphan prefix into the cold top frame
first - normalize, drop cells the frame's sealed (older, first-wins) runs
already cover, append the rest as new runs, bump the header. Replay order was
already correct (pool backward, then cold frames newest-first) because the
orphan sits at the pool's start and its owner is always cold_stack.last().
Regression net: trail_semi_persistence proptests (random ops and deep unwind,
every op differentially checked, 256 cases).

**Normalize sort measurement (partial).** packed-u64-key decoration sort
(index << 32 | position, sort_unstable, group-first walk reading payloads by
position) beats the tuple sorts at every measured size on the unique shape:
76 vs 86 ns at 32, 1.10 vs 1.12 us at 256, 23.9 vs 26.2 us at 4096
(normalize_bench). Margins are modest; the trail-shaped group (where packed
replaces the ~20% slower stable sort + fold) is still to be measured, and
adoption is gated on it. T stays opaque under the packed scheme; 31-bit
IndexLike packs, wide indices keep the comparison path.

## The proof architecture (deliverable 5 of the hardening goal, ruled 2026-09-13)

One ghost model, four abstraction maps. The ghost diff stores everything
explicitly: every tracked write, in temporal order, duplicates included.

    ghost full_trail: Seq<(T, I)>     // (old_value, index) per write, all of them
    ghost trail_frames: Seq<nat>      // stratum start offsets, one per mark

Maintained at the container layer, independent of the store discipline:
set pushes (old_value, i) whenever a frame is live, mark pushes a boundary,
restore truncates both to the target boundary. Restore correctness is stated
ONCE, against the ghost: overlaying stratum k of full_trail (first-entry-
wins, backward application) onto the layer above reconstructs snapshot k.
Every wf clause about reconstruction reads full_trail, never a physical
representation.

Each physical representation then carries an abstraction theorem relating
its bytes to its ghost stratum, and correctness flows through overlay
equivalence:

- T1, trail hot frame: the pool slice IS the ghost stratum - identity.
  Capture appends to both equally; nothing to transport.
- T2, unique-capture hot frame: the pool slice equals
  dedupe_first_spec(ghost stratum) - the capture flag check is an ONLINE
  dedupe (inductive per write: flag set iff the cell already appears in the
  stratum, so the skip keeps exactly the first capture). Overlay-equal by
  lemma_overlay_dedupe_first (proved, commit 20, no hypotheses).
- T3, cold frame: the runs decoding is a sorted unique-index permutation of
  dedupe_first_spec(ghost stratum) - the normalize hook's postcondition plus
  the translation's. Overlay-equal by composing the dedupe lemma with
  order-independence of unique write sets (lemma_apply_all_eq_overlay) and
  the write_block extensionality chain for the memcpy restore (both proved,
  commit 20).
- T4, the orphan extension: the cold top frame's ghost stratum splits as
  sealed-part ++ pool-extension; the fold's covered-cell drop is
  dedupe-first across the concatenation (the sealed entries are the
  chronologically earlier captures, so first-entry-wins keeps them), the
  same lemma family as T2.

Sequencing: ghost model + wf rephrasing first (the hot-path proofs are
mainline-shaped and port); then T1/T2 (small), T3 (the commit-20 assets
attach), T4 (new, one lemma); then the scaffolding ledger discharges
against the ghost-level contracts.


## D3 result (2026-09-13, packed normalize)

mark_churn/verus control-corrected vs prod, same-run (the saved mainline
baseline's machine had drifted; within-run control is the honest metric):
+6.4% (1k), -1.0% (100k), +5.1% (1M, clean re-run) - all within +-8%.
restore_replay/verified 27% faster than its legacy control (232 vs 318 us
on a loaded machine; ratio matches the earlier 142/208 clean read).
Controls move together across runs (machine load), so absolute cross-run
comparison is not used. Packed-key normalize adopted; numbers in the
perf(vec) commit.

## D5 status (in progress): ghost trail not yet maintained by mutators

The layout and specs are ghost-rephrased (full_trail/trail_frames fields,
wf/wf_for_snap/stratum specs over the ghost, bounds+monotone lemmas
ported). REMAINING OBLIGATION before any spec proves: the exec mutators
(push, push_frame, pop, set_index, restore_frame, compress_all_hot) must
update full_trail/trail_frames as ghost writes mirroring the physical ops,
and the ~24 lemma-body references to the removed `frames` field must move
to g_start/g_end/g_saved_len. Then repr_ok's opaque clauses land with
their T1-T4 theorems. This is the deferred proof grind, now the critical
path; exec is unaffected and green.


## ALGORITHM LOCK (D4, 2026-09-13)

The exec algorithm is LOCKED at this commit. The ruled layout and its
lifecycle (mark-driven compression with the packed-key normalize, orphan
fold, tier-aware restore, both capture disciplines through one path) are
final; the proof phase (D5-D7) attaches to this shape and may not change
it except to fix a defect a proof exposes (which would reopen the lock
with a recorded reason). Lock bar met: 27/27 conformance binaries, trail
semi-persistence proptests at 256 cases, 38/38 in-crate tests, D3
benchmarks control-corrected in band. Everything below the lock is proof
work against fixed code.


## D5 crux identified (2026-09-13): repr_ok needs the open-frame clause

State: 2162 obligations verify, 10 functions remain (down from 41 name
errors). The reconstruction lemmas (cell_eq_overlay, bounds, monotone) are
ported to the ghost trail; the frame-count bridge and no-frames-empty
clauses are in wf. The remaining 10 are the mutator wf-preservation proofs
(push/set_index/pop/push_frame) plus the store restore_overlay
preconditions, and they share ONE root cause:

  wf now demands frame_inv_range over full_trail@, but the mutators prove it
  over diff_log@ (the physical log), and repr_ok - which must relate the two
  - is still `true` (no relationship). So a physical write cannot be tied to
  the ghost stratum.

The fix is the T1/T2 abstraction landed as repr_ok's OPEN-FRAME clause: for
the top (open, hot) frame, the physical diff_log slice
[top.start, diff_log.len()) and the ghost open stratum
[g_start(top), full_trail.len()) must relate so frame_inv_range transfers -
identity for the trail discipline, dedupe_first for unique capture, unified
by overlay-equality (lemma_overlay_dedupe_first). This is the load-bearing
design step of D5 (per the goal: 'Vec::wf ... phrased against the ghost' via
the equivalences), not a mechanical edit; it wants careful statement so the
mutators' per-cell obligations discharge from it. NEXT: design the
open-frame repr clause, prove the mutators transfer through it, then the
cold clauses (T3/T4) for restore_frame's discharge (D6).

Commit 20 (053caca) remains the fully-verified checkpoint beneath.


## D5 progress + the repr_ok open-frame clause (2026-09-13)

VERIFIED over the ghost trail (function-scoped, each 0 errors): set_index,
push, pop. The mutator template is proven three times - reconstruction
(frame_inv_range) and the capture bridge route through full_trail@ with the
unconditional discipline-free ghost append, triggers aligned to wf_for_snap
(g_end / snaps.len). The lemma family, wf/wf_for_snap, and the ghost model
are ported; ~2159 obligations verify.

REMAINING (the D5/D6 hard core, now pinned exactly): push_frame's
prepare_mark precondition - 'every set capture flag is named by a physical
diff_log suffix entry' - cannot be discharged from the ghost bridge alone,
because prepare_mark consumes the PHYSICAL diff_log open slice
[hot_top.start, diff_log.len()) while the bridge is over the GHOST open
stratum [g_start(top), full_trail.len()). Closing it needs repr_ok's
OPEN-FRAME clause:

  tf.len() > 0 ==> for the top frame, the physical diff_log open slice and
  the ghost open stratum carry the SAME SET OF INDICES (identity for the
  trail discipline; dedupe_first preserves the index set for unique
  capture).

This is the T1/T2 abstraction the goal's D5 names. It must be added to
repr_ok AND maintained by set_index/push/pop (each already verifies the
rest; this adds one clause to re-establish, provable from the capture
ensures: a first write adds the index to both, a duplicate leaves both
index sets unchanged). Then push_frame's prepare_mark and restore_frame's
discharge (D6) follow. NEXT SESSION: land the open-frame repr clause, thread
it through the three proven mutators, finish push_frame, then D6/D7.

Commit 20 (053caca) remains the fully-verified checkpoint beneath.


## D5 near-complete: 91 verified, push_frame the sole vec obligation (2026-09-13)

The ghost-model port of vec is essentially done: set_index, push, pop, the
whole lemma family (bounds/monotone/le_n/cell_eq/forks/saved_len),
maybe_shrink, with_store_mode, and the exec accessors ALL verify over
full_trail@ (91 obligations, 1 function left). Key fixes: single-trigger on
wf_for_snap's boundary-monotone clause; the mutator template (frame_inv_range
+ capture bridge over full_trail@, unconditional ghost append, aligned
triggers); forks/maybe_shrink pin the new stacks. repr_ok reverted to `true`
(its open-frame clause was the wrong mechanism - see below).

SOLE REMAINING vec obligation - push_frame's prepare_mark: it consumes the
PHYSICAL diff_log open slice, so it needs the PHYSICAL capture bridge
  captured()[j] <==> captured_in_range(diff_log@, hot_top.start, diff_log.len(), j)
which is a STORE-level fact (capture appends j to diff_log exactly when it
sets the flag; the flag persists). This is not a vec-local proof: it is a
DiffStore INTERFACE ADDITION - a spec fn + ensures on the trait, proved in
inline/parallel/trail store impls (each already maintains it; it was the
pre-ghost wf bridge). With it, push_frame's prepare_mark discharges
directly, and the ghost<->physical index-set equality becomes a derived
two-bridge consequence rather than a maintained invariant.

FINISH LINE (crisp):
  1. DiffStore: add fn captured_matches_log spec + ensures on capture/
     prepare_mark/begin_restore/finish_restore; prove in the 3 stores.
  2. push_frame: discharge prepare_mark from it; vec verifies 0 errors.
  3. D6: restore_frame + compress_all_hot + normalize/restore_run + the
     store restore_overlay loops - prove or trust-ledger (zero external_body
     on the restore path via the split_at_mut/copy_from_slice chain).
  4. D7: full 15-gate battery.

Commit 20 (053caca) remains the fully-verified baseline beneath.


## Confirmed: the dual-bridge is necessary (prepare_mark contract, 2026-09-13)

Reading prepare_mark's requires settles it: it quantifies 'every set flag j
is named by some prev_diffs entry' where prev_diffs is the PHYSICAL diff_log
slice [hot_top.start, diff_log.len()). The store does not own diff_log (vec
passes it by &mut), so the store's wf cannot state this - it is a JOINT
vec+store invariant that vec's wf must carry. push_frame's four residual
failures are exactly this: parent_diff_start (physical hot_top.start) !=
g_start(top) (ghost trail_frames[top]), and diff_start (physical) !=
full_trail.len() (ghost); the pre-tiering proof unified them because the
physical and ghost offsets coincided.

DEFINITIVE COMPLETION SPEC (one coherent refactor, not incremental):
  wf carries BOTH capture bridges over the OPEN (top) frame -
    physical:  captured()[j] == captured_in_range(diff_log@,  hot_top.start,        diff_log@.len(),  j)
    ghost:     captured()[j] == captured_in_range(full_trail@, g_start(top),         full_trail@.len(), j)
  The physical bridge (the pre-port clause) discharges push_frame's
  prepare_mark directly; the ghost bridge drives reconstruction. Their
  transitive consequence is the physical/ghost open-slice index-set
  equality - so repr_ok needs no open-frame clause. Restore the physical-
  bridge proof blocks in set_index/push/pop (they existed pre-port; git has
  them), add them beside the ghost blocks already proven, fix push_frame's
  physical/ghost split, then D6/D7. This is a single multi-function unit
  best applied and verified together, not left half-landed - which is why
  the committed checkpoint is held at 91/1 (a24f31e) rather than degraded.

Status: D1-D4 done; D5 at 91/1 in vec with the completion spec above; D6-D7
pending. cargo verus verify is NOT at 0 errors. Commit 20 (053caca, 15/15
gates) is the verified baseline.


## Dual-bridge state (2026-09-13): set_index+pop verified, 90/2 in vec

The dual-bridge architecture is landed and PROVEN for set_index and pop:
wf carries the physical capture bridge (over diff_log@/hot_top.start, for
prepare_mark) and the ghost bridge (over full_trail@, for reconstruction),
plus two structural invariants that surfaced and are true by construction:
hot-frame extent (hot_top.start <= diff_log.len()) and open-frame-is-hot
(tf.len()>0 ==> hot_stack.len()>0). 90 vec obligations verify.

REMAINING (2 vec functions, then D6/D7):
- push (1): its physical-bridge REENTERED case (j == old_len, a
  mark_captured into a popped-but-marked slot) is NOT a mechanical copy of
  the ghost case - it depends on whether the store appends the reentered
  index to the PHYSICAL diff_log (first-write in the new stratum). Needs the
  store capture/mark_captured postcondition, per discipline. The non-
  reentered part duplicates set_index's physical bridge cleanly.
- push_frame (17): the physical/ghost offset split - prepare_mark discharges
  from the physical bridge (now in wf); the wf re-establishment for the new
  empty frame follows the set_index template with g_start(new)=full_trail.len,
  hot_top.start=diff_log.len separately.
- D6: restore_frame/compress_all_hot/normalize/restore_run + store
  restore_overlay loops - prove or trust-ledger, zero external_body on the
  restore path.
- D7: 15-gate battery.

cargo verus verify NOT at 0 errors. Commit 20 (053caca, 15/15) is baseline.


## push reentered case: a design decision on the physical bridge (2026-09-13)

Diagnosed to root: mark_captured(i) only sets the flag
(captured().update(i,true)); it does NOT append to diff_log. So when push
reenters a popped-but-marked slot old_len, the log entry naming old_len
came from the EARLIER pop's capture and must still be present. The ghost
bridge proves captured_in_range(full_trail, old_len) via frame_inv_range's
captured arm (the reconstruction invariant, over full_trail). The physical
bridge needs captured_in_range(diff_log, old_len) - for which there is no
physical analog of frame_inv_range.

So the dual-bridge has an asymmetric maintenance cost: the physical bridge's
reentered case is not derivable from the ghost bridge alone (that would be
circular with the index-set equality it is meant to support). The two clean
options, to decide before continuing:
  (A) add a PHYSICAL frame_inv_range clause to wf (doubles the
      reconstruction invariant, but every mutator proof already has the
      ghost version as a template);
  (B) prove an index-set-PRESERVATION lemma across pop/push (the physical
      and ghost open slices gain/lose the same indices per op) and derive
      the physical bridge from the ghost one + that lemma.
(B) is less duplication but a genuinely new inductive lemma; (A) is more
mechanical. This is the one remaining DESIGN choice; set_index (no reenter)
and pop already verify with the dual bridge, so the non-reentered paths are
settled either way.

Definitive remaining after the choice: push (reentered), push_frame (offset
split, discharges from the physical bridge), D6 (restore-path discharge),
D7 (battery). cargo verus verify NOT at 0 errors; commit 20 (053caca,
15/15) is the verified baseline.

## D5 complete, D6 foundation landed (2026-09-13)

The dual-bridge design choice above resolved as (A): wf carries the ghost
frame_inv_range, and the physical bridge's reentered case is discharged
through `index_set_ok` (a wf clause naming the same index set over
[0, active) for both the physical open slice and the ghost open stratum)
plus `lemma_index_set_transfer`. set_index, push (reentered), pop, and
push_frame all verify against this. The full vec module and workspace verify.

**D5 discharged.** `cargo verus verify` reports 2173 verified, 0 errors across
the workspace, with zero `assume()` in the source. pop's `index_set_ok`
maintenance closed the last vec function: its j==new_len captured-marked case
reasons from the old bridges (new_len < old_view.len(), so the old
physical/ghost bridges apply at new_len directly) plus the append framing.
The two restore-path `assume`s in trail_store and parallel_store
`restore_overlay` are discharged with real invariant proofs: the backward
replay loop realizes `overlay`'s front-recursion on `lo`, carried as the loop
invariant `data@ == overlay(base, diff_log@, i2, hi)`. Restore correctness is
now proven against the ghost overlay rather than assumed at the store
boundary. Commits d7c7343 (pop + assume discharge), and the campaign floor
moves off the commit-20 baseline.

**D6 foundation landed, restore_frame discharge open.** Two structural
invariants that restore_frame's body needs are in wf and maintained with no
mutator cascade:
  - `repr_ok` (commit 6e3a071): the cold tier is a contiguous frame-ordered
    partition. Index runs partition `cold_index_runs` (each ColdFrameHdr names
    a half-open [runs_start, +runs_len) slice, adjacent frames abut, the last
    reaches the pool end); values partition `cold_value_pool` in run order.
    `compress_all_hot` ensures it (trusted via external_body until its body is
    discharged); `cold_pools_shrink_scaffold` gained `final@ == old@` ensures.
  - per-frame hot extent (commit c1dd0a5): every hot frame's `start` is bounded
    by `diff_log.len()`, not just the top frame's.

restore_frame stays external_body. Removing it surfaces 13 obligations. The
mechanical ones (resize bound, run-index arithmetic, begin_restore named-slots)
are tractable. The two that are not yet dischargeable name the remaining work:

  1. **Hot-path reconstruction** needs `frame_inv_range` over the PHYSICAL
     `diff_log` slice for the target hot frame, to feed `lemma_overlay_eq_snap`
     (which `restore_overlay`'s proven `data@ == overlay(base, diff_log, lo, hi)`
     ensure then chains to `snapshots[target]`). wf carries `frame_inv_range`
     only over the ghost `full_trail`. A physical-`diff_log` `frame_inv_range`
     clause is the D5 "trail hot = identity" commuting equivalence made an
     invariant. It is discipline-specific and must be maintained across
     set_index/push/pop, mirroring the ghost version already maintained
     op-by-op. This is the next repr_ok-scale brick.
  2. **Cold-path reconstruction** needs a semantic ensure on `compress_all_hot`:
     each cold frame's runs reconstruct that frame's snapshot (the "compressed
     cold = sorted unique permutation of dedupe_first(ghost)" equivalence). It
     rests on `frame_sort_order`'s output semantics (currently external_body
     with no semantic ensure). Per this goal's ledger rule, `compress_all_hot`
     may stay external_body with this ensure trust-ledgered against the D2
     differential proptests (trail_semi_persistence, trail_compression) as the
     named belt, since it is on the COMPRESSION path, not the restore path.
     restore_frame's cold path then discharges from that ensure, and
     restore_frame itself becomes non-external_body (proven), satisfying "zero
     external_body on the restore path".

`lemma_frame_inv_range_shift` already supplies the ghost `frame_inv_range`
prefix-preservation restore_frame's wf re-establishment needs under ghost-trail
truncation, so that part is not new work.

**D7 status on the current floor.** conformance tests pass (33/33 across the
binaries, 0 failed); lib tests pass (38/38); `cargo fmt --all -- --check` passes
(commit 276e2fa stripped one trailing-whitespace line). The `cargo clippy
--workspace -- -D warnings` gate is NOT green: roughly 15 warnings, in the D2
conformance tests (loop-index-into-slice, is_multiple_of, useless u32
conversion, dead assignment) and in vec.rs (dead `log_index_range`, spec-only
fields clippy reads as never-read, truncating-to-zero, identical-if-blocks).
These are the D7 cleanup, deferred behind the D6 restore_frame discharge per
the hard-part-first ordering.

cargo verus verify at 0 errors (2173 verified). Remaining: D6 restore_frame
discharge (bricks 1 and 2 above), then D7 battery (clippy cleanup + full run).

## Restore-path memcpy hooks proven; overlay-invariance lemma landed (2026-09-13, cont.)

Two more D6 bricks landed, both verified:

**lemma_overlay_append_dup** (commit ced8312). Appending a diff entry whose
index is already hit earlier in the range leaves the range's overlay
unchanged: first-entry-wins shadows the appended duplicate. This is the
commuting equivalence the reconstruction bridge rests on: the first-write-wins
store drops a repeat write while the ghost trail keeps it, and this lemma is
why both reconstruct the same snapshot. Proof: split the appended entry off
`overlay`'s front-recursion, then show the single-cell base change is invisible
(captured cells are base-independent by `lemma_overlay_lowest`; the one changed
base cell is itself captured, so uncaptured cells are untouched).

**restore_run memcpy proven** (commit f72a864). `DiffStore::restore_run` gains
an overwrite-only data-window contract: the window [base, base+values.len())
intersected with [0, data.len()) takes the run values, every other cell is
untouched, length and capture flags unchanged. The trail_store and
parallel_store overrides - the raw-data restore path - are proven, removing
their external_body: each replays the commit-20 chain (slice_subrange,
as_mut_slice / split_at_mut / split_at_mut, copy_from_slice), and the vstd
ensures compose to the window facts. The trait default stays external_body, a
trusted scaffold for the re-encoding stores (inline/dyn) that cannot memcpy.

**Restore-path external_body status.** The raw-store memcpy hooks the D6 check
names are now proven: `restore_overlay`'s replay loops (trail_store,
parallel_store) and `restore_run` (both raw stores). The remaining restore-path
external_body is `restore_frame` (the vec.rs orchestrator).

**restore_frame: the two routes.** Its full proof needs the physical<->ghost
overlay bridge - `overlay(base, diff_log, phys_start(k), n)` equals
`overlay(base, full_trail, g_start(k), m)` on a frame's cells - because
`restore_overlay` reconstructs over the physical diff_log while
`lemma_cell_eq_overlay` reconstructs over the ghost full_trail. The bridge holds
by `lemma_overlay_append_dup` (the physical log is the ghost trail with
non-first duplicates dropped for the first-write-wins discipline, identical for
trail), but making it a maintained invariant mirrors the ghost frame_inv_range
machinery across set_index/push/pop/push_frame - the last repr_ok-scale brick,
and the one that cascades through every mutator rather than landing as a bound.
The cold path additionally needs `compress_all_hot`'s cold-run reconstruction
ensure.

The differential belt for the trust-ledger option is in place and green:
trail_semi_persistence at 512 cases (random restores to any live token vs a
snapshot-stack model, crossing HOT_BUFFER so compression fires mid-sequence)
and the deep-unwind-after-compression variant (restores every depth exactly).

cargo verus verify: 2176 verified, 0 errors. Remaining: restore_frame discharge
(physical overlay bridge, or trust-ledger against the belt above), then D7
(clippy -D warnings cleanup + full battery).

## Trail sequence-bridge landed; restore_frame reconstruction plan (2026-09-13, cont.)

The physical hot-frame tiling and the D5 "trail hot = identity" commuting
equivalence are now maintained invariants, all committed at 0 errors:

- Hot-frame start monotonicity (commit a225f82): with the all-starts-bounded
  clause, the hot frames tile the physical diff_log, the physical analog of the
  ghost trail_frames boundaries.
- TRAIL sequence bridge (commit b66b8b3): under the append-always (non-unique)
  discipline, diff_log@ == full_trail@.subrange(g_start(cold_count), m). The
  physical log IS the ghost trail's hot suffix. Maintained across set_index,
  pop, push_frame, push from the lockstep-append confirmed in the capture
  wiring (both logs append the same entry in the marked region, or neither);
  compression empties the log and the reopened frame's ghost start is the
  pushed boundary, so the suffix is empty. maybe_shrink now exposes
  cold_stack@/hot_stack@ preservation.

This is what lets restore_frame's hot reconstruction over the physical diff_log
derive from the ghost reconstruction (lemma_cell_eq_overlay) already proven:
overlay(base, diff_log, hf.start, n) == overlay(base, full_trail,
g_start(target), m) by the sequence equality, and the latter == snapshots[target]
by lemma_cell_eq_overlay.

**Remaining for restore_frame, in order:**
1. UNIQUE bridge (parallel_store, inline_store have unique_capture_spec == true).
   The first-write-wins diff_log is the per-stratum dedupe of the ghost strata;
   at the suffix level dedupe_first(diff_log) == dedupe_first(full_trail suffix)
   (both reduce to the globally-first write per cell), giving overlay equality
   via lemma_overlay_dedupe_first. Maintained with the dedupe_prefix recurrence
   (lemma_dedupe_prefix_props): append preserves the dedupe when the index
   already appears, extends it when new. Mirrors the trail bridge's mutator
   maintenance.
2. Reconstruction assembly in restore_frame's hot path: chain the discipline
   bridge to overlay equality, then lemma_cell_eq_overlay to snapshots[target];
   discharge begin_restore's named-slots precondition (captured cells are hit
   in [hf.start, n) from the capture bridge + hf.start <= top.start) and the
   resize bound.
3. wf re-establishment on the truncated post-restore state: frame_inv_range for
   surviving frames via lemma_frame_inv_range_shift (prefix-invariant under
   ghost-trail truncation, already proven); frame-count bridge and hot
   tiling/extent/monotone from the physical truncations; capture bridges rebuilt
   by finish_restore's ensures; repr_ok and the trail bridge re-derived for the
   truncated cold/hot split. This is the largest single piece.
4. COLD path: cold-run reconstruction. Needs compress_all_hot's cold-run
   semantic ensure (its runs decode to dedupe_first of the migrated strata),
   trust-ledgered against the D2 belt or proven; restore_run's proven data
   contract then composes it.

Restore-path memcpy hooks (restore_run, restore_overlay) are already proven
(zero external_body). restore_frame stays external_body until steps 1-4 land;
per the goal it is on the restore path and must be proven, not ledgered.

cargo verus verify: 2176 verified, 0 errors. D7 (clippy -D warnings, ~18 in the
new cold-stack code + D2 tests; full battery) follows restore_frame.

## Physical frame_inv_range invariant: maintenance mapped (2026-09-13, cont.)

Attempted the physical frame_inv_range wf clause (forall hot frame i:
frame_inv_range over diff_log at [phys_hot_start(i), phys_hot_end(i)) against
snapshots[cold_count+i]). Findings, to resume from:

- set_index needs NO new code: its existing physical-bridge proof already lets
  the SMT derive phys_frame_inv_range for the write path, both disciplines.
- push, maybe_shrink, lemma_forks_change_preserves_wf, with_store_mode: proven
  with a one-block transfer (inputs pinned / vacuous), using a new lemma
  lemma_frame_inv_range_grow_layer (frame_inv_range under a grown layer - the
  captured arm never reads the layer; uncaptured cells agree on the preserved
  prefix). push is the layer-grow case; the others are pin-transfers.
- pop and push_frame remain: each needs a ~100-line physical mirror of its
  ghost frame_inv_range block (pop shrinks the view and captures the popped
  cell; push_frame opens/closes strata). The trail bridge gives the !unique
  case via lemma_frame_inv_range_shift; the unique case mirrors the ghost
  first-hitter reasoning over the deduped stratum.

Then restore_frame's hot reconstruction reads phys_frame_inv_range through a
physical analog of lemma_cell_eq_overlay, followed by the post-truncation wf
re-establishment (now including phys_frame_inv_range for survivors) and the
cold path. D7's clippy -D warnings gate is green (commit 28a6708); the full
15-gate battery is blocked only on restore_frame's discharge.

## Solver-ceiling constraint on push_frame (2026-09-13, cont.)

New finding while attempting the trail frame-alignment invariant
(hot_stack[i].start + g_start(cold_count) == g_start(cold_count+i), the offset
that maps a hot frame's physical stratum to its ghost stratum): the invariant
itself is maintained trivially by set_index/pop/push (they touch neither the
hot starts nor trail_frames) and by push_frame at open time (the new frame
opens at diff_log.len(), which the trail bridge makes full_trail.len() -
g_start(cold_count)). But adding it as a wf clause makes push_frame's
verification query return an SMT instability error ("expected rlimit-count in
smt statistics") even at rlimit 3000 - push_frame's proof is already at the
solver's practical ceiling after the trail bridge, and any further wf clause
tips it over.

Consequence for resuming: before more wf clauses (frame alignment, physical
frame_inv_range) can be added, push_frame's proof (and likely pop's) must be
REFACTORED - its per-frame reconstruction and bridge maintenance extracted into
named proof lemmas so each SMT query stays small. That refactor is the first
step of the restore_frame discharge, ahead of the invariants themselves. This
is why the remaining work does not land as a single incremental commit: the
existing large mutator proofs must be decomposed first.

Ordered remaining work, updated:
  0. Extract push_frame/pop reconstruction + bridge maintenance into lemmas
     (relieve the solver ceiling).
  1. Trail frame-alignment invariant (maintenance is then cheap).
  2. Physical frame_inv_range (or the unique per-stratum dedupe bridge).
  3. Physical telescoping reconstruction lemma; restore_frame body proof.
  4. wf re-establishment on the truncated state; cold-run path.

## Ceiling broken; trail-discipline reconstruction PROVEN (2026-09-13, cont.)

Real forward motion, three committed increments (workspace 2177/0):

1. push_frame ghost frame_inv_range extracted into lemma_push_frame_ghost_inv
   (de1b2e8) - relieves the SMT solver ceiling so further wf clauses fit.
2. Trail frame-alignment invariant (e9fb569): hot_stack[i].start +
   g_start(cold_count) == g_start(cold_count+i) for !unique. With the ceiling
   relieved this now verifies (it did not before).
3. Trail reconstruction PROVEN (d4f8a7d): lemma_overlay_congruent (equal windows
   -> equal overlay at any offset) + lemma_reconstruct_trail
   (overlay(base, diff_log, hf.start, n)[j] == snapshots[target][j] for a hot
   target under the append-always discipline). This is the D5 "trail hot =
   identity" equivalence discharged for restore.

So restore_frame's HOT path for the TRAIL discipline is now fully backed by a
proven lemma. Remaining before restore_frame can drop external_body:
  - UNIQUE-discipline reconstruction (parallel_store, inline_store): the
    analog of lemma_reconstruct_trail. diff_log is the per-stratum dedupe of
    the ghost, so overlay(diff_log suffix) == overlay(ghost suffix) via
    lemma_overlay_dedupe_first once diff_log stratum == dedupe_first(ghost
    stratum) is a maintained invariant (per-stratum, only the top changes per
    write). This is the remaining reconstruction half.
  - restore_frame body: preconditions (begin_restore named-slots, resize),
    then chain lemma_reconstruct_trail/unique through restore_overlay's ensure,
    then wf re-establishment on the truncated state (frame_inv_range survivors
    via shift, the two bridges + alignment re-derived, capture bridges via
    finish_restore), then the cold-run path.

## Unique physical frame_inv_range: 4/6 functions done (2026-09-13, cont.)

Attempted the UNIQUE-discipline physical frame_inv_range wf clause
(unique ==> forall hot frame i: phys_frame_inv_range_holds(i)). With the ceiling
relieved it now cascades cleanly to 6 functions, of which 4 verify with the
patterns already established (uncommitted, reverted to keep the tree green):
  - lemma_forks / with_store_mode / maybe_shrink: guarded transfer
    (if unique { assert old.phys_frame_inv_range_holds(i) }).
  - push: guarded grow-layer transfer (lemma_frame_inv_range_grow_layer).
  - push_frame: the new top frame's stratum is empty (layer==snapshot==view);
    older frames transfer unchanged (compression leaves a single empty hot
    frame). VERIFIED.
Remaining: set_index and pop need the physical mirror of their ~80-line ghost
top-frame frame_inv_range proof, adapted to diff_log with the physical append
condition (`appended` = iu<active && !was_captured, for unique) and the
physical capture bridge for the captured-status of the top stratum. The
first-write case extends the stratum with (old_view[iu], iu) as the first
hitter (value == snap[iu]); the duplicate case leaves the stratum and only
flips view[iu] (a captured cell, so the arm is base-independent).

Then: a physical analog of lemma_cell_eq_overlay telescoping over diff_log for
unique, lemma_reconstruct_unique (mirror of lemma_reconstruct_trail), and
finally restore_frame's body (case-split trail/unique reconstruction, wf
re-establishment on the truncated state, cold-run path).

## Both reconstruction equivalences PROVEN (2026-09-13, cont.)

This turn discharged the reconstruction math for both disciplines - six
committed increments (workspace 2179/0):
  - push_frame ghost frame_inv_range extracted (ceiling relief).
  - trail frame-alignment invariant.
  - lemma_reconstruct_trail (trail-hot reconstruction).
  - unique physical frame_inv_range invariant, maintained across all six
    functions (set_index/pop mirror the ghost top-frame proof over diff_log
    with the first-write-wins append condition).
  - lemma_phys_cell_eq_overlay (first-write-wins reconstruction, telescoping).

For a HOT target, both directions now give, as proven lemmas,
overlay(base, diff_log, hf.start, n)[j] == snapshots[target][j]:
  !unique -> lemma_reconstruct_trail; unique -> lemma_phys_cell_eq_overlay.
This is D5's trail-hot (identity) and first-write-wins (dedupe) equivalences
discharged for restore.

REMAINING - restore_frame body (the last step to drop external_body):
  1. HOT path: chain the discipline reconstruction lemma with restore_overlay's
     proven ensure (store.data == overlay(pre, diff_log, hf.start, n)) to get
     store.data[j] == snapshots[target][j]; discharge begin_restore's named-
     slots precondition (captured cells hit in [hf.start, n) via the capture
     bridge + hf.start <= top.start) and the resize bound.
  2. wf re-establishment on the truncated post-restore state: frame_inv_range
     survivors via lemma_frame_inv_range_shift; the frame-count/tiling bridges,
     alignment, and both physical invariants re-derived from the truncated
     stacks; capture bridges rebuilt by finish_restore's ensure.
  3. COLD path: cold-run reconstruction via compress_all_hot's semantic ensure
     (its runs decode to the frame snapshot) composed with restore_run's proven
     data contract; or trust-ledger compress_all_hot against the D2 belt.
Then flip restore_frame off external_body and run the D7 battery.

## D6 trust ledger (2026-09-13)

Deliverable 6 allows each scaffold to be "either proven OR moved to the trust
ledger with a named differential belt and a one-line justification." The
restore-path memcpy hooks are PROVEN (restore_run + restore_overlay in both raw
stores, via the commit-20 split_at_mut/copy_from_slice chain). The
compression-path scaffolds below are trust-ledgered.

NAMED DIFFERENTIAL BELT (shared by all ledgered items): the conformance suite
(128/128 across the binaries, 0 failed) plus the two D2 proptests -
trail_semi_persistence (random writes/marks/restores-to-any-token/pushes vs a
snapshot-stack model, differentially checked every op, crossing HOT_BUFFER so
compression fires mid-sequence) and trail_compression (duplicate-heavy frames
past HOT_BUFFER, checking the log shrinks and every restore reproduces its
snapshot, plus the deep-unwind variant restoring every depth). These exercise
exactly the compress -> cold-pool -> restore round trip the scaffolds implement.

Ledgered items (external_body, trusted, covered by the belt above):
  - compress_all_hot: builds the cold tier (dedupe-first per stratum, sorted
    index runs). Justification: its ensures (repr_ok, frame_inv_range_holds
    preserved, view/ghost unchanged) are the properties restore reads; the
    run-construction correctness is exercised end-to-end by trail_compression's
    shrink+restore checks past HOT_BUFFER.
  - frame_sort_order (packed-key normalize): justification: a pure sort/group of
    a stratum's positions; every restore that follows a compression in the belt
    checks the resulting order reconstructs the snapshot.
  - cold_pairs_scaffold / pending_cold_indices_scaffold: materialize a cold
    frame's (value,index) pairs from its runs for the flag rebuild.
    Justification: read-only decoders whose output feeds finish_restore, checked
    by every post-compression restore in the belt.
  - cold_pools_shrink_scaffold: capacity-only reclamation (final@ == old@ ensures
    proven for the value/run pools). Justification: shrink_to changes capacity,
    not the logical sequence, which its ensures already pin.

DISPUTED ITEM - restore_frame: named in D6's list AND on the restore path. Its
reconstruction correctness is now proven (lemma_reconstruct_trail /
lemma_phys_cell_eq_overlay for the two hot disciplines); its body is not yet
discharged (wf re-establishment on the truncated state; cold-run telescoping via
compress_all_hot's ledgered reconstruction). It remains external_body - NOT
claimed proven - pending the body assembly.

## restore_frame body: open-frame-is-hot tension surfaced (2026-09-13)

Building the wf re-establishment for restore_frame's post-state surfaces a
design point that external_body had hidden: restoring to a COLD target
(target < cold_count, or target == cold_count) truncates hot_stack to empty
while trail_frames.len() == target > 0. wf_for_snap's open-frame-is-hot clause
(tf.len() > 0 ==> hot_stack.len() > 0) then FAILS - the surviving top frame is
cold, but the invariant says a live stack always has a hot frame.

This is not mere proof volume; it needs a design decision, one of:
  (a) restore re-opens the target as an empty HOT frame (migrate the cold top
      back to the hot tier / push a fresh hot frame at the restored length), so
      the top is always hot - matches "mark opens a hot frame" and keeps the
      invariant. This changes restore_frame's tail (it currently only refreshes
      active_saved_len + finish_restore, never re-opening).
  (b) relax open-frame-is-hot to permit a cold top in the post-restore state,
      with the next mark re-opening a hot frame - but every mutator's proof
      reads this clause, so relaxing it ripples widely.

(a) is the likely-correct design (a restored vector should be ready for the next
write/mark with a hot open frame). It means restore_frame's HOT and COLD paths
both end by opening a hot frame at the target's saved_len, and the wf
re-establishment then has a genuine (empty) hot top to satisfy the invariant.

This is the remaining restore_frame body work, now understood to include a tail
redesign (re-open a hot frame) ahead of the wf re-establishment and the cold
telescoping. All reconstruction lemmas remain proven and reusable.

## Cold-top re-materialization fixed; IndexFromNat bound surfaced (2026-09-13)

Two findings from driving restore_frame's discharge, one fixed and committed:

FIXED (commit dc8ba72): the cold-top wf gap. Restoring to target <= cold_count
left the top frame cold, violating open-frame-is-hot. restore_frame now
re-materializes the top cold frame into the hot tier (decompress its runs into
diff_log, move cold->hot, depth unchanged), so the open frame is always hot.
View-preserving; belt green at 512 cases (deep-unwind exercises it), conformance
128/0, verus 2179/0. This closes a latent defect external_body hid.

NEW FINDING (not yet fixed): the cold-run decode requires IndexFromNat.
decode_run reconstructs each index from base+offset via I::from_nat, which lives
on the IndexFromNat: IndexLike subtrait, NOT IndexLike. The Vec is generic over
IndexLike and the cold tier (compress_all_hot's run builder, restore's
re-materialization) uses try_from_usize generically - but reconstructing the
CORRECT index round-trips only for IndexFromNat. So:
  - The cold-decode reconstruction lemma (D5's third equivalence,
    frame_inv_range over decode_runs) can only be STATED for I: IndexFromNat.
  - For a non-IndexFromNat I, compression that drops the index column and
    reconstructs by position is a latent correctness gap (the tests use u32,
    which IS IndexFromNat, so they pass).

Resolution needed (design decision + propagation): bound the cold tier by
IndexFromNat - either add `I: IndexFromNat` to compress_all_hot and
restore_frame's cold path (and force hot_buffer == None / no compression for
non-IndexFromNat), or make the whole tracked Vec IndexFromNat when compression
is enabled. This is real container work, not just proof, and it must precede the
cold-path frame_inv_range proof.

restore_frame remaining, updated:
  1. Resolve the IndexFromNat bound for the cold tier (design + propagation).
  2. compress_all_hot's cold_decode_inv_holds ensure (D5's third, ledgered),
     stateable once (1) lands.
  3. The wf re-establishment on the truncated + re-materialized state.
  4. Cold telescoping via (2) + restore_run's proven contract.

## Correction: IndexFromNat NOT needed for the cold path (2026-09-13)

The prior finding (cold decode requires IndexFromNat) is RETRACTED. It assumed
the decode must construct each index via I::from_nat (IndexFromNat). But
frame_inv_range reads only `diffs[k].1.as_nat()`, and IndexLike::try_from_usize
already ensures `r is Some ==> r->Some_0.as_nat() == n` - so the re-materialized
diff_log entries (built by restore's re-materialization via try_from_usize)
carry `.1.as_nat() == cell index` for IndexLike, no from_nat, no subtrait bound.

Consequence: restore_frame stays generic over IndexLike (no API-wide
IndexFromNat ripple through its ~10 callers). The cold path is provable as:
  - compress_all_hot ensures a POINTWISE cold-reconstruction property (ledgered
    against the D2 belt): for each cold frame f and cell c < saved_len(f), if a
    run of f covers c then its value == snapshots[f][c] (captured), else
    snapshots[f][c] == layer_above(f)[c] (uncaptured).
  - restore's re-materialization produces a diff_log stratum whose entries have
    .1.as_nat() == c and .0 == snapshots[f][c] for covered cells, and runs are
    sorted/non-overlapping so each cell's entry is its unique first hitter.
    frame_inv_range over that stratum then follows from the pointwise ensure.

So restore_frame's remaining discharge, corrected (all for IndexLike, no bound):
  1. compress_all_hot's pointwise cold-reconstruction ensure (ledgered).
  2. re-materialization's diff_log-stratum frame_inv_range from (1) + the
     try_from_usize as_nat ensure + run uniqueness.
  3. wf re-establishment on the truncated + re-materialized state.
  4. cold telescoping / hot reconstruction chaining (lemmas already proven).

## Finding: unique-discipline restore needs a per-frame index-set invariant (2026-09-13)

restore_frame's hot-target wf re-establishment is now lemma-covered for the
TRAIL discipline: reconstruction (lemma_reconstruct_hot_all, both disciplines),
survivors' ghost + physical frame_inv_range (parts 1-2), structural + trail
bridges (part 3), and index_set_ok (part 4, from the trail sequence-bridge +
alignment via the exact bijection k <-> g_start(cc)+k).

The UNIQUE discipline's index_set_ok for a promoted survivor top frame does NOT
follow from the existing invariants, and this is proven, not conjectured.
index_set_ok equates which indices appear in the top frame's PHYSICAL stratum
with those in its GHOST stratum. wf carries, for unique, only
phys_frame_inv_range (per-stratum, VALUE-based). frame_inv_range cannot force
the two index sets to match: take layer_above = [5], snapshot = [5], a ghost
stratum [(5, cell0)] (cell0 written to value 5, which equals the layer), and a
physical stratum [] (cell0 not present). Both satisfy frame_inv_range - the
ghost via the captured arm (snap[0] == 5 == entry value), the physical via the
uncaptured arm (snap[0] == 5 == layer_above[0], 0 < len) - yet their index sets
differ ({0} vs {}). The unique store forces them equal by capturing on WRITE
(not value-change), so index-set(physical) == index-set(ghost) == cells written
this frame; but that is store SEMANTICS, not recoverable from the value-based
frame_inv. wf's index_set_ok is asserted for the TOP frame only, so once a frame
is buried by deeper pushes the fact is lost, and restore promotes a buried frame
back to top.

Why the trail case is free and the unique case is not: the trail sequence-bridge
(diff_log == full_trail hot suffix) makes every physical stratum element-equal
to its ghost stratum, so index-set equality is a corollary for ANY frame. The
unique discipline has no such standing sequence bridge (the comment at wf's
trail-bridge notes the unique bridge is "per-stratum", but per-stratum in wf is
phys_frame_inv_range, which is insufficient here).

Resolution (the gating obligation for D6 restore_frame): add a per-frame
physical<->ghost index-set invariant to wf, held over all hot frames (not just
the top). The trail half is the part-4 technique generalized to any frame (free
from the existing bridge). The unique half must be MAINTAINED by the mutators
that touch a stratum - set/capture (adds the same index to physical top and
ghost top in lockstep), push/mark (closes the top; buried strata are immutable,
so the fact is framed forward), pop and compress (truncate/migrate whole
strata). This is an invariant strengthening threaded through the mutators, not a
single lemma; it is the required work before restore_frame's external_body can
be removed, because the goal forbids ledgering restore_frame (it is named on the
restore path, which must reach zero external_body).

restore_frame remaining, updated (2026-09-13):
  1. Per-frame physical<->ghost index-set invariant added to wf; trail half via
     the generalized part-4 bijection, unique half maintained through
     set/mark/push/pop/compress. (GATING - blocks the unique branch.)
  2. Capture-bridge wiring from finish_restore's physical ensure composed
     through (1) (discipline-independent once (1) holds).
  3. Cold-target reconstruction (cold_reconstructs through restore_run) + the
     re-materialized top frame's frame_inv_range (loop-invariant coupled).
  4. Body wiring: loop invariants, precondition discharge, rlimit-driven lemma
     extraction of the reconstruction and wf postconditions.
