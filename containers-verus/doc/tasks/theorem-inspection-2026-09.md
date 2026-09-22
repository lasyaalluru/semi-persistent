# Theorem inspection: the semi-persistence proof surface, September 2026

A full inspection of what `containers-verus` proves, what it trusts, and where
the perimeter has gaps, taken after the store-selection campaign
(`spvec-compression` through commit `9f55448`). Three sweeps produced the raw
inventories (reconstruction core; genealogy and aggregates; stores and trust
surface); this document is the synthesis and the ranked findings. Every claim
names a file and line at the inspected revision.

## 1. What is proved: the theorem map

### 1.1 Reconstruction (vec.rs, diff_log.rs) — the unconditional core

The restore theorem is `Vec::restore_frame` (vec.rs:3811): `wf` preserved,
`view() == old snapshots[target]`, depth drops to `target`, snapshot stack
truncates. It is discharged cell-by-cell by the central lemma
`lemma_cell_eq_overlay` (vec.rs:1655), a downward induction over frames whose
captured arm is pinned by `lemma_overlay_lowest` (vec.rs:245): the
lowest-position hitter of a cell wins under the reverse replay. The invariant
vocabulary is `frame_cell_inv` (vec.rs:696) in FIRST-HITTER form plus the
coverage clause for popped cells, and `frame_inv_range` (vec.rs:744).

The reconstruction core is DISCIPLINE-UNCONDITIONAL: none of it assumes
one-entry-per-cell strata, which is what makes the chronological trail store
sound with zero extra hypotheses. `stratum_unique` (vec.rs:730) lives only in
a `wf` clause gated on `unique_capture_spec()` (vec.rs:1319) and is consumed
only by the sealing and reordering entries.

Totality wrappers carry the negative half: `try_restore`/`try_mark`
(vec.rs:2233/2197) prove that a rejected token or refused mark changes
NOTHING, and `is_valid_token` (vec.rs:2292) returns exactly the restorability
predicate. The untracked family (vec.rs:1767-1830) proves observational
equivalence to `std::Vec` while untracked.

### 1.2 Compression (diff_log.rs, diff_compress.rs, value_compressor.rs)

The codec contract is one obligation: `decode(encode(d))` carries the same
write multiset (`lemma_multiset_eq_overlay`, vec.rs:377), lifted to `Vec::wf`
by the multiset frame rule (`lemma_frame_inv_range_multiset` vec.rs:836,
`lemma_diff_log_rep_change_preserves_wf_multiset` vec.rs:1467). Order-
preserving codecs prove exact sequence equality instead. The three fold
entries (`compact_tail_sorted`, `compact_adaptive`, `compact_adaptive_copy`,
diff_log.rs:1011/1159/1240) all REQUIRE `unique_idx` of the folded region,
which is exactly the discipline-gated wf clause; `compress_frame`
(diff_compress.rs:1236) instead probes uniqueness at runtime and falls back,
so Auto mode carries no precondition. The forward-restore fast path is sound
by `lemma_apply_all_eq_overlay` (vec.rs:1013): forward equals backward on a
unique-indexed frame. `ValueCompressor::compress` (value_compressor.rs:48) is
deliberately EXACT (sequence equality), which keeps the layered selector
correctness-invisible: whichever candidate wins, its own contract restores.

### 1.3 Stores (diff_store.rs and the four implementations)

The trait's capture contract is a three-way outcome (diff_store.rs:280-327):
first write appends and flags; out-of-frame is a no-op; already-captured
splits on the discipline (unique no-ops, chronological appends the inert
duplicate). Since the store-selection campaign, the discipline is an INSTANCE
property with a constancy ensures on all 14 mutating methods: chosen at
construction, provably immutable. `InlineStore` proves the packed-tag
representation (flags cost zero memory, sparse O(diffs) clears);
`ParallelStore` proves the lazy bitmap view-equivalence (`tail_clear` makes a
push's flag extension free) over the fully verified `capture_bits.rs` (bit
lemmas down to shift/mask level); `TrailStore` proves the ghost-flag protocol
(exec no-op frame operations); `DynStore` proves delegation with the
discipline a function of the never-mutated discriminant.

### 1.4 Genealogy and aggregates (history.rs, gen_stamps.rs, union_find.rs, eclasses.rs, sync_group.rs)

`History::is_valid` (history.rs:112) equals validity exactly (token forgery
rejection); `lemma_bump_invalidates` (gen_stamps.rs:165) proves the O(1)
branch cut BOTH ways: everything at or above the cut dies, everything below
is untouched. `Solo`/`SyncPair`/`ForkHistory` (history.rs:150/223,
sync_group.rs:197) prove the group composition: one token restores every
member to its snapshot, with the fan-out loop invariant carrying the split
state. On the union-find: `find` (union_find.rs:588) proves path compression
is observationally neutral; `union` proves the exact `merge_roots` map;
`restore` (union_find.rs:1409) proves the partition rolls back exactly and
the abandoned archive is physically truncated. `EClasses::merge_with`
(eclasses.rs:1583) proves the aggregate merge across five components with
`num_classes` decreasing by exactly one, and `frames_agree` (eclasses.rs:3102)
states the nine-way frankentoken defense as an iff.

Zero `assume`, zero `admit`, zero `#[verifier::external]` anywhere in src.

## 2. The trust surface: measured, and the ledger is stale

Actual `#[verifier::external_body]` in the default build: **72** (plus 5
gated behind `literal-types`). `doc/design/02-trust-boundary.md` documents 27
and `.github/workflows/verus.yml:146` pins `EXPECTED_DEFAULT=27`. **The gate
built to catch quiet TCB growth has been failing (or not running) through
the compression and store-selection campaigns**, and about 45 markers are
undocumented. Composition of the 72:

- 42 are spec-free diagnostics (byte counters over unmodeled
  `capacity`/`size_of`, saturating stats, env levers, shadow-log I/O, enum
  names). They carry no ensures and can affect no theorem.
- The contract-carrying remainder groups into: bit packing (`pack_codes`/
  `packed_get`), unmodeled std structures (`assign_codes`, `is_unique_idx`,
  the map key-model items), raw slice copies (`restore_runs_into`,
  `RunCol::restore_to`), std capacity facts (`shrink_*`,
  `data_capacity_bits`), the bplus layout primitives, `guard::
  check_precondition`, the hasher axiom (mirroring vstd's own), and
  `GenStamps::bump_from` (wrapping_add distinctness; ABA at 2^64 restores,
  documented).
- The two largest semantic gaps between a trusted body and its assumed
  contract are `sync_group.rs:362/403` (`mark_parallel`/`restore_parallel`):
  full sequential contracts assumed across a rayon fan-out, justified by a
  prose disjointness argument and one differential test. Their self-label
  ("trust ledger group B") also misuses the ledger taxonomy.

## 3. The perimeter gaps, ranked

**G1 — the proof forest is entirely unspecified.** `explain`,
`explain_with_lca`, `record_proof_edge`, `reroot_proof`, `union_justified*`,
`merge_justified*` all sit outside `verus!` (union_find.rs after 1685,
eclasses.rs after 3424) with NO contracts: nothing proves the returned steps
are sound, complete, or acyclic, and `restore` does not export what the
restored forest satisfies (the content equality is proved internally at
union_find.rs:1485 but not in the ensures; wf's proof arm is length-lockstep
only). This is not hypothetical: BOTH latent defects this campaign surfaced
(the explain_deep congruence cycle, egraph commit 4819d7d; the conflict-
antecedent unsoundness fixed earlier in sundance) lived exactly in this
unspecified layer. Largest-value verification target in the codebase.

**G2 — ledger and CI gate stale** (section 2). The fix is a ledger update
campaign: document the 45, reclassify the two rayon fan-outs into their own
group with the disjointness argument stated as the trusted claim, then
re-pin the workflow count.

**G3 — the hashcons hint index is outside the perimeter.** Now feasible to
bring in: the index has no removal, no rebuild, no restore path, so the
obligations reduce to probe soundness (content compare against the verified
arena) and the completeness invariant (every live node's content findable —
today a debug oracle only), plus three compaction-droppability lemmas whose
informal arguments ("no live mark can revive it") are already theorem-shaped.
Realistic form: a `ContentIndex<T, I>` in containers-verus beside the arena,
with hashbrown behind an axiomatized model (`Map<u32, Seq<I>>`) in a named
trust group.

**G4 — small contract asymmetries.** `EClasses::is_valid_token`
(eclasses.rs:3090) has no ensures where `UnionFind::is_valid_token`
(union_find.rs:1374) proves exactness; `class_size` (eclasses.rs:2610) does
not export the W7 ring-length equality it maintains; `EClasses::try_restore`'s
Ok case exports no view equation. Cheap fixes, each a one-clause ensures plus
a proof nudge.

**G5 — restore's proof-forest silence** (the exportable half of G1): adding
the already-proved `parent_proof == archived frame` equality to
`UnionFind::restore`'s ensures is nearly free and would give the unverified
explain layer a stated foundation to stand on.

## 4. Recommended order

1. G2 ledger repair (mechanical, restores the guardrail).
2. G4+G5 quick ensures (small verify waves, immediate contract value).
3. G3 ContentIndex (bounded new-code campaign, kills the debug-oracle gap).
4. G1 proof-forest specification (the real prize: contracts for
   `record_proof_edge`/`explain` at minimum stating soundness of steps
   against a ghost union log; acyclicity next). Sized as its own goal.
