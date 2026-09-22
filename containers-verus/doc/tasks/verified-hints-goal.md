# Goal: discharge the critical trusted surface and verify the hinted arena

Two outcomes, both BUILT (verified artifacts, not designs):

1. **Discharge wave**: the contract-carrying campaign-added `external_body`
   items from `external-body-audit-2026-09.md` section 2.3 become proofs
   where a proof is possible, and the remainder get their honest minimal
   ledger form. Target state per item:
   - PROVE (drop the marker): `bump_from` (wrapping distinctness is a
     theorem, not an axiom), `adaptive_len_exec` (bound in `DiffLog::wf`),
     `decode_exec_i` (mirror the loop), `pack_codes`/`packed_get`
     (bit_vector, capture_bits style), `sort_frame_by_index` (verified
     insertion sort), `is_unique_idx` (adjacent scan over the verified
     sort), `assign_codes` (sort-dedup dictionary construction, no HashMap),
     `restore_runs_into`/`RunCol::restore_to` (verified per-element loops;
     if the memcpy delta measures, the fallback is recorded with numbers,
     not defaulted).
   - KEEP, minimized and honestly grouped: `mark_parallel`/
     `restore_parallel` (the trusted claim narrowed to the rayon iteration
     semantics over verified per-member bodies; new ledger group).

2. **The hinted arena enters the perimeter**: a verified
   `HintedArena<T, I>` in containers-verus combining a semi-persistent
   column (`VecD`) with a verified no-deletion fingerprint index (open
   addressing over plain vectors; no hashbrown, no external model). Its
   contract is the collision theorem the e-graph needs:
   - `probe(t) == Some(id)  ==>  view[id] == t` (soundness), and
   - `probe(t) == None      ==>  forall id < len: view[id] != t`
     (**completeness: a collision cannot be missed**),
   - both preserved by push, set (capture + re-hint), **and restore with
     ZERO index maintenance** - the history-completeness invariant
     (every snapshot cell's content is hinted, hints are never removed
     while revivable) makes the post-restore completeness a theorem, not
     an oracle.
   Fingerprints are an abstract deterministic function (a spec-carrying
   trait); correctness never depends on their values, only their
   determinism, so the router is swappable.

Acceptance (all runnable):
- `cargo verus verify` 0 errors at every commit; the CI trust gate count
  moves DOWN with each discharge and the ledger row moves in the same
  commit.
- Containers suites green; a differential test drives `HintedArena`
  against a naive scan oracle across marks, deep restores, duplicate
  contents, and re-keys (the boolean_backtracking oscillation pattern).
- The e-graph's fixed-arity caches adopt `HintedArena` behind the same
  cache API; e-graph suites (all diff modes), sundance corpus sweep
  (0 non-arith disagreements) and the SMT/EqSat benchmark envelope
  (cyclic_scheduler.3 wall within noise of 0.36s; math-microbenchmark
  no-change vs main) all hold. A slower-than-envelope result is a
  finding to record and fix, not a silent acceptance.

Forbidden proxies: an axiomatized-hashbrown model in place of the
verified table (that is the fallback to argue for explicitly, not the
deliverable); completeness as a debug assert; "wired but not proven".
Hard part first: the `HintedArena` invariant design and its restore
theorem are the highest-risk item and get built before the e-graph
adoption; the discharge wave's independent items may proceed in
parallel with it but adoption waits for the theorem.
