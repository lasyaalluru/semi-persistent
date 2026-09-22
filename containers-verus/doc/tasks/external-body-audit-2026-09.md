# external_body audit, September 2026: the 27 -> 72 drift, item by item

The trust-surface gate (`.github/workflows/verus.yml`, `EXPECTED_DEFAULT=27`)
pins the count the ledger (`doc/design/02-trust-boundary.md`) argues for. The
tree now holds 77 markers: 72 in the default build plus 5 gated behind
`literal-types`. This audit establishes when the drift happened, what each
undocumented marker trusts, ranks the risk, and sets the remediation.

## 1. When it happened (git archaeology, exact)

| revision | date | markers (total) | delta |
|---|---|---|---|
| `ea7b20b` (gate pinned at 27+5) | 2026-08-21 | 32 | baseline; ledger accurate |
| `af65d0b` (F2/F5/H1-H4 goal close) | 2026-09-08 | 76 | **+44, the entire drift** |
| `9f55448` (store-selection close) | 2026-09-10 | 77 | +1 (`env_diff_store_kind`) |

The drift is the compression-and-parallelism goal campaign: 107 commits into
`containers-verus/src` between the two revisions. The gate never fired
because the branch has not been pushed; CI has not run on any of it. The
gate's design assumption ("update the ledger AND the constant in the same
commit") silently degraded into "neither," which is exactly the failure mode
its comment warns about. The store-selection campaign is exonerated except
for one env lever.

Top introducing commits (marker count): `cb9ee8c` shadow-encode harness F4
(7), `28886de` FrameStats/calibration (6), `53dd17b` ValueCompressor F2.1
(3), `c658bbc` parallel mark/restore H3 (2), `97ec666` SyncMember H1 (2),
`963303a` bit-packed codes (2), `712c4b4` GenStamps reclamation (2), plus
singles across diff_log, diff_compress, layered, compressed_stack,
compression_config, parallel, and the two store `heap_bytes`.

## 2. The 72, classified

### 2.1 Spec-free (no ensures; cannot affect any theorem) - 43 markers

Every one is a diagnostic reading state Verus does not model. Sub-groups:

- **Byte/capacity counters (24)**: `heap_bytes`/`byte_len`/`total_bytes`/
  `tracking_bytes` across vec.rs (2066, 2075), capture_bits.rs:499,
  parallel_store.rs:527, inline_store.rs:533, list.rs (2472, 2487),
  gen_stamps.rs:116, diff_log.rs:776, compressed_stack.rs:185,
  layered.rs:576, diff_compress.rs (92, 105, 302, 1413, 1879, 2187, 2437),
  value_compressor.rs (121, 379, 601), compression_stats.rs (34, 41, 59).
  Trusted content: `capacity()`/`size_of`/saturating arithmetic. Risk: none;
  consumed only by prints and the size-only layered selector, whose choice
  carries no proof weight by design.
- **F4 shadow/stats harness (10)**: compression_stats.rs (93, 128, 200, 233,
  242, 270, 314, 366, 381, 399) - env-gated measurement I/O and heuristic
  counters. Risk: none (no ensures, no proof consumers).
- **Env levers (2)**: compression_config.rs:174 (`SEMPER_COMPRESS`), :191
  (`SEMPER_DIFF`). Every branch they select carries the same verified
  contract, so the flags are correctness-invisible by construction. Risk:
  none.
- **Misc (7)**: `choose_mode` diff_compress.rs:1109 (heuristic, any answer
  correct), `shadow_key`/`cold_frame_count` diff_log.rs (1338, 1344),
  `par_sum_canary` parallel.rs:27, `values_equal` sparse_set.rs:1356
  (unconstrained bool), `debug_check_different_rings` circular_list.rs:667
  (requires-only debug mirror), `white_box_head` list.rs:424 (test
  accessor), `refuse` guard.rs:53 (diverges; no post-state).
  Update 2026-09-17: `debug_check_different_rings` no longer exists — the
  public `splice`/`splice_absorb` run a verified walk of the absorbed ring
  (total public API); the default count is 49.

### 2.2 Contract-carrying, structurally trusted (std/runtime facts) - 15

These assume something Verus cannot state about std or the runtime; each is
narrow and std-documented:

- Capacity-only shrinks: `shrink_vec_capacity` parallel_store.rs:541,
  `shrink_aov_capacity` append_only_vec.rs:501 (element sequence unchanged);
  `data_capacity_bits` parallel_store.rs:555 (`capacity >= len`).
- bplus layout primitives (5): `arr_get`/`slice_get`/`sel_usize`/`arr_set`/
  `arr_shift_up` bplus_layout.rs (138-237) - `get_unchecked`, `select_
  unpredictable`, `copy_within` with their std contracts; property-tested.
- `guard::check_precondition` guard.rs:33 (panic-on-false; format machinery
  unmodeled - vstd's own pattern).
- Key-model/hasher (4 + gated): `clone_key_exact` map.rs:640 (projects a
  vstd prose clause), `ExIndexHasher`/`ExFoldHasher` registrations
  hasher_spec.rs (327-333), the determinism axiom hasher_spec.rs:342
  (mirrors vstd's shipped admit), `ContainerId` trio container_id.rs
  (70/82/95).

### 2.3 Contract-carrying, campaign-added, conformance-backed - 12

The real new TCB from the goal campaign. Each has an ensures a proof reads,
a named conformance/property test, and no `unsafe` except the two memcpys:

| item | loc | trusted claim | check |
|---|---|---|---|
| `pack_codes` | diff_compress.rs:223 | packed words match `packed_code_at` | `packed_codes_roundtrip` |
| `packed_get` | :249 | extract half of the pair | same |
| `assign_codes` | :410 | dict codes round-trip (std HashMap unmodeled) | `dict_roundtrip` |
| `decode_exec_i` | :668 | exec run-walk equals spec decode | `run_frame_roundtrip` |
| `sort_frame_by_index` | :964 | permutation + sorted + unique preserved | `sort_frame_roundtrip` |
| `is_unique_idx` | :993 | equals `unique_idx` spec | `unique_idx_check` |
| `restore_runs_into` | :1657 | memcpy equals in-order decode application | `run_col_index_major` |
| `RunCol::restore_to` | :2010 | sliced memcpy meets `apply_all` ensures | conformance vs scattered |
| `adaptive_len_exec` | diff_log.rs:559 | running length sum does not overflow | (wf-adjacent) |
| `bump_from` | gen_stamps.rs:143 | wrapping_add changes a u64 (ABA at 2^64) | frame-liveness backstop |
| `mark_parallel` | sync_group.rs:362 | full sequential mark contract across rayon | differential test |
| `restore_parallel` | sync_group.rs:403 | full sequential restore contract across rayon | differential test |

**Risk ranking within 2.3.** The two rayon fan-outs are the widest gap: an
entire verified contract assumed across a concurrency dispatch, justified by
a prose disjointness argument (each member owns its columns; genealogy
written outside the fan-out) plus one differential test - and their comment
mislabels them "group B". They deserve their own ledger group (concurrency
dispatch) with the disjointness argument stated as the trusted claim.
`bump_from` is second (load-bearing for branch-cut soundness; residual ABA
documented). The codec items are third: pure representation transforms whose
contracts are exercised on every seal/restore and property-tested.

### 2.4 Gated (`literal-types`) - 5, unchanged

external_specs.rs registrations + key-model axioms for BigInt/BigUint/
canonical floats. Documented already.

## 3. Discharge candidates (trusted -> proved, ranked by value/effort)

1. **`pack_codes`/`packed_get`** - capture_bits.rs proves the identical
   class of shift/mask facts with `bit_vector` asserts; porting that style
   discharges both. Medium effort, removes bit-level trust from every Dict
   frame.
2. **`sort_frame_by_index`** - a verified insertion sort over `(T, I)` by
   `idx.as_nat()` is a contained exercise; the contract (permutation +
   sortedness + uniqueness preservation) is already exactly what a verified
   sort proves. Removes the only trusted step in the sorted-fold path.
3. **`is_unique_idx`** - via the verified sort (check adjacent pairs) or a
   verified map; falls out of item 2.
4. **`decode_exec_i`** - the loop is spec-mirrorable; the marker exists for
   effort reasons, not modeling reasons.
5. **`restore_runs_into`/`RunCol::restore_to`** - replace `copy_from_slice`
   with a verified per-element loop behind the same signature, measure the
   memcpy delta; if the loop costs real time, keep the marker and record the
   number (the trade is then a recorded decision, not a default).
6. **`assign_codes`** - swap std HashMap for the crate's own verified map if
   its capacity profile fits; otherwise stays.
7. **`adaptive_len_exec`** - add the sum bound to `DiffLog::wf` and prove.

Not dischargeable in principle: std capacity facts, panic runtime, hasher
determinism, ContainerId global freshness, rayon dispatch (would need a
concurrency logic Verus does not offer; the honest form is the dedicated
ledger group).

## 4. Remediation (the order to do it)

1. Re-pin the gate AND rewrite the ledger in one commit: counts 72+5, the
   2.1 items as a bulk-documented diagnostics group, 2.2/2.3 as per-item
   rows, the rayon pair in a new group with the disjointness claim stated.
2. Push the branch so the gate actually runs from now on.
3. Work the discharge list top-down; every discharge trips the gate
   downward, which is the gate recording the win.
