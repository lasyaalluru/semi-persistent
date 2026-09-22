# Provisional interface → production instantiation (Step 3 inventory)

`composition.rs` proves the restore theorem for any `Runtime<T>` whose
provisional methods satisfy the listed contracts. Production code does not
import that target; instead every provisional method is instantiated by a
checked function of `Vec` whose Verus contract states the same effect over the
actual physical pools, snapshot history, capture state and canonical history.
This table is the dependency map. "Supplier" is the checked caller that
establishes the precondition; "consumer" is the next checked function that uses
the postcondition. No entry relies on an assumed contract.

| Provisional method (`composition.rs`) | Concrete checked function (`src/vec.rs`) | Precondition supplier | Postcondition consumer | Evidence |
|---|---|---|---|---|
| `token_bounds` | `is_valid_token` (`is_restorable_spec`), `depth_exec` | public `try_restore` | `restore` (frame index below depth) | full default/literal runs |
| `resize` (fixed target window, filler agrees with live) | `reconstruct_target_checked` (one-time `resize_default`, capture preparation) | `runtime_restore_frame` | `replay_all_tiers_checked` | progress doc "Mixed-tier reconstruction" |
| `prepare` (store protocol, tags subset, pre-clear unless fused) | `runtime_begin_restore` | `reconstruct_target_checked` | `replay_persistence_pair_checked` | same |
| `pair_batch` (one Trail or Hot batch, exact shared-map application, tags cleared) | `replay_persistence_pair_checked` (batched pool overlay), wrapper `replay_physical_range` | `replay_all_tiers_checked` | `replay_all_tiers_checked` / Cold suffix | progress doc "Physical storage refines the shared top-down model" |
| `cold_frame` (direct run replay of one Cold frame) | `replay_persistence_cold_checked` | `replay_all_tiers_checked` (reverse Cold traversal) | next Cold frame / `truncate_restored_history_checked` | same |
| `retire` (exact retained prefixes, canonical prefix, tier counts) | `truncate_restored_history_checked` (exports `restored_history_prefix`, all three tier representations, `wf_for_snap`, exact shared-frame prefix) | `reconstruct_target_checked` | survivor reopening / capture finalization | progress doc "Restore prefixes and zero-target closure", "Retained … representation after truncation" |
| `reopen_hot` (Hot survivor becomes a Trail frame) | `promote_hot_survivor_checked` inside `restore_hot_promotion_checked` | `runtime_restore_frame` dispatch (`!unique && target > cold`) | `finish_survivor_checked` | progress doc "Checked Hot-to-Trail survivor promotion", "Exact shared-map retirement and Hot survivor reopening" |
| `reopen_cold` (Cold survivor decoded into the store-selected tier) | `promote_cold_storage_checked` inside `restore_cold_survivor_checked` (`cold_decode::decode_into`) | `runtime_restore_frame` dispatch (`target <= cold`) | `finish_survivor_checked` | progress doc "Checked Cold promotion and complete Cold-survivor restore" |
| `finish_capture` (flags equal membership, active saved length) | `finish_restore_range_checked`, `finish_survivor_checked` | each survivor path | `reclaim_cold_checked` | progress doc "Capture rebuilding and retained-ingress restore" |
| `finish_empty` (zero target) | `restore_zero_all_tiers_checked` | `runtime_restore_frame` (`target == 0`) | `reclaim_cold_checked` | progress doc "Restore prefixes and zero-target closure" |
| `reclaim` (capacity only) | `reclaim_cold_checked`, `hot_defer_restore_reclaim_checked` | every restore path | public `restore` / `try_restore` | trust ledger group B (shrink helpers keep views) |
| `restore_public` / `try_restore_public` | `restore`, `runtime_restore_frame` (dispatch over `hot_defer_scope`, zero target, retained ingress, Hot promotion, Cold survivor), public `try_restore` | public API | callers | `try_restore` contract: exact `S[k]`, depth `k`, snapshot prefix `S[..k]`; rejection leaves view/depth/snapshots unchanged |

Mutation, mark and rollover are outside the abstract restore theorem but are
the other half of the end-to-end sequence theorem. Their production contracts:

| Operation | Checked function(s) | Contract on the public model `(view, depth, snapshots)` |
|---|---|---|
| constructor | `with_store_mode`, `with_store_policy`, `new*` | `wf`, empty view and history |
| set / push / pop | `set_index`, `try_push`, `pop` (checked Hot scope and mixed-tier cores) | view updated exactly, snapshots unchanged |
| mark | `try_mark_with` → `runtime_push_frame` (Hot Defer, general Defer, or `runtime_push_frame_fallback` with configured/forced rollover) | view unchanged, depth + 1, snapshots pushed with the old view; rejection unchanged |
| rollover (any legal sequence) | `runtime_migrate_trail`, `runtime_migrate_hot`, `runtime_apply_tier_policy`, `runtime_apply_configured_rollover`, `runtime_rollover_on_mark`, `runtime_apply_adaptive`; public `apply_tier_policy`, `flush_trail`, `compress_hot`, `apply_adaptive` | `tiers_only_changed`: only the seven physical tier vectors move; view, depth, snapshots, canonical history, store and policy unchanged |
| restore | `try_restore` | as above |

Because each public operation's contract is an exact function of the abstract
model `(view, depth, snapshots)` and preserves `wf`, any legal sequence of
public operations keeps the container well-formed and its abstract model equal
to the fold of the abstract steps; `restore` after any interleaving yields
exactly the archived snapshot, the archived depth and the snapshot prefix. The
checked function `sequence_witness_checked` in `src/vec.rs` exercises one
representative interleaving (mark, write, mark, restore, write, older restore,
rollover, restore) end to end and asserts the model consequences from the
contracts alone.
