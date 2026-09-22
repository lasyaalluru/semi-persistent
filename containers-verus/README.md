# containers-verus: Verified Semi-Persistent Containers

The verified counterpart of `semi-persistent-containers`, and the
semi-persistent container dependency the e-graph engine runs on:
`egraph/Cargo.toml` aliases `semi-persistent-containers` to this crate. Engine
logic still uses ordinary Rust collections for transient indexes, scratch, and
worklists; those are outside these container proofs. The unverified reference
implementation lives in [`containers/`](../containers) and serves as the
conformance oracle and performance baseline.

## What is proved

For the verified core API of each `TRACK`-parameterized container:

1. **Untracked equivalence (`TRACK = false`).**
   Its abstract contents follow the corresponding non-semi-persistent model
   (`Seq<T>` for `Vec`, a map model for `SpMap`, set models for `SparseSet` /
   `BPlusTreeSet`, etc.). `mark` and `restore` are statically uncallable.
   This is not a claim of identical layout, panic behavior, trait surface, or
   behavior for methods outside the proved core API.

2. **Tracked correctness (`TRACK = true`).**
   An internal ghost stack `snapshots: Seq<Spec>` records the deep copy of
   `view()` at each `mark()`. `restore(token)` resets to that checkpoint
   and keeps its frame open (design doc 08 §1): afterwards
   `view() == snapshots[token.depth]`, the depth is `token.depth + 1`, and
   `snapshots` is the old prefix of length `token.depth + 1`. `pop_scope()`
   drops the open top frame; `restore_and_pop(t)` is the two fused on one
   pop core (the SMT-LIB `pop`, and exactly what the legacy restore always
   was, at the same cost).

3. **Branch-cut safety.**
   Each token carries the id of the manager that minted it, a generation
   stamp and a depth (`GroupToken`; every container owns a manager, a
   synced group shares one). A token is valid iff it names this manager and
   the stamp at its depth is live: a restore cuts every stamp above the
   checkpoint, a pop cuts the popped depth, and stamps are never reused, so
   a cut token never comes back and a foreign token is refused whatever its
   numbers. `restore`/`pop_scope` are total (refuse on a bad token or an
   empty stack); `try_restore`/`try_pop_scope` return `Result`; the exec
   `is_valid_token` computes the same predicate the contracts use.

The aggregate structures add their own joint invariants on top; the largest is
the class layer's `eg_model_wf` (invariants W1..W7, defined in the
`eclasses.rs` module header), which ties rings, union-find roots, class keys,
use-lists, the min-monomial pool, and the per-class size counter together at
every method boundary and in every archived frame.

## What is trusted

The proofs carry no `admit`s or `assume`s. The trust boundary is the set of
`#[verifier::external_body]` items modeling what the logic cannot describe:
27 in the default build, 32 with the `literal-types` feature, enumerated and
justified one by one in
[`doc/design/02-trust-boundary.md`](doc/design/02-trust-boundary.md). Read
that chapter to know exactly what the verification does and does not
guarantee.

**Usable from unverified Rust.** A Verus-checked caller proves each public
method's preconditions; an ordinary Rust caller does not, and the erased
`requires` would offer no protection against, for example, restoring past the
`u32` fork-history limit or pushing past the index type, which would silently
wrap. The overflow/capacity preconditions are therefore also enforced at
runtime: such a call panics with a descriptive message instead of corrupting
the container. The fork-history headroom is queryable via
`restores_remaining()`. Every public function is total: the only
precondition it may state is the container's own well-formedness, which every
constructor and operation upholds; anything else is either checked at runtime
(a `Result` for operational refusal, a documented panic for a contract
violation) or stated as a conditional postcondition. `partial-api-allowlist.txt`
is empty and `tools/check_partial_api.py` keeps it so.

## Architecture

```
Layer 0: tagged.rs / index_like.rs       -- Trait specs (niche, bijection)
Layer 1: diff_store.rs                   -- Capture-protocol contract (trait)
Layer 2: parallel_store.rs / inline_store.rs -- Two impls of DiffStore
Layer 3: frame.rs / container_id.rs / fork_history.rs -- Frame stack, identity, branches
Layer 4: vec.rs                          -- Vec<T,I,S,TRACK> proved over the trait specs
Layer 5: append_only_vec / map / sparse_set / list / circular_list  -- containers over the verified Vec/arena
         bplus (+ bplus_tree / bplus_layout / bplus_search)         -- BPlusTreeSet over its own InlineStore arena
         dense_span_map / layered_span_map                          -- span-table multimaps (index families)
         dense_id / opt / capture_bits                              -- supporting value types
Layer 6: union_find.rs / eclasses.rs     -- the verified class layer (aggregate)
```

## Verification status

`cargo verus verify` prints **1703 facts verified, 0 errors**; add
`-- --time-expanded` for the per-module tally. What each proof covers is
chapter 1's subject; the trust framing is chapter 2's. The verified set:

- **`Vec`** (the semi-persistent core): the reconstruction theorem at
  arbitrary mark-nesting depth, over both `DiffStore` backends
  (`ParallelStore` / `InlineStore`), plus branch-cut safety and faithful `pop`.
- **`AppendOnlyVec`, `Map` (`SpMap`), `SparseSet`, `ListArena`, `CircularList`**:
  each verified for its core API, including `mark`/`restore`.
- **`BPlusTreeSet`**: `insert` (with split propagation, new-root growth, and
  production's O(1) append fast path over a `wf`-bound `last_leaf` cache) is
  total and carries its full model transition; sound in-order traversal and
  `seek`; the arena provably never overflows; `mark`/`restore`. Insert-only.
- **`SortedVecCursor`**: the galloping seek the e-graph's leapfrog joins run
  on, verified against the same `seek_target_idx` spec as the B+tree cursor,
  so the two are substitutable at the `SortedCursor` boundary. The engine
  re-exports this type and defines no cursor of its own.
  See [`doc/design/12-sorted-vec-cursor.md`](doc/design/12-sorted-vec-cursor.md).
- **`DenseSpanMap`**: the build-once index behind the engine's per-round index
  families: a two-pass counting build refined to the per-key filter of its
  input stream, with the generation-stamped arena-reuse build path.
  See [`doc/design/15-dense-span-map.md`](doc/design/15-dense-span-map.md).
- **`LayeredSpanMap`**: incremental maintenance over the dense span map
  (base generation, one delta generation, per-key invalidation). Verified;
  not enabled in the engine, which uses the stamped-reuse `DenseSpanMap`
  path. See [`doc/design/16-layered-span-map.md`](doc/design/16-layered-span-map.md).
- **`UnionFind` and `EClasses`** (the class layer): union with rank and with a
  caller-chosen survivor, path compression, the proof forest under `PROOFS`,
  and the aggregate invariants W1..W7, including W7: the stored per-class
  size equals the class ring's length, in the current state and in every
  archived frame. The engine's `--union-by` survivor policies read these
  verified counters. See the `eclasses.rs` module header for the invariant
  table and [`doc/design/egraph-class-layer.md`](doc/design/egraph-class-layer.md)
  for the direct engine-integration statement and historical compatibility
  boundary.

Runtime property suites exercise the executable code against plain-`std`
oracles; the finite differential comparison against the legacy reference
implementation lives in [`containers-conformance/`](../containers-conformance).

## Prerequisites

- [Verus](https://github.com/verus-lang/verus) pinned in `.verus-version`
- [`cargo-verus`](https://github.com/verus-lang/verus)
- Rust toolchain in `rust-toolchain.toml`

## Running

```bash
# Verify everything
cargo verus verify

# Per-module timing breakdown (finds the hot modules)
cargo verus verify -- --time-expanded

# One module, or one function within it
cargo verus verify -- --verify-only-module list
cargo verus verify -- --verify-only-module list --verify-function splice_raw
```

Ordinary `cargo build` compiles the crate with ghost code erased; that build
is what the engine links.

## License

Apache-2.0.
