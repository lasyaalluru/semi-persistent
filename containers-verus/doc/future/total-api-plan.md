# Total Public API

## Goal

No safe Rust caller should be able to invoke a public operation whose memory
safety or functional result depends on a Verus `requires` clause. Verus erases
preconditions, so an unverified caller cannot be expected to establish one.

The preferred public shapes are:

- a total operation with unconditional postconditions;
- `Result<_, ContainerError>` for operational refusal;
- an explicit panic/refusal check for programmer-contract violations; or
- a crate-private verified core called by a total public wrapper.

## Enforcement

`containers-verus/tools/check_partial_api.py` scans public executable
functions. CI rejects any new public `requires` occurrence not listed in
`partial-api-allowlist.txt`, and the allowlist may only shrink.

The allowlist is a boundary inventory, not a proof that listed functions are
safe for arbitrary callers. Each entry must belong to one of the classes below.

## Status (2026-09-17): complete

Every public executable function of the crate is total: the checker reports
0 public `requires` clauses (beyond the receiver's own `wf`-class predicates,
which every constructor and operation upholds) and the allowlist is empty. It
also reads module visibility from `lib.rs`, so items of a `pub(crate)` module
are not counted as public. Each boundary class below drained as follows:

- **Runtime-rechecked layout operations** — the `check_precondition`
  mirrors in the layout impls became refuse-guards and the nine trait
  primitives plus `internal_insert_at`/`first_key` carry requires-free
  conditional contracts (the pattern `leaf_fill_keys` already used). A new
  exec twin `is_node_wf` lets the generic helpers re-establish `node_wf`
  after their own guard, since the spec predicate is opaque through `L`.
- **Inaccessible store receivers** — the thirteen protocol operations (with
  the ghost views they are stated over) moved to the crate-private
  supertrait `diff_store_ops::DiffStoreOps`; `DiffStore` keeps the total
  queries and maintenance operations and remains the bound consumers name.
  The protocol test that drove stores directly moved in-crate.
- **Type laws** — `SpMap::new` ensures `obeys_key_model::<K>() ==> m.wf()`
  (a property of the type; nothing to check at runtime) and the `Tagged`
  operations ensure `repr_wf(r) ==> …`; `capture_bits::set_true` and
  `guard::check_precondition` are `pub(crate)`.
- **Component boundaries** — `CircularList::{splice, splice_absorb}` refuse
  a same-ring pair after a verified walk of the absorbed ring, with an O(1)
  fast path for a singleton absorbed ring (`next(aid) == aid`) (option 2 of
  the design list below, chosen because the e-graph's merge keeps the
  walk-free crate-private cores `splice_core`/`splice_absorb_core`, whose
  distinct-rings precondition is a theorem there); the external_body
  debug-only walk is gone. The "no ring walk on every splice" requirement
  below holds where it matters: the e-graph never walks, and the public
  component API walks only a non-singleton absorbed ring. `SparseSet::restore` archives the snapshot
  well-formedness in `wf` (lockstep stacks, every archived triple
  `snap_wf`), so token validity plus equal frame indices make it total.
- **Everything else** — `History::{mark, restore_to}`, `GenStamps`,
  `HintedArena` (whose `complete` predicate joined `wf`, with a `wf_struct`
  form for the mid-operation `note_hint`), the cold and compressed stacks,
  every frame's `decode_at`, `Codes`, the run compressors and the sync group
  took refuse-guards; the remaining internal primitives are `pub(crate)`.

The "Remaining Design Work" and "Current Boundary Classes" sections below
are kept as the record of the options considered; only "Keyed Maps" is still
open (the key-model law is no longer a precondition, but it remains the one
uninterpreted assumption a custom key type must satisfy).

## Current Boundary Classes (historical)

### Runtime-Rechecked Layout Operations

`NodeLayout` operations retain Verus preconditions so verified tree code can
consume precise contracts. Their executable bodies mirror those preconditions
with release-mode refusal checks before any unchecked index operation.

This is memory-safe for unverified callers, but the signatures remain partial
in the verifier. A future cleanup may split the public layout metadata from a
crate-private operations trait, or replace preconditions with conditional
postconditions where that remains useful.

### Inaccessible Store Receivers

`DiffStore` methods carry preconditions, but external safe Rust cannot obtain a
store value because constructors and aggregate access are crate-private. This
is compiler-enforced. Making the trait itself crate-private would simplify the
surface further if no external type-level use requires it.

### Type-Law Assumptions

Some preconditions express laws with no executable decision procedure:

- `obeys_key_model::<K>()`;
- `Tagged` representation laws; and
- erased ghost-parameter contracts.

These are trust-boundary items, not runtime input checks. The key-model
assumption has a separate elimination design in
[key-model-tcb.md](key-model-tcb.md).

### Component-Boundary Preconditions

The direct component APIs still expose obligations that their aggregate
callers prove:

- circular-list splice requires distinct rings;
- sparse-set restore requires an archived well-formed snapshot.

These are the main callable partial operations still to eliminate.

## Remaining Design Work

### Circular Lists

Provide one of:

1. an O(1) executable ring-identity witness checked by a total splice wrapper;
2. a `Result`-returning API that refuses same-ring inputs; or
3. crate-private splice primitives exposed only through `EClasses`, where
   distinctness is already a theorem.

The selected design must not add a ring walk to every splice.

### Sparse-Set Restore

Archive the snapshot permutation/well-formedness fact in the container's own
invariant, then make token validity sufficient for a total `try_restore`.
Alternatively, keep the primitive crate-private and expose restore only through
an aggregate that already archives the fact.

### Layout Surface

Separate metadata needed by external generic code from unsafe-to-misuse node
operations. The target is either:

- public constants and associated types plus crate-private operations; or
- public total operations with explicit refusal and requires-free conditional
  contracts.

Do not weaken the existing release guards around unchecked indexing.

### Keyed Maps

Eliminate `obeys_key_model` assumptions by moving verified maps to an index
whose correctness does not depend on vstd's uninterpreted `HashMap` key model.
Canonical key wrappers are already available; the remaining work is the
verified index and consumer integration.

## Performance Requirements

Total wrappers on hot paths must be measured with Criterion. Report the
estimate, confidence interval, benchmark configuration, and target
architecture. A fixed ratio from one wall-clock run is not acceptance
evidence.

Batch APIs should discharge a bound once when that avoids repeated checks. A
reservation witness is justified only when a real caller cannot batch and
Criterion identifies per-element checking as material.

## Acceptance Criteria

The goal is complete when:

1. the allowlist contains only non-runtime-testable type laws or entries whose
   receivers are compiler-inaccessible;
2. no public safe operation can reach unchecked indexing without a release
   guard;
3. direct circular-list and sparse-set callers need no erased precondition;
4. misuse tests cover every refusal path;
5. Verus verification, Rust tests, and the partial-API CI gate pass; and
6. any hot-path API change has Criterion evidence.

The allowlist and generated API documentation are the current status sources;
this file specifies the target and acceptance conditions only.
