# The B+ Tree Set: Design and Proof

[Table of Contents](00-table-of-contents.md)

`BPlusTreeSet` is the verified, packed, insert-only B+ tree used by the
container crate. It is parameterized over key type, node layout, in-node search,
and tracking:

```rust
pub struct BPlusTreeSet<
    K: DenseId,
    L: NodeLayout<Word = K::Index> = Layout64U32,
    S: SearchKind = BinarySearch,
    const TRACK: bool = true,
> { /* ... */ }
```

The executable tree is an arena of fixed-size nodes plus a small header. The
specification is a recursive ghost tree whose in-order key sequence is the
public model. The proof connects the packed arena, child pointers, and linked
leaves to that model.

## 1. Representation

Each `NodeLayout` supplies a fixed-size node, a word type, an arena-index type,
and capacities.

- A leaf stores sorted keys in `data[0..count]`; `link` names the next leaf.
- An internal node stores sorted separators and child indices; its final child
  occupies `link`.
- `ArenaIdx::MAX` is the null link and is never a real node index.
- The node header also carries the capture bit used when `TRACK = true`.

The six supported layouts pair 31-bit keys with `u32` words and 63-bit keys
with `u64` words. The default is `Layout64U32`. Layout geometry is part of the
type, so capacities and index-width relationships are available to Verus as
associated constants.

The arena is append-only during normal operation. Insertion mutates existing
nodes and appends split nodes; it never deletes or reuses an arena slot.
Restoring an earlier mark may truncate slots allocated after that mark.

## 2. Abstract Model

The ghost shape is:

```text
Tree::Leaf  { id, keys }
Tree::Inner { id, seps, kids }
```

`tree_keys(tree)` concatenates leaf keys in order and is the set's public
sequence model. `tree_ids(tree)` and `tree_leaf_ids(tree)` describe the arena
footprint and leaf order.

The main well-formedness relation establishes:

1. every tree id is in range and bound to the corresponding arena node;
2. each arena id occurs at most once in the tree;
3. all leaves have one depth;
4. non-root occupancy bounds hold;
5. keys and separators are sorted;
6. each separator bounds the adjacent child ranges;
7. the leaf-link chain follows `tree_leaf_ids` and ends at `NIL`;
8. the executable key count equals `tree_keys(tree).len()`;
9. every model key fits the selected key representation.

Separators are bounds, not copies of the right child's minimum. Split proofs
therefore carry cross-child ordering directly. They do not assume that a
promoted separator remains in either output half.

`binds(arena, tree)` connects the packed node representation to the ghost tree.
`tree_disjoint(tree)` supplies the dynamic frame needed to mutate one subtree
while preserving its siblings.

## 3. Capacity

Insertion has no caller-visible arena-capacity precondition. The proof derives
enough index headroom from:

- the insert-only set cardinality;
- the minimum occupancy of non-root nodes;
- the selected key and arena-index widths; and
- the reserved null index.

Before an insertion, at most one new node can be required per tree level plus
a new root. The node-count and height lemmas show that this amount fits whenever
another distinct key fits the key domain.

## 4. Search

`SearchKind` is active in the verified implementation:

- leaf lookup dispatches to `S::find_ge`;
- internal descent dispatches to `S::find_gt`.

`NodeLayout::keys` exposes only the live key prefix, and the search contracts
return an in-bounds split point unconditionally. When the prefix is sorted, the
conditional postcondition gives the full lower-bound or upper-bound
characterization consumed by the tree proof.

`BinarySearch` is the default. `Branchless` is available for target/layout
combinations where its linear comparison loop performs better. That choice is
machine dependent; use the Criterion B+ benchmarks and their confidence
intervals rather than a static timing claim.

## 5. Insert

`insert(key)` returns `true` exactly when the model did not already contain the
key and ensures:

```text
model_after == sorted_unique(model_before ++ [key])
```

The implementation first tries the right-edge append path. Otherwise
`insert_rec` descends recursively by tree height:

1. search the target node;
2. update a non-full node in place; or
3. split a full node and return the promoted separator and right node;
4. absorb the child split or split the parent in turn;
5. create a new root if the old root split.

The recursive result uses a footprint contract rather than exact footprint
equality:

- every old subtree id remains reachable;
- every newly reachable id is a fresh arena-tail id;
- split halves are disjoint; and
- the left output keeps the old subtree's first leaf.

A result that does not split the current root can still contain fresh nodes: a
deeper split may have been absorbed below it. Exact footprint equality would
therefore be too strong. `footprint_contract_holds` exercises this case in the
runtime property suite.

First-leaf preservation is the boundary fact required to recompose the linked
leaf chain. A split inserts its new leaf to the right, so it does not move the
subtree's leftmost leaf.

**Rightmost-leaf tracking (2026-09-16).** `insert` used to recompute the
cached `last_leaf` by descending from the root to the rightmost leaf after
every insert (`rightmost_leaf_of`); production updates it only when the
rightmost leaf splits. The recursion now returns, as a fifth component, the
fresh right leaf iff the subtree's rightmost leaf split (`last_after`,
`last_lift`): a leaf split reports its right sibling; an internal node
forwards its child's report only when the child was its last one, else
`None`; the root applies the report to `last_leaf`. Three lemmas
(`lemma_last_after_absorb`, `_child_split`, `_parent_split`) carry the
`last_leaf_id` argument per arm so `insert_rec` stays under the default
solver budget. The descent is gone from the insert path.

## 6. Bulk Construction

`from_sorted(keys)` builds a fresh tree bottom-up. Its input must be strictly
ascending and duplicate-free.

The loader:

1. partitions keys into balanced leaves;
2. writes leaf links while constructing the leaves;
3. carries each node's first key to the next level;
4. partitions each internal level into balanced groups; and
5. repeats until one root remains.

Balanced partitioning is required by the non-root occupancy invariant. A final
undersized `chunks(cap)` group would not satisfy `tree_wf`.

The proof establishes the same model and well-formedness relation as repeated
insertion. Performance comparisons for construction live in Criterion
benchmarks; they are not part of the proof contract.

**Leaf fill (2026-09-16).** The bulk loader writes each leaf with the total
`NodeLayout::leaf_fill_keys`: the key-to-word conversion is fused into the
copy, the window and leaf shape are refused once per leaf (an unverified
caller cannot reach a malformed write), and the contract is conditional on the
same facts, which `bulk_fill_leaf` establishes. The strict-order validation in
`from_sorted`/`try_from_sorted` is a branch-free reduction with one refusal
after the loop, and `try_from_sorted` no longer re-validates through
`from_sorted`. Measured against legacy (16 384 keys): 11.3 µs vs 13.5 µs.

## 7. Cursor

`BPlusCursor` carries an executable leaf/index pair and a ghost index into the
tree model.

- `seek_first()` positions at the least key.
- `seek(target)` positions at the least key greater than or equal to `target`,
  or at exhaustion.
- `key()` returns the current key when positioned.
- `step()` advances one key and follows the leaf link at a boundary.

The cursor proves:

- repeated `step()` enumerates `tree_keys(tree)` in order without gaps or
  duplicates; and
- `seek(target)` never skips a present key at or above the target.

The lower-bound specification is shared with the sorted-vector cursor through
`seek_target_idx`, so both implementations refine the same `SortedCursor`
contract.

**Cached leaf (2026-09-16).** The cursor keeps a copy of the leaf it stands
on (`leaf`), refreshed only when `node` changes (`seek`, `seek_first`, and the
link-follow in `step`). `key` and `step` read that copy, so the per-key
arena fetch (a whole-node copy, which production still performs) is gone.
The invariant `cursor_ok` is `cursor_wf` (positioning against the in-order
model) plus `leaf_cached` (`leaf == arena[node]` while positioned); the
public contracts are stated over `cursor_ok`. Measured against legacy: a
scan of 16 384 keys takes 15.5 µs vs 57.5 µs.

## 8. Semi-Persistence

`mark` delegates to the arena's semi-persistent vector and archives the header
and ghost tree. `restore` rewinds all three in lockstep and re-establishes the
full tree well-formedness relation.

The observable theorem is:

```text
model_after_restore == model_at_mark
```

Marks are not claimed to be O(1). The inline store clears capture bits
associated with the prior frame, with work proportional to the relevant
captured cells. Restore replays the child-vector diff and rebuilds the parent
frame's capture state.

With `TRACK = false`, capture checks, logging, and restore execution branches
are removed by constant specialization. Tracking-related fields still exist in
the generic layout but remain empty or at their initial values; this is an
execution-overhead claim, not a zero-memory-overhead claim.

## 9. Verification Boundary

The B+ implementation verifies without `admit` or `assume`. Run:

```text
cargo verus verify
```

for the current fact count and solver result. The verified surface includes:

- layout access and mutation contracts;
- construction, membership, insertion, and length;
- bulk construction;
- cursor traversal and seek;
- arena-capacity sufficiency; and
- mark/restore refinement.

Property tests compare executable behavior with standard sorted-set and
layout-level oracles. These tests complement but do not replace the Verus
proofs.

Low-level array operations and machine-code helpers classified as
`external_body` are listed in [the trust boundary](02-trust-boundary.md) and
covered by runtime contract tests. Public layout operations mirror verified
preconditions with release-mode refusal checks, so safe Rust misuse cannot
reach unchecked indexing.

## 10. Scope

- Insert-only set; deletion and merge/borrow rebalancing are absent.
- Duplicate insertion is a no-op.
- Layout and search choices are explicit type parameters.
- Performance evidence must come from Criterion on the target architecture.
- The executable reference design is documented in
  [`containers/doc/design/07-bplus-tree.md`](../../../containers/doc/design/07-bplus-tree.md).

---
[Table of Contents](00-table-of-contents.md)
