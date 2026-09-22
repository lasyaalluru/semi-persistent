# Verified Node Caches: the Hint Index as a Lower Bound

Design sketch, 2026-09-20. Status: nothing implemented beyond the core this
chapter builds on (`hinted_arena.rs`, verified). The e-graph's three node
caches (`egraph/src/caches.rs`: fixed arity, variable arity, literal) are
unverified and are what this chapter proposes to replace.

## 1. What the structure is

A node cache is two things and a protocol:

- **The arena**, a semi-persistent column of node content, one cell per
  local node id. Content is what hash-consing compares: an operator plus
  children, in one of three shapes — `K` children inline (fixed arity), a
  span into a shared child pool (variable arity, where the pool is itself a
  semi-persistent column), or an operator plus a literal id. Each cell also
  carries the node's global id, which is the value a probe answers with, and
  which is not part of the content.
- **The hint index**, a map from a 32-bit fingerprint of content to a set of
  local ids (the *bucket* for that fingerprint). It is not versioned: marks
  and restores never touch it. Every write to a cell adds the cell's id to the
  bucket of the new content's fingerprint. Nothing is ever removed from a
  bucket except by the two reclamation rules of §4.
- **The frame protocol** (`Member`): `push_frame`, `reset_frame`,
  `restore_frame`, `pop_frame`, driven by the group's `History`, which mints
  and validates tokens. A restore rolls the arena (and the child pool) back
  to a snapshot and does no index work at all.

`HintedArena<T, I, TRACK>` in the verified crate is exactly this pair for an
abstract content type `T: HintContent`, with a `SpUniqueMap<u32, usize>` from
fingerprint to bucket slot and a `Vec<Vec<I>>` of buckets. The e-graph's
caches are the same structure specialised three times, plus four things the
arena does not have yet: a packed single-id slot in the index (no bucket for a
fingerprint with one id), move-to-front on a hit, lazy reclamation and
compaction of buckets, and a recanonicalization history column.

## 2. What it does

Three operations carry the e-graph's correctness; everything else is access.

- `probe_or_insert(global_id, content)`: if a live cell holds content equal
  to `content`, answer `Hit { global_id }` with that cell's global id; else
  append a cell with this content and global id and answer `Inserted {
  local_id }`. This is hash-consing: it is what guarantees one node per
  content.
- `recanonize_node(local_id, find)`: rewrite the cell's children through
  `find` (the union-find's representative), and if the rewritten content now
  equals another live cell's content, report the pair of global ids as a
  collision for the congruence closure to merge. With `PROOFS`, the first
  rewrite of a node records its original content in the history column, so
  a proof can be replayed.
- `restore_frame(depth)` / `reset_frame(depth)`: roll the arena back to the
  snapshot at `depth`. The index is untouched.

## 3. How it works

**Fingerprints route, content decides.** A probe hashes the query's content
to a fingerprint, reads that fingerprint's bucket, and tests each candidate
cell's *current content* for equality with the query. A bucket may contain
ids whose content no longer hashes to the fingerprint (the cell was rewritten
or restored) and ids whose content hashes to it but is unequal (a collision
of the hash). Both are skipped by the equality test. The index is therefore
never trusted; it only says where to look.

**Restore is free because the invariant already covers the past.** A hint is
a pair `(fingerprint, cell)` with no state. Rolling a cell back to content it
held at a mark does not require re-hinting it, because the hint recorded when
that content was written is still in its bucket. The invariant of §4 says
precisely that, for every cell of every live snapshot.

**Reclamation is lazy and bounded by the same invariant.** During a probe, a
candidate id at or past the live length is removed from the bucket on the
spot (the cell was truncated by a restore). At a bucket-length threshold the
bucket is compacted: sorted, deduplicated, ids past the live length dropped,
and — only when no mark is live — ids whose current content does not
fingerprint to this bucket dropped too. §5 derives when each drop is legal.

**The single-id slot.** The common case is one id per fingerprint. The index
value is the id family's own repr word with the family's reserved bit as a
marker: bit clear, the word is the single hinted id; bit set, the low bits
index the bucket table. A bucket exists only once a fingerprint has two ids.

## 4. Why it works: the invariant

Content is abstract: a trait supplies the collision predicate `eq_spec`, a
fingerprint `fp_spec`, exact executable twins of both, and one proof
obligation, the routing lemma:

```
eq_spec(a, b)  ⟹  fp_spec(a) == fp_spec(b)
```

Nothing is assumed about unequal content: collisions are allowed and the
proofs hold in their presence. The invariant is a **lower bound** on the hint
set:

```
complete(self) ≜
    ∀ j < |view|.                                 hinted(fp(view[j]), j)
  ∧ ∀ k < |snapshots|, j < |snapshots[k]|.        hinted(fp(snapshots[k][j]), j)
```

where `hinted(fp, j)` says cell `j` is in the bucket for `fp` (or is the
single id of that slot). Extra hints are permitted without limit; a missing
hint for a live or snapshot cell is what the invariant forbids. From it:

- **Probe soundness.** A `Some(id)` answer names a live cell whose content is
  `eq_spec`-equal to the query (the equality test ran on it).
- **Probe completeness, the hash-consing theorem.** A `None` answer means no
  live cell holds equal content: an equal cell `j` would have `fp(view[j]) ==
  fp(query)` by the routing lemma, would be hinted under it by clause 1, and
  would have passed the equality test.
- **Restore preserves the invariant with no index work.** After restoring to
  frame `k`, the new view is `snapshots[k]`, whose cells are hinted by clause
  2 of the pre-state; the surviving snapshots are a prefix of the old ones.
  This is `lemma_complete_after_cut`, proved.

The value of verification is concentrated in one place. Probe soundness is
cheap: the equality test is executable and exact. What a test suite cannot
protect is the lower bound, because a bug that drops a needed hint is silent:
the e-graph keeps running and interns a second node with the same content,
possibly in a different class, and congruence closure stops seeing the two as
one. For a client that reads a failed merge as "not equal", that is an
unsound answer. Every operation below is stated so that violating the lower
bound is a build error.

## 5. Bi-abduction: what each operation must assume and what it must leave alone

For each operation we start from the postcondition the e-graph needs, then
abduce two things: the **anti-frame** `M`, the weakest missing precondition
that makes the postcondition provable, and the **frame** `F`, the part of the
state the operation must not disturb so that the invariant survives. The
invariant of §4 is what falls out when every anti-frame is made a permanent
clause. In the tables, `pre` is `old(self)` and `post` is `final(self)`.

### `probe(content) -> Option<G>`

- Wanted: `None ⟹ ∀ j < |view|. ¬eq_spec(view[j], content)`.
- Abduced `M`: every live cell with content equal to `content` is hinted
  under `fp(content)`. Generalised over all queries this is clause 1 of
  `complete`, and it is why clause 1 quantifies over every cell rather than
  over the queried fingerprint.
- Frame `F`: the arena, the snapshots and the buckets. A probe's only
  mutation is the lazy drop of an id at or past the live length, whose
  legality is the compaction lemma below with `F` restricted to live cells.

### `push(content) -> id` (the `Inserted` arm)

- Wanted: `post.view == pre.view.push(content)`, `post.complete()`.
- Abduced `M`: none beyond `pre.complete()` and capacity; the new cell is
  hinted by the operation itself, so clause 1 extends; the snapshots are
  untouched, so clause 2 is inherited.
- Frame `F`: every existing hint survives (`note_hint` preserves buckets),
  and the snapshot stack is unchanged.

### `set(id, content)` — the rewrite half of `recanonize_node`

- Wanted: `post.view == pre.view.update(id, content)`, `post.complete()`.
- Abduced `M`: the *new* content must be hinted under its fingerprint (the
  operation does this), and the *old* content's hint must survive if any live
  snapshot holds it at `id`. The cheapest sufficient `M` is "old hints are
  never removed here", which is what the arena does; it is a legal
  over-approximation because the invariant is a lower bound.
- Frame `F`: all other cells, all other hints, the snapshots.

### `recanonize_node(id, find) -> collisions` (the full operation)

- Wanted, beyond `set`: the collision report is complete —
  `(∃ j ≠ id. j < |view| ∧ eq_spec(view[j], new)) ⟹ collisions ≠ ∅`, and
  sound — every reported pair names two live cells with equal content.
- Abduced `M`: the collision probe must run *after* the write and exclude
  `id`, with `complete()` holding on the post-write state; that is exactly
  the probe contract with `skip = id`. No further assumption.
- Frame `F`: with `PROOFS`, the history column gains one entry the first time
  `id` is rewritten and is otherwise untouched; `original_children(g)` is
  then the first recorded content for `g`, and the history column is itself
  a `Member` so a restore rolls it back with the arena.

### `restore_frame(k)` / `reset_frame(k)` / `pop_frame`

- Wanted: `post.view == pre.snapshots[k]`, `post.complete()`, and *no index
  mutation* (the performance property the design rests on).
- Abduced `M`: clause 2 of `complete` on the pre-state. This is the
  abduction that puts the snapshot clause into the invariant: restore cannot
  establish clause 1 for its new view from anything else without touching the
  index.
- Frame `F`: the whole index. This frame is what "restore does no index
  work" means as a contract.

### `push_frame`

- Wanted: `post.snapshots == pre.snapshots.push(pre.view)`, `post.complete()`.
- Abduced `M`: clause 1 on the pre-state, since the new snapshot is the
  current view and its cells must already be hinted. Nothing else.
- Frame `F`: the index and the arena's content.

### Compaction and lazy reclamation — the soundness-critical obligations

- Wanted: `post.complete()` after removing a set `D` of hints from a bucket.
- Abduced `M`, the **droppability condition**: for every `(fp, j) ∈ D`,
  neither clause needs it:
  `¬(j < |view| ∧ fp(view[j]) == fp)` and
  `∀ k. ¬(j < |snapshots[k]| ∧ fp(snapshots[k][j]) == fp)`.
  The two executable rules discharge it in two ways:
  1. `j` at or past the live length: `j` is beyond every snapshot too,
     because every saved length is at most the current length (a clause of
     the arena column's `wf`). Provable at any depth.
  2. no mark live and `fp(view[j]) ≠ fp`: the snapshot stack is empty, so the
     second conjunct is vacuous, and the first is the executable test. The
     guard "no mark live" must be the *group's* truth: with the external
     history, that is the lockstep between this member's depth and the
     group's, which `ForkHistory` maintains and which the verified twin states
     as `depth_spec == snapshots.len()`.
- Frame `F`: every hint not in `D`, the arena, the snapshots.

Dedup and move-to-front need no `M`: a bucket's meaning is a set, and both
are permutations or duplicate removals of it.

### The dual duty: writes must hint

The abductions above expose the invariant's other failure mode. Clause 1 can
be broken by a write that forgets to hint just as silently as by a drop that
removes too much. Every content mutation (`push`, `set`, the rewrite inside
`recanonize_node`, the child pool's `set` in the variable-arity cache) carries
`post.complete()` in its postcondition, so a forgotten hint is a build error
rather than a convention.

## 6. Public API and contracts

Contracts are written in the verified crate's idiom (`requires`/`ensures`
over the spec functions `view`, `snapshots_view`, `complete`, `eq_spec`,
`fp_spec`). Each is total: preconditions are `wf` only; misuse is refused
through the documented panic branch, as everywhere in the crate.

### `HintContent` (existing)

```
trait HintContent {
    spec fn eq_spec(a: &Self, b: &Self) -> bool;
    fn content_eq(a: &Self, b: &Self) -> (r: bool)  ensures r == eq_spec(a, b);
    spec fn fp_spec(&self) -> u32;
    fn fp(&self) -> (r: u32)                          ensures r == self.fp_spec();
    proof fn lemma_fp_respects_eq(a, b)  requires eq_spec(a, b)  ensures a.fp_spec() == b.fp_spec();
}
```

Implemented by the three content types: `FixedArityNode<G, O, K>` (equality
on `op` and the `K` children, global id excluded), the variable-arity node
paired with its pool span (equality on `op` and the span's elements), and the
literal node (`op` and literal id). The routing lemma is an obligation on each
type, discharged from the executable hash's determinism, never assumed.

### `NodeArena<T, I, TRACK>` (the existing `HintedArena`, extended)

```
new_kind(kind) -> arena           ensures wf, view.len == 0, snapshots.len == 0
len(&self) -> I                   ensures r == view.len
get(&self, id) -> T               ensures id < view.len ⟹ r == view[id]
push(&mut self, t) -> Result<I>   ensures Ok(id) ⟹ id == old.view.len ∧ view == old.view.push(t) ∧ snapshots unchanged ∧ complete
set(&mut self, id, t)             ensures id < old.view.len ⟹ view == old.view.update(id, t); snapshots unchanged; complete
probe(&self, t) -> Option<I>      ensures Some(id) ⟹ id < view.len ∧ eq_spec(view[id], t)
                                          None    ⟹ ∀ j < view.len. ¬eq_spec(view[j], t)
probe_skip(&self, t, skip) -> Option<I>   same, with j ≠ skip in both clauses
compact(&mut self, fp)            ensures view, snapshots unchanged; complete   (the droppability lemma inside)
Member: push_frame / reset_frame / restore_frame / pop_frame / depth_exec / can_push_now
                                  ensures the Member contract, plus complete, plus index unchanged on the restores
```

Additions to the existing arena: the packed single-id slot (`bucket_spec`
becomes a match on the slot's tag), `probe_skip`, move-to-front (a bucket
permutation, no contract change), `compact` with the two droppability rules
as proof obligations, and the `depth_spec == snapshots.len()` lockstep clause
that the "no mark live" rule reads.

### `FixedArityCache<G, O, L, K, TRACK, PROOFS>`

```
probe(&self, op, children) -> Option<G>
    ensures Some(g) ⟹ ∃ j < view.len. view[j].op == op ∧ view[j].children == children ∧ view[j].global_id == g
            None    ⟹ ∀ j < view.len. ¬(view[j].op == op ∧ view[j].children == children)
probe_or_insert(&mut self, g, op, children) -> InsertResult<G, L>
    ensures Hit { global_id: g' }  ⟹ view unchanged ∧ (∃ j. content(view[j]) == (op, children) ∧ view[j].global_id == g')
            Inserted { local_id } ⟹ local_id == old.view.len ∧ view == old.view.push(node(g, op, children))
            complete; snapshots unchanged
recanonize_node(&mut self, id, find, collisions, touched)
    requires id < old.view.len
    ensures let new = canon(old.view[id], find);
            new.children == old.view[id].children ⟹ nothing changes
            otherwise: view == old.view.update(id, new); complete;
                       (∃ j ≠ id. j < view.len ∧ content(view[j]) == content(new)) ⟹ collisions grew by a pair naming view[id].global_id and such a j's global_id;
                       every appended pair names two live cells with equal content;
                       touched == old.touched.push(new.global_id);
                       PROOFS ⟹ history == old.history ∨ history == old.history.push(old.view[id])  (the latter iff first rewrite of id)
original_children(&self, g) -> Option<[G; K]>
    ensures Some(c) ⟹ ∃ h ∈ history. h.global_id == g ∧ h.children == c ∧ h is the earliest such entry
            None    ⟹ ∀ h ∈ history. h.global_id ≠ g
Member as the arena's, applied jointly to the arena and (with PROOFS) the history column.
```

`insert` and `insert_fp` are `probe_or_insert`'s inserted arm exposed for
callers that have already probed; their contract is `push`'s.

### `VariableArityCache<G, O, C, L, TRACK, PROOFS>`

The same contracts with content `(op, pool[start .. start+len])`, plus:

```
children_vec(&self, node) -> Vec<C>   ensures r@ == pool_view.subrange(node.start, node.start + node.len)
pool_get / pool_set                   the pool column's get/set; pool_set additionally ensures complete
                                      (a child rewrite changes the content of every node whose span covers it, so it re-hints each of them —
                                       this is the one place the abduced M is non-trivial and is stated as a precondition on the caller's
                                       protocol: recanonization rewrites spans through recanonize_node, never through raw pool_set)
```

The abduction for `pool_set` is worth stating plainly: a raw write to a
shared child cell changes the content of every node whose span contains it,
and the lower bound then demands a hint for each. Rather than pay that scan,
the verified cache makes `pool_set` crate-private and routes every child
rewrite through `recanonize_node`, whose contract hints the one node it
rewrites. The public surface then has no operation that can break clause 1.

### `LitCache<G, O, V, L, TRACK>`

The fixed-arity contracts with content `(op, lit)` and no recanonization
(literal content never changes), so no history column and no `set`.

## 6a. The store: the two-step id protocol and the routing bijection

The caches do not work alone. A node's *global* id `G` is what the rest of
the e-graph holds (classes, use-lists, proofs); its *local* id `L` is a
position in one of the ten kind-specific caches. The node store owns the
mapping and the minting of global ids, and every cache's correctness theorem
is only useful through it. This section states the protocol and the
invariant that makes the caches one structure, again by abduction.

### The routing table

`TypedRouting` is an `AppendOnlyVec<NodeRef, Index, TRACK>` (verified) plus
one flag. A global id *is* a position in that column: `routing[g]` is the
kind-tagged local id `Kind(l)` of the node minted as `g`. Ids are never reused
while a node lives, and a restore rolls the column back by length, so the
column carries the mark/restore proofs already.

### The two-step protocol

Minting a node is a probe-then-commit in which the global id is chosen
*before* the cache is consulted, because the cache stores the global id in
the cell it appends:

```
reserve() -> g            requires ¬reserved
                          ensures  g == |entries| ∧ reserved ∧ entries unchanged
probe_or_insert(g, content)   (the cache; §6)
finalize(g, Kind(l))      requires reserved ∧ g == |entries|
                          ensures  entries == old.entries.push(Kind(l)) ∧ ¬reserved
unreserve()               requires reserved
                          ensures  ¬reserved ∧ entries unchanged
```

`add(op, children)` is: reserve `g`; dispatch on the operator's kind to one
cache; on `Inserted { l }` finalize `g ↦ Kind(l)` and answer `Fresh(g)`; on
`Hit { g' }` unreserve and answer `Existing(g')`. The flag is the executable
form of a linear token: exactly one reservation is open at a time, and every
frame operation clears it.

### The store invariant

Let `C_kind` be the cache of each kind. The store's `wf` is the caches' and
the routing's `wf` together with three clauses that tie them:

```
route_ok:    ∀ g < |routing|. routing[g] == Kind(l) ⟹ l < |C_kind.view| ∧ C_kind.view[l].global_id == g
cell_ok:     ∀ kind, l < |C_kind.view|.  let g = C_kind.view[l].global_id in  g < |routing| ∧ routing[g] == Kind(l)
lockstep:    depth(routing) == depth(C_kind) == depth(pool) for every kind   (one History drives them all)
```

`route_ok` and `cell_ok` together say routing is a bijection between minted
global ids and live cells across all caches. With it the store-level theorem
is:

```
unique_content:  ∀ kind, l₁ ≠ l₂ < |C_kind.view|. ¬eq_spec(content(C_kind.view[l₁]), content(C_kind.view[l₂]))
```

which is each cache's hash-consing theorem, made global by the fact that an
operator's kind is a function of the operator (the registry fixes it at
registration and never changes it), so two nodes of the same content are in
the same cache.

### Abductions

- **`Fresh(g)` must satisfy `route_ok` and `cell_ok`.** The cell appended by
  `probe_or_insert` carries `g` (the cache's `Inserted` contract), and
  `finalize` writes `Kind(l)` at position `g`. For the two to line up,
  `finalize` needs `g == |entries|` *at commit time*, which is the abduced
  anti-frame of the whole protocol: **no other `finalize` and no frame
  operation may happen between `reserve` and `finalize`.** The flag enforces
  the first executably; clearing the flag on every frame operation enforces
  the second, since a stale reservation across a restore would commit at a
  position that no longer equals `g`. In the verified store the reservation
  is a ghost-tracked obligation carried from `reserve` to `finalize` or
  `unreserve`, and the frame operations require it to be closed.
- **`Existing(g')` must leave the store unchanged.** `Hit` leaves the cache
  unchanged (§6); `unreserve` leaves the routing unchanged. Nothing else was
  touched: that is the frame.
- **Restore must preserve the bijection without repair.** A restore truncates
  the routing and every cache to the same mark (`lockstep`). A cell and its
  routing entry were appended between the same two marks, because the
  protocol forbids a frame operation between them, so they are cut together
  or kept together. This is why `lockstep` is a clause of `wf` and not an
  external assumption, and it is the abduced precondition of the restore
  postcondition `route_ok ∧ cell_ok`.
- **Id reuse after a restore is safe.** `reserve` returns `|entries|`, so
  after a restore the first truncated global id is minted again, and the
  cache's first truncated local id likewise. The old cell's content hint
  `(fp_old, l)` may still be in a bucket; it now names a live cell with
  different content, is skipped by the equality test, and the new content has
  its own hint. The lower bound is untouched. (Droppability rule 1 could have
  removed the stale hint only while `l` was past the live length; once `l` is
  reused the hint is junk, not a hole.)
- **`recanonize` dispatches through the routing.** The union-find hands the
  store a global id; `routing[g]` says which cache and which cell; `route_ok`
  is exactly the precondition `recanonize_node` needs (`l < |view|` and the
  cell is the node `g`). The collision pairs it reports are global ids read
  from cells, which `cell_ok` guarantees route back to those cells.

### Contracts for the store

```
add(op, children) -> Added<G>
    ensures Existing(g) ⟹ store unchanged ∧ g < |routing| ∧ content(cell_of(g)) == (op, children)
            Fresh(g)    ⟹ g == old|routing| ∧ routing == old.routing.push(Kind(l)) ∧ C_kind.view == old.C_kind.view.push(node(g, op, children))
                          ∧ every other cache and the pools unchanged
            store.wf ∧ unique_content
recanonize(g, find, collisions, touched)
    ensures the dispatched cache's recanonize_node contract on cell_of(g); store.wf ∧ unique_content-modulo-collisions
            (the pairs in `collisions` are the only equal-content pairs, and the closure merges them)
Member: the group protocol over routing, caches and pools, ensures store.wf, lockstep, and the bijection after every frame move.
```

`unique_content-modulo-collisions` names the one moment the store is allowed
to hold two equal cells: between a recanonize that created a collision and
the closure's merge, which is how congruence closure works. Its contract is
that the pair is reported; the store's invariant is restored when the
closure merges the classes and the duplicate is retired.

## 6b. Batching and parallel insertion: two designs for the id space

The protocol of §6a is strictly sequential: one open reservation, one cache
touched at a time. Two designs lift that, at different costs.

### Design A: probe first, mint only misses

Probing needs no id; the id exists before the probe in §6a only because the
cache stores it in the cell it might append. So:

```
probe_many(contents) -> [Hit(g) | Miss]      read-only, the probe contract elementwise on one state
insert_many(misses)  -> ids                  sequential appends, ids len, len+1, …; in-batch equal misses deduplicated
```

Failures consume nothing, so there is nothing to return and no gap. The
probe phase is reads only and fans out over the batch and over the ten caches
with no synchronisation; the insert phase is a short sequential tail. The
routing stays append-only and every proof of §6a stands. This is the cheap
design; it parallelises probes, not inserts.

### Design B: a pool-first allocator over a captured routing column

To insert in parallel too, ids must be handed out before the caches are
consulted and returned when the cache says `Hit`. The id space becomes a bump
allocator with a pool of freed lower ids and the theorem:

```
alloc_wf ≜  free ⊆ [0, max)
          ∧ ∀ g < max.  g ∈ free  ⟺  routing[g] is empty
          ∧ ∀ g ≥ max.  routing[g] is empty
alloc():     free ≠ ∅ ⟹ r ∈ free ∧ free' == free \ {r} ∧ max' == max
             free == ∅ ⟹ r == max ∧ max' == max + 1
release(g):  requires g < max ∧ routing[g] empty;  ensures free' == free ∪ {g}
```

Pool-first: nothing is minted beyond `max` while a lower id is free, so gaps
are temporary and the id space consumed is the live count plus the pool. The
model changes in two places, both to columns the crate already verifies:

- **Routing becomes a captured-write column** (`VecI` with the empty entry as
  the niche): a hole filled later is a write below the length, which an
  append-only column cannot roll back. Its `set` captures the old value and a
  restore replays it, so holes reopen exactly as they were at the mark.
- **The pool is a semi-persistent set** (`SparseSet`): after a restore, ids
  allocated since the mark are free again and ids freed since are not. Both
  columns sit under the one history, so `alloc_wf` is restored by lockstep,
  not by repair; that lockstep is a clause of the store's `wf`, as in §6a.

The store invariant of §6a changes only in its domain: the bijection is
between *allocated* ids (`g < max ∧ g ∉ free`) and live cells.

### The parallel shape under design B

```
prologue  (sequential):  for each cache k, hand worker k a slice of `free` and a bump range of `max`
parallel  (rayon):       worker k runs probe_or_insert on cache k alone, taking ids from its slice, recording (g, l) for successes and unused ids
epilogue  (sequential):  write routing[g] = Kind(l) for every success; release every unused id; advance max
```

Nothing in the parallel phase is shared: each worker owns one cache by
`&mut` (the shape the restore fan-out already uses) and its own id slice.
The verified contracts are therefore single-threaded per cache and the proofs
never see an interleaving; the store-level `alloc_wf` and bijection are
established by the epilogue from the workers' records. The two constraints of
design A carry over: equal misses in one batch land in one cache and are
caught by that cache's sequential loop, and a node whose child is in the same
batch needs the child's id first, so batches are layers.

### Cost and choice

Design A costs nothing per node beyond today. Design B costs, per inserted
node, a captured set plus a pool pop instead of a push (a few nanoseconds
against a probe that costs tens), and a pool push per pre-reserved id that
turned out to be a hit; it gains parallel inserts across caches. Which is
worth it depends on how much of a saturation round is insertion into distinct
caches, a number not yet measured. The single-node `add` of §6a is the
degenerate batch of either design.

## 7. Trust

Nothing new. The arena's only external fact is the hasher's validity, already
in the ledger (§D-hasher of chapter 2). The routing lemma is a proof
obligation on each content type. The compaction rules are lemmas. The
fingerprint function itself (rapidhash folded to 32 bits) is executable code
whose only proved property is determinism; if it were replaced by a constant,
every theorem would still hold and every probe would scan one bucket.

## 8. Plan

1. **Fixed-arity cache on the arena.** Packed slot, `probe_skip`,
   move-to-front, `compact` with both droppability lemmas, the history column,
   `probe_or_insert` and `recanonize_node` with the contracts above, the
   `Member` impl over arena plus history. Runtime suites against the e-graph
   cache as oracle. Two to three days.
2. **Variable-arity cache.** The pool as a `Member` column, spans, the
   content type over spans with its routing lemma, `pool_set` made private.
   Two to three days.
3. **Literal cache.** One day.
4. **The store.** The routing table is already a verified column; what is
   left is the reservation as a ghost obligation (`reserve` opens it,
   `finalize`/`unreserve` close it, frame operations require it closed), the
   three tying clauses as `wf`, and the store-level theorems `unique_content`
   and the bijection after every frame move. Two to three days.
5. **Wiring.** `NodeStore` on the three verified caches and the verified
   routing; the store and saturation traces paired against the previous
   commit at the usual protocol; the `HintSlot` width test and the
   completeness debug check retired in favour of the contracts. One to two
   weeks, the uncertain part.
