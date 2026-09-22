# The `matchable` e-class flag

A per-e-class bit that excludes a whole class from e-matching, generalizing the
node-level `:subsume` to class granularity. It lets a client (the SMT relevancy
layer) *skip* irrelevant e-classes from matching entirely, rather than matching
and then filtering. It is a design doc; CI gates are the source of truth.

## Motivation

Z3 is fast on quantifiers partly because relevancy propagation keeps E-matching
from ever touching irrelevant terms. Our engine already has a node-level
exclusion — `:subsume` (`FLAG_SUBSUMED`) — implemented by **not filing a node
into the matcher's indexes at build time**, so subsumed nodes are never
enumerated as candidates. That is exactly the "skip, don't filter" shape we
want, but at node granularity. A relevancy client needs to shield a **whole
e-class** (all its nodes) when the class is irrelevant, and un-shield it when it
becomes relevant.

Today the satcore adapter computes the relevant cone and filters matcher
candidates one by one (match-then-filter). This primitive inverts that: mark the
class shielded, and the matcher never enumerates it.

## Non-goals

- **Not relevancy itself.** The e-graph stays a theory-agnostic equality engine.
  It offers the generic shield; the *relevancy rules* (the and/or/ite
  witness-polarity propagation) stay in the client, which decides which classes
  to shield. This mirrors Z3's new core, which deliberately keeps
  Boolean-connective semantics out of the e-graph.
- **Not a soundness mechanism.** Shielding only removes matches; see below.

## The primitive

A `matchable: bool` field on the per-class payload (`ClassData` in the
sparse-set-backed `EClasses`), default `true`.

- `matchable == true` (default): the class participates in matching as today.
- `matchable == false` (shielded): none of the class's nodes are filed into the
  matcher's indexes, so the matcher never enumerates them — as a match root or
  as a matched subterm/child (the join walks the same indexes at every level).

Shielded classes **still participate fully in congruence and merges**; only
matching is affected. This is the exact contract `:subsume` has for nodes (a
subsumed node is still a legal child, just not a match candidate).

### Why per-class, not "subsume every node"

Relevancy flips both ways over a class's lifetime and must be O(1) to toggle. A
per-class bit is one write; subsuming/un-subsuming every node of a class would
be O(class size) per relevance change and `:subsume` is monotone (cannot
un-subsume). A settable per-class bit is the right granularity.

## Semi-persistence

The bit lives in `ClassData`, which is stored in the semi-persistent sparse set,
so it **rolls back for free** on `restore`. This is essential: relevancy tracks
a live assignment, so a class shielded/un-shielded within a decision scope must
revert on backtrack. Within a scope relevancy only grows (Z3's invariant:
un-shield as terms become relevant, never re-shield until pop), which is the same
monotone-within-scope + rolled-back model `:subsume` already uses; across scopes
the bit is set both ways, which the semi-persistent store supports.

## Merge rule

Relevancy is class-closed — a class is relevant if *any* member is — so the bit
folds by disjunction on merge:

```
merged.matchable = a.matchable || b.matchable
```

This is added to the existing per-class fold in `EClasses::merge_with`, alongside
`min_monomial` / `atomic`. It is the one place the engine's merge learns the new
field. (Equivalently: a class is shielded only if *both* sides were shielded, so
a merge with any matchable side un-shields the result — the relevancy-closed
behavior.)

## Soundness is free

Shielding can only *remove* candidates, and a match that is never produced cannot
cause an unsound instantiation (the instance lemma `¬q ∨ body[σ]` is what carries
soundness, and not producing it is always safe). So:

- The client may set `matchable` arbitrarily and matching stays **sound**; the
  client's relevancy logic controls **completeness**, never soundness.
- The Verus obligation is therefore small: prove the bit's **semi-persistence**
  (it rolls back with `ClassData`) and the **merge fold** (disjunction), not any
  soundness theorem about matching under shielding. No proof needs to reason
  about *which* classes are shielded.

## API

Mirroring `subsume` / `is_subsumed`:

```
impl EGraph {
    pub fn set_class_matchable(&mut self, id: Cfg::G, matchable: bool);
    pub fn is_class_matchable(&self, id: Cfg::G) -> bool;   // by class root
}
```

`set_class_matchable` resolves `id` to its class root and writes the bit through
the semi-persistent class store (so it is captured and rolls back). Both
directions are supported (unlike `subsume`, which is `|=`-only), because
relevancy un-shields.

## Matcher integration

`IndexStore::build` already filters `FLAG_SUBSUMED` per node. Extend that
predicate: skip a node if its class is not `matchable`. Concretely the build
gains one check, `eg.is_class_matchable(node_root)`, ANDed with the existing
not-subsumed test. Shielded classes then contribute nothing to `by_op`,
`by_repr`, `by_child_pos`, `by_contains`, so the leapfrog join never enumerates
them. The per-node check at build is O(nodes) and cheap (a class-root lookup +
bit read); the win is that the join — the expensive part — is over a smaller
index.

For clients using the compiled matcher directly, this is transparent. For the
satcore adapter's ported matcher (pre-bridge), the same bit is checked in its
candidate loop — still one class-level bit instead of a per-term relevance
recompute, so it is a strict improvement even before the bridge.

## egg-language surface

A command to shield/un-shield a term's class, primarily for testing the
primitive and for egg programs that want "do not match here":

```
(no-match <term>)     ; set the term's class matchable = false
(match-ok <term>)     ; set it back to true
```

The dynamic relevancy use is through the API (relevancy tracks a live
assignment, not a static program annotation); the command exists so the
primitive is exercisable and gate-testable in the `.egg` conformance suite (e.g.
"a shielded class yields no matches; un-shielding restores them; matching stays
in the index-skip path, not a post-filter").

## Interaction with other core work

- Independent of diff-stack compression and shared fork history; composes with
  both (a shielded class in a group of `COMPRESS = true` vectors is well
  defined).
- Depends on the e-matching engine work only to the extent that the index-build
  skip is where it plugs in; the primitive itself (bit + merge fold + API) is
  self-contained.

## Plan

Implemented as part of the core e-graph work (compression, fork-history sharing,
e-matching). Steps:

1. Add `matchable` to `ClassData` (default true) and the merge-fold in
   `EClasses::merge_with`; prove semi-persistence + fold in Verus.
2. `set_class_matchable` / `is_class_matchable` on `EGraph`.
3. Extend `IndexStore::build`'s skip predicate with the class check.
4. egg command `(no-match)` / `(match-ok)` + conformance tests (shield ⇒ zero
   matches; skip-path, not filter).
5. Adapter: replace per-candidate relevance filtering with
   `set_class_matchable` calls driven by the existing relevancy descent.

The satcore integration branch will be rebased onto `main` after this core work
lands.
