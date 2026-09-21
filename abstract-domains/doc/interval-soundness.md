# Interval soundness model

This document describes the unsigned interval implementation generated for
`u8`, `u16`, `u32`, and `u64` by `abstract-domains/src/domains.rs`. The live
verification inventory is in [`proof-status.md`](proof-status.md).

## Representation

An interval is either the canonical empty value or a closed, non-wrapping
range:

```text
Interval { is_bottom, lo, hi }
gamma(bottom) = {}
gamma([lo, hi]) = { x | lo <= x <= hi }
wf(bottom) = is_bottom && lo == 0 && hi == 0
wf(nonbottom [lo, hi]) = !is_bottom && lo <= hi
```

`Interval::has(x)` is the Verus specification of membership in `gamma`.
`bottom()` is the canonical empty value, `constant(x)` denotes `{x}`, and
`top()` is `[0, MAX]`. The representation does not encode nonempty wrapped or
disjoint ranges.

## Verified transfer contracts

The executable methods carry containment postconditions:

- `add(a, b)` contains every machine-width wrapping sum of one value from each
  operand. If endpoint arithmetic can wrap or invert the range, it returns
  `top`; otherwise monotonicity gives `[a.lo + b.lo, a.hi + b.hi]`.
- `join(a, b)` is the interval hull and contains every value represented by
  either operand.
- `meet(a, b)` returns their intersection and returns `bottom` when the
  intersection is empty.
- `div_const(a, d)`, with `d > 0`, returns `[a.lo / d, a.hi / d]` and contains
  every concrete quotient. Its proof uses monotonicity of unsigned division.

Each result is also proved well formed. These are universal Verus
postconditions, not conclusions inferred from the Rust property tests.

`meet_spec` and `join_spec` expose the executable lattice operations to proofs.
For each enabled machine width, Verus proves that meet and join are idempotent,
commutative, and associative; that top is the identity for meet and absorbing
for join; and that bottom is absorbing for meet and the identity for join.

## Reduced-product use

`ReducedProduct` denotes the intersection of its Tnum, Anum, Interval, and Unum
components. Its reduction step narrows interval bounds using information from
the other domains and then rebuilds compatible component values. Operations
without an interval transfer function use `Interval::top()`. This loses
interval precision but remains sound because `top` contains every machine
value and the other components continue to constrain the product.

## Scope

The current generated interval API does not provide interval-by-interval
division, alarms, abstract booleans, backward assumptions, wrapped intervals,
or strided intervals. The standalone `exec_tnum.rs` experiment has a broader
Rust surface, but it is not the contract inventory described here. No claim in
this document applies to the disabled `u128` instantiation.

The maintained designs and proof obligations for those extensions are in
[`future/interval-extensions.md`](future/interval-extensions.md).

The mirror tests in `abstract-domains/tests/fuzz.rs` add finite executable
evidence, including exhaustive lattice-law checks over a small set of `u8`
intervals. The machine-checked claim comes from:

```text
cargo verus verify
```

CI separately rejects project-local `admit()`/`assume()` calls. The pinned
`vstd` dependency contains admitted specifications, so global
`--no-cheating` is not a supported reproduction command for this revision.
