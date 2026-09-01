# Kangjie ramp-up (`cursor/kangjie-ramp-up-d1be`)

Week 1–2 katas for the Lattice Semantics practicum, on the team fork of Semper.
This directory is a standalone crate so it does not join the engine workspace CI.

```bash
cd practicum/kangjie
cargo test
```

- `REPORT.md` — what each kata produced and what is still gated on Verus.
- `egg/` — saturate / diverge / union-by programs, plus the §2 baseline.
- `verus/interval_u8.rs` — kata 3–5 contracts to run under the pinned Verus.
- `kata6-trace.md` — hand trace of `(union c (True))`.

Remi’s workflow: develop on this branch, then open a PR into `lasyaalluru/semi-persistent` `main`.
