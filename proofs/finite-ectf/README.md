# Finite existentially complete triangle-free graphs

For each natural number k, Problem29.finite_ectf supplies a finite simple triangle-free graph with the following extension property. Given disjoint vertex sets A and B of total size at most k, if A is independent, there is a vertex outside both sets adjacent to every member of A and to no member of B. Problem29.finite_4ectf specializes this single result to k = 4.

## Extension to every forbidden clique size

The [all-clique-sizes extension](HENSON.md) and its first-order consequence are also formalized. The original triangle-free file below is unchanged.

## Replay

From the repository root, with Elan and Git available, run

```sh
cd proofs/finite-ectf
lake build Problem29
lake env lean --trust=0 Problem29.lean
lake env lean --trust=0 CheckStatement.lean
```

Lean is pinned to 4.19.0 (6caaee842e9495688c1567e78c0e68dbb96942aa). Lake pins Mathlib to c44e0c8ee63ca166450922a373c7409c5d26b00b and records the exact revisions of its eight dependencies in lake-manifest.json. A fresh installation needs those upstream sources or existing local copies of them.

Both checks print

```text
'Problem29.finite_ectf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Problem29.finite_4ectf' depends on axioms: [propext, Classical.choice, Quot.sound]
```

CheckStatement.lean directly assigns each existing theorem to its fully expanded proposition. AUDIT.md records the source comparison, mathematical provenance, and dependency notices.
