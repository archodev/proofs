# Two thin-cuboid dismantlings in Lean 4

This source verifies two finite counterexamples to Conjecture 2 of Barát and
Wanless. A lawful path from the full cuboid leaves an independent terminal
set of the indicated size.

| Cuboid | Deletions | Survivors | Theorem in namespace `Cuboid` |
| --- | ---: | ---: | --- |
| 2 × 3 × 9 | 37 | 17 | `dismantling_2_3_9` |
| 3 × 3 × 6 | 39 | 15 | `dismantling_3_3_6` |

## Replay

From the repository root, run these commands with Elan installed. Once the
pinned toolchain is installed, the file checks offline.

```sh
cd proofs/thin-cuboid
elan toolchain install leanprover/lean4:v4.19.0
lean --version
lean --trust=0 CuboidDisproof.lean
```

The checked release is Lean 4.19.0, commit `6caaee842e94`, x86-64 Linux.
The last seven commands in the source print the axioms of the two
dismantlings, the two ordinary-solution theorems, and the three negations.
Each reports `[propext, Quot.sound]`.

## Statements and scope

The two main negations have the following types.

```lean
Cuboid.not_second_clause :
  ¬ (∀ k : Nat, 0 < k → (Cuboid.HasSolution 2 3 k ↔ k = 6))

Cuboid.not_third_clause :
  ¬ (∀ k : Nat, 0 < k → (Cuboid.HasSolution 3 3 k ↔ k % 2 = 1 ∨ k = 4))
```

`Cuboid.HasSolution a b k` asserts that there is a reachable independent
position whose size is `(a*b + a*k + b*k + 2) / 3` using natural-number
division. Both examples attain the unrounded bound, respectively 51/3 and
45/3. The positive side lengths in the theorems reflect the ordinary cuboid
interpretation. Section 6 gives no separate cutoff for the varying length.
Both witnesses have all sides at least 2 and a longest side strictly greater
than 3. The file also states `not_second_clause_long` under that strict
length restriction. The formal scope is clauses two and three.

A vertex belongs to `Fin a × Fin b × Fin k`. In the two constructions,
Dukes, Noel and Romer use row, column, layer order. A one-based triple
`(r,c,l)` in their diagrams is `(l-1,r-1,c-1)` in the Lean arrays.
Face adjacency requires one natural-coordinate difference of one
and equality of the other two coordinates. The three nested enumerations
visit each vertex once. A deletion requires a present vertex with exactly
three neighbors among the vertices currently present. Its successor position
clears precisely that vertex. `Dismantles` records each such step, and
`Reachable` fixes the starting position to `full`. Independence is checked for every pair of present vertices,
and the proof derives terminality from independence.

The witness vectors give one label per vertex. Zero labels identify the
survivors. Positive labels are processed in decreasing order, and cells
within one label are processed in increasing coordinate order. Every
individual deletion is checked after its predecessors. The endpoint is
checked on every coordinate against the entire zero-label set.
`lawful_sound` converts the ordinary `decide` checks to an inductive proof.
The two existential solution proofs specialize the respective universal
clauses at 9 and 6.

## Sources and dependency notices

János Barát and Ian M. Wanless define the dismantling rule and ordinary
solutions in Section 1. Section 6 states Conjecture 2 and Figure 9 depicts
their examples. The paper appeared in the *Journal of Statistical Physics*
in 2012. [Paper and journal reference](https://arxiv.org/abs/2603.23913)
and [Section 6](https://arxiv.org/html/2603.23913#S6).

The prior percolating constructions are due to Peter J. Dukes, Jonathan A.
Noel, and Abel E. Romer. The two finite instances here use Proposition 5.4
and Figure 11 for length 9, and Proposition 5.8 for length 6. This Lean
source supplies exact-degree deletion certificates for those instances.
[Paper](https://arxiv.org/abs/2209.07594) and
[constructions](https://arxiv.org/html/2209.07594v2#S5).

There is no vendored third-party code, paper text, or artwork. The Lean
formalization and its documentation were written for this task. Both arXiv
records identify the papers' arXiv perpetual non-exclusive distribution
license. The only external software dependency is the stock Lean toolchain
with its standard library. The `Std.lean` entry point credits Lean FRO, LLC
(2024) and names Sebastian Ullrich as author. Lean's upstream license is
Apache-2.0. Additional binary-distribution notices are in the official
release's `LICENSES` file. This source archive carries no separate license
declaration for the newly authored files.
[Lean license](https://github.com/leanprover/lean4/blob/v4.19.0/LICENSE),
[Std notice](https://github.com/leanprover/lean4/blob/v4.19.0/src/Std.lean),
and [official release](https://github.com/leanprover/lean4/releases/tag/v4.19.0).
