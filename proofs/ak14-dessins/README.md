# Universal oriented uniqueness for the tetrahedral passports

The entry point is `AK14/Dessins.lean`. Theorem `AK14.oriented_triples_conjugate` applies to both families of Adrianov–Kreines, Theorem 1.3, in arbitrary degree. The single sheet permutation it produces acts on the three labeled permutations in their given order.

## Statement

Let p have rows (2^r,a | 3^s,b | 3^t,c) or (2^r,a | 3^s | 3^t,b,c), where a,b,c are positive, a is odd, and neither b nor c is divisible by 3. All three rows sum to the degree n, each is a genuine branch row, and the total number of parts in the three rows is n+2. Fixed points count as parts of size one. For every two ordered triples T and U on n sheets that each have product one, generate a transitive group, and have precisely those rows, there exists q in S_n with U_i = q T_i q⁻¹ for all three i. This is the orientation-preserving, color-preserving notion of dessin isomorphism over the fixed target.

* `tetrahedral_dessin_uniqueness` proves universal uniqueness.
* `oriented_triples_conjugate` exposes each hypothesis and the common conjugator.
* `exactly_one_for_realized_passport` gives exactly one class given one realization.
* `tetrahedral_exactly_one` combines the checked uniqueness with `Theorem13Existence`, the separate existence result proved in the source paper. The Lean project does not independently formalize the source's existence proof.

See [Adrianov–Kreines, §1.4](https://arxiv.org/html/2606.10079#S1.SS4). Van Hoeij–Weil's earlier pullback uniqueness, including the order-three exchange, is credited in the [mathematical proof](conjecture_1_4.md). See [Lemma 5.2 and Remark 5.3](https://www.math.fsu.edu/~hoeij/papers/issac05/f99HoeijWeil.pdf#page=6).

## Formal proof

1. Glue two triangles per sheet of an arbitrary ordered transitive triple. Compute the corner cycles and construct a complex power chart at every point. Path lifts in the resulting analytic surface recover the given generators.
2. Compute the orders of the differential of this particular projection. The divisor has degree −2 by the cycle-count equality. Vanishing for negative degree and the canonical-dimension identity give analytic genus zero. This step proves the needed genus statement on the actual glued surface.
3. Riemann–Roch gives a meromorphic function with a single simple pole. Its degree-one map is bijective and its inverse holomorphic. This constructs the biholomorphic sphere parameter used in the rest of the proof. The simple-pole, Riemann–Roch and inverse results use the pinned Rado Kirov Dolbeault library as ported and extended by Michael R. Douglas and the Jacobian challenge contributors.
4. Normalize the three exceptional points. The projection is represented by a rational function with the prescribed germs and the three labeled monodromies. Tetrahedral Schwarzian uniqueness, irreducibility of the tetrahedral inverse pullback, and descent with fixed branch labels give equality of the normalized maps. Lifting the same loops gives the sheet conjugator.

## Replay

Use stock Lean 4.30.0, commit d024af099ca4bf2c86f649261ebf59565dc8c622, and its bundled Lake. Mathlib is pinned to c5ea00351c28e24afc9f0f84379aa41082b1188f. The upstream Rado Kirov dependency is the vendor/kirov-dolbeault-port subtree of [the Jacobian challenge](https://github.com/mrdouglasny/jacobian-challenge/tree/8ce1ec28aed1c78b3b39d0bae26e2858c82f5143/vendor/kirov-dolbeault-port), commit 8ce1ec28aed1c78b3b39d0bae26e2858c82f5143. The bootstrap checks the revision, applies the included patch, selects the 298 dependency modules in the actual Lean import closure, and verifies the resulting source digest. Five upstream files have narrower or explicit Mathlib imports. Four further files omit seven unrelated declarations. No retained proof was replaced or weakened. The original upstream license and provenance are retained. It requires Python 3.12 or newer, git, and initial read access to the public dependencies. All project proof sources are in this archive.

Run `sh replay.sh` from the extracted ak14-lean430 directory with Lean available via elan or the pinned toolchain on PATH. The script runs the following mathematical and audit checks.

```sh
python3 prepare_dependency.py
lake build
lake env lean Audit.lean > replay-audit.txt
python3 check_audit.py replay-audit.txt
lake env lean AuditImports.lean
lake env leanchecker -v AK14.Dessins AK14.Uniformization
python3 check_dessins.py
```

The project was rebuilt with an initially empty project build directory using the pinned, locally built dependency. `audit-output.txt` records the declarations and their actual axiom reports. All 13 audited results depend only on `propext`, `Classical.choice` and `Quot.sound`. `AuditImports.lean` additionally checks the transitive axioms of every AK14 and Kirov declaration in the actual imported environment. It aborts on any axiom outside the three listed above. The transcript is `import-audit.txt`. `kernel-replay.txt` records the independent stock leanchecker run on the two named modules. The finite checker reports eight counts of one and two classes for the mirror-pair control in the source's Example 1.2.
