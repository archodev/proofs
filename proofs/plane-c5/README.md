# Monochromatic unit five-cycles in the Euclidean plane

`C5.plane_C5` proves that every function from the real Euclidean plane to
`Bool` admits five distinct points of one color with consecutive distances
one, including the distance from the last point to the first. Chords are
unrestricted. The proof establishes existence.

## Replay

Use a Linux or macOS system with Bash 4 or later, Git, and
[Elan](https://github.com/leanprover/elan). From the directory containing
`lean-toolchain`, run

```sh
elan toolchain install leanprover/lean4:v4.35.0
bash replay.sh
```

The script uses the official Mathlib cache for the imported Mathlib modules.
It builds the bundled Lean sources, then checks the two expanded theorem
statements in `Audit.lean` and compares the printed axiom lists with
`axioms.txt`. A first replay requires network access for the public
dependencies. The version pins are Lean 4.35.0 at
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and Mathlib 4.35.0 at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Lake pins the transitive
packages in `lake-manifest.json`.

With those dependencies installed, the proof and axiom check can be run directly.

```sh
lake build C5
lake env lean Audit.lean
```

## Theorems

Both public statements are in `C5/Final.lean`. The index type is
`Fin 5`, where adding one wraps from 4 to 0.

```lean
abbrev Plane := EuclideanSpace ℝ (Fin 2)
def PlaneMono (c : Plane → Bool) : Prop :=
  ∃ p : Fin 5 → Plane, Function.Injective p ∧
    (∀ i : Fin 5, dist (p i) (p (i+1)) = 1) ∧
    ∀ i, c (p i) = c (p 0)
```

| Theorem | Hypotheses on the coloring |
| --- | --- |
| `C5.plane_C5` | Any function `c : Plane → Bool` |
| `C5.measurable_plane_C5` | The true color class is null-measurable for `volume`, which allows Lebesgue completion |

The two proofs first work in the complex plane. The orthonormal basis
`Complex.orthonormalBasisOneI` supplies the isometry to the requested real
Euclidean space. The measurable case also uses its measure-preserving property.

## The two-circle lemma

Write ζ = (−1 + i√3)/2 and ρ = (−5 + i√11)/6. At the origin, take the two
outer triples Aⱼ = ζʲ and Bⱼ = ζʲρ, and the inner triple Zⱼ = ζʲ(1 + ρ),
with j = 0, 1, 2. For j ≠ k the ordered points
`0, Aⱼ, Zⱼ, Zₖ, Aₖ` make a unit five-cycle, as do
`0, Bⱼ, Zⱼ, Zₖ, Bₖ`. The outer vertices have norm 1, the inner
vertices have squared norm 1/3, and two different inner vertices have
distance 1. The same construction works after any translation and rotation.
`C5.two_circles` checks the distances and injectivity.

Suppose each color occupies a whole outer triple, the inner triple uses
both colors, and the coloring avoids a monochromatic unit five-cycle.
Two inner vertices of the center's color would complete such a cycle
through the outer triple of that color. Consequently exactly one inner
vertex has the center's color. The four points consisting of the center
and the inner triple split two to two. This is `C5.angular_count`.

## Proof map

1. `Geometry` constructs the two-circle configuration and proves that the
   five vertices in each specified cycle are distinct and every successive
   distance is one. `Coloring`, `Prism` and `Fold` prove its binary coloring
   restrictions and the equilateral prism restrictions.
2. `Density`, `Support`, `Angles`, `Boundary` and `Measurable` prove the
   measurable theorem via area density, support at a common boundary point,
   and an irrational circle rotation. `Stability` proves stability of the
   density witness under perturbations.
3. `Model` constructs the stationary law from a hypothesized avoiding
   coloring on the complex algebraic carrier. The bundled proof of Haar
   rigidity yields vanishing off-diagonal correlations of its residual
   vectors. `Average`, `Sampling` and `ShapeDensity` show that if the
   residual vanished, a measurable coloring would contradict the density
   witness. Algebraic unit-pentagon approximation is proved here.
4. `Limits`, `ConvexLimit`, `Rooted`, `AngularTransfer`, `Purity` and
   `Moments` transfer the rooted restrictions and prove that some
   monochromatic unit triangle must have positive probability.
   `Flex`, `MovingFold` and `Triangles` classify the three projected values
   on a unit triangle. `Agreement` and `PrismLaw` convert the classification
   and prism constraint into the contradiction in `Final`.

The axiom audit of each final theorem reports only `propext`,
`Classical.choice` and `Quot.sound`. The Haar-rigidity proof is included as
Lean source. The density and transfer arguments also have checked proofs.
The axiom report in `axioms.txt` includes named steps from each argument.

The problem is the five-cycle part of [Axenovich, Liu and Sagdeev,
Question 3](https://arxiv.org/html/2512.15516v3#S6.SS1).
Upstream proof credits and licensing are in [THIRD-PARTY.md](THIRD-PARTY.md).

## Statement and source audit

In Section 1.1 the paper defines a unit-copy by a bijection from the graph
vertices onto a set of points, with unit distance on every graph edge.
Section 6.1, Question 3 asks for the least ℓ between 2 and 13 for which
every two-coloring of the plane contains a unit-copy of the cycle of length
2ℓ + 1. It explicitly asks whether ℓ = 2. The checked five-cycle theorem
gives ℓ = 2, the lower end of that interval. [Paper, v3](https://arxiv.org/html/2512.15516v3#S6.SS1)

The independent type check in `Audit.lean` uses this expanded statement.

```lean
example (c : EuclideanSpace ℝ (Fin 2) → Bool) :
    ∃ p : Fin 5 → EuclideanSpace ℝ (Fin 2), Function.Injective p ∧
      (∀ i : Fin 5, dist (p i) (p (i + 1)) = 1) ∧
      ∀ i : Fin 5, c (p i) = c (p 0) :=
  C5.plane_C5 c
```

Injectivity gives a bijection onto the five-point image. Addition in
`Fin 5` makes the five successors 1, 2, 3, 4, 0. The distance
condition specifies those five edges and permits all chord distances.
The quantifier covers constant colorings as well as those using both
colors. The algebraic carrier is constructed inside the proof.

To replay the compiled declarations in the stock Lean kernel after
running `bash replay.sh`, run

```sh
LEAN_NUM_THREADS=1 lake env leanchecker -v C5 Erdos173 OAI
```

This rechecks each of the 66 library modules against its imports. The
standalone audit is elaborated separately by the replay script. The
file `axioms.txt` is its path-free expected output. Every archive member
is listed in `INVENTORY.txt`.
