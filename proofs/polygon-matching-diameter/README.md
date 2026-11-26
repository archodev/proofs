# Gross–Šarković Conjecture 2.10

For each positive integer g, the full labelled genus-g chord-swap graph on
n = 2g+1 chords has diameter at most 32g. On this family n+g² = (g+1)².
The resulting ratio tends to zero, refuting the uniform joint lower bound in
Conjecture 2.10. The formalized result concerns the upper bound on this family
and the refutation. A matching linear lower bound is outside this Lean file.

## Source and antecedents

Renan Gross and Anđela Šarković, *Polynomial mixing for polygonal side matchings*,
arXiv:2607.02410v1, July 2, 2026. Definition 1.1 specifies the chain.
Equation (1.1) and Definition 2.4 relate genus to vertex cycles. Theorem 2.2
identifies the connected range. The conjecture concerns the two-parameter
diameter. [Paper and version history](https://arxiv.org/abs/2607.02410v1)
and [Section 2](https://arxiv.org/html/2607.02410#S2).

The paper introduces the canonical diagrams in Definition 2.3 and gives local
canonical moves in Claim 2.5. Claim 2.9 supplies the short-chord creation
argument for n>2g. The proof of Theorem 2.2 uses contraction and lifting of
moves, and Figure 14 illustrates a two-swap extraction with a short chord
beside a Bolza subdiagram. The formal proof establishes a uniform extraction
for every matching in the odd family. It also proves that a local repair of
the target costs at most twelve moves, so the induction costs at most sixteen
moves per handle to a common labelled target.

GrossSarkovic.lean is the original formalization prepared for this result.
The six-side base cases and local swap sequences are original finite
certificates checked inside Lean. Earlier exact enumeration was a diagnostic.
The replay requires only the Lean source and its stock toolchain.

## Exact statements

Both declarations are in the namespace OddDiameter.

```lean
theorem labelled_graph_diameter_bound (g : Nat) (hg : 0 < g) :
    ∃ d, IsDiameter (2*g+1) g d ∧ d ≤ 32*g

theorem no_joint_diameter_omega :
    ¬ ∃ K N : Nat, 0 < K ∧ ∀ n g d : Nat,
      N ≤ n → N ≤ g → 2*g < n → IsDiameter n g d → n+g*g ≤ K*d
```

## Interpretation of the definitions

- **Vertices.** A state is a fixed-point-free involution on Fin (2*n). Side
  label 0 corresponds to the paper's label 1. The clockwise successor is
  addition by one modulo 2n. The vertex permutation sends a side to the
  successor of its mate. The genus predicate is the integer equation
  V+2g=n+1. The theorem orbit_representatives identifies the computed V with
  the number of vertex components. On n=2g+1 the equation gives V=2.
- **Edges.** PaperSwap specifies both alternative pairings on four distinct
  sides from two chords and fixes every other mate. StateWalk uses PaperSwap
  on the fixed-genus subtype. A unit of length is one genuine swap. Omitting
  the Markov holding transitions preserves shortest distances. The state
  type retains all side labels.
- **Diameter.** Within n g k means that every two states have a walk of at most
  k swaps. IsDiameter n g d says that d is the least such k. The canonical
  construction gives a state for every g on the asserted family. The upper
  bound supplies paths between all states. Both nonemptiness and connectivity
  therefore hold on the family used to refute the conjecture.
- **Range.** For g≥1, n=2g+1 gives n≥3 and n>2g, inside the connected range
  of Theorem 2.2. The even case n=2g with an isolated Bolza state does not
  enter. The general Lean predicates accept natural numbers, but the
  counterexamples always have admissible positive parameters.
- **Quantifiers.** The negated bound permits any common threshold N for n and
  g, and any positive integer denominator K. Any uniform positive real lower
  constant can be weakened to 1/K. For proposed K,N the formal contradiction
  takes g=32K+N+1 and n=2g+1. The integer theorem is checked in Lean. The
  interpretation for real constants uses the ordinary Archimedean property.
- **Choice of paths.** Multiple shortest paths, possible extraction sites,
  and choices of canonical tiles require no tie convention. Only existence
  and a length bound enter the diameter statement.

The induction proves constant-cost extraction (labelled_extraction), lifting
of walks through an inserted handle (walk_insert), local restriction and
lifting (patch_count, patch_move), and bounded target repair (repair_three,
use_repair). The six-side base case and bounded local configurations are
enumerated. The genus induction and the endpoint quantifiers are unrestricted.

## Replay and trust

From the repository root, with elan, run

```sh
cd proofs/polygon-matching-diameter
elan toolchain install leanprover/lean4:v4.19.0
elan run leanprover/lean4:v4.19.0 lean --trust=0 -t 0 GrossSarkovic.lean
```

With the pinned stock lean executable already on PATH, run
`lean --trust=0 -t 0 GrossSarkovic.lean`. The verified release is Lean 4.19.0,
commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. The sole import is Std.
A replay from a clean directory with trust level zero produced ten axiom
reports. Both main declarations, and each of the eight intermediate
declarations queried in the source, report the identical list
`[propext, Classical.choice, Quot.sound]`. The proof uses no custom axioms,
admissions, unsafe declarations or native_decide.

## Dependencies and notices

The archive contains original proof source, these notes and the version pin.
It vendors no third-party code, toolchain components or paper assets. The
paper is distributed on arXiv under its perpetual nonexclusive license.
The external Lean 4 toolchain and Std entry point use Apache License 2.0.
The upstream Std.lean header credits Lean FRO, LLC (2024) and Sebastian
Ullrich. The Lean binary distribution also carries notices for bundled
components in LICENSES. Those notices accompany the separately installed
toolchain. No license for the new proof is inferred from Lean's license.
[Pinned upstream license](https://github.com/leanprover/lean4/blob/v4.19.0/LICENSE)
and [Std entry point](https://github.com/leanprover/lean4/blob/v4.19.0/src/Std.lean).
