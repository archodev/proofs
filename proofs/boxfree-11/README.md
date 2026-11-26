# The minimum number of monochromatic boxes on the 11-cube is zero

The principal Lean theorem is `BoxFree.m11_eq_zero : BoxFree.m 11 = 0`. The same witness construction proves `BoxFree.m16_eq_zero`. This settles Section 8, Problem 1 of Jeremy F. Alm and Alex Miller, *Constructive and computational methods for extremal and near-extremal box colorings*. [Problem 1](https://arxiv.org/html/2611.19635v1#S8) · [Grid and box definitions](https://arxiv.org/html/2611.19635v1#S1)

## Replay

Use the pinned stock Lean 4.19.0 release, commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. With Elan, the included toolchain file selects this release. From the repository root run

```sh
cd proofs/boxfree-11
lean --trust=0 -j1 -t0 -DwarningAsError=true BoxFree.lean
```

The source imports `Init` and prints the axiom dependencies of its six public theorems.

| Theorems in the BoxFree namespace | Axioms reported by Lean |
|---|---|
| noBox11, noBox16 | propext, Quot.sound |
| m_spec, m11_eq_zero, m16_eq_zero, conjecture_false | propext, Classical.choice, Quot.sound |

## Statement correspondence

`Fin n` labels the same coordinate set as the paper's `[n]` by subtracting one. A coloring is an arbitrary function from three such coordinates to `Bool`. The two witness theorems quantify over every pair of distinct values on each axis in either order. `Monochromatic` requires a single common color for the four corners of each of the two faces, eight corners altogether.

`boxCount` enumerates all three pairs independently and counts a box exactly once by requiring increasing endpoints. Equal endpoints are excluded. `m_spec` proves both attainment and the lower-bound property over every coloring, so ties between minimizing colorings give the same minimum. There are no hypotheses on `m11_eq_zero`.

The kernel verifies the table directly using `decide +kernel`. During audit, the expanded eight-corner statement typechecked directly against `noBox11`. Independent enumeration of all 166,375 boxes on side 11 and all 1,728,000 on side 16 gave zero of each color. The 11-cube uses both colors, on 666 and 665 vertices.

## Provenance and licensing

Dean Menezes, *The Three-Dimensional Erdős Box Problem Has Exponent 11/4*, gives the antecedent one-class construction in Construction 3.1. At q = 2, toggling the scalar bit of the first coordinate interchanges edges and nonedges. Consequently both classes are box-free, and restriction to eleven labels on each axis yields the zero minimum. The formalization certifies the resulting two-color table. Its attribution to the field formula was checked separately on all 4,096 entries. [Menezes, Construction 3.1](https://arxiv.org/html/2609.22381v2#S3)

Both cited arXiv versions carry [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The Lean proof is original code for this result. The table was generated from the mathematical formula. The archive contains no vendored code, copied witness file or upstream article text. Lean is an external dependency. Its source is licensed under Apache-2.0 and its binary release carries separate third-party notices. [Lean 4.19.0 license](https://github.com/leanprover/lean4/blob/v4.19.0/LICENSE) · [Release notices](https://github.com/leanprover/lean4/blob/v4.19.0/LICENSES)
