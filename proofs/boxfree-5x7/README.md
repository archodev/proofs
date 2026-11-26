# The exact 5 × 7 box-free height is 52

`Box57.lean` is a standalone Lean 4.19.0 source file. It imports `Std`
and contains the complete coloring and proof. In the namespace `Box57` the
top-level theorem has the following type.

```lean
theorem exact_52 :
    (∃ f : Coloring 52, BoxFree f) ∧
    (∀ h : Nat, 52 < h → ¬ ∃ f : Coloring h, BoxFree f)
```

Here `Coloring h` abbreviates `Fin 5 → Fin 7 → Fin h → Bool`. For every
pair of distinct rows, columns and layers and each color, `BoxFree`
forbids all four row-column intersections from having that color in both
layers. Adding one to each coordinate gives the paper's indexing. Layer
order, the two color names, and the use of curried functions have no effect
on the box predicate. At height 52 it covers 278,460 nondegenerate boxes.
The upper bound quantifies over every natural height and every coloring.
`colorable_iff` also characterizes the smaller heights, including zero.

## Replay

With Elan installed, run the following from the repository root.

```sh
cd proofs/boxfree-5x7
elan toolchain install leanprover/lean4:v4.19.0
lean --githash
lean --trust=0 -t 0 -DwarningAsError=true Box57.lean > /tmp/box57-axioms.actual
diff -u AXIOMS.txt /tmp/box57-axioms.actual
```

The expected compiler commit is `6caaee842e9495688c1567e78c0e68dbb96942aa`.
A stock standalone installation of that release also works with its `bin`
directory on PATH. Checking requires no network access once Lean is installed.
The source emits eight axiom lists. The comparison should exit successfully
with empty output.

## What the proof checks

The 52 row-major masks have the upper-left cell at bit 34. The kernel checks
that all 1,820 cells agree with a second table that stores one word per cell.
A bit in the intersection of four colored words is set precisely when that
layer contains the corresponding monochromatic rectangle. Each intersection
is zero or a power of two, which proves box-freeness of the original masks.

In an arbitrary layer, each column contributes at least four same-color
row pairs. For each of the twenty row-pair/color choices, the number of
matching columns exceeds the number of matching column pairs by at most
one. Consequently the layer has at least eight monochromatic rectangles.
A box-free stack can use each of the 420 colored rectangle positions in
at most one layer, giving 8h ≤ 420. The proof uses the distinctness
hypotheses on all three axes and makes no assumptions about layer symmetry.

An independent check of the masks counted eight rectangles in each of the
52 layers, 416 distinct colored rectangle positions, and zero monochromatic
boxes among all 278,460 choices. The Lean proof carries its own verification.
