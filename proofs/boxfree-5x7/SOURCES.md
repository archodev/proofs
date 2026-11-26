# Sources, construction and dependency notices

Jeremy F. Alm and Alex Miller, *Constructive and computational methods for
extremal and near-extremal box colorings*, arXiv:2611.19635v1. Section 1
defines the grid and the eight-corner box. Section 4 gives the colored
rectangle counting bound. Section 6 constructs 50 layers, gives 52 as the
upper bound, and conjectures 50. Section 8, Problem 3 asks for the largest
attainable height. This formalization resolves the pair (5,7). The arXiv
record labels this version CC BY 4.0. [Paper](https://arxiv.org/html/2611.19635v1)

The authors' earlier 50-layer witness is in their public repository at
commit `a1494d7027a2ca36261ad8b3660c686b3083ba41`. GitHub listed no
repository license at the time of review. This archive includes none
of that repository's files. [Earlier certificate](https://github.com/algorithmachine/box-free-colorings/blob/a1494d7027a2ca36261ad8b3660c686b3083ba41/5x7x50_exact_zero_certificate.txt)

Joshua Cooper, Stephen Fenner and Semmy Purewal earlier studied the
equivalent guaranteed-grid formulation in *Monochromatic Boxes in Colored
Grids*. [Paper](https://arxiv.org/abs/0810.3019)

The 52-layer witness and Lean source were generated in the proof-discovery
and formalization work for this result. The search packed orbits of layers
under two commuting involutions. The resulting coloring has twelve
four-layer orbits and two two-layer orbits. The earlier 50-layer certificate
was a reference and was not an input to this packing search. Only the
resulting masks and their transposition enter the formal construction.

## Software

The sole Lean import is stock `Std`. The upstream Lean license is Apache
License 2.0. The `Std.lean` entry point carries a 2024 Lean FRO, LLC
copyright notice and credits Sebastian Ullrich. The official binary release
also ships a `LICENSES` file for bundled components. Lean and Std are
installed separately. No upstream software, third-party certificate,
binary, or copied paper text is vendored in this archive. [Lean license](https://github.com/leanprover/lean4/blob/v4.19.0/LICENSE) · [Std notice](https://github.com/leanprover/lean4/blob/v4.19.0/src/Std.lean)
