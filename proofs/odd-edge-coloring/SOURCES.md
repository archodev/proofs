# Sources and scope

The mathematical statement is Conjecture 6 of Mikio Kano, Shun-ichi Maezawa and Kenta Ozeki, “Odd Edge Colorings of Graphs with Odd Order,” arXiv:2604.15824v1 (17 April 2026). Its introduction uses “graph” for a simple graph. An odd color class has odd degree at every vertex incident to an edge in that class. At all other vertices its degree in that color is zero. [Primary source](https://arxiv.org/html/2604.15824)

## Antecedents

- The multiple-even-vertex proof follows the path extension of Section 4.2 (Theorem 7). The underlying parity-join, forest coloring and odd-factor ingredients are Lemmas 11–13 of the paper. The paper attributes the latter two to M. Petruševski, “Odd 4-edge-colorability of graphs,” *Journal of Graph Theory* 87 (2018), 460–474, Propositions 2.3 and 2.6(i).
- The star configuration generalizes the construction in Section 4.3 for a universal even-degree vertex. The mixed-cycle argument adapts the complementary cycle edge sets, opposite support parities and Eulerian-subgraph coloring from Section 4.4. The separator and homogeneous-side arguments supply configurations when deleting the unique even-degree vertex leaves a graph with a separating pair. These ingredients are assembled here for Conjecture 6.
- The prescribed-edge, avoided-vertex form of the induced nonseparating cycle theorem is Theorem 14 of the source paper, attributed to W. T. Tutte, “A theory of 3-connected graphs,” *Indagationes Mathematicae* 23 (1961), 441–455. The Lean project proves this form and derives the induced-path result it uses. It also proves the nonadjacent-pair fact in the cases needed for the star argument. See Theorem 15 and Lemma 17 of the paper for the corresponding antecedents.
- Theorem 7 is checked in its full stated scope. The universal-vertex branch checks the specialization of Theorem 8 to Conjecture 6. Theorem 5 follows as a corollary.

## Mathematical audit

Any finite simple graph has a labeling on `Fin n`. The recursive sum in `total` visits vertex zero followed by all successors, so `card` counts each vertex once. Connectivity quantifies over arbitrary vertex deletion sets of size at most two. The size guard and odd order give at least five vertices. The hypotheses hold, for example, for the complete graph on five vertices.

Strict endpoint order stores each undirected edge once. The color type has three values, and the two inverse identities for `Color.code` and `Color.decode` verify the indexing. Taking fibers of the total color map permits unused colors. The exact degree alternative rules out every positive even degree.

Minimal separator sides are compared by a non-strict cardinal inequality against every valid side. The construction works with any minimizing side. It assumes neither a unique minimizer nor an ordering of ties. The statement of `TuttePeripheral` appears as a premise in an intermediate reduction and is discharged by the proved `tutte_peripheral` at the top level.

## Source and license notices

The Lean declarations and proof scripts are the original formalization from this task. The archive contains no vendored project, toolchain, third-party Lean source, paper text or figures. The external software dependency is stock Lean 4.19.0 including Std. The Lean project states Apache License 2.0 and distributes third-party notices with its binary releases. Std's entry module credits Lean FRO, LLC (2024). [Pinned Lean license](https://github.com/leanprover/lean4/blob/v4.19.0/LICENSE) · [Pinned Std source notice](https://github.com/leanprover/lean4/blob/v4.19.0/src/Std.lean)

The arXiv page identifies the paper's license as CC BY-NC-ND 4.0. The bibliographical references credit the mathematical sources. This handoff assigns no new license to the original proof files.
