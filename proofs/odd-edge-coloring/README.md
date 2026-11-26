# Odd edge colorings of graphs of odd order

This package proves Conjecture 6 of Mikio Kano, Shun-ichi Maezawa and Kenta Ozeki. Every finite simple 3-connected graph of odd order and minimum degree at least four admits an odd edge coloring with at most three colors. The proof uses stock Lean 4.19.0 and its standard library. [Original paper, Conjecture 6](https://arxiv.org/html/2604.15824#S1)

## Exact statement

The declaration in `KMO.lean` is in the `KMO` namespace.

```lean
theorem odd_edge_coloring (n : Nat) (G : Graph n) (odd_order : n % 2 = 1)
    (three_connected : ThreeConnected G) (minimum_degree : ∀ v, 4 ≤ G.degree v) :
    ∃ paint : Edge G → Fin 3, ∀ v c, incidentDegree paint v c = 0 ∨
      ∃ k : Nat, incidentDegree paint v c = 2 * k + 1
```

`Graph n` is a symmetric, loopless adjacency relation on `Fin n`. Any finite simple graph on $n$ vertices can be labeled this way. The degree counts distinct neighbors. `ThreeConnected` requires at least four vertices and reachability between every surviving pair after deleting any set of at most two vertices. `Reach` starts at a vertex in the surviving set and extends one edge at a time inside that set.

`Edge G` stores adjacent endpoints in strictly increasing order. `edge_exists` and `edge_unique` prove that each adjacent pair gives exactly one such edge. `incidentDegree paint v c` counts the other endpoints of edges incident to `v` that receive `c`. Each edge has one color, a color may be unused, and several edges of the same color may meet at a vertex.

The source also exports `conjecture_six : ConjectureSix`. Its conclusion `OddThree G` supplies three pairwise edge-disjoint spanning subgraphs whose union is exactly `G`. Every degree in each subgraph is zero or odd. The lemma `paint_of_partition` turns this partition into the literal edge-color map above.

## Replay

From the repository root, run these commands with the pinned toolchain installed. The manifest has no external packages.

```sh
cd proofs/odd-edge-coloring
lean --version
lake build
lake env lean --trust=0 Audit.lean
```

The verified release is `leanprover/lean4:v4.19.0`, commit `6caaee842e94`. An installation managed by elan reads `lean-toolchain`. For a standalone stock installation, put that release's `bin` directory first on `PATH`. Lean 4.19 emits an experimental-tactic notice for uses of `grind`.

`Audit.lean` prints the statements, graph definitions and transitive axiom dependencies. It also checks the exact axiom list for the final theorem with `#guard_msgs`. The printed dependency list for both main results is `[propext, Classical.choice, Quot.sound]`. Run the audit command above to reproduce the full output. See [sources and scope](SOURCES.md) for mathematical antecedents and software notices.

## Proof map

Write $w$ for the unique even-degree vertex in the principal case, $H=G-w$, and $T=N_G(w)$.

1. **Star construction.** If $x$ belongs to $T$, take a connected even-sized vertex set in $H-x$ that contains all neighbors of $x$ in $H$ and whose additional vertices belong to $T$. Color an odd factor of this set green, all edges at $x$ blue, and use the edges from $w$ to those additional vertices to complete the blue class. Checking the three degrees at every vertex gives `star_coloring`. See `Parity.lean` and `Star.lean`.

2. **Cycle construction and support parity.** Take an induced cycle that meets both $T$ and its complement and whose removal leaves $H$ connected. On the cycle use complementary edge sets having the same odd-degree vertices. Selected edges from the cycle to its exterior, together with a parity join in that exterior, make both choices have boundary $T$ and make each nontrivial component meet $T$. Their supports differ on an odd number of vertices. Adding the star of $w$ to the choice of odd support gives a connected even-degree graph with even support size. An odd factor and its complement provide two colors, and the remaining edges provide the third. See `switch_odd_support`, `odd_support_coloring` and `mixed_cycle_coloring` in `Euler.lean`, `Rim.lean` and `Cycle.lean`. The proof permits the selected edges to share exterior endpoints and accounts for their degrees modulo two.

3. **Tutte's induced nonseparating cycle.** `tutte_peripheral : TuttePeripheral` proves the prescribed-edge, avoided-vertex form of the theorem, on any induced domain of size at least four. A connected set containing the avoided vertex is maximized subject to retaining an alternate path between the prescribed edge's endpoints. A shortest alternate path closes to a chordless cycle. The rerouting and attachment arguments in `peripheral_trace` prove its complement is connected. `Trace.lean` and `RingIndex.lean` supply the path and cyclic-order facts used in `Tutte.lean`. This is Theorem 14 as attributed to W. T. Tutte in the [source paper](https://arxiv.org/html/2604.15824#S3.SS2).

4. **Minimal separator piece.** When $H$ is 2-connected but fails 3-connectivity, `Piece.exists_minimal` minimizes the size of a nonempty proper side remaining after deleting two vertices. `Piece.inner_conn` proves the minimizing side is connected. On this side and its two separator vertices, `Piece.torso_three` proves 3-connectivity after adjoining the edge between the separator vertices. A mixed side gives a peripheral cycle avoiding one separator vertex. `Piece.lift_cycle` and `Piece.lift_complement` prove that the cycle stays induced and its complement stays connected back in $H$, including when the adjoining edge was absent in $H$. If the entire side lies in $T$, `Leaf.has_star` finds the star configuration. The end-block choices, degree counts and parity arguments are in `Separator.lean`, `End.lean`, `Pair.lean`, `Leaf.lean`, `LeafStar.lean` and `Reduction.lean`.

5. **Case split and earlier results.** Handshaking on odd order gives an even-degree vertex. With at least two, `multiple_even` proves the authors' Theorem 7 under its original hypotheses. `OpenPath.lean` derives the induced nonseparating path, `Tree.lean`, `ForestColor.lean` and `Prepare.lean` construct the odd factor with a residual forest away from one vertex, and `PathColors.lean` and `Finish.lean` extend the coloring along the path. With a unique universal even-degree vertex, `universal_coloring` proves the part of Theorem 8 needed here using a nonadjacent pair and the star construction. With a unique nonuniversal even-degree vertex, `unique_even_of_tutte` uses either a cycle in $H$ itself or the minimal-piece argument. The main proof supplies its Tutte premise with `tutte_peripheral`. The 4-connected result, Theorem 5, follows as the separately checked corollary `four_connected_coloring`. [Earlier cases in the original paper](https://arxiv.org/html/2604.15824#S1)

All graph-theoretic inputs to the exported theorem are proved in the source.
