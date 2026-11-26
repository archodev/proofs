# Uniqueness of the tetrahedral dessins

Every genus-zero passport of either form in Adrianov and Kreines, Theorem 1.3, has exactly one realization up to orientation-preserving, color-preserving dessin isomorphism. The target branch values are individually fixed. Existence is Theorem 1.3 of the [source paper](https://arxiv.org/html/2606.10079#S1.SS4).

## Prior result

The analytic uniqueness statement predates the conjecture. Van Hoeij and Weil recover the pullback function for a fixed normalized tetrahedral differential operator up to sign. Their two signs exchange the two order-three values of the standard equation. In the present application the three exceptional points determine the projective equation, its projective monodromy is the full tetrahedral group, and the target value assigned to the exceptional point of degree \(b\) selects the sign. [Van Hoeij and Weil, Lemma 5.2 and Remark 5.3](https://www.math.fsu.edu/~hoeij/papers/issac05/f99HoeijWeil.pdf#page=6). For the unique three-singularity operator with fixed exponent differences, see [Chou, pp. 2–3](https://arxiv.org/pdf/1611.06643#page=2).

## Proof

Fix the ordered target values \(0,1,\infty\). Suppose \(f_1,f_2\) realize the same one of the passports
\[
(2^r,a\mid 3^s,b\mid 3^t,c),\qquad
(2^r,a\mid 3^s\mid 3^t,b,c),
\]
where \(a\) is odd, \(3\nmid b\), and \(3\nmid c\). In each source mark the three distinct points belonging to the displayed exceptional parts, including any exceptional parts of size one. Match the points by their degrees and target values. Genus zero permits a Möbius coordinate on each source putting these points, in the order \(a,b,c\), at \(x=0,1,\infty\). From now on compare the maps in these coordinates.

For clarity, the passage from triples to rational maps here is the classical genus-zero Riemann existence correspondence. An ordered product-one triple prescribes the action of the peripheral generators on the sheets of an unbranched covering of the thrice-punctured target sphere. Transitivity makes the cover connected. Pull back the complex coordinate charts. A cycle of length \(e\) gives one connected degree-\(e\) covering of a punctured disc. Such a covering is analytically equivalent over the disc to \(u\mapsto u^e\) on a punctured disc, by the universal covering of the punctured disc or the classification of its subgroups \(e\mathbb Z\subset\mathbb Z\). Filling in \(u=0\) gives a compact Riemann surface and the required holomorphic branched covering. Its Euler characteristic is the sum of the numbers of cycles minus the degree, which is two by the passport hypothesis. The genus-zero uniformization theorem identifies it biholomorphically with the Riemann sphere, on which every meromorphic function is rational. A source biholomorphism over the identity of the target induces one bijection of the base fiber commuting with all three positive path transports. This supplies exactly the simultaneous conjugacy needed below.

Let \(G=A_4\) act on the Riemann sphere by rotations of a regular tetrahedron. The quotient \(Q:\mathbb P^1_w\to\mathbb P^1_w/G\) has three branch orbits, given by the radial directions of edge midpoints, vertices, and face centers. Their stabilizer orders are \(2,3,3\), respectively. The quotient surface has genus zero by Riemann–Hurwitz. Identify it with the target sphere by mapping the three branch values to \(0,1,\infty\) in that order.

For either \(f=f_i\), continue a local branch \(F\) of \(Q^{-1}\circ f\). Its branches differ by elements of \(G\). If \(f\) has local degree \(e\) over a branch value of order \(k\), then locally \(F\) is a Möbius transformation of \(u^{e/k}\) for a source coordinate \(u\) centered at the point. Indeed, choose a Möbius coordinate at the lift in which its cyclic stabilizer acts by \(w\mapsto\zeta_k w\). In a local target coordinate the quotient is \(w\mapsto w^k\), and in a suitable source coordinate \(f\) is \(u\mapsto u^e\) in that same target coordinate. Thus \(F\) extends locally univalently at all the usual points where \(e=k\). Away from the three target fibers both maps are unramified. Only the three marked points remain, with respective exponents
\[
\alpha=a/2,\qquad \beta=b/3,\qquad \gamma=c/3.
\]

The Schwarzian \(S_xF=F'''/F'-(3/2)(F''/F')^2\) is single-valued by Möbius invariance. The chain rule \(S(H\circ u)=(SH\circ u)(u')^2+Su\) shows that at a marked point of exponent \(\theta\) its double-pole coefficient is \((1-\theta^2)/2\) in any centered local coordinate. It is holomorphic at every other point. Set
\[
A=(1-\alpha^2)/2,\quad B=(1-\beta^2)/2,\quad C=(1-\gamma^2)/2.
\]
Since inversion is Möbius, the coefficient at infinity requires \(S_xF=C/x^2+O(x^{-3})\) as \(x\to\infty\). Partial fractions now give
\[
S_xF=\frac{A}{x^2}+\frac{B}{(x-1)^2}+
      \frac{C-A-B}{x(x-1)}.
\]
In particular \(F_1,F_2\) have the same Schwarzian. They differ on a common regular disc by a Möbius transformation \(M\). Indeed \(S(F_2\circ F_1^{-1})=0\), whose locally univalent solutions are precisely the Möbius maps. The identity \(F_2=M\circ F_1\) persists under continuation on the universal cover of the thrice-punctured source.

Write \(H_i\leq G\) for the monodromy image of \(F_i\). The local power description gives a monodromy element of order \(k/\gcd(e,k)\). The \(a\)- and \(b\)-points therefore give elements of orders two and three. Consequently \(|H_i|\) is divisible by six. An order-six subgroup would yield a nontrivial homomorphism \(A_4\to C_2\), impossible since \(A_4\) is generated by 3-cycles. Hence \(H_1=H_2=G\).

Continuation of \(F_2=M\circ F_1\) conjugates \(H_1\) onto \(H_2\), so \(MGM^{-1}=G\). It follows that \(M\) induces a Möbius map \(h\) on the quotient, defined by \(h(Q(w))=Q(Mw)\). Thus \(f_2=h\circ f_1\). The map \(h\) permutes the three branch values of \(Q\) and preserves their stabilizer orders. It fixes the unique order-two value. It also fixes the common value \(f_1(1)=f_2(1)\) of the marked \(b\)-point, which is the order-three value \(1\) in the first family and \(\infty\) in the second. It therefore fixes the third branch value as well, and \(h\) is the identity. This argument includes \(b=c\) in the first family, since the two points were matched by their target labels.

We have proved equality of the normalized maps. Undoing their source normalizations gives a holomorphic source isomorphism commuting with the Belyi maps over the identity on the target. It preserves orientation, the two vertex colors, and the cyclic orders at all vertices. Equivalently the ordered transitive permutation triples form one simultaneous-conjugacy class. Together with existence, this proves Conjecture 1.4.

## Finite check

The accompanying [Python checker](check_dessins.py) enumerates oriented triples for eight passports of degrees 3, 5, 7, and 9. It also counts the two mirror-image realizations in the paper's Example 1.2. Run it with `python3 check_dessins.py`. The eight counts are all one and the control count is two.
