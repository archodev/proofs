import Problem29

/- The expected statement spells out the graph property independently of
Problem29.Extension and Problem29.TriangleFree. Type checking these assignments
also checks that the two definitions expand to the expected propositions. -/

example (k : ℕ) : ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    (∀ x y z : V, G.Adj x y → G.Adj y z → ¬ G.Adj z x) ∧
    (∀ A B : Finset V, Disjoint A B → A.card + B.card ≤ k →
      (∀ y ∈ A, ∀ z ∈ A, y ≠ z → ¬ G.Adj y z) →
      ∃ x : V, x ∉ A ∧ x ∉ B ∧
        (∀ y ∈ A, G.Adj x y) ∧ (∀ b ∈ B, ¬ G.Adj x b)) :=
  Problem29.finite_ectf k

example : ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    (∀ x y z : V, G.Adj x y → G.Adj y z → ¬ G.Adj z x) ∧
    (∀ A B : Finset V, Disjoint A B → A.card + B.card ≤ 4 →
      (∀ y ∈ A, ∀ z ∈ A, y ≠ z → ¬ G.Adj y z) →
      ∃ x : V, x ∉ A ∧ x ∉ B ∧
        (∀ y ∈ A, G.Adj x y) ∧ (∀ b ∈ B, ¬ G.Adj x b)) :=
  Problem29.finite_4ectf

#print axioms Problem29.finite_ectf
#print axioms Problem29.finite_4ectf
