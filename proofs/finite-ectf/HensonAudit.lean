import HensonLogic

open Finset FirstOrder

-- Check the full finite extension statement, with no custom graph predicates.
example (r k : ℕ) (hr : 3 ≤ r) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), G.CliqueFree r ∧
      ∀ A B : Finset V, Disjoint A B → A.card + B.card ≤ k →
        G.CliqueFreeOn (A : Set V) (r - 1) →
        ∃ x, x ∉ A ∧ x ∉ B ∧ (∀ y ∈ A, G.Adj x y) ∧ (∀ b ∈ B, ¬ G.Adj x b) :=
  HensonAll.finiteCliqueExtension r k hr

-- Check the conclusion in Mathlib's first-order graph language.
example {U : Type*} (r : ℕ) (hr : 3 ≤ r) (G : SimpleGraph U)
    (hG : G.CliqueFree r)
    (ext : ∀ A B : Finset U, Disjoint A B → G.CliqueFreeOn (A : Set U) (r - 1) →
      ∃ x, x ∉ A ∧ x ∉ B ∧ (∀ y ∈ A, G.Adj x y) ∧ (∀ b ∈ B, ¬ G.Adj x b))
    (φ : Language.graph.Sentence) (hφ : @Language.Sentence.Realize _ U G.structure φ) :
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (H : SimpleGraph V), H.CliqueFree r ∧
      @Language.Sentence.Realize _ V H.structure φ :=
  HensonAll.hensonPseudofinite r hr G hG ext φ hφ

/-- info: 'HensonAll.finiteCliqueExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HensonAll.finiteCliqueExtension

/-- info: 'HensonAll.hensonPseudofinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HensonAll.hensonPseudofinite

/-- info: 'HensonAll.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HensonAll.bound
