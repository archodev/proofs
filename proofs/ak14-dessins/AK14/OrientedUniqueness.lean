import AK14.Public

namespace AK14

/-- The literal oriented at-most-one assertion for both Theorem 1.3 families. -/
def OrientedUniqueness : Prop :=
  ∀ (p : Passport) (n : ℕ), p.Admissible n → ∀ T U : Triple n,
    Realizes p T → Realizes p U → SameDessin T U

theorem conjecture14_iff_existence_and_uniqueness :
    Conjecture14 ↔ Theorem13Existence ∧ OrientedUniqueness := by
  constructor
  · intro h
    constructor
    · intro p n hp
      obtain ⟨T,hT,_⟩ := h p n hp
      exact ⟨T,hT⟩
    · intro p n hp T U hT hU
      obtain ⟨V,_,k⟩ := h p n hp
      exact (sameDessin_equivalence n).trans ((sameDessin_equivalence n).symm (k T hT)) (k U hU)
  · rintro ⟨existence,unique⟩ p n hp
    obtain ⟨T,hT⟩ := existence p n hp
    exact ⟨T,hT,fun U hU => unique p n hp T U hT hU⟩

theorem orientedUniqueness_of_normalizedRiemannExistence
    (h : NormalizedRiemannExistence) : OrientedUniqueness :=
  fun _ _ hp _ _ hT hU => uniqueness_of_realization h hp hT hU

end AK14
