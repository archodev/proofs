import AK14.BranchPaths
import AK14.StandardLoops
import AK14.GeometricCorners
import AK14.Unnormalized
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The target, its verified rational and oriented-monodromy part, and the
remaining realization statements, recorded as propositions. -/
namespace AK14
open SeriesAt
noncomputable section

/-- The existence assertion of Adrianov–Kreines Theorem 1.3, in ordered
permutation language. -/
def Theorem13Existence : Prop :=
  ∀ (p : Passport) (n : ℕ), p.Admissible n → ∃ T : Triple n, Realizes p T

/-- Genus-zero Riemann existence with the three exceptional source points
normalized. The rational witness must have the actual given path lifts along
the displayed positive loops, with just one numbering of all sheets. -/
def NormalizedRiemannExistence : Prop :=
  ∀ (p : Passport) (n : ℕ), p.Admissible n → ∀ T : Triple n, Realizes p T →
    ∃ f : RatFunc ℂ, NormalizedCover p f ∧ Carries f standardLoops T

/-- The all-degree, both-family uniqueness theorem for triples coming from
rational coverings. Orientation and the individual target labels are fixed. -/
theorem rational_branch_cycles_same {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {T U : Triple n} {f g : RatFunc ℂ}
    (hf : NormalizedCover p f) (hg : NormalizedCover p g)
    (hT : Carries f standardLoops T) (hU : Carries g standardLoops U) : SameDessin T U :=
  normalized_branch_cycles_unique hp hf hg standardLoops hT hU

/-- At most one simultaneous-conjugacy class for every passport, conditional
only on normalized complex realization of each input triple. -/
theorem uniqueness_of_realization (uniformization : NormalizedRiemannExistence)
    {p : Passport} {n : ℕ} (hp : p.Admissible n) {T U : Triple n}
    (hT : Realizes p T) (hU : Realizes p U) : SameDessin T U := by
  obtain ⟨f,hf,ft⟩ := uniformization p n hp T hT
  obtain ⟨g,hg,gu⟩ := uniformization p n hp U hU
  exact rational_branch_cycles_same hp hf hg ft gu

/-- The two missing existence statements would close the exact public target.
They are ordinary explicit inputs to this reduction theorem. -/
theorem conjecture14_of_realization (existence : Theorem13Existence)
    (uniformization : NormalizedRiemannExistence) : Conjecture14 := by
  intro p n hp
  obtain ⟨T,hT⟩ := existence p n hp
  refine ⟨T,hT,fun U hU => ?_⟩
  exact uniqueness_of_realization uniformization hp hT hU

end
end AK14
