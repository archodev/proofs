import AK14.ParameterRamification
import AK14.ParameterLifts
import AK14.OrientedUniqueness
import AK14.GluedDifferential

namespace AK14
open Gluing
noncomputable section

theorem Passport.positive_degree {p : Passport} {n : ℕ} (h : p.Admissible n) : 0<n := by
  have total := h.totals 0
  have pos := h.a_pos
  cases hf : p.family <;> simp [Passport.rows,hf,Multiset.sum_replicate,nsmul_eq_mul] at total <;> omega

/-- The geometric input: the connected glued surface has a conformal sphere
parameter, sending 0, 1 and infinity to its three marked exceptional sites. -/
def MarkedSphereUniformization : Prop :=
  ∀ (p : Passport) (n : ℕ) [NeZero n], p.Admissible n → ∀ (T : Triple n) (ht : Realizes p T),
    ∃ M : Marking T p, Nonempty (ConformalParameter ht.product M)

theorem normalized_realization_of_uniformization (h : MarkedSphereUniformization) :
    NormalizedRiemannExistence := by
  intro p n hp T ht
  letI : NeZero n := ⟨(Passport.positive_degree hp).ne'⟩
  obtain ⟨M,⟨N⟩⟩ := h p n hp T ht
  obtain ⟨f,eq⟩ := parameter_rational N
  exact ⟨f,parameter_normalized N (projection_cofinite T ht.product N.phi eq),parameter_carries N eq⟩

/-- The public oriented uniqueness assertion from solely the marked sphere
parameter theorem for the concrete glued surfaces. -/
theorem oriented_uniqueness_of_uniformization (h : MarkedSphereUniformization) : OrientedUniqueness :=
  orientedUniqueness_of_normalizedRiemannExistence (normalized_realization_of_uniformization h)

theorem exactly_one_of_uniformization_and_existence (h : MarkedSphereUniformization)
    (ex : Theorem13Existence) : Conjecture14 :=
  conjecture14_iff_existence_and_uniqueness.mpr ⟨ex,oriented_uniqueness_of_uniformization h⟩

end
end AK14

