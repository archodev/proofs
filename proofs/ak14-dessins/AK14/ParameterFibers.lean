import AK14.ConformalParameter
import AK14.GluedComplexRealization

namespace AK14.Gluing
open Complex Set Filter Topology
open scoped OnePoint unitInterval
open SeriesAt (affineValue fiberPoly AffineFiber basePoint standardLoops Carries)
noncomputable section

def markedValue : Fin 3 → OnePoint ℂ := ![((0:ℂ):OnePoint ℂ),((1:ℂ):OnePoint ℂ),∞]

theorem site_value {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (s : CornerSite T) :
    gluedMap T (sitePoint T pr s)=markedValue s.1 := by
  change complexTarget (coveringProjection T (geometric_corner_fiber T pr s.1 s.2).val)=_
  rw [(geometric_corner_fiber T pr s.1 s.2).property]
  obtain ⟨j,c⟩ := s; fin_cases j
  · exact complexTarget_zero
  · exact complexTarget_one
  · exact complexTarget_infty

theorem finite_poles {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) : {y | gluedMap T y=∞}.Finite := by
  apply (Set.finite_range (fun c : Corners (T 2) => sitePoint T pr ⟨2,c⟩)).subset
  intro y h
  have eq := complexTarget.injective (h.trans complexTarget_infty.symm)
  obtain ⟨c,hc⟩ := (geometric_corner_fiber T pr 2).surjective ⟨y,eq⟩
  exact ⟨c,congrArg Subtype.val hc⟩

theorem projection_scalar_cofinite {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1)
    (φ : OnePoint ℂ ≃ₜ Surface T) :
    ∀ᶠ w : ℂ in cofinite, gluedMap T (φ (w : OnePoint ℂ))=(pulledScalar T φ w : OnePoint ℂ) := by
  have H : {w : ℂ | gluedMap T (φ (w : OnePoint ℂ))=∞}.Finite :=
    (finite_poles T pr).preimage (φ.injective.comp OnePoint.coe_injective).injOn
  have ne : ∀ᶠ w : ℂ in cofinite, gluedMap T (φ (w : OnePoint ℂ))≠∞ := Filter.mem_cofinite.mpr (by simpa only [Set.compl_setOf,not_not] using H)
  filter_upwards [ne] with w nw
  obtain ⟨z,hz⟩ := OnePoint.ne_infty_iff_exists.mp nw
  change _= (planeValue (gluedMap T (φ (w : OnePoint ℂ))) : OnePoint ℂ)
  rw [←hz]; rfl

theorem projection_at_denominator {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1)
    (φ : OnePoint ℂ ≃ₜ Surface T) {f : RatFunc ℂ}
    (eq : ∀ z : ℂ, pulledScalar T φ=ᶠ[𝓝[≠] z] affineValue f) {z : ℂ} (d : f.denom.eval z≠0) :
    gluedMap T (φ (z : OnePoint ℂ))=OnePoint.some (affineValue f z) := by
  have le := Filter.le_cofinite_iff_eventually_ne.mpr (puncture_avoids z)
  have h : ∀ᶠ w : ℂ in 𝓝[≠] z, gluedMap T (φ (w : OnePoint ℂ))=OnePoint.some (affineValue f w) := by
    filter_upwards [(projection_scalar_cofinite T pr φ).filter_mono le,eq z] with w hw he
    exact hw.trans (congrArg OnePoint.some he)
  have cp := ((gluedMap_continuous T).comp (φ.continuous.comp OnePoint.continuous_coe)).continuousAt (x:=z)
  have cr : ContinuousAt (affineValue f) z := f.num.continuous.continuousAt.div f.denom.continuous.continuousAt d
  exact tendsto_nhds_unique ((cp.tendsto.mono_left nhdsWithin_le_nhds).congr' h)
    ((OnePoint.continuous_coe.continuousAt.comp cr).tendsto.mono_left nhdsWithin_le_nhds)

theorem projection_cofinite {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (φ : OnePoint ℂ ≃ₜ Surface T)
    {f : RatFunc ℂ} (eq : ∀ z : ℂ, pulledScalar T φ=ᶠ[𝓝[≠] z] affineValue f) :
    pulledScalar T φ=ᶠ[cofinite] affineValue f := by
  filter_upwards [SeriesAt.denominator_cofinite f] with z dz
  exact congrArg planeValue (projection_at_denominator T pr φ eq dz)

theorem affine_fiber_iff {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (φ : OnePoint ℂ ≃ₜ Surface T)
    {f : RatFunc ℂ} (eq : ∀ z : ℂ, pulledScalar T φ=ᶠ[𝓝[≠] z] affineValue f) (z u : ℂ) :
    gluedMap T (φ (z : OnePoint ℂ))=(u : OnePoint ℂ) ↔ (fiberPoly f u).IsRoot z := by
  constructor
  · intro H
    let P (w : ℂ) := gluedMap T (φ (w : OnePoint ℂ))
    have cp : Continuous P := (gluedMap_continuous T).comp (φ.continuous.comp OnePoint.continuous_coe)
    let s := affineInclusion.symm
    have aff (w : ℂ) : s (w : OnePoint ℂ)=w := OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv _
    have hz : P z∈s.source := by
      rw [show P z=(u : OnePoint ℂ) from H]
      exact affineInclusion.map_source (by simp [affineInclusion])
    have co : ∀ᶠ w : ℂ in cofinite, P w=OnePoint.some (affineValue f w) :=
      (SeriesAt.denominator_cofinite f).mono (fun _ => projection_at_denominator T pr φ eq)
    have le := Filter.le_cofinite_iff_eventually_ne.mpr (puncture_avoids z)
    have prod : ∀ᶠ w in 𝓝[≠] z, s (P w)*f.denom.eval w=f.num.eval w := by
      filter_upwards [co.filter_mono le,(SeriesAt.denominator_cofinite f).filter_mono le] with w hw dw
      rw [hw,aff]
      exact div_mul_cancel₀ _ dw
    have c := ((s.continuousAt hz).comp cp.continuousAt).mul f.denom.continuous.continuousAt
    have value := tendsto_nhds_unique ((c.tendsto.mono_left nhdsWithin_le_nhds).congr' prod)
      (f.num.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    change s (P z)*f.denom.eval z=f.num.eval z at value
    rw [show P z=(u : OnePoint ℂ) from H,aff] at value
    simpa [Polynomial.IsRoot.def,fiberPoly] using sub_eq_zero.mpr value.symm
  · intro H
    obtain ⟨d,ev⟩ := SeriesAt.fiber_roots.mp H
    exact (projection_at_denominator T pr φ eq d).trans (congrArg OnePoint.some ev)

end
end AK14.Gluing
