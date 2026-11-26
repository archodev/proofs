module
public import C5.PrismLaw
public import C5.Agreement
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section
namespace C5
noncomputable section
open MeasureTheory Filter Set OAI.PlaneFiveColor.Spectral

namespace Model
variable [Carrier]

private theorem middle_half {a b c : ℂ} (h : classification a b c)
    (ha : a=1/2) (hc : c=1/2) : b=1/2 := by
  rcases h with ⟨z,o⟩|h
  · rw [ha,hc] at z o
    norm_num at z o
    simp_all
  · exact h.2.1

theorem no_avoiding_law (ω : Space templates) : False := by
  obtain ⟨u,hu,hm⟩ := triangle_needed ω
  let v := u*omegaE
  have hv : ‖(v:ℂ)‖=1 := by simp [v,omegaE,norm_mul,hu,omega_unit]
  have e : u+v*omegaE = v := by
    unfold v
    have h := omega_equation
    linear_combination u*h
  have c₀ := triangle_classification ω 0 u hu
  have c₁ := triangle_classification ω u v hv
  have c₂ := triangle_classification ω u u hu
  simp only [zero_add] at c₀
  rw [e] at c₁
  have pl (b) := prism_law ω 0 u u hu hu b
  have nonmono : ∀ᵐ η ∂measure templates ω, ¬(η.val 0=η.val u ∧ η.val 0=η.val v) := by
    filter_upwards [c₀,c₁,c₂,pure_agreement ω 0,pure_agreement ω u,pure_agreement ω v,
      ae_all_iff.mpr pl] with η h₀ h₁ h₂ p₀ p₁ p₂ hp ⟨eu,ev⟩
    change classification (P ω 0 η) (P ω u η) (P ω v η) at h₀
    rcases h₀ with ⟨z,o⟩|⟨ha,hb,hc⟩
    · have f : η.val 0=false := by rcases z with h|h|h; exact p₀.1 h; exact eu.trans (p₁.1 h); exact ev.trans (p₂.1 h)
      have t : η.val 0=true := by rcases o with h|h|h; exact p₀.2 h; exact eu.trans (p₁.2 h); exact ev.trans (p₂.2 h)
      simp_all
    · have hsum := middle_half h₁ hb hc
      have htwo := middle_half h₂ hb hsum
      have row (i : Fin 3) : η.val (T 0 u i)=η.val 0 := by
        fin_cases i <;> simp [T,base,←eu,←ev,v] at * <;> assumption
      have h := hp (η.val 0) row
      change P ω (u+v) η=1/2 at hsum
      have eq : v+u=u+v := add_comm _ _
      simp only [Fin.sum_univ_three,T,base] at h
      change matchWeight (η.val 0) (P ω (0+u*0+u) η) +
        matchWeight (η.val 0) (P ω (0+u*1+u) η) +
        matchWeight (η.val 0) (P ω (0+v+u) η) = 1 at h
      simp only [mul_zero,mul_one,zero_add,eq,hb,htwo,hsum] at h
      cases ec : η.val 0 <;> norm_num [ec,matchWeight] at h
  exact hm (by simpa [ae_iff,v,mul_comm u omegaE] using nonmono)

end Model

/-- Every unrestricted binary coloring of the real plane, modeled by the
complex numbers with their Euclidean metric, has a monochromatic unit C5. -/
theorem unrestricted_C5 (c : ℂ → Bool) : HasMono c := by
  classical
  by_contra h
  letI : Carrier := algebraicCarrier
  exact Model.no_avoiding_law ⟨fun a => c (a:ℂ),Model.input h⟩

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def PlaneMono (c : Plane → Bool) : Prop :=
  ∃ p : Fin 5 → Plane, Function.Injective p ∧ (∀ i : Fin 5, dist (p i) (p (i+1))=1) ∧
    ∀ i, c (p i)=c (p 0)

theorem to_euclidean (c : Plane → Bool) (h : HasMono (c ∘ Complex.orthonormalBasisOneI.repr)) :
    PlaneMono c := by
  obtain ⟨p,hp,hc⟩ := h
  let e := Complex.orthonormalBasisOneI.repr
  exact ⟨fun i => e (p i),e.injective.comp hp.distinct,fun i =>
    (e.dist_map _ _).trans (hp.edges i),hc⟩

/-- The measurable statement, with measurability in the completion of area. -/
theorem measurable_plane_C5 (c : Plane → Bool) (h : NullMeasurableSet {x | c x=true} volume) :
    PlaneMono c :=
  to_euclidean c (measurable_C5 _ (h.preimage Complex.orthonormalBasisOneI.measurePreserving_repr.quasiMeasurePreserving))

/-- No regularity assumptions on c. -/
theorem plane_C5 (c : Plane → Bool) : PlaneMono c :=
  to_euclidean c (unrestricted_C5 _)

end
end C5
end
