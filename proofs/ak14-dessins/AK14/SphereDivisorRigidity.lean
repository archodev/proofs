import AK14.GluedDifferential
import Mathlib.Analysis.Complex.Liouville

namespace AK14.Gluing
open Complex Set Filter Topology Bornology
noncomputable section

def fillHoles (h : ℂ → ℂ) (z : ℂ) : ℂ := limUnder (𝓝[≠] z) h

theorem puncture_avoids (z p : ℂ) : ∀ᶠ y in 𝓝[≠] z, y≠p := by
  by_cases eq : z=p
  · subst p; exact self_mem_nhdsWithin
  · exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds eq)

theorem fills_germ {h u : ℂ → ℂ} {z : ℂ} (a : AnalyticAt ℂ u z)
    (eq : h=ᶠ[𝓝[≠] z] u) : fillHoles h=ᶠ[𝓝 z] u := by
  have E := eventually_nhdsWithin_iff.mp eq
  have U := eventually_eventually_nhds.mpr E
  filter_upwards [U,a.eventually_analyticAt] with w hw aw
  have agree : h=ᶠ[𝓝[≠] w] u := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hw,puncture_avoids w z] with v hv nz using hv nz
  exact ((aw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' agree.symm).limUnder_eq

theorem ratio_germ {f g : ℂ → ℂ} {z : ℂ} {m : ℤ} (hf : exactOrder f z m) (hg : exactOrder g z m) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u z ∧ u z≠0 ∧ (f/g)=ᶠ[𝓝[≠] z] u := by
  obtain ⟨a,aa,na,ea⟩ := hf
  obtain ⟨b,ab,nb,eb⟩ := hg
  refine ⟨a/b,aa.div ab nb,div_ne_zero na nb,?_⟩
  filter_upwards [ea,eb,puncture_avoids z z] with w ew gw nz
  change f w/g w=a w/b w
  rw [ew,gw,mul_div_mul_left _ _ (zpow_ne_zero _ (sub_ne_zero.mpr nz))]

/-- Equal signed orders at all finite points and at infinity force proportionality
of meromorphic germs on the actual sphere. -/
theorem sphere_functions_proportional {f g : ℂ → ℂ}
    (finite : ∀ z, ∃ m : ℤ, exactOrder f z m ∧ exactOrder g z m)
    (infty : ∃ m : ℤ, exactOrder (f ∘ Inv.inv) 0 m ∧ exactOrder (g ∘ Inv.inv) 0 m) :
    ∃ c : ℂ, c≠0 ∧ ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, f w=c*g w := by
  let h := f/g
  have loc (z : ℂ) : ∃ u : ℂ → ℂ, AnalyticAt ℂ u z ∧ u z≠0 ∧ h=ᶠ[𝓝[≠] z] u := by
    obtain ⟨_,ff,gg⟩ := finite z; exact ratio_germ ff gg
  have entire : Differentiable ℂ (fillHoles h) := by
    intro z; obtain ⟨u,a,_,eq⟩ := loc z
    exact a.differentiableAt.congr_of_eventuallyEq (fills_germ a eq)
  obtain ⟨_,fi,gi⟩ := infty
  obtain ⟨u,a,nu,eq⟩ := ratio_germ fi gi
  have outer : ∀ᶠ w in cobounded ℂ, h w=u w⁻¹ := by
    have p := tendsto_inv₀_cobounded'.eventually eq
    filter_upwards [p] with w hw
    simpa [h,Function.comp_def] using hw
  have cont : ∀ᶠ w in cobounded ℂ, AnalyticAt ℂ (fun t : ℂ => u t⁻¹) w := by
    have no : ∀ᶠ w in cobounded ℂ, w≠0 := tendsto_inv₀_cobounded'.eventually (puncture_avoids 0 0) |>.mono (by simp)
    filter_upwards [tendsto_inv₀_cobounded.eventually a.eventually_analyticAt,no] with w aw nz
    exact aw.comp (analyticAt_id.inv nz)
  have nearOuter : ∀ᶠ w in cobounded ℂ, h=ᶠ[𝓝 w] (fun t : ℂ => u t⁻¹) := by
    rw [Metric.cobounded_eq_cocompact] at outer ⊢
    obtain ⟨K,compact,sub⟩ := mem_cocompact.mp outer
    filter_upwards [compact.compl_mem_cocompact] with w hw
    exact Filter.mem_of_superset (compact.isClosed.isOpen_compl.mem_nhds hw) sub
  have outside : fillHoles h=ᶠ[cobounded ℂ] (fun w : ℂ => u w⁻¹) := by
    filter_upwards [nearOuter,cont] with w hw aw
    exact (fills_germ aw (hw.filter_mono nhdsWithin_le_nhds)).self_of_nhds
  have lim : Tendsto (fillHoles h) (cocompact ℂ) (𝓝 (u 0)) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact (a.continuousAt.tendsto.comp tendsto_inv₀_cobounded).congr' outside.symm
  have constant := entire.eq_const_of_tendsto_cocompact lim
  refine ⟨u 0,nu,?_⟩
  intro z
  obtain ⟨v,av,_,ev⟩ := loc z
  have cv := fills_germ av ev; rw [constant] at cv
  obtain ⟨m,_,b,ab,nb,eb⟩ := finite z
  have nonb : ∀ᶠ t in 𝓝[≠] z, b t≠0 := mem_nhdsWithin_of_mem_nhds
    (ab.continuousAt.tendsto.eventually (isOpen_ne.mem_nhds nb))
  filter_upwards [ev,cv.filter_mono nhdsWithin_le_nhds,eb,nonb,puncture_avoids z z] with w ew cw gw bw nz
  have ng : g w≠0 := gw ▸ mul_ne_zero (zpow_ne_zero _ (sub_ne_zero.mpr nz)) bw
  exact (div_eq_iff ng).mp (ew.trans cw.symm)

end
end AK14.Gluing
