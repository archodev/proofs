import AK14.SphereParameterData
import Mathlib.Geometry.Manifold.ContMDiff.Defs

namespace AK14.Gluing
open Complex Set Filter Topology
open scoped Manifold OnePoint
noncomputable section

theorem analytic_map_in_charts {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y] {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ f) (x : X) :
    AnalyticAt ℂ (chartAt ℂ (f x) ∘ f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
  have h := (contMDiffAt_iff.mp (hf x)).2
  simp only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,range_id,contDiffWithinAt_univ,id_eq] at h
  exact h.analyticAt

theorem biholo_chart_deriv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y] (e : X ≃ₜ Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ e) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ e.symm) (x : X) :
    deriv (chartAt ℂ (e x) ∘ e ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)≠0 := by
  let a := chartAt ℂ x
  let b := chartAt ℂ (e x)
  let F := b ∘ e ∘ a.symm
  let G := a ∘ e.symm ∘ b.symm
  have ax : x∈a.source := mem_chart_source ℂ x
  have bx : e x∈b.source := mem_chart_source ℂ (e x)
  have asym : a.symm (a x)=x := a.left_inv ax
  have center : F (a x)=b (e x) := by simp [F,asym]
  have af : AnalyticAt ℂ F (a x) := analytic_map_in_charts hf x
  have ag : AnalyticAt ℂ G (F (a x)) := by
    rw [center]; simpa only [e.symm_apply_apply] using analytic_map_in_charts hg (e x)
  have inverse : G ∘ F=ᶠ[𝓝 (a x)] id := by
    have con := e.continuous.continuousAt.comp (a.symm.continuousAt (a.map_source ax))
    have bx2 : (e ∘ a.symm) (a x)∈b.source := by simpa only [Function.comp_apply,asym] using bx
    have mem : ∀ᶠ z in 𝓝 (a x), e (a.symm z)∈b.source :=
      con.tendsto.eventually (b.open_source.mem_nhds bx2)
    filter_upwards [mem,a.open_target.mem_nhds (a.map_source ax)] with z hz ha
    change a (e.symm (b.symm (b (e (a.symm z)))))=z
    rw [b.left_inv hz,e.symm_apply_apply,a.right_inv ha]
  have chain := ag.differentiableAt.hasDerivAt.comp (a x) af.differentiableAt.hasDerivAt
  intro h
  have hz : deriv F (a x)=0 := h
  have one := inverse.deriv_eq
  rw [chain.deriv,hz,mul_zero,deriv_id] at one
  exact zero_ne_one one

/-- Read a biholomorphism as an unmarked parameter whenever the sphere
atlas has its usual centered affine and reciprocal coordinates. -/
def parameter_of_biholomorphism {n : ℕ} [NeZero n] {T : Triple n} (pr : T 0*T 1*T 2=1)
    [ChartedSpace ℂ (OnePoint ℂ)]
    (coord : ∀ (x : OnePoint ℂ) (w : ℂ),
      sphereArgument x w=(chartAt ℂ x).symm (w+chartAt ℂ x x))
    (e : OnePoint ℂ ≃ₜ Surface T)
    (hf : letI := surfaceAtlas T pr; ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ e)
    (hg : letI := surfaceAtlas T pr; ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ e.symm) : SphereParameter pr := by
  letI := surfaceAtlas T pr
  have result (x : OnePoint ℂ) : AnalyticAt ℂ (readChart T pr e x) 0 ∧ deriv (readChart T pr e x) 0≠0 := by
    let a := chartAt ℂ x x
    let F := chartAt ℂ (e x) ∘ e ∘ (chartAt ℂ x).symm
    have eq : readChart T pr e x=F ∘ (fun w : ℂ => w+a) := by
      funext w; unfold readChart; rw [coord]; rfl
    have h : AnalyticAt ℂ F (0+a) := by simpa using analytic_map_in_charts hf x
    have d := h.differentiableAt.hasDerivAt.comp 0 ((hasDerivAt_id (𝕜:=ℂ) 0).add_const a)
    rw [eq]
    refine ⟨h.comp (f:=fun w : ℂ => w+a) (analyticAt_id.add analyticAt_const),?_⟩
    have ds : HasDerivAt (F ∘ (fun w : ℂ => w+a)) (deriv F (0+a)*1) 0 := d
    rw [ds.deriv,zero_add,mul_one]
    exact biholo_chart_deriv e hf hg x
  exact ⟨e,fun x => (result x).1,fun x => (result x).2⟩

end
end AK14.Gluing

