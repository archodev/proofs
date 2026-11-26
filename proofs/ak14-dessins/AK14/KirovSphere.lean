import AK14.BiholomorphicCharts
import KirovDolbeault.ProjectiveLine

namespace AK14.Gluing
open Jacobians
open scoped Manifold OnePoint
noncomputable section

theorem kirov_centered_chart (x : OnePoint ℂ) (w : ℂ) :
    sphereArgument x w=(chartAt ℂ x).symm (w+chartAt ℂ x x) := by
  cases x with
  | coe a =>
    change ((w+a:ℂ):OnePoint ℂ)=((w+RiemannSphere.chartCoe (a : OnePoint ℂ):ℂ):OnePoint ℂ)
    rw [RiemannSphere.chartCoe_apply_coe]
  | infty =>
    change sphereArgument ∞ w=RiemannSphere.chartInfty.symm (w+RiemannSphere.chartInfty ∞)
    rw [RiemannSphere.chartInfty_apply_infty,add_zero]
    rfl

theorem parameter_from_kirov_sphere {n : ℕ} [NeZero n] {T : Triple n} (pr : T 0*T 1*T 2=1)
    (h : letI := surfaceAtlas T pr
         ∃ e : Surface T ≃ OnePoint ℂ, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ e ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ e.symm) :
    Nonempty (SphereParameter pr) := by
  letI := surfaceAtlas T pr
  obtain ⟨g,df,dg⟩ := h
  let e : OnePoint ℂ ≃ₜ Surface T := ⟨g.symm,dg.continuous,df.continuous⟩
  exact ⟨parameter_of_biholomorphism pr kirov_centered_chart e dg df⟩

end
end AK14.Gluing

