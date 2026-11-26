import AK14.ComputedGenus
import AK14.KirovSphere
import KirovDolbeault.RiemannRoch
import KirovDolbeault.DegreeOneGenusTransport

namespace AK14.Gluing
open Jacobians
open scoped Manifold
noncomputable section

/-- Riemann–Roch on the computed genus-zero surface produces a meromorphic
function with one simple pole. Its degree-one map and holomorphic inverse are
the actual sphere uniformization. -/
theorem glued_surface_uniformizes {p : Passport} {n : ℕ} [NeZero n] (hp : p.Admissible n)
    {T : Triple n} (ht : Realizes p T) :
    letI := surfaceAtlas T ht.product
    ∃ e : Surface T ≃ OnePoint ℂ, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ e ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ e.symm := by
  letI := surfaceAtlas T ht.product
  letI := surface_analytic T ht.product
  letI := surface_compact T
  letI := surface_hausdorff T
  letI := surface_connected (NeZero.pos n) ht.transitive ht.product
  obtain ⟨P,f,hP⟩ := exists_singleSimplePole_of_genus_zero_of_rr (glued_holomorphic_genus_zero hp ht)
  let F := f.toSphere P
  have hF := f.contMDiff_toSphere hP
  have hnc := f.toSphere_not_isConstant hP
  have bij := degreeOne_bijective F hF hnc (f.degreeFiber_toSphere_eq_one hP hF)
  exact ⟨Equiv.ofBijective F bij,hF,bijective_inverse_contMDiff F hF hnc bij⟩

theorem full_glued_uniformization : GluedSphereUniformization := by
  intro p n inst hp T ht
  exact parameter_from_kirov_sphere ht.product (glued_surface_uniformizes hp ht)

end
end AK14.Gluing

