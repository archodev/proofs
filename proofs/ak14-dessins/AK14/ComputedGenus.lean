import AK14.GluedDifferential
import KirovDolbeault.Dolbeault.FormRemovableSingularity
import KirovDolbeault.Dolbeault.CanonicalFormDifferential
import KirovDolbeault.RiemannRochDegree

namespace AK14.Gluing
open Jacobians Jacobians.Dolbeault
open scoped Manifold Topology
noncomputable section

/-- A concrete nonzero meromorphic differential of negative divisor degree
forces the space of global holomorphic one-forms to have dimension zero. -/
theorem genus_from_computed_divisor {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]
    (f : Jacobians.MeromorphicFunction X) (K : X →₀ ℤ) (hk : K.degree<0)
    (ord : ∀ y : X, exactOrder (deriv (f.toFun ∘ (chartAt ℂ y).symm)) (chartAt ℂ y y) (K y)) :
    kirovGenus X=0 := by
  have H (y : X) : (differentialForm f).formOrderW y=(K y : WithTop ℤ) := by
    rw [formOrderW_differentialForm]
    apply (meromorphicOrderAt_eq_int_iff (f.meromorphic y).deriv).mpr
    exact ord y
  let data : CanonicalForm17Data X :=
    { ω₀ := differentialForm f, K := K, order_eq := H,
      nontrivial := ⟨Classical.arbitrary X,by rw [H]; exact WithTop.coe_ne_top⟩ }
  rw [←data.hKgenus_unconditional]
  exact lDim_eq_zero_of_deg_neg K hk

theorem glued_holomorphic_genus_zero {p : Passport} {n : ℕ} [NeZero n] (hp : p.Admissible n)
    {T : Triple n} (ht : Realizes p T) :
    letI := surfaceAtlas T ht.product
    letI := surface_analytic T ht.product
    letI := surface_compact T
    letI := surface_hausdorff T
    letI := surface_connected (NeZero.pos n) ht.transitive ht.product
    kirovGenus (Surface T)=0 := by
  letI := surfaceAtlas T ht.product
  letI := surface_analytic T ht.product
  letI := surface_compact T
  letI := surface_hausdorff T
  letI := surface_connected (NeZero.pos n) ht.transitive ht.product
  let f : Jacobians.MeromorphicFunction (Surface T) := ⟨surfaceFunction T,projection_meromorphic T ht.product⟩
  exact genus_from_computed_divisor f (branchDivisor T ht.product) (by rw [branchDivisor_degree hp ht]; norm_num)
    (projection_differential_orders T ht.product)

end
end AK14.Gluing

