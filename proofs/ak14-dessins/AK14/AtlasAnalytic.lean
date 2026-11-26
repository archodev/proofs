import AK14.CornerModels
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Geometry.Manifold.IsManifold.Basic

namespace AK14.Gluing
open Complex Set Filter Topology
open scoped OnePoint Manifold
noncomputable section

def scalarModel (j : Fin 3) (d : ℕ) (z : ℂ) : ℂ := ![z^d,1-z^d,(z^d)⁻¹] j

theorem branchModel_finite (j : Fin 3) (d : ℕ) {z : ℂ} (nz : z≠0) :
    branchModel j (z^d)=(scalarModel j d z : OnePoint ℂ) := by
  fin_cases j <;> simp [branchModel,scalarModel,pow_ne_zero _ nz]

theorem scalarModel_regular (j : Fin 3) {d : ℕ} (dn : d≠0) {z : ℂ} (nz : z≠0) :
    ∃ a : ℂ, a≠0 ∧ HasStrictDerivAt (scalarModel j d) a z := by
  have hp := hasStrictDerivAt_pow d z
  have cz : (d:ℂ)≠0 := by exact_mod_cast dn
  have derivnz : (d:ℂ)*z^(d-1)≠0 := mul_ne_zero cz (pow_ne_zero _ nz)
  fin_cases j
  · exact ⟨_,derivnz,hp⟩
  · exact ⟨_,neg_ne_zero.mpr derivnz,hp.const_sub 1⟩
  · exact ⟨_,mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (pow_ne_zero d nz)))) derivnz,
      (hasStrictDerivAt_inv (pow_ne_zero d nz)).comp z hp⟩

/-- Differentiation through a locally invertible right-hand model. -/
theorem differentiable_lift {f g u : ℂ → ℂ} {z a : ℂ}
    (eq : ∀ᶠ w in 𝓝 z, f w=g (u w)) (cf : DifferentiableAt ℂ f z)
    (cu : ContinuousAt u z) (dg : HasStrictDerivAt g a (u z)) (nz : a≠0) : DifferentiableAt ℂ u z := by
  let inv := dg.localInverse g a (u z) nz
  have ci : DifferentiableAt ℂ inv (f z) := eq.self_of_nhds.symm ▸ dg.to_localInverse nz |>.hasDerivAt.differentiableAt
  have near : ∀ᶠ v in 𝓝 (u z), inv (g v)=v := (dg.hasStrictFDerivAt_equiv nz).eventually_left_inverse
  apply (ci.comp z cf).congr_of_eventuallyEq
  filter_upwards [eq,cu.tendsto.eventually near] with w hw invw
  exact (congrArg inv hw).trans invw |>.symm

def adapted {X : Type*} [TopologicalSpace X] (F : X → OnePoint ℂ) (e : OpenPartialHomeomorph X ℂ) : Prop :=
  ∃ (j : Fin 3) (d : ℕ), d≠0 ∧ ∀ y∈e.source, F y=branchModel j ((e y)^d)

theorem adapted_transition {X : Type*} [TopologicalSpace X] {F : X → OnePoint ℂ}
    {e e' : OpenPartialHomeomorph X ℂ} (h : adapted F e) (h' : adapted F e') :
    AnalyticOnNhd ℂ (e.symm.trans e') (e.symm.trans e').source := by
  obtain ⟨j,d,dn,model⟩ := h
  obtain ⟨k,m,mn,model'⟩ := h'
  let t := e.symm.trans e'
  have reg (z : ℂ) (inside : z∈t.source) (nz : z≠0) (nz' : t z≠0) : DifferentiableAt ℂ t z := by
    obtain ⟨a,_,dh⟩ := scalarModel_regular j dn nz
    obtain ⟨c,cn,dg⟩ := scalarModel_regular k mn nz'
    apply differentiable_lift (f:=scalarModel j d) (g:=scalarModel k m) _ dh.hasDerivAt.differentiableAt (t.continuousAt inside) dg cn
    have n1 : ∀ᶠ w in 𝓝 z, w≠0 := isOpen_ne.mem_nhds nz
    have n2 : ∀ᶠ w in 𝓝 z, t w≠0 := (t.continuousAt inside).tendsto.eventually (isOpen_ne.mem_nhds nz')
    filter_upwards [t.open_source.mem_nhds inside,n1,n2] with w hw nonzero nonzero'
    have eq := (model (e.symm w) (e.symm.map_source hw.1)).symm.trans (model' _ hw.2)
    rw [e.right_inv hw.1,branchModel_finite j d nonzero] at eq
    change (_ : OnePoint ℂ)=branchModel k ((t w)^m) at eq
    rw [branchModel_finite k m nonzero',OnePoint.coe_eq_coe] at eq
    exact eq
  intro z hz
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ (t.continuousAt hz)
  have N : ∀ᶠ w in 𝓝[≠] z, w≠z := self_mem_nhdsWithin
  have V : t.source∈𝓝[≠] z := mem_nhdsWithin_of_mem_nhds (t.open_source.mem_nhds hz)
  have non : ∀ᶠ w in 𝓝[≠] z, w≠0 := by
    by_cases ez : z=0
    · exact ez ▸ N
    · exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds ez)
  have non' : ∀ᶠ w in 𝓝[≠] z, t w≠0 := by
    by_cases ez : t z=0
    · filter_upwards [V,N] with w hw nz
      exact fun zero => nz (t.injOn hw hz (zero.trans ez.symm))
    · exact mem_nhdsWithin_of_mem_nhds ((t.continuousAt hz).tendsto.eventually (isOpen_ne.mem_nhds ez))
  filter_upwards [V,non,non'] with w hw h0 h1 using reg w hw h0 h1

end
end AK14.Gluing
