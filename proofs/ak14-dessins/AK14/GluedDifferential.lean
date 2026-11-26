import AK14.BranchDivisor
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.Deriv.ZPow

namespace AK14.Gluing
open Complex Set Filter Topology
open scoped OnePoint Manifold
noncomputable section

def planeValue (w : OnePoint ℂ) : ℂ := (w : Option ℂ).getD 0
def surfaceFunction {n : ℕ} (T : Triple n) (y : Surface T) : ℂ := planeValue (gluedMap T y)

theorem plane_branch (j : Fin 3) (d : ℕ) (z : ℂ) : planeValue (branchModel j (z^d))=scalarModel j d z := by
  fin_cases j
  · rfl
  · rfl
  · change planeValue (if z^d=0 then ∞ else (((z^d)⁻¹:ℂ):OnePoint ℂ))=(z^d)⁻¹
    split_ifs with h
    · rw [h,inv_zero]; rfl
    · rfl

theorem scalarModel_meromorphic (j : Fin 3) (d : ℕ) (z : ℂ) : MeromorphicAt (scalarModel j d) z := by
  fin_cases j
  · exact (MeromorphicAt.id z).pow d
  · exact (MeromorphicAt.const 1 z).sub ((MeromorphicAt.id z).pow d)
  · exact ((MeromorphicAt.id z).pow d).inv

theorem cornerChart_center {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n) :
    cornerChart T pr j x (cell T (true,x) (vertex j))=0 := by
  have eq := cornerChart_power T pr j x _ _ (corner_mem_chart T pr j x)
  have zero : cornerValue j true (vertex j)=0 := by
    rw [cornerValue,frame_vertex]; apply Complex.ext
    · change (0*(1+0)+0*(0-1))/(1+0)^2=(0:ℝ); norm_num
    · change sideSign _*(2*Real.sqrt (1*0*0))/(1+0)^2=(0:ℝ); norm_num
  by_contra nz; exact pow_ne_zero _ nz (eq.trans zero)

theorem ordinary_scalar_germ {n : ℕ} (T : Triple n) {e : OpenPartialHomeomorph (Surface T) ℂ} {y : Surface T}
    (hy : y∈e.source) (H : ∀ v∈e.source, gluedMap T v=(e v : OnePoint ℂ)) :
    surfaceFunction T ∘ e.symm =ᶠ[𝓝 (e y)] id := by
  filter_upwards [e.open_target.mem_nhds (e.map_source hy)] with z hz
  change planeValue (gluedMap T (e.symm z))=z
  rw [H _ (e.symm.map_source hz),e.right_inv hz]; rfl

theorem corner_scalar_germ {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n)
    {y : Surface T} (hy : y∈(cornerChart T pr j x).source) :
    surfaceFunction T ∘ (cornerChart T pr j x).symm =ᶠ[𝓝 (cornerChart T pr j x y)] scalarModel j (degreeAt T j x) := by
  let e := cornerChart T pr j x
  filter_upwards [e.open_target.mem_nhds (e.map_source hy)] with z hz
  change planeValue (gluedMap T (e.symm z))=_
  rw [chart_represents_projection T pr j x (e.symm.map_source hz)]
  change planeValue (branchModel j ((e (e.symm z))^_))=_
  rw [e.right_inv hz]; exact plane_branch _ _ _

theorem projection_meromorphic {n : ℕ} [NeZero n] (T : Triple n) (pr : T 0*T 1*T 2=1) (y : Surface T) :
    letI := surfaceAtlas T pr
    MeromorphicAt (surfaceFunction T ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := by
  letI := surfaceAtlas T pr
  let e := chartAt ℂ y
  have pref : preferred T pr y e := (preferred_charts_cover T pr y).choose_spec.2
  have dom : y∈e.source := mem_chart_source ℂ y
  rcases pref with ⟨_,h⟩|⟨j,x,_,eq⟩
  · exact (MeromorphicAt.id _).congr ((ordinary_scalar_germ T dom h).symm.filter_mono nhdsWithin_le_nhds)
  · change MeromorphicAt (surfaceFunction T ∘ e.symm) (e y)
    rw [eq] at dom ⊢
    exact (scalarModel_meromorphic j _ _).congr ((corner_scalar_germ T pr j x dom).symm.filter_mono nhdsWithin_le_nhds)

/-- A meromorphic local expansion with a nonzero analytic unit and signed order. -/
def exactOrder (f : ℂ → ℂ) (z : ℂ) (m : ℤ) : Prop :=
  ∃ u : ℂ → ℂ, AnalyticAt ℂ u z ∧ u z≠0 ∧ ∀ᶠ w in 𝓝[≠] z, f w=(w-z)^m*u w

theorem order_congr_germ {f g : ℂ → ℂ} {z : ℂ} {m : ℤ} (eq : f=ᶠ[𝓝 z] g) (h : exactOrder g z m) :
    exactOrder f z m := by
  obtain ⟨u,a,non,rep⟩ := h
  exact ⟨u,a,non,(eq.filter_mono nhdsWithin_le_nhds).trans rep⟩

theorem scalarModel_derivative_order (j : Fin 3) (d : ℕ) (dn : d≠0) :
    exactOrder (deriv (scalarModel j d)) 0 (differentialWeight j d) := by
  have nd : (d:ℂ)≠0 := by exact_mod_cast dn
  have pw (z : ℂ) : deriv (fun w : ℂ => w^d) z=(d:ℂ)*z^((d:ℤ)-1) := by
    simpa only [zpow_natCast,Int.cast_natCast] using (deriv_zpow (d:ℤ) z)
  fin_cases j
  · refine ⟨fun _ => (d:ℂ),analyticAt_const,nd,Eventually.of_forall (fun w => ?_)⟩
    change deriv (fun z : ℂ => z^d) w=(w-0)^((d:ℤ)-1)*(d:ℂ)
    rw [pw,sub_zero,mul_comm]
  · refine ⟨fun _ => -(d:ℂ),analyticAt_const,neg_ne_zero.mpr nd,Eventually.of_forall (fun w => ?_)⟩
    change deriv (fun z : ℂ => 1-z^d) w=(w-0)^((d:ℤ)-1)*(-(d:ℂ))
    rw [deriv_const_sub,pw,sub_zero]; ring
  · refine ⟨fun _ => -(d:ℂ),analyticAt_const,neg_ne_zero.mpr nd,Eventually.of_forall (fun w => ?_)⟩
    change deriv (fun z : ℂ => (z^d)⁻¹) w=(w-0)^(-(d:ℤ)-1)*(-(d:ℂ))
    have eq := deriv_zpow (-(d:ℤ)) w
    simp only [zpow_neg,zpow_natCast,Int.cast_neg,Int.cast_natCast] at eq
    rw [eq,sub_zero,mul_comm]

/-- The branch divisor is the actual order divisor of dP in the preferred complex charts. -/
theorem projection_differential_orders {n : ℕ} [NeZero n] (T : Triple n) (pr : T 0*T 1*T 2=1) (y : Surface T) :
    letI := surfaceAtlas T pr
    exactOrder (deriv (surfaceFunction T ∘ (chartAt ℂ y).symm)) (chartAt ℂ y y) (branchDivisor T pr y) := by
  letI := surfaceAtlas T pr
  let e := chartAt ℂ y
  have pref : preferred T pr y e := (preferred_charts_cover T pr y).choose_spec.2
  have dom : y∈e.source := mem_chart_source ℂ y
  change exactOrder (deriv (surfaceFunction T ∘ e.symm)) (e y) _
  rcases pref with ⟨reg,h⟩|⟨j,x,pt,eq⟩
  · rw [divisor_at_regular T pr reg]
    apply order_congr_germ (ordinary_scalar_germ T dom h).deriv
    exact ⟨fun _ => 1,analyticAt_const,one_ne_zero,Eventually.of_forall (fun w => by simp)⟩
  · rw [eq] at dom ⊢
    apply order_congr_germ (corner_scalar_germ T pr j x dom).deriv
    rw [←pt,cornerChart_center,←sitePoint_mk T pr j x,divisor_at_site]
    change exactOrder _ 0 (differentialWeight j (classDegree (T j) (cornerClass (T j) x)))
    rw [classDegree_at]; exact scalarModel_derivative_order j _ (degreeAt_ne T j x)

end
end AK14.Gluing
