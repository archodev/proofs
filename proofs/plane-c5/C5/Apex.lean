module
public import C5.Model

@[expose] public section
namespace C5
noncomputable section
open OAI.PlaneFiveColor.Spectral Filter Topology

theorem sqdist_one {x y : ℂ} : dist x y = 1 ↔ Complex.normSq (x-y) = 1 := by
  rw [dist_eq_norm,Complex.norm_def,Real.sqrt_eq_one]

theorem sqdist_swap (x y : ℂ) : Complex.normSq (x-y) = Complex.normSq (y-x) := by
  rw [←Complex.sq_norm,←Complex.sq_norm,norm_sub_rev]

def height (a b : ℂ) := Real.sqrt ((Complex.normSq (b-a))⁻¹-1/4)
def coeff (k : ℝ) : ℂ := ⟨1/2,k⟩
def apex (a b : ℂ) (positive : Bool) := a+(b-a)*coeff (if positive then height a b else -height a b)

private theorem apex_height {a b : ℂ} (h : a ≠ b) (hd : Complex.normSq (b-a) < 4) :
    (height a b)^2 = (Complex.normSq (b-a))⁻¹-1/4 := by
  have hp := Complex.normSq_pos.mpr (sub_ne_zero.mpr h.symm)
  apply Real.sq_sqrt
  rw [le_sub_iff_add_le,zero_add,inv_eq_one_div,le_div_iff₀ hp]
  linarith

theorem apex_edges {a b : ℂ} (h : a ≠ b) (hd : Complex.normSq (b-a) < 4) (s : Bool) :
    dist (apex a b s) a = 1 ∧ dist (apex a b s) b = 1 := by
  have hp := Complex.normSq_pos.mpr (sub_ne_zero.mpr h.symm)
  have hh := apex_height h hd
  let k := if s then height a b else -height a b
  have hk : k^2 = (Complex.normSq (b-a))⁻¹-1/4 := by cases s <;> simpa [k] using hh
  have coeffSq : Complex.normSq (coeff k) = (Complex.normSq (b-a))⁻¹ := by
    change (1/2)*(1/2)+k*k = _; nlinarith
  have coef1 : Complex.normSq (coeff k-1) = (Complex.normSq (b-a))⁻¹ := by
    change (1/2-1)*(1/2-1)+(k-0)*(k-0) = _; nlinarith
  change dist (a+(b-a)*coeff k) a = 1 ∧ dist (a+(b-a)*coeff k) b = 1
  rw [sqdist_one,sqdist_one,add_sub_cancel_left,
    show a+(b-a)*coeff k-b=(b-a)*(coeff k-1) by ring,
    Complex.normSq_mul,Complex.normSq_mul,coeffSq,coef1]
  simp [hp.ne']

theorem apex_represents {a b v : ℂ} (h : a ≠ b) (h₁ : dist v a = 1) (h₂ : dist v b = 1) :
    ∃ s, apex a b s = v := by
  let z := (v-a)/(b-a)
  have hba := sub_ne_zero.mpr h.symm
  have hZ : (b-a)*z = v-a := by dsimp [z]; field_simp
  have h₁' : Complex.normSq z = (Complex.normSq (b-a))⁻¹ := by
    rw [show z = (v-a)/(b-a) by rfl,Complex.normSq_div,sqdist_one.mp h₁,one_div]
  have h₂' : Complex.normSq (z-1) = (Complex.normSq (b-a))⁻¹ := by
    have hz : z-1 = (v-b)/(b-a) := by dsimp [z]; field_simp; ring
    rw [hz,Complex.normSq_div,sqdist_one.mp h₂,one_div]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.one_re,Complex.sub_im,
    Complex.one_im,sub_zero] at h₁' h₂'
  have hre : z.re = 1/2 := by nlinarith
  have him : (z.im)^2 = (Complex.normSq (b-a))⁻¹-1/4 := by simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]; rw [hre] at h₁'; nlinarith
  have hh : height a b = |z.im| := by rw [height,←him,Real.sqrt_sq_eq_abs]
  by_cases hz : 0 ≤ z.im
  · refine ⟨true,?_⟩
    have ez : coeff (height a b) = z := Complex.ext hre.symm (hh.trans (abs_of_nonneg hz))
    simp only [apex,ite_true,ez,hZ]; ring
  · refine ⟨false,?_⟩
    have ez : coeff (-height a b) = z := Complex.ext hre.symm (by change -height a b = z.im; rw [hh,abs_of_neg (lt_of_not_ge hz),neg_neg])
    simp [apex,ez,hZ]
    
theorem apex_continuous {a b : ℂ} (h : a ≠ b) (s : Bool) :
    ContinuousAt (fun t : ℂ × ℂ => apex t.1 t.2 s) (a,b) := by
  have hn : Complex.normSq (b-a) ≠ 0 := (Complex.normSq_pos.mpr (sub_ne_zero.mpr h.symm)).ne'
  cases s <;> simp [apex,coeff,height,Complex.mk_eq_add_mul_I] <;> fun_prop (disch := assumption)

theorem apex_mem [Carrier] {a b : ℂ} (ha : a ∈ E) (hb : b ∈ E) (s : Bool) : apex a b s ∈ E := by
  have hd := E.sub_mem hb ha
  have hn : Complex.normSq (b-a) ∈ F := by
    rw [←Complex.sq_norm]
    exact F.pow_mem (Carrier.norm_mem hd) 2
  have hq : (1/4 : ℝ) ∈ F := F.div_mem F.one_mem (by norm_num)
  have hh : height a b ∈ F := Carrier.sqrt_mem (F.sub_mem (F.inv_mem hn) hq)
  apply E.add_mem ha (E.mul_mem hd _)
  apply (Carrier.mem_iff _).mpr
  constructor
  · exact F.div_mem F.one_mem (by norm_num)
  · cases s <;> first | exact hh | exact F.neg_mem hh

/-- At a vertex of maximal squared norm the two neighbors are strictly
less than two apart. This selects a nondegenerate circle intersection. -/
theorem extremal_chord {a v b : ℂ} (h₁ : dist v a = 1) (h₂ : dist v b = 1)
    (ha : Complex.normSq a ≤ Complex.normSq v) (hb : Complex.normSq b ≤ Complex.normSq v) :
    Complex.normSq (b-a) < 4 := by
  have h₁ := sqdist_one.mp h₁
  have h₂ := sqdist_one.mp h₂
  have par : Complex.normSq (b-a) + Complex.normSq (a+b-2*v) = 4 := by
    simp [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im] at h₁ h₂ ⊢
    nlinarith
  by_contra! h
  have zero := Complex.normSq_eq_zero.mp (show Complex.normSq (a+b-2*v) = 0 by linarith [Complex.normSq_nonneg (a+b-2*v)])
  have eb : b = 2*v-a := by linear_combination zero
  rw [eb] at hb
  simp [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im] at ha hb h₁
  nlinarith
end
end C5
end
