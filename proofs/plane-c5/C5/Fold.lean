module

public import C5.Density

@[expose] public section

namespace C5
noncomputable section
open Filter Topology Erdos173
def bx (t : ℝ) := Real.sqrt (1-t^2)
def offset (t : ℝ) := Real.sqrt (1-(t+1/2)^2)
def fold (t : ℝ) : Fin 5 → ℂ :=
  ![0, ⟨bx t,-t⟩, ⟨bx t + offset t,1/2⟩, ⟨bx t + offset t,-1/2⟩, ⟨bx t,t⟩]

theorem folded_geometry (t : ℝ) (hp : 0 < t) (ht : t < 1/2) : Pentagon (fold t) := by
  have hb : (bx t)^2 = 1-t^2 := Real.sq_sqrt (by nlinarith [mul_pos hp (sub_pos.mpr ht)])
  have hd : (offset t)^2 = 1-(t+1/2)^2 :=
    Real.sq_sqrt (by nlinarith [mul_pos (sub_pos.mpr ht) (show 0 < 3/2 + t by linarith)])
  constructor
  · intro i j e
    have := congrArg Complex.im e
    fin_cases i <;> fin_cases j <;> first | rfl |
      (simp [fold] at this <;> exfalso <;> linarith)
  · intro i
    rw [dist_eq_norm, Complex.norm_def, Real.sqrt_eq_one]
    fin_cases i <;> change Complex.normSq (_ - _) = 1 <;>
      simp [fold, Fin.reduceFinMk, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] <;>
      nlinarith

def leftPoint : ℂ := ⟨Real.sqrt 3/2,-1/2⟩
def rightPoint : ℂ := ⟨Real.sqrt 3/2,1/2⟩

theorem fold_half : fold (1/2) =
    (![0,leftPoint,rightPoint,leftPoint,rightPoint] : Fin 5 → ℂ) := by
  have hb : bx (1/2) = Real.sqrt 3/2 := by
    unfold bx
    have e : (1-(1/2 : ℝ)^2) = 3/4 := by norm_num
    rw [e,Real.sqrt_div (by norm_num)]
    norm_num
  have hd : offset (1/2) = 0 := by norm_num [offset]
  unfold fold leftPoint rightPoint
  rw [hb,hd,add_zero]
  congr 3 <;> norm_num

theorem continuous_fold (i : Fin 5) : Continuous (fun t => fold t i) := by
  fin_cases i <;> simp [fold,bx,offset,Complex.mk_eq_add_mul_I] <;> fun_prop

theorem fold_approximates :
    Approximates 0 ![leftPoint,rightPoint,leftPoint,rightPoint] := by
  intro r hr
  have H (i : Fin 5) : ∀ᶠ t in 𝓝 (1/2 : ℝ), dist (fold t i) (fold (1/2) i) < r :=
    (Metric.tendsto_nhds.mp (continuous_fold i).continuousAt.tendsto) r hr
  have hall : ∀ᶠ t in 𝓝[<] (1/2 : ℝ), ∀ i, dist (fold t i) (fold (1/2) i) < r :=
    (Filter.eventually_all.mpr H).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in 𝓝[<] (1/2 : ℝ), 0 < t :=
    (lt_mem_nhds (by norm_num : (0:ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ t in 𝓝[<] (1/2 : ℝ), t < 1/2 := self_mem_nhdsWithin
  obtain ⟨t,hall,ht,hp⟩ := (hall.and (hlt.and hpos)).exists
  refine ⟨_,folded_geometry t hp ht,rfl, fun i => ?_⟩
  have e := (hall i.succ).le
  rw [fold_half] at e
  exact e

theorem approx_place {x : ℂ} {q : Fin 4 → ℂ} (h : Approximates x q)
    (z : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    Approximates (place z u x) (fun i => place z u (q i)) := by
  intro r hr
  obtain ⟨p,hp,he,hd⟩ := h r hr
  exact ⟨_,hp.place z hu,congrArg (place z u) he,fun i => (dist_place z hu _ _).le.trans (hd i)⟩

theorem right_unit : ‖rightPoint‖ = 1 := by
  rw [Complex.norm_def,Real.sqrt_eq_one]
  simp [rightPoint,Complex.normSq_apply] <;> ring_nf <;> norm_num

theorem right_left : rightPoint*leftPoint = 1 := by
  apply Complex.ext <;> simp [rightPoint,leftPoint,Complex.mul_re,Complex.mul_im] <;>
    ring_nf <;> norm_num

theorem right_right : rightPoint*rightPoint = omega := by
  apply Complex.ext <;> simp [rightPoint,omega,Complex.mul_re,Complex.mul_im] <;>
    ring_nf <;> norm_num

/-- The two endpoints have density one, while the apex needs only positive upper density. -/
theorem triangle_transfer {K : Set ℂ} {x u : ℂ} (hu : ‖u‖ = 1)
    (hx : ¬ DensityZero K x)
    (h₁ : DensityZero Kᶜ (x+u)) (h₂ : DensityZero Kᶜ (x+u*omega)) : InClass K := by
  have h := approx_place fold_approximates x (u := u*rightPoint) (by simp [norm_mul,hu,right_unit])
  simp only [place,mul_zero,add_zero] at h
  apply density_transfer hx _ h
  intro i
  fin_cases i <;> first | simpa [mul_assoc,right_left] using h₁ | simpa [mul_assoc,right_right] using h₂

end
end C5

end
