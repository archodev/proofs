module
public import C5.Model
@[expose] public section
namespace C5.Model
noncomputable section
open MeasureTheory OAI OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
open OAI.EuclideanFiveColor.ContinuousVectors
open scoped InnerProductSpace
variable [Carrier] (R : Set (Fin 5 → E)) (ω : Space R)

def average {H : Type*} [AddCommGroup H] [Module ℝ H] {n : ℕ} (f : Fin n → H) :=
  (n : ℝ)⁻¹ • ∑ i, f i

theorem norm_residual_average {n : ℕ} (hn : 0<n) {a : Fin n → E} (ha : Function.Injective a) :
    ‖average (fun i => op (representation R ω) (a i) (residual R ω))‖ =
      ‖residual R ω‖ / Real.sqrt n := by
  let b := fun i => op (representation R ω) (a i) (residual R ω)
  have hv (i : Fin n) : ‖b i‖ = ‖residual R ω‖ := Unitary.norm_map _ _
  have ho (i j : Fin n) (h : i ≠ j) : ⟪b i,b j⟫_ℂ = 0 := residual_orthogonal R ω (ha.ne h)
  have he (i : Fin n) : ∑ j, ⟪b i,b j⟫_ℂ = ⟪b i,b i⟫_ℂ := by
    apply Finset.sum_eq_single i
    · intro j _ hj; exact ho i j hj.symm
    · simp
  have hsq : ‖∑ i, b i‖^2 = (n:ℝ)*‖residual R ω‖^2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),sum_inner]
    simp only [inner_sum,he,inner_self_eq_norm_sq_to_K,hv,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    simp [← Complex.ofReal_pow]
  have hs : ‖∑ i,b i‖ = Real.sqrt n * ‖residual R ω‖ := by
    have e := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
    nlinarith [sq_nonneg (‖∑ i,b i‖ - Real.sqrt n * ‖residual R ω‖),
      sq_nonneg (‖∑ i,b i‖ + Real.sqrt n * ‖residual R ω‖),
      mul_nonneg (Real.sqrt_nonneg (n:ℝ)) (norm_nonneg (residual R ω)),
      norm_nonneg (∑ i,b i),show (Real.sqrt (n:ℝ)*‖residual R ω‖)^2 =
        (n:ℝ)*‖residual R ω‖^2 by rw [mul_pow,e]]
  have nn : (n:ℝ) ≠ 0 := by positivity
  have sn : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  change ‖(n : ℝ)⁻¹ • ∑ i,b i‖ = _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),hs]
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)]

theorem average_shift {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {n : ℕ} (hn : 0<n) (f : Fin n → H) (v : H) {ε : ℝ} (h : ∀ i, ‖f i - v‖ ≤ ε) :
    ‖average f - v‖ ≤ ε := by
  have hn' : (n:ℝ) ≠ 0 := by positivity
  have eq : average f - v = (n:ℝ)⁻¹ • ∑ i,(f i-v) := by
    simp [average,Finset.sum_sub_distrib,smul_sub,← Nat.cast_smul_eq_nsmul ℝ n v,smul_smul,hn']
  rw [eq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc _ ≤ (n:ℝ)⁻¹ * ∑ _i : Fin n, ε := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => h i)
       _ = ε := by simp [hn']

/-- Uniform estimate for any injective finite list, given a common bound on
the continuous projected field over that list. -/
theorem raw_average_bound {n : ℕ} (hn : 0<n) {a : Fin n → E} (ha : Function.Injective a)
    (z : ℂ) {ε : ℝ} (h : ∀ i, ‖field R ω (a i:ℂ)-field R ω z‖ ≤ ε) :
    ‖average (fun i => op (representation R ω) (a i) (raw R ω)) - field R ω z‖ ≤
      ‖residual R ω‖ / Real.sqrt n + ε := by
  have e (i : Fin n) : op (representation R ω) (a i) (raw R ω) =
      op (representation R ω) (a i) (residual R ω) + field R ω (a i:ℂ) := by
    rw [field_at,residual,map_sub,sub_add_cancel]
  simp_rw [e]
  have ea : average (fun i => op (representation R ω) (a i) (residual R ω) + field R ω (a i:ℂ)) =
      average (fun i => op (representation R ω) (a i) (residual R ω)) +
      average (fun i => field R ω (a i:ℂ)) := by simp [average,Finset.sum_add_distrib,smul_add]
  rw [ea,add_sub_assoc]
  exact (norm_add_le _ _).trans (add_le_add (norm_residual_average R ω hn ha).le (average_shift hn _ _ h))

end
end C5.Model
end
