module
public import C5.Measurable

@[expose] public section
namespace C5
open Erdos173 MeasureTheory Metric Set
noncomputable section

/-- Every sufficiently close five-point pattern has a positive area of common
translations into K when all five limiting positions are density-one points. -/
theorem positive_translations {K : Set ℂ} {v : Fin 5 → ℂ}
    (h : ∀ i, DensityZero Kᶜ (v i)) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : Fin 5 → ℂ, (∀ i, dist (w i) (v i) ≤ r) →
      volume {d | ∀ i, d + w i ∈ K} ≠ 0 := by
  choose δ hδ hd using fun i => h i (Real.pi/32) (by positivity)
  let m := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin 5)).Nonempty) δ
  have hm : 0 < m := by simpa [m,Finset.lt_inf'_iff] using hδ
  let r := m/4
  have hr : 0<r := by dsimp [r]; positivity
  refine ⟨r,hr,fun w hw hz => ?_⟩
  let C := ENNReal.ofReal (Real.pi/32 * (2*r)^2)
  let bad (i : Fin 5) := (· + w i) ⁻¹' (Kᶜ ∩ closedBall (v i) (2*r))
  have hbad (i : Fin 5) : volume (bad i) ≤ C := by
    unfold bad
    rw [measure_preimage_add_right]
    apply hd i _ (by positivity)
    have : m ≤ δ i := Finset.inf'_le _ (Finset.mem_univ i)
    unfold r; linarith
  have cover : closedBall (0:ℂ) r ⊆ {d | ∀ i, d+w i ∈ K} ∪ ⋃ i, bad i := by
    intro d hd'
    by_cases hh : ∀ i, d+w i ∈ K
    · exact Or.inl hh
    push Not at hh
    obtain ⟨i,hi⟩ := hh
    refine Or.inr (mem_iUnion.mpr ⟨i,hi,?_⟩)
    change dist (d+w i) (v i) ≤ 2*r
    calc dist (d+w i) (v i) ≤ dist (d+w i) (w i) + dist (w i) (v i) := dist_triangle _ _ _
      _ ≤ 2*r := by simpa [two_mul] using add_le_add (show dist d 0 ≤ r from hd') (hw i)
  have bound : volume (closedBall (0:ℂ) r) ≤ ∑ _i : Fin 5, C := calc
    _ ≤ _ := measure_mono cover
    _ ≤ _ := measure_union_le _ _
    _ ≤ 0 + ∑ _i : Fin 5, C := by
      rw [hz, zero_add]
      exact (measure_iUnion_le _).trans (by simpa using ENNReal.tsum_le_tsum hbad)
    _ = _ := zero_add _
  have ball : volume (closedBall (0:ℂ) r) = ENNReal.ofReal (Real.pi*r^2) := by
    rw [Complex.volume_closedBall, ENNReal.ofReal_mul Real.pi_pos.le,ENNReal.ofReal_pow hr.le,mul_comm]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal,NNReal.coe_real_pi]
  rw [ball] at bound
  have ht : (∑ _i : Fin 5, C) < ENNReal.ofReal (Real.pi*r^2) := by
    simp only [Fin.sum_univ_five,C]
    repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    nlinarith [sq_pos_of_pos hr,mul_pos Real.pi_pos (sq_pos_of_pos hr)]
  exact (not_lt_of_ge bound) ht

/-- A countable dense test family can be imposed simultaneously on a measurable
sample. The density assumption here is a property of the family of *shapes*. -/
theorem measured_test_family (c : ℂ → Bool) (hm : NullMeasurableSet (cls c true) volume)
    {ι : Type*} (v : ι → Fin 5 → ℂ)
    (dense : ∀ p, Pentagon p → ∀ r : ℝ, 0 < r → ∃ n, ∀ i, dist (v n i) (p i) ≤ r) :
    ∃ n a, volume {d | ∀ i, c (d+v n i) = a} ≠ 0 := by
  obtain ⟨a,p,hp,ha⟩ := measurable_core c hm
  obtain ⟨r,hr,h⟩ := positive_translations (K := cls c a) (v := p) (fun i => (ha i).2)
  obtain ⟨n,hn⟩ := dense p hp r hr
  exact ⟨n,a,h (v n) hn⟩

end
end C5
end
