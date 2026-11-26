module

public import Erdos173.Measurable.SelfSupport
public import Mathlib.Tactic

@[expose] public section
namespace C5
open MeasureTheory OAI.EuclideanFiveColor Erdos173 Set Filter
noncomputable section

/-- Centers from which a positive measure of steps of radius r enter S. -/
def hits (r : ℝ) (S : Set ℂ) : Set ℂ :=
  {x | angularMeasure {t | x + (r : ℂ) * direction t ∈ S} ≠ 0}

theorem not_hits {r : ℝ} {S : Set ℂ} {x : ℂ} :
    x ∉ hits r S ↔ ∀ᵐ t ∂angularMeasure, x + (r:ℂ)*direction t ∉ S := by
  simp [hits, ae_iff]

theorem measurable_hits {r : ℝ} {S : Set ℂ} (hS : MeasurableSet S) : MeasurableSet (hits r S) := by
  have h : MeasurableSet {q : ℂ × Angles | q.1 + (r : ℂ)*direction q.2 ∈ S} :=
    hS.preimage (continuous_fst.add (continuous_const.mul (direction_continuous.comp continuous_snd))).measurable
  exact (measurableSet_eq_fun (measurable_measure_prodMk_left (ν := angularMeasure) h)
    measurable_const).compl

theorem hits_mono (r : ℝ) {S T : Set ℂ} (h : S ⊆ T) : hits r S ⊆ hits r T :=
  fun _ hx hzero => hx (measure_mono_null (fun _ ht => h ht) hzero)

theorem hits_union (r : ℝ) (S T : Set ℂ) : hits r (S ∪ T) = hits r S ∪ hits r T := by
  ext x
  rw [← not_iff_not, not_hits]
  simp only [mem_union, not_or, not_hits, Filter.eventually_and]

theorem hits_null {r : ℝ} {S : Set ℂ} (hS : MeasurableSet S) (hn : volume S = 0) :
    volume (hits r S) = 0 := by
  have h : MeasurableSet {q : ℂ × Angles | q.1 + (r:ℂ)*direction q.2 ∉ S} :=
    hS.compl.preimage (continuous_fst.add (continuous_const.mul (direction_continuous.comp continuous_snd))).measurable
  have h1 : ∀ᵐ t ∂angularMeasure, ∀ᵐ x : ℂ, x + (r:ℂ)*direction t ∉ S := by
    apply Eventually.of_forall
    intro t
    rw [ae_iff]
    simp only [not_not]
    change volume ((· + (r:ℂ)*direction t) ⁻¹' S) = 0
    exact
      (show volume ((· + (r:ℂ)*direction t) ⁻¹' S) = 0 by rw [measure_preimage_add_right,hn])
  have h2 := (Measure.ae_ae_comm h).mpr h1
  have h3 : ∀ᵐ x : ℂ, x ∉ hits r S := h2.mono fun _ hx => not_hits.mpr hx
  simpa using (ae_iff.mp h3)

theorem hits_comm (r s : ℝ) {S : Set ℂ} (hS : MeasurableSet S) :
    hits r (hits s S) = hits s (hits r S) := by
  ext x
  rw [← not_iff_not, not_hits, not_hits]
  simp_rw [not_hits]
  have hm : MeasurableSet {q : Angles × Angles |
      x + (r:ℂ)*direction q.1 + (s:ℂ)*direction q.2 ∉ S} :=
    hS.compl.preimage (((continuous_const.add (continuous_const.mul (direction_continuous.comp
      continuous_fst))).add (continuous_const.mul (direction_continuous.comp continuous_snd))).measurable)
  simpa only [add_right_comm x] using (Measure.ae_ae_comm (μ := angularMeasure) (ν := angularMeasure) (p := fun t u => x + (r:ℂ)*direction t + (s:ℂ)*direction u ∉ S) hm)

theorem hits_twice {r : ℝ} (hr : 0 < r) {S : Set ℂ} (hS : MeasurableSet S) (hn : volume S = 0) :
    hits r (hits r S) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x
  rw [not_hits]
  simp_rw [not_hits]
  let N := (fun z : ℂ => x + (r:ℂ)*z) ⁻¹' S
  have hm : MeasurableSet N := hS.preimage (continuous_const.add
    (continuous_const.mul continuous_id)).measurable
  have hn' : volume N = 0 := by
    have e : N = (fun z : ℂ => r • z) ⁻¹' ((x + ·) ⁻¹' S) := by ext; simp [N,Complex.real_smul]
    rw [e,Measure.addHaar_preimage_smul volume hr.ne',measure_preimage_add,hn,mul_zero]
  have h := angularMeasure_prod_add_mem hm hn'
  have he : ∀ᵐ q : Angles × Angles ∂angularMeasure.prod angularMeasure,
      direction q.1 + direction q.2 ∉ N := by simpa [ae_iff] using h
  simpa [N,mul_add,add_assoc] using Measure.ae_ae_of_ae_prod he

/-- One boundary point works for two prescribed radii. Three steps suffice:
each radius-word of length three has a repeated radius, and the operators commute. -/
theorem good_two_radii {S : Set ℂ} (hS : MeasurableSet S) (hn : volume S = 0)
    (hne : S.Nonempty) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∃ x ∈ S, x ∉ hits r S ∧ x ∉ hits s S := by
  by_contra hno
  have hsub : S ⊆ hits r S ∪ hits s S := by
    intro x hx
    by_contra he
    exact hno ⟨x,hx,not_or.mp he⟩
  let F := fun T : Set ℂ => hits r T ∪ hits s T
  have mono : Monotone F := fun _ _ h => union_subset_union (hits_mono r h) (hits_mono s h)
  have inc : S ⊆ F (F (F S)) := hsub.trans ((mono hsub).trans (mono (mono hsub)))
  have he (a : ℝ) : hits a ∅ = ∅ := by ext; simp [hits]
  have rr := hits_twice hr hS hn
  have ss := hits_twice hs hS hn
  have rrs := hits_twice hr (measurable_hits (r := s) hS) (hits_null hS hn)
  have ssr := hits_twice hs (measurable_hits (r := r) hS) (hits_null hS hn)
  have rsr : hits r (hits s (hits r S)) = ∅ := by rw [hits_comm s r hS,rrs]
  have srs : hits s (hits r (hits s S)) = ∅ := by rw [hits_comm r s hS,ssr]
  have emp : F (F (F S)) = ∅ := by
    simp only [F,hits_union,rr,ss,he,rrs,ssr,rsr,srs,union_empty]
  exact hne.ne_empty (subset_empty_iff.mp (emp ▸ inc))

end
end C5
end
