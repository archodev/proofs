module
public import C5.ShapeDensity
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

@[expose] public section
namespace C5.Model
noncomputable section
open Set MeasureTheory Filter Topology OAI OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
open OAI.EuclideanFiveColor.ContinuousVectors

variable [Carrier] {R : Set (Fin 5 → E)} (ω : Space R)

theorem empirical_limit {a : ℕ → E} (inj : Function.Injective a) {t : ℂ}
    (ht : Tendsto (fun k => (a k:ℂ)) atTop (𝓝 t)) :
    Tendsto (fun n => average (fun i : Fin n => op (representation R ω) (a i) (raw R ω)))
      atTop (𝓝 (field R ω t)) := by
  let U := representation R ω
  have hP := ((field_continuous R ω).continuousAt.tendsto.comp ht).cesaro_smul
  have hP' : Tendsto (fun n => average (fun i : Fin n => field R ω (a i:ℂ))) atTop (𝓝 (field R ω t)) := by
    simpa [average,Finset.sum_range,Function.comp_def] using hP
  have hB : Tendsto (fun n => average (fun i : Fin n => op U (a i) (residual R ω))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn := (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    apply (tendsto_const_nhds.div_atTop hn : Tendsto (fun n : ℕ => ‖residual R ω‖ / Real.sqrt n) atTop (𝓝 0)).congr'
    filter_upwards [eventually_gt_atTop 0] with n h
    exact (norm_residual_average R ω h (inj.comp Fin.val_injective)).symm
  have he (n : ℕ) : average (fun i : Fin n => op (representation R ω) (a i) (raw R ω)) =
      average (fun i : Fin n => op U (a i) (residual R ω)) + average (fun i : Fin n => field R ω (a i:ℂ)) := by
    simp [average,residual,field_at,U,map_sub,Finset.sum_sub_distrib,smul_sub]
  simpa only [he,zero_add] using hB.add hP'

theorem empirical_ae (a : ℕ → E) (n : ℕ) :
    (average (fun i : Fin n => op (representation R ω) (a i) (raw R ω))) =ᵐ[measure R ω]
      fun η => average (fun i : Fin n => binary (η.val (a i))) := by
  unfold average
  filter_upwards [Lp.coeFn_smul ((n:ℝ)⁻¹) (∑ i : Fin n, op (representation R ω) (a i) (raw R ω)),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin n => op (representation R ω) (a i) (raw R ω)),
    ae_all_iff.mpr (fun i : Fin n => raw_at R ω (a i))] with η h1 h2 h3
  simp only [h1,Pi.smul_apply,h2,h3,binary]

/-- A nonzero limiting color frequency forces some occurrence in every tail.
This holds along every specified injective converging sequence of sites. -/
theorem frequently_label {a : ℕ → E} (inj : Function.Injective a) {t : ℂ}
    (ht : Tendsto (fun k => (a k:ℂ)) atTop (𝓝 t)) (b : Bool) :
    ∀ᵐ η ∂measure R ω, field R ω t η ≠ binary (!b) →
      ∃ᶠ k in atTop, η.val (a k) = b := by
  obtain ⟨φ,hφ,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp (empirical_limit ω inj ht)).exists_seq_tendsto_ae
  filter_upwards [hlim,ae_all_iff.mpr (empirical_ae ω a)] with η hlim hrep hp
  by_contra hn
  have he : ∀ᶠ k in atTop, binary (η.val (a k)) = binary (!b) := by
    have he : ∀ᶠ k in atTop, η.val (a k) ≠ b := not_frequently.mp hn
    filter_upwards [he] with k hk
    cases h : η.val (a k) <;> cases b <;> simp_all
  have hv : Tendsto (fun k => binary (η.val (a k))) atTop (𝓝 (binary (!b))) :=
    tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
  have hav := hv.cesaro_smul.comp hφ.tendsto_atTop
  apply hp
  have HL : Tendsto (fun n => average (fun i : Fin (φ n) => binary (η.val (a i))))
      atTop (𝓝 (field R ω t η)) := hlim.congr' (.of_forall fun n => hrep (φ n))
  exact tendsto_nhds_unique HL (by simpa [Function.comp_def,average,Finset.sum_range] using hav)

/-- Passing an implication conditional on one actual label to its projected
value. The allowed set for the remaining coordinates must be closed. -/
theorem relax_label {ι : Type*} [Fintype ι] {a : ℕ → E} (inj : Function.Injective a) {t : ℂ}
    (ht : Tendsto (fun k => (a k:ℂ)) atTop (𝓝 t)) (b : Bool)
    {Y : ℕ → ι → Hilbert R ω} {L : ι → Hilbert R ω}
    (hlim : ∀ i, Tendsto (fun n => Y n i) atTop (𝓝 (L i)))
    {S : Set (ι → ℂ)} (hS : IsClosed S)
    (rule : ∀ n, ∀ᵐ η ∂measure R ω, η.val (a n) = b → (fun i => Y n i η) ∈ S) :
    ∀ᵐ η ∂measure R ω, field R ω t η ≠ binary (!b) → (fun i => L i η) ∈ S := by
  obtain ⟨φ,hφ,hl⟩ := joint_subsequence _ _ hlim
  have ha := frequently_label ω (inj.comp hφ.injective) (ht.comp hφ.tendsto_atTop) b
  filter_upwards [ha,hl,ae_all_iff.mpr rule] with η hcolor hl hr hp
  exact hS.mem_of_frequently_of_tendsto ((hcolor hp).mono fun n hn => hr (φ n) hn)
    (tendsto_pi_nhds.mpr hl)

end
end C5.Model
end
