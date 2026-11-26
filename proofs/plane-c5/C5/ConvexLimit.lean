module
public import C5.Limits
public import Mathlib.Analysis.Convex.Combination

@[expose] public section
namespace C5.Model
noncomputable section
open MeasureTheory Filter Topology Set OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
variable [Carrier] {R : Set (Fin 5 → E)} (ω : Space R)

/-- Simultaneously replace moving labels by projected values in a closed
convex restriction. A fixed event can gate the restriction. Distinctness is
needed within each list of sites, not between different lists. -/
theorem convex_limit {ι : Type*} [Fintype ι] {a : ι → ℕ → E} {z : ι → ℂ}
    (hi : ∀ j, Function.Injective (a j)) (ht : ∀ j, Tendsto (fun n => (a j n:ℂ)) atTop (𝓝 (z j)))
    {G : Space R → Prop} {S : Set (ι → ℂ)} (closed : IsClosed S) (conv : Convex ℝ S)
    (rule : ∀ n, ∀ᵐ η ∂measure R ω, G η → (fun j => binary (η.val (a j n))) ∈ S) :
    ∀ᵐ η ∂measure R ω, G η → (fun j => field R ω (z j) η) ∈ S := by
  let v := fun n j => average (fun i : Fin n => OAI.EuclideanFiveColor.ContinuousVectors.op
    (representation R ω) (a j i) (raw R ω))
  have lim (j) : Tendsto (fun n => v n j) atTop (𝓝 (field R ω (z j))) := empirical_limit ω (hi j) (ht j)
  obtain ⟨φ,hφ,hlim⟩ := joint_subsequence _ _ lim
  have repr (n j) := empirical_ae ω (a j) n
  filter_upwards [hlim,ae_all_iff.mpr rule,ae_all_iff.mpr (fun n => ae_all_iff.mpr (repr n))] with η hl hr he hg
  apply closed.mem_of_tendsto (tendsto_pi_nhds.mpr hl)
  filter_upwards [hφ.tendsto_atTop.eventually_gt_atTop 0] with n hn
  let m := φ n
  have hm : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmem : (∑ i : Fin m, (m:ℝ)⁻¹ • (fun j => binary (η.val (a j i)))) ∈ S :=
    conv.sum_mem (fun _ _ => by positivity) (by simp [hm]) (fun i _ => hr i hg)
  convert hmem using 1
  funext j
  change v (φ n) j η = _
  rw [show v (φ n) j η = average (fun i : Fin m => binary (η.val (a j i))) from he _ _]
  simp [average,Finset.sum_apply,Finset.smul_sum]

end
end C5.Model
end
