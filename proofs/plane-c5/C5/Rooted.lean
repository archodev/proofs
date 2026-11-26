module
public import C5.ConvexLimit

@[expose] public section
namespace C5.Model
noncomputable section
open MeasureTheory Filter Topology Set OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor

def arcParam (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹
def arc (n : ℕ) : ℂ := ⟨Real.sqrt (1-arcParam n^2),arcParam n⟩
theorem arc_inj : Function.Injective arc := by
  intro n m e
  have h := congrArg Complex.im e
  change ((n:ℝ)+1)⁻¹ = ((m:ℝ)+1)⁻¹ at h
  exact_mod_cast add_right_cancel (inv_injective h)
theorem arc_unit (n : ℕ) : ‖arc n‖ = 1 := by
  have h : 0 ≤ arcParam n := by unfold arcParam; positivity
  have h' : arcParam n ≤ 1 := by unfold arcParam; rw [inv_le_one₀ (by positivity)]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hs := Real.sq_sqrt (show 0 ≤ 1-arcParam n^2 by nlinarith [mul_nonneg h (sub_nonneg.mpr h')])
  rw [Complex.norm_def,Real.sqrt_eq_one]
  change Real.sqrt (1-arcParam n^2) * Real.sqrt (1-arcParam n^2) + arcParam n * arcParam n = 1
  nlinarith
theorem arc_lim : Tendsto arc atTop (𝓝 1) := by
  have ht : Tendsto arcParam atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_add (tendsto_const_nhds (x:=1)))
  have hc : Continuous (fun t : ℝ => Complex.mk (Real.sqrt (1-t^2)) t) := by
    simp only [Complex.mk_eq_add_mul_I]; fun_prop
  change Tendsto (fun n => Complex.mk _ (arcParam n)) atTop (𝓝 (Complex.mk 1 0))
  simpa [Function.comp_def] using hc.continuousAt.tendsto.comp ht

variable [Carrier]
theorem arc_mem (n : ℕ) : arc n ∈ E := by
  have ht : arcParam n ∈ F := F.inv_mem (F.add_mem (F.natCast_mem n) F.one_mem)
  exact (Carrier.mem_iff _).mpr ⟨Carrier.sqrt_mem (F.sub_mem F.one_mem (F.pow_mem ht 2)),ht⟩

def kArc (n : ℕ) : E := ⟨_,arc_mem n⟩
theorem kArc_inj : Function.Injective kArc := fun _ _ h => arc_inj (congrArg Subtype.val h)
theorem kArc_unit (n : ℕ) : ‖(kArc n:ℂ)‖ = 1 := arc_unit n

theorem unit_ne {u : E} (h : ‖(u:ℂ)‖ = 1) : u ≠ 0 := by intro e; simp [e] at h

/-- For a finite star of nonzero offsets, rotate about the fixed root, then
translate the root. This turns one actual color at the root into positive
projected weight of that color. -/
theorem rooted_rule {R : Set (Fin 5 → E)} (ω : Space R) {ι : Type*} [Fintype ι]
    (v : ι → E) (hv : ∀ i, v i ≠ 0) (b : Bool) {S : Set (ι → ℂ)}
    (closed : IsClosed S) (conv : Convex ℝ S)
    (rule : ∀ (x u : E), ‖(u:ℂ)‖ = 1 → ∀ η : Space R, η.val x = b →
      (fun i => binary (η.val (x+u*v i))) ∈ S)
    (x u : E) (hu : ‖(u:ℂ)‖ = 1) :
    ∀ᵐ η ∂measure R ω, field R ω (x:ℂ) η ≠ binary (!b) →
      (fun i => field R ω ((x+u*v i:E):ℂ) η) ∈ S := by
  have aux (y : E) : ∀ᵐ η ∂measure R ω, η.val y = b →
      (fun i => field R ω ((y+u*v i:E):ℂ) η) ∈ S := by
    apply convex_limit ω (a := fun i n => y+(u*kArc n)*v i) _ _ closed conv
    · intro n; exact .of_forall (rule _ _ (by simp [norm_mul,hu,kArc_unit]))
    · intro i n m e
      exact kArc_inj (mul_left_cancel₀ (unit_ne hu) (mul_right_cancel₀ (hv i) (add_left_cancel e)))
    · intro i
      simpa [kArc] using (tendsto_const_nhds (x:=(y:ℂ))).add (((tendsto_const_nhds (x:=(u:ℂ))).mul arc_lim).mul_const (v i:ℂ))
  let t := fun n => x + (kArc n - 1)
  have tlim : Tendsto (fun n => (t n:ℂ)) atTop (𝓝 (x:ℂ)) := by
    simpa [t,kArc] using (tendsto_const_nhds (x:=(x:ℂ))).add (arc_lim.sub_const 1)
  apply relax_label ω (a := t) (fun n m e => kArc_inj (sub_left_inj.mp (add_left_cancel e))) tlim b
    (Y := fun n i => field R ω ((t n+u*v i:E):ℂ)) _ closed (fun n => aux (t n))
  intro i
  exact (field_continuous _ _).continuousAt.tendsto.comp (tlim.add_const _)

end
end C5.Model
end
