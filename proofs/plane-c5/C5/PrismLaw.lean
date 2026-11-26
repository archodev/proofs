module
public import C5.Triangles

@[expose] public section
namespace C5.Model
noncomputable section
open MeasureTheory Filter Topology Set OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
variable [Carrier]

def base : Fin 3 → E := ![0,1,omegaE]
theorem base_triangle : triangle (fun i => (base i:ℂ)) := by
  have hu := omega_unit
  have h : ‖1-omega‖=1 := Erdos173.norm_one_sub_ζ
  intro i j e
  fin_cases i <;> fin_cases j <;> first | exact (e rfl).elim |
    simp [base,dist_eq_norm,omegaE,hu,h,norm_sub_rev omega 1]
theorem base_inj : Function.Injective base := by
  intro i j eq
  by_contra h
  have ht := base_triangle i j h
  simp [eq] at ht
def T (x u : E) (i : Fin 3) := x+u*base i
theorem T_triangle (x u : E) (hu : ‖(u:ℂ)‖=1) : triangle (fun i => (T x u i:ℂ)) :=
  fun i j h => (dist_place (x:ℂ) hu _ _).trans (base_triangle i j h)

private theorem color_unique {f : Fin 3 → Fin 3 → Bool} {a : Bool}
    (h0 : ∀ i, f 0 i = a)
    (rule : ∀ {r s : Fin 3}, r≠s → ∀ b, (∀ i, f r i=b) →
      ∀ i j, i≠j → f s i=b → f s j≠b) : ∃! i,f 1 i=a := by
  by_cases h : ∃ i,f 1 i=a
  · obtain ⟨i,hi⟩ := h
    exact ⟨i,hi,fun j hj => by_contra fun ne => rule (r:=0) (s:=1) (by decide) a h0 i j (Ne.symm ne) hi hj⟩
  · have h1 (i) : f 1 i = !a := by
      have he : f 1 i ≠ a := fun e => h ⟨i,e⟩
      cases a <;> cases e : f 1 i <;> simp_all
    obtain ⟨i,j,hij,e⟩ := two_equal (f 2)
    by_cases ei : f 2 i = a
    · exact (rule (r:=0) (s:=2) (by decide) _ h0 i j hij ei (e.symm.trans ei)).elim
    · have ei' : f 2 i = !a := by cases a <;> cases he : f 2 i <;> simp_all
      exact (rule (r:=1) (s:=2) (by decide) _ h1 i j hij ei' (e.symm.trans ei')).elim

theorem prism_law (ω : Space templates) (x u w : E) (hu : ‖(u:ℂ)‖=1) (hw : ‖(w:ℂ)‖=1) (a : Bool) :
    ∀ᵐ η ∂measure templates ω, (∀ i, η.val (T x u i)=a) →
      ∑ i : Fin 3, matchWeight a (P ω (T x u i+w) η) = 1 := by
  let t := T x u
  let v := fun n => w*kArc n
  have hv : Function.Injective v := fun _ _ eq => kArc_inj (mul_left_cancel₀ (unit_ne hw) eq)
  have hvu (n) : ‖(v n:ℂ)‖=1 := by simp [v,norm_mul,hw,kArc_unit]
  have htl : Tendsto (fun n => (v n:ℂ)) atTop (𝓝 (w:ℂ)) := by
    simpa [v,kArc] using (tendsto_const_nhds (x:=(w:ℂ))).mul arc_lim
  let grid := fun n (z : Fin 3 × Fin 3) => t z.2 + v n*base z.1
  have tinj : Function.Injective t := fun _ _ h => base_inj (mul_left_cancel₀ (unit_ne hu) (add_left_cancel h))
  have hi : ∀ᶠ n in atTop, Function.Injective (grid n) := by
    have one (p q : Fin 3 × Fin 3) : ∀ᶠ n in atTop, grid n p=grid n q → p=q := by
      obtain ⟨r,i⟩ := p; obtain ⟨s,j⟩ := q
      by_cases h : r=s
      · subst s
        exact .of_forall fun n eq => Prod.ext rfl (tinj (add_right_cancel eq))
      · have inj : Function.Injective (fun n => v n*(base r-base s)) :=
          fun _ _ e => hv (mul_right_cancel₀ (sub_ne_zero.mpr (base_inj.ne h)) e)
        filter_upwards [eventually_ne_point _ inj (t j-t i)] with n hn eq
        apply False.elim (hn ?_)
        change t i+v n*base r=t j+v n*base s at eq
        linear_combination eq
    filter_upwards [eventually_all.mpr fun p => eventually_all.mpr (one p)] with n hn
    exact fun i j => hn i j
  obtain ⟨N,hN⟩ := eventually_atTop.mp hi
  let S := {f : Fin 3 → ℂ | ∑ i, matchWeight a (f i) = 1}
  have closed : IsClosed S := by
    apply isClosed_eq _ continuous_const
    cases a <;> simp [matchWeight,Fin.sum_univ_three] <;> fun_prop
  have conv : Convex ℝ S := by
    intro f hf g hg r s hr hs eq
    cases a <;> simp [S,matchWeight,Fin.sum_univ_three,Complex.smul_re] at hf hg ⊢ <;>
      first | linear_combination r*hf+s*hg+eq | linear_combination r*hf+s*hg-2*eq
  let dirs := fun i n => t i + v (N+n)
  apply convex_limit ω (a:=dirs) _ _ closed conv
  · intro n; apply Eventually.of_forall; intro η hrow
    let f := fun r i => η.val (grid (N+n) (r,i))
    have H0 (i) : f 0 i=a := by simpa [f,grid,base] using hrow i
    have rule {r s : Fin 3} (hrs : r≠s) (d : Bool) (hd : ∀ i,f r i=d) (i j : Fin 3)
        (hij : i≠j) (ei : f s i=d) : f s j≠d := by
      intro ej
      obtain ⟨k,hik,hjk⟩ := (by decide : ∀ i j : Fin 3,i≠j→∃ k : Fin 3,i≠k ∧ j≠k) i j hij
      let v' := fun z => (grid (N+n) z:ℂ)
      have hin : Function.Injective v' := Subtype.val_injective.comp (hN _ (Nat.le_add_right _ _))
      have ed (z w' : Fin 3 × Fin 3) (had : Adj z w') : dist (v' z) (v' w')=1 := by
        have := prism_edges (T_triangle x u hu) (T_triangle 0 (v (N+n)) (hvu _)) z w' had
        simpa [prism,T,grid,v',t] using this
      have hp := prism_pentagon hin ed hrs hij hik hjk
      let p := grid (N+n) ∘ prismPath r s i j k
      apply η.property p hp 0 1
      simp only [kCoeff_one,one_mul,zero_add]
      intro m
      change f (prismPath r s i j k m).1 (prismPath r s i j k m).2 = f r i
      rw [hd i]; fin_cases m <;> first | exact hd _ | exact ei | exact ej
    obtain ⟨i,hfi,hi⟩ := color_unique H0 (fun hr d hd j k hj he => rule hr d hd j k hj he)
    have e (j) : η.val (dirs j n)=f 1 j := by simp [dirs,f,grid,base]
    change ∑ j,matchWeight a (binary (η.val (dirs j n))) = 1
    simp_rw [e]
    rw [Finset.sum_eq_single i]
    · rw [hfi]; cases a <;> simp [matchWeight,binary]
    · intro j _ hj
      have ne : f 1 j ≠ a := fun he => hj (hi j he)
      cases a <;> cases e : f 1 j <;> simp_all [matchWeight,binary]
    · simp
  · intro j n m eq
    exact Nat.add_left_cancel (hv (add_left_cancel eq))
  · intro i
    exact tendsto_const_nhds.add (htl.comp ((show StrictMono (fun n : ℕ => N+n) from fun _ _ h => Nat.add_lt_add_left h N).tendsto_atTop))

end
end C5.Model
end
