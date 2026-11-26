module
public import C5.Flex

@[expose] public section
namespace C5.Model
noncomputable section
open MeasureTheory Filter Topology Set OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
variable [Carrier]

def tilt (n : ℕ) : ℝ := 1/2-arcParam n/4
private theorem tilt_bounds (n) : 0<tilt n ∧ tilt n<1/2 := by
  have h : 0 < arcParam n := by unfold arcParam; positivity
  have h' : arcParam n ≤ 1 := by unfold arcParam; rw [inv_le_one₀ (by positivity)]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  unfold tilt; constructor <;> linarith
private theorem tilt_lim : Tendsto tilt atTop (𝓝 (1/2)) := by
  have h : Tendsto arcParam atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_add (tendsto_const_nhds (x:=1)))
  unfold tilt
  simpa [tilt] using (tendsto_const_nhds (x:=(1/2:ℝ))).sub (h.div_const 4)

def hinge (n : ℕ) (i : Fin 5) := fold (tilt n) 4 * fold (tilt n) i

private theorem bx_sq (n) : (bx (tilt n))^2 = 1-(tilt n)^2 := by
  have h := tilt_bounds n; apply Real.sq_sqrt; nlinarith [mul_pos h.1 (sub_pos.mpr h.2)]

theorem hinge_root (n) : hinge n 0 = 0 := by simp [hinge,fold]
theorem hinge_first (n) : hinge n 1 = 1 := by
  have h := bx_sq n
  apply Complex.ext <;> simp [hinge,fold,Complex.mul_re,Complex.mul_im] <;> nlinarith
theorem hinge_unit (n) : ‖fold (tilt n) 4‖=1 := by
  rw [Complex.norm_def,Real.sqrt_eq_one]
  have h := bx_sq n
  simp [fold,Complex.normSq_apply]; nlinarith
theorem hinge_shape (n) : Pentagon (hinge n) := by
  unfold hinge
  simpa [place] using (folded_geometry _ (tilt_bounds n).1 (tilt_bounds n).2).place 0 (hinge_unit n)
theorem hinge_lim (i) : Tendsto (fun n => hinge n i) atTop (𝓝 ((![0,1,omega,1,omega]:Fin 5→ℂ) i)) := by
  have h (j) := (continuous_fold j).continuousAt.tendsto.comp tilt_lim
  have e := (h 4).mul (h i)
  rw [fold_half] at e
  fin_cases i <;> simpa [hinge,Function.comp_def,right_left,right_right] using e
theorem hinge_last_inj : Function.Injective (fun n => hinge n 4) := by
  intro n m e
  have h := congrArg Complex.re e
  simp [hinge,fold,Complex.mul_re] at h
  have hn := bx_sq n; have hm := bx_sq m
  have e' : tilt n=tilt m := by nlinarith [(tilt_bounds n).1,(tilt_bounds m).1,sq_nonneg (tilt n-tilt m)]
  have eq : arcParam n = arcParam m := by unfold tilt at e'; linarith
  unfold arcParam at eq
  exact_mod_cast add_right_cancel (inv_injective eq)
theorem hinge_mem (n i) : hinge n i ∈ E := by
  have p : arcParam n ∈ F := F.inv_mem (F.add_mem (F.natCast_mem n) F.one_mem)
  have h₂ : (1/2:ℝ) ∈ F := F.div_mem F.one_mem (by norm_num)
  have h : tilt n ∈ F := F.sub_mem h₂ (F.div_mem p (by norm_num))
  have hb : bx (tilt n) ∈ F := Carrier.sqrt_mem (F.sub_mem F.one_mem (F.pow_mem h 2))
  have hd : offset (tilt n) ∈ F := Carrier.sqrt_mem (F.sub_mem F.one_mem (F.pow_mem (F.add_mem h h₂) 2))
  have v (j : Fin 5) : fold (tilt n) j ∈ E := by
    fin_cases j
    · exact E.zero_mem
    · exact (Carrier.mem_iff _).mpr ⟨hb,F.neg_mem h⟩
    · exact (Carrier.mem_iff _).mpr ⟨F.add_mem hb hd,h₂⟩
    · exact (Carrier.mem_iff _).mpr ⟨F.add_mem hb hd,by change -1/2 ∈ F; simpa [neg_div] using F.neg_mem h₂⟩
    · exact (Carrier.mem_iff _).mpr ⟨hb,h⟩
  exact E.mul_mem (v 4) (v i)
def hingeE (n : ℕ) (i : Fin 5) : E := ⟨_,hinge_mem n i⟩

theorem relax_gate {R} (ω : Space R) {ι : Type*} [Fintype ι]
    {a : ℕ → E} (inj : Function.Injective a) {t : ℂ} (ht : Tendsto (fun k => (a k:ℂ)) atTop (𝓝 t))
    (b : Bool) {Y : ℕ → ι → Hilbert R ω} {L : ι → Hilbert R ω}
    (hlim : ∀ i, Tendsto (fun n => Y n i) atTop (𝓝 (L i))) {S : Set (ι→ℂ)} (hS : IsClosed S)
    {G : Space R → Prop}
    (rule : ∀ᶠ n in atTop, ∀ᵐ η ∂measure R ω, G η → η.val (a n)=b → (fun i => Y n i η) ∈ S) :
    ∀ᵐ η ∂measure R ω, G η → field R ω t η ≠ binary (!b) → (fun i => L i η) ∈ S := by
  obtain ⟨φ,hφ,hl⟩ := joint_subsequence _ _ hlim
  have ha := frequently_label ω (inj.comp hφ.injective) (ht.comp hφ.tendsto_atTop) b
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hφ.tendsto_atTop.eventually rule)
  have hall (n : ℕ) : ∀ᵐ η ∂measure R ω, N ≤ n → G η → η.val (a (φ n))=b → (fun i => Y (φ n) i η) ∈ S := by
    by_cases he : N≤n
    · exact (hN n he).mono fun _ hh _ => hh
    · exact .of_forall fun _ h => (he h).elim
  filter_upwards [ha,hl,ae_all_iff.mpr hall] with η hcolor hl hr hg hp
  exact hS.mem_of_frequently_of_tendsto (((hcolor hp).and_eventually (eventually_ge_atTop N)).mono
    fun n ⟨hn,hn'⟩ => hr n hn' hg hn) (tendsto_pi_nhds.mpr hl)

theorem folded_two_fixed (ω : Space templates) (x u : E) (hu : ‖(u:ℂ)‖=1) (b : Bool) :
    ∀ᵐ η ∂measure templates ω, (η.val x=b ∧ η.val (x+u)=b) →
      field templates ω ((x+u*omegaE:E):ℂ) η ≠ binary (!b) →
      matchWeight b (field templates ω ((x+u:E):ℂ) η)+
        matchWeight b (field templates ω ((x+u*omegaE:E):ℂ) η) ≤ 1 := by
  let v := fun n i => x+u*hingeE n i
  let lim : Fin 5 → E := ![x,x+u,x+u*omegaE,x+u,x+u*omegaE]
  have hv (i : Fin 5) : Tendsto (fun n => (v n i:ℂ)) atTop (𝓝 (lim i:ℂ)) := by
    have h := (tendsto_const_nhds (x:=(x:ℂ))).add ((tendsto_const_nhds (x:=(u:ℂ))).mul (hinge_lim i))
    fin_cases i <;> simpa [lim,v,hingeE,omegaE] using h
  have hi : Function.Injective (fun n => v n 4) :=
    fun _ _ e => hinge_last_inj (congrArg Subtype.val (mul_left_cancel₀ (unit_ne hu) (add_left_cancel e)))
  have hch : ∀ᶠ n in atTop, Complex.normSq ((v n 4:ℂ)-(v n 2:ℂ)) < 4 := by
    apply (Complex.continuous_normSq.continuousAt.tendsto.comp ((hv 4).sub (hv 2))).eventually_lt tendsto_const_nhds
    norm_num [lim]
  let ix := fun j : Bool => if j then (2:Fin 5) else 3
  apply relax_gate ω hi (hv 4) b (Y:=fun n j => field templates ω (v n (ix j):ℂ))
    (L:=fun j => field templates ω (lim (ix j):ℂ)) _ (closed_matchPair b)
  · filter_upwards [hch] with n hn
    have hp := (hinge_shape n).place (x:ℂ) hu
    have h0 : v n 0=x := by change x+u*hingeE n 0=x; rw [show hingeE n 0=0 from Subtype.ext (hinge_root n)]; simp
    have h1 : v n 1=x+u := by change x+u*hingeE n 1=x+u; rw [show hingeE n 1=1 from Subtype.ext (hinge_first n)]; simp
    have sh : Pentagon (![x,x+u,v n 2,v n 3,v n 4]:Fin 5→ℂ) := by
      convert hp using 1
      funext i; fin_cases i <;> simp [v,hingeE,place,hinge_first,hinge_root]
    filter_upwards [flex_pair ω x (x+u) (v n 2) (v n 3) (v n 4) sh hn b] with η hh ⟨hx,hb⟩ hc
    change matchWeight b (field templates ω (v n 3:ℂ) η) + matchWeight b (field templates ω (v n 2:ℂ) η) ≤ 1
    rw [add_comm]; exact hh ⟨hx,hb,hc⟩
  · intro j; exact (field_continuous _ _).continuousAt.tendsto.comp (hv _)

end
end C5.Model
end
