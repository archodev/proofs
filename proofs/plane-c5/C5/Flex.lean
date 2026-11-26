module
public import C5.AngularTransfer

@[expose] public section
namespace C5.Model
noncomputable section
open Filter Topology MeasureTheory Set OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
variable [Carrier]

def apexE (a b : E) (s : Bool) : E := ⟨apex a b s,apex_mem a.property b.property s⟩

theorem eventually_injective {ι : Type*} [Finite ι] {f : ℕ → ι → ℂ} {g : ι → ℂ}
    (hg : Function.Injective g) (ht : ∀ i,Tendsto (fun n => f n i) atTop (𝓝 (g i))) :
    ∀ᶠ n in atTop, Function.Injective (f n) := by
  classical
  have h (i j : ι) : ∀ᶠ n in atTop, i≠j → f n i≠f n j := by
    by_cases e : i=j
    · simp [e]
    · exact (tendsto_const_nhds.eventually_lt ((ht i).dist (ht j)) (dist_pos.mpr (hg.ne e))).mono fun _ h _ => dist_pos.mp h
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (h i))] with n hh
  exact fun i j he => by_contra fun hn => hh i j hn he

theorem extract_distinct {f : ℕ → ℂ} {z : ℂ} (ht : Tendsto f atTop (𝓝 z))
    (hn : ∀ᶠ n in atTop,f n ≠ z) : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Function.Injective (f ∘ ψ) := by
  have ha : Tendsto (fun n => dist (f n) z) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using ht.dist (tendsto_const_nhds (x:=z)),hn.mono fun _ h => dist_pos.mpr h⟩
  obtain ⟨ψ,hψ,hmono⟩ := strictMono_subseq_of_tendsto_atTop (tendsto_inv_nhdsGT_zero.comp ha)
  exact ⟨ψ,hψ,fun i j he => hmono.injective (congrArg (fun v => (dist v z)⁻¹) he)⟩

theorem eventually_ne_point {α : Type*} (f : ℕ → α) (hf : Function.Injective f) (p : α) :
    ∀ᶠ n in atTop, f n ≠ p := by
  by_cases h : ∃ k,f k=p
  · obtain ⟨k,rfl⟩ := h
    exact (eventually_gt_atTop k).mono fun _ hn => hf.ne hn.ne'
  · exact .of_forall (not_exists.mp h)

def matchPair (b : Bool) : Set (Bool → ℂ) :=
  {f | matchWeight b (f false)+matchWeight b (f true) ≤ 1}
theorem closed_matchPair (b : Bool) : IsClosed (matchPair b) := by
  apply isClosed_le _ continuous_const
  cases b <;> simp [matchWeight] <;> fun_prop
theorem convex_matchPair (b : Bool) : Convex ℝ (matchPair b) := by
  intro f hf g hg a d ha hd had
  cases b <;> simp [matchPair,matchWeight,Complex.smul_re] at hf hg ⊢ <;>
    nlinarith only [mul_le_mul_of_nonneg_left hf ha,mul_le_mul_of_nonneg_left hg hd,had]

/-- Flex the middle two vertices while the other three labels stay fixed. -/
theorem flex_pair (ω : Space templates) (a b p q c : E)
    (hp : Pentagon (![a,b,p,q,c] : Fin 5 → ℂ))
    (hch : Complex.normSq ((c:ℂ)-(p:ℂ)) < 4) (color : Bool) :
    ∀ᵐ η ∂measure templates ω, (η.val a=color ∧ η.val b=color ∧ η.val c=color) →
      matchWeight color (field templates ω (p:ℂ) η) +
      matchWeight color (field templates ω (q:ℂ) η) ≤ 1 := by
  have distQP : dist (q:ℂ) p = 1 := (dist_comm _ _).trans (hp.edges 2)
  have distQC : dist (q:ℂ) c = 1 := hp.edges 3
  have epc : (p:ℂ) ≠ c := hp.distinct.ne (show (2:Fin 5) ≠ 4 by decide)
  have ebq : (b:ℂ) ≠ q := hp.distinct.ne (show (1:Fin 5) ≠ 3 by decide)
  have epb : p ≠ b := fun e => hp.distinct.ne (show (2:Fin 5) ≠ 1 by decide) (congrArg Subtype.val e)
  obtain ⟨s,es⟩ := apex_represents epc distQP distQC
  let u := fun n => b+kArc n*(p-b)
  let v := fun n => apexE (u n) c s
  have hu : Function.Injective (fun n => (u n:ℂ)) := by
    intro n m e
    exact kArc_inj (mul_right_cancel₀ (sub_ne_zero.mpr epb) (add_left_cancel (Subtype.ext e : u n=u m)))
  have lu : Tendsto (fun n => (u n:ℂ)) atTop (𝓝 (p:ℂ)) := by
    simpa [u,kArc] using (tendsto_const_nhds (x:=(b:ℂ))).add (arc_lim.mul_const ((p:ℂ)-b))
  have lv : Tendsto (fun n => (v n:ℂ)) atTop (𝓝 (q:ℂ)) := by
    rw [←es]; exact (apex_continuous epc s).tendsto.comp (lu.prodMk_nhds tendsto_const_nhds)
  let f := fun n => (![a,b,u n,v n,c] : Fin 5 → E)
  have lin (i : Fin 5) : Tendsto (fun n => (f n i:ℂ)) atTop (𝓝 ((![a,b,p,q,c] : Fin 5 → ℂ) i)) := by
    fin_cases i <;> first | exact lu | exact lv | exact tendsto_const_nhds
  have hi := eventually_injective hp.distinct lin
  have chord : ∀ᶠ n in atTop, Complex.normSq ((c:ℂ)-(u n:ℂ)) < 4 :=
    (Complex.continuous_normSq.continuousAt.tendsto.comp (tendsto_const_nhds.sub lu)).eventually_lt tendsto_const_nhds hch
  have valid : ∀ᶠ n in atTop,f n ∈ templates := by
    filter_upwards [hi,chord] with n hin hn
    have hne : (u n:ℂ)≠c := hin.ne (show (2:Fin 5)≠4 by decide)
    have he := apex_edges hne hn s
    refine ⟨hin,fun i => ?_⟩
    fin_cases i
    · exact hp.edges 0
    · have hbp : ‖(p:ℂ)-b‖=1 := by rw [norm_sub_rev,←dist_eq_norm]; exact hp.edges 1
      change dist (b:ℂ) (↑b+(kArc n:ℂ)*((p:ℂ)-b))=1
      simp [dist_eq_norm,norm_mul,kArc_unit,hbp]
    · exact (dist_comm _ _).trans he.1
    · exact he.2
    · exact hp.edges 4
  have avoidLimit : ∀ᶠ n in atTop, (v n:ℂ) ≠ q := by
    filter_upwards [valid,eventually_ne_point _ hu (apex b q false),eventually_ne_point _ hu (apex b q true)] with n hn h0 h1 eq
    have hB : dist (u n:ℂ) b=1 := (dist_comm _ _).trans (hn.edges 1)
    have hQ : dist (u n:ℂ) q=1 := eq ▸ hn.edges 2
    obtain ⟨d,hd⟩ := apex_represents ebq hB hQ
    cases d <;> first | exact h0 hd.symm | exact h1 hd.symm
  obtain ⟨ψ,hψ,hv⟩ := extract_distinct lv avoidLimit
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hψ.tendsto_atTop.eventually valid)
  let g := fun n => ψ (N+n)
  have hg : StrictMono g := hψ.comp (fun _ _ h => Nat.add_lt_add_left h N)
  have hvg : Function.Injective (fun n => v (g n)) := fun _ _ e => Nat.add_left_cancel (hv (congrArg Subtype.val e))
  let fidx := fun (j : Bool) n => if j then v (g n) else u (g n)
  have lidx (j : Bool) : Tendsto (fun n => (fidx j n:ℂ)) atTop (𝓝 (if j then (q:ℂ) else p)) := by
    cases j <;> first | exact lv.comp hg.tendsto_atTop | exact lu.comp hg.tendsto_atTop
  apply convex_limit ω (a:=fidx) (z:=fun j : Bool => if j then (q:ℂ) else p) _ lidx (closed_matchPair color) (convex_matchPair color)
  · intro n; apply Eventually.of_forall
    intro η ⟨ha,hb,hc⟩
    have htmp := hN (N+n) (Nat.le_add_right _ _)
    have hno := η.property (f (g n)) htmp 0 1
    simp only [kCoeff_one,one_mul,zero_add] at hno
    have hne : ¬(η.val (u (g n))=color ∧ η.val (v (g n))=color) := by
      rintro ⟨hU,hV⟩; apply hno; intro i
      change η.val (f (g n) i) = η.val a
      rw [ha]; fin_cases i <;> first | exact ha | exact hb | exact hU | exact hV | exact hc
    change matchWeight color (binary (η.val (u (g n)))) + matchWeight color (binary (η.val (v (g n)))) ≤ 1
    cases color <;> cases eu : η.val (u (g n)) <;> cases ev : η.val (v (g n)) <;> simp_all [matchWeight,binary]
  · intro j; cases j
    · exact fun _ _ e => hg.injective (hu (congrArg Subtype.val e))
    · exact hvg

end
end C5.Model
end
