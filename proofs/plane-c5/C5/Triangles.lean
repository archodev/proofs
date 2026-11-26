module
public import C5.MovingFold
public import C5.Moments

@[expose] public section
namespace C5.Model
noncomputable section
open MeasureTheory Filter Topology Set OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
variable [Carrier]

def edgeTuple (x u : E) (i : Bool) := if i then x+u*omegaE else x+u
def exempt (c : Bool) (i : Bool) : Set (Bool→ℂ) := {y | y i=binary (!c)}
private theorem closed_exempt (c i) : IsClosed (exempt c i) := isClosed_eq (continuous_apply i) continuous_const

theorem folded_one_fixed (ω : Space templates) (x u : E) (hu : ‖(u:ℂ)‖=1) (c : Bool) :
    ∀ᵐ η ∂measure templates ω, η.val x=c → P ω (x+u) η ≠ binary (!c) →
    (fun i => P ω (edgeTuple x u i) η) ∈ exempt c true ∪ matchPair c := by
  let v := fun n => u*kArc n
  have hv (n) : ‖(v n:ℂ)‖=1 := by simp [v,norm_mul,hu,kArc_unit]
  have hl : Tendsto (fun n => (v n:ℂ)) atTop (𝓝 (u:ℂ)) := by simpa [v,kArc] using (tendsto_const_nhds (x:=(u:ℂ))).mul arc_lim
  have hb : Tendsto (fun n => ((x+v n:E):ℂ)) atTop (𝓝 ((x+u:E):ℂ)) := tendsto_const_nhds.add hl
  have hi : Function.Injective (fun n => x+v n) := fun _ _ he => kArc_inj (mul_left_cancel₀ (unit_ne hu) (add_left_cancel he))
  apply relax_gate ω hi hb c (Y:=fun n i => P ω (edgeTuple x (v n) i))
    (L:=fun i => P ω (edgeTuple x u i)) _ ((closed_exempt c true).union (closed_matchPair c))
  · apply Eventually.of_forall; intro n
    filter_upwards [folded_two_fixed ω x (v n) (hv n) c] with η h hx hb'
    by_cases hc : P ω (x+v n*omegaE) η = binary (!c)
    · exact Or.inl hc
    · exact Or.inr (h ⟨hx,hb'⟩ hc)
  · intro i
    apply (field_continuous _ _).continuousAt.tendsto.comp
    cases i
    · exact hb
    · exact tendsto_const_nhds.add (hl.mul_const _)

theorem folded_projected (ω : Space templates) (x u : E) (hu : ‖(u:ℂ)‖=1) (c : Bool) :
    ∀ᵐ η ∂measure templates ω,
      P ω x η ≠ binary (!c) → P ω (x+u) η ≠ binary (!c) → P ω (x+u*omegaE) η ≠ binary (!c) →
      matchWeight c (P ω (x+u) η)+matchWeight c (P ω (x+u*omegaE) η) ≤ 1 := by
  let y := fun n => x+(kArc n-1)
  have hy : Tendsto (fun n => (y n:ℂ)) atTop (𝓝 (x:ℂ)) := by
    simpa [y,kArc] using (tendsto_const_nhds (x:=(x:ℂ))).add (arc_lim.sub_const 1)
  have hi : Function.Injective y := fun _ _ e => kArc_inj (sub_left_inj.mp (add_left_cancel e))
  let S := exempt c false ∪ (exempt c true ∪ matchPair c)
  have rules (n) : ∀ᵐ η ∂measure templates ω, η.val (y n)=c → (fun i => P ω (edgeTuple (y n) u i) η) ∈ S := by
    filter_upwards [folded_one_fixed ω (y n) u hu c] with η h hc
    by_cases he : P ω (y n+u) η = binary (!c)
    · exact Or.inl he
    · exact Or.inr (h hc he)
  have lim (i) : Tendsto (fun n => P ω (edgeTuple (y n) u i)) atTop (𝓝 (P ω (edgeTuple x u i))) := by
    apply (field_continuous _ _).continuousAt.tendsto.comp
    cases i <;> exact hy.add_const _
  have h := relax_label ω hi hy c lim ((closed_exempt c false).union ((closed_exempt c true).union (closed_matchPair c))) rules
  filter_upwards [h] with η hh ha hb hc
  exact ((hh ha).resolve_left hb).resolve_left hc

/-- The two possible outcomes of the folded inequalities. -/
def classification (a b c : ℂ) : Prop :=
  ((a=0 ∨ b=0 ∨ c=0) ∧ (a=1 ∨ b=1 ∨ c=1)) ∨ (a=1/2 ∧ b=1/2 ∧ c=1/2)

theorem classify_scalar (a b c : ℂ) (ha : a.im=0 ∧ 0≤a.re ∧ a.re≤1)
    (hb : b.im=0 ∧ 0≤b.re ∧ b.re≤1) (hc : c.im=0 ∧ 0≤c.re ∧ c.re≤1)
    (h : ∀ d : Bool, a ≠ binary (!d) → b ≠ binary (!d) → c ≠ binary (!d) →
      matchWeight d a + matchWeight d b ≤ 1 ∧ matchWeight d b + matchWeight d c ≤ 1 ∧
      matchWeight d c + matchWeight d a ≤ 1) : classification a b c := by
  by_cases h₀ : a=0 ∨ b=0 ∨ c=0 <;> by_cases h₁ : a=1 ∨ b=1 ∨ c=1
  · exact Or.inl ⟨h₀,h₁⟩
  · push Not at h₁
    have hB := h false h₁.1 h₁.2.1 h₁.2.2
    simp [matchWeight] at hB
    obtain ⟨ai,al,ah⟩ := ha; obtain ⟨bi,bl,bh⟩ := hb; obtain ⟨ci,cl,ch⟩ := hc
    rcases h₀ with rfl|rfl|rfl
    · exfalso; apply h₁.2.1; apply Complex.ext _ bi; simp at hB; change b.re=1; linarith
    · exfalso; apply h₁.1; apply Complex.ext _ ai; simp at hB; change a.re=1; linarith
    · exfalso; apply h₁.1; apply Complex.ext _ ai; simp at hB; change a.re=1; linarith
  · push Not at h₀
    have hR := h true h₀.1 h₀.2.1 h₀.2.2
    simp [matchWeight] at hR
    rcases h₁ with rfl|rfl|rfl <;> simp at hR <;> exfalso
    all_goals first | (apply h₀.1; apply Complex.ext <;> simp_all <;> linarith) |
      (apply h₀.2.1; apply Complex.ext <;> simp_all <;> linarith)
  · push Not at h₀ h₁
    have hR := h true h₀.1 h₀.2.1 h₀.2.2; have hB := h false h₁.1 h₁.2.1 h₁.2.2
    simp [matchWeight] at hR hB
    right; obtain ⟨aI,aL,aH⟩ := ha; obtain ⟨bI,bL,bH⟩ := hb; obtain ⟨cI,cL,cH⟩ := hc
    constructor
    · apply Complex.ext <;> norm_num <;> linarith
    constructor <;> apply Complex.ext <;> norm_num <;> linarith

theorem omega_equation : omegaE*(omegaE-1) = -1 := by
  apply Subtype.ext
  apply Complex.ext <;> simp [omegaE,omega,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im] <;> ring_nf <;> norm_num

theorem triangle_classification (ω : Space templates) (x u : E) (hu : ‖(u:ℂ)‖=1) :
    ∀ᵐ η ∂measure templates ω, classification (P ω x η) (P ω (x+u) η) (P ω (x+u*omegaE) η) := by
  let d := u*(omegaE-1)
  let e := -(u*omegaE)
  have hd : ‖(d:ℂ)‖=1 := by simpa [d,norm_mul,hu,omegaE,omega,Erdos173.ζ] using Erdos173.norm_ζ_sub_one
  have he : ‖(e:ℂ)‖=1 := by simp [e,norm_mul,hu,omegaE,omega_unit]
  have eqs : x+u+d = x+u*omegaE := by dsimp [d]; ring
  have eqt : x+u+d*omegaE = x := by unfold d; rw [mul_assoc,mul_comm (omegaE-1),omega_equation]; ring
  have eqs' : x+u*omegaE+e=x := by dsimp [e]; ring
  have eqt' : x+u*omegaE+e*omegaE=x+u := by
    have h := omega_equation
    dsimp [e]; linear_combination -u*h
  have h (b) := folded_projected ω x u hu b
  have h' (b) := folded_projected ω (x+u) d hd b
  have h'' (b) := folded_projected ω (x+u*omegaE) e he b
  simp only [eqs,eqt] at h'
  simp only [eqs',eqt'] at h''
  filter_upwards [P_range ω x,P_range ω (x+u),P_range ω (x+u*omegaE),ae_all_iff.mpr h,ae_all_iff.mpr h',ae_all_iff.mpr h''] with η ha hb hc hh hh' hh''
  exact classify_scalar _ _ _ ha hb hc (fun b ea eb ec => ⟨hh'' b ec ea eb,hh b ea eb ec,hh' b eb ec ea⟩)

end
end C5.Model
end
