module
public import C5.Purity

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace C5.Model
noncomputable section
open MeasureTheory Filter Topology Set OAI OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
open OAI.EuclideanFiveColor.ContinuousVectors
open scoped InnerProductSpace

variable [Carrier] {R : Set (Fin 5 → E)} (ω : Space R)
abbrev X (a : E) := op (representation R ω) a (raw R ω)
abbrev P (a : E) := field R ω (a:ℂ)

theorem P_range (a : E) : ∀ᵐ η ∂measure R ω, (P ω a η).im = 0 ∧ 0 ≤ (P ω a η).re ∧ (P ω a η).re ≤ 1 := by
  unfold P
  rw [field_at,op_apply]
  filter_upwards [Lp.coeFn_compMeasurePreserving (proj R ω) (trans_preserving R ω a),
    (trans_preserving R ω a).quasiMeasurePreserving.ae (projected_range R ω)] with η h1 h2
  simpa only [h1,Function.comp_apply] using h2

theorem cross_same {a b : E} (hne : a ≠ b) : ⟪P ω a,P ω b⟫_ℂ = ⟪X ω a,X ω b⟫_ℂ := by
  let U := representation R ω
  have moved (V : Hilbert R ω) : ⟪op U a V,op U b V⟫_ℂ = ⟪V,op U (b-a) V⟫_ℂ := by
    have h : b = a+(b-a) := by abel
    conv_lhs => rhs; rw [h,op_add (A:=E) U a (b-a) V]
    exact Unitary.inner_map_map _ _ _
  unfold P X
  rw [field_at,field_at,moved,moved]
  exact projection_coefficient _ _ _ (residual_correlation R ω (sub_ne_zero.mpr hne.symm))

theorem first_same (a : E) : ⟪oneVector ω,P ω a⟫_ℂ = ⟪oneVector ω,X ω a⟫_ℂ := by
  have hh := (Submodule.mem_orthogonal _ _).mp (op_orthogonal (representation R ω) a
    ((space _).sub_starProjection_mem_orthogonal (raw R ω))) _ (one_mem ω)
  change ⟪oneVector ω,op (representation R ω) a (raw R ω-proj R ω)⟫_ℂ = 0 at hh
  rw [map_sub,inner_sub_right,sub_eq_zero] at hh
  unfold P; rw [field_at]; exact hh.symm

def poly (a b c : ℝ) := 1-a-b-c+a*b+a*c+b*c
theorem poly_eq (a b c : ℝ) : poly a b c = a*b*c+(1-a)*(1-b)*(1-c) := by unfold poly; ring

theorem integrate_poly (A B C : Hilbert R ω)
    (ha : ∀ᵐ η ∂measure R ω,(A η).im=0) (hb : ∀ᵐ η ∂measure R ω,(B η).im=0) :
    Integrable (fun η => poly (A η).re (B η).re (C η).re) (measure R ω) ∧
    ∫ η, poly (A η).re (B η).re (C η).re ∂measure R ω =
      1-(⟪oneVector ω,A⟫_ℂ).re-(⟪oneVector ω,B⟫_ℂ).re-(⟪oneVector ω,C⟫_ℂ).re+
      (⟪A,B⟫_ℂ).re+(⟪A,C⟫_ℂ).re+(⟪B,C⟫_ℂ).re := by
  let μ := measure R ω
  have pair (V W : Hilbert R ω) (hV : ∀ᵐ η ∂μ,(V η).im=0) :
      Integrable (fun η => (V η).re*(W η).re) μ ∧ ∫ η, (V η).re*(W η).re ∂μ = (⟪V,W⟫_ℂ).re := by
    have h : (fun η => RCLike.re (⟪V η,W η⟫_ℂ)) =ᵐ[μ] fun η => (V η).re*(W η).re :=
      hV.mono fun η he => by simp [RCLike.inner_apply,he,mul_comm]
    refine ⟨(L2.integrable_inner (𝕜:=ℂ) V W).re.congr h,?_⟩
    rw [←integral_congr_ae h,integral_re (L2.integrable_inner V W),←L2.inner_def]; rfl
  have first (V : Hilbert R ω) : Integrable (fun η => (V η).re) μ ∧
      ∫ η, (V η).re ∂μ = (⟪oneVector ω,V⟫_ℂ).re := by
    have h1 : ∀ᵐ η ∂μ,(oneVector ω η).im=0 := (one_ae ω).mono fun η h => by simp [h]
    obtain ⟨h,h'⟩ := pair _ V h1
    have e : (fun η => (oneVector ω η).re*(V η).re) =ᵐ[μ] fun η => (V η).re :=
      (one_ae ω).mono fun η h => by simp [h]
    exact ⟨h.congr e,(integral_congr_ae e).symm.trans h'⟩
  have fA := first A; have fB := first B; have fC := first C
  have ab := pair A B ha; have ac := pair A C ha; have bc := pair B C hb
  have i0 : Integrable (fun η => 1-(A η).re) μ := (integrable_const (μ:=μ) (1:ℝ)).sub fA.1
  have i1 : Integrable (fun η => 1-(A η).re-(B η).re) μ := i0.sub fB.1
  have i2 : Integrable (fun η => 1-(A η).re-(B η).re-(C η).re) μ := i1.sub fC.1
  have i3 : Integrable (fun η => 1-(A η).re-(B η).re-(C η).re+(A η).re*(B η).re) μ := i2.add ab.1
  have i4 : Integrable (fun η => 1-(A η).re-(B η).re-(C η).re+(A η).re*(B η).re+(A η).re*(C η).re) μ := i3.add ac.1
  refine ⟨i4.add bc.1,?_⟩
  unfold poly
  rw [integral_add i4 bc.1,integral_add i3 ac.1,integral_add i2 ab.1,integral_sub i1 fC.1,
    integral_sub i0 fB.1,integral_sub (integrable_const _) fA.1,fA.2,fB.2,fC.2,ab.2,ac.2,bc.2]
  simp

theorem saturated_of_mixed {a b c : E} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hm : ∀ᵐ η ∂measure R ω, ¬(η.val a=η.val b ∧ η.val a=η.val c)) :
    ∀ᵐ η ∂measure R ω, ((P ω a η)=0 ∨ (P ω b η)=0 ∨ (P ω c η)=0) ∧
      ((P ω a η)=1 ∨ (P ω b η)=1 ∨ (P ω c η)=1) := by
  have rawR (d : E) : ∀ᵐ η ∂measure R ω, (X ω d η).im=0 := by
    filter_upwards [raw_at R ω d] with η h; rw [h] <;> split <;> simp
  have zero : (fun η => poly (X ω a η).re (X ω b η).re (X ω c η).re) =ᵐ[measure R ω] 0 := by
    filter_upwards [hm,raw_at R ω a,raw_at R ω b,raw_at R ω c] with η hh h1 h2 h3
    change poly (X ω a η).re (X ω b η).re (X ω c η).re = 0
    rw [show X ω a η = _ from h1,show X ω b η = _ from h2,show X ω c η = _ from h3]
    cases hA : η.val a <;> cases hB : η.val b <;> cases hC : η.val c <;> simp_all [poly]
  have hX := (integrate_poly ω _ _ (X ω c) (rawR a) (rawR b)).2
  have hP := integrate_poly ω _ _ (P ω c) ((P_range ω a).mono fun _ h => h.1)
    ((P_range ω b).mono fun _ h => h.1)
  have eq := hP.2
  rw [first_same,first_same,first_same,cross_same ω hab,cross_same ω hac,cross_same ω hbc,
    ←hX,integral_congr_ae zero] at eq
  simp only [Pi.zero_apply,integral_zero] at eq
  have hpos : ∀ᵐ η ∂measure R ω, 0 ≤ poly (P ω a η).re (P ω b η).re (P ω c η).re := by
    filter_upwards [P_range ω a,P_range ω b,P_range ω c] with η ⟨_,h1,h2⟩ ⟨_,h3,h4⟩ ⟨_,h5,h6⟩
    rw [poly_eq]; exact add_nonneg (by positivity) (by apply mul_nonneg (mul_nonneg _ _) _ <;> linarith)
  have he := (integral_eq_zero_iff_of_nonneg_ae hpos hP.1).mp eq
  filter_upwards [he,P_range ω a,P_range ω b,P_range ω c] with η he ⟨ea,ha,ha'⟩ ⟨eb,hb,hb'⟩ ⟨ec,hc,hc'⟩
  change poly _ _ _ = 0 at he
  rw [poly_eq] at he
  have h1 := mul_nonneg (mul_nonneg ha hb) hc
  have h2 := mul_nonneg (mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hb')) (sub_nonneg.mpr hc')
  have e0 : (P ω a η).re*(P ω b η).re*(P ω c η).re=0 := by linarith
  have e1 : (1-(P ω a η).re)*(1-(P ω b η).re)*(1-(P ω c η).re)=0 := by linarith
  simp only [mul_eq_zero,sub_eq_zero] at e0 e1
  constructor
  · rcases e0 with (h|h)|h
    · exact Or.inl (Complex.ext h ea)
    · exact Or.inr (Or.inl (Complex.ext h eb))
    · exact Or.inr (Or.inr (Complex.ext h ec))
  · rcases e1 with (h|h)|h
    · exact Or.inl (Complex.ext h.symm ea)
    · exact Or.inr (Or.inl (Complex.ext h.symm eb))
    · exact Or.inr (Or.inr (Complex.ext h.symm ec))

theorem triangle_needed (ω : Space templates) :
    ∃ u : E, ‖(u:ℂ)‖=1 ∧
      (measure templates ω) {η | η.val 0=η.val u ∧ η.val 0=η.val (omegaE*u)} ≠ 0 := by
  by_contra! hn
  apply impossible_alternation ω
  have cond (u : E) : ∀ᵐ η ∂measure templates ω, MixedOrigin ω η → ‖(u:ℂ)‖=1 →
      ∃ b : Bool, P ω u η=binary b ∧ P ω (omegaE*u) η=binary (!b) := by
    by_cases h : ‖(u:ℂ)‖=1
    · have hu := unit_ne h
      have hw : omegaE ≠ 0 := unit_ne omega_unit
      have hw' : omegaE ≠ 1 := by intro e; have := congrArg (fun z : E => (z:ℂ).re) e; norm_num [omegaE,omega] at this
      have hne : u ≠ omegaE*u := by intro e; apply hw'; exact mul_right_cancel₀ hu (by simpa using e.symm)
      have mix := saturated_of_mixed ω (a:=0) (b:=u) (c:=omegaE*u) hu.symm
        (mul_ne_zero hw hu).symm hne (by simpa [ae_iff] using hn u h)
      filter_upwards [mix] with η ⟨z,o⟩ hm _
      have h0 := hm.1; have h1 := hm.2
      change P ω 0 η ≠ 0 at h0; change P ω 0 η ≠ 1 at h1
      rcases z.resolve_left h0 with zu|zv <;> rcases o.resolve_left h1 with ou|ov
      · simp_all
      · exact ⟨false,zu,ov⟩
      · exact ⟨true,ou,zv⟩
      · simp_all
    · exact .of_forall fun _ _ hu => (h hu).elim
  filter_upwards [ae_all_iff.mpr cond] with η hh hm u hu
  exact hh u hm hu

end
end C5.Model
end
