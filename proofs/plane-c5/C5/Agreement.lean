module
public import C5.Moments

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace C5.Model
noncomputable section
open MeasureTheory Filter Topology Set OAI OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
open OAI.EuclideanFiveColor.ContinuousVectors
open scoped InnerProductSpace
variable [Carrier] {R : Set (Fin 5 → E)} (ω : Space R)

def project := (space (A:=E) (representation R ω)).starProjection

theorem project_range (V : Hilbert R ω)
    (h : ∀ᵐ η ∂measure R ω, (V η).im=0 ∧ 0≤(V η).re ∧ (V η).re≤1) :
    ∀ᵐ η ∂measure R ω, ((project ω V) η).im=0 ∧ 0≤((project ω V) η).re ∧ ((project ω V) η).re≤1 :=
  projection_range _ (representation R ω) _ (trans_preserving R ω) (op_apply R ω) V h

/-- A positive projection preserving constants agrees with a binary vector on
the region where its projection is zero. -/
theorem agree_zero (V : Hilbert R ω)
    (hV : ∀ᵐ η ∂measure R ω, V η=0 ∨ V η=1) :
    ∀ᵐ η ∂measure R ω, project ω V η=0 → V η=0 := by
  classical
  let U := project ω V
  let g := fun η => if V η=1 ∧ U η=0 then (1:ℂ) else 0
  have hg : MemLp g 2 (measure R ω) := by
    refine MemLp.of_bound ?_ 1 (.of_forall fun η => ?_)
    · let S := {η : Space R | V η=1 ∧ U η=0}
      have hS : MeasurableSet S := (measurableSet_eq_fun (Lp.stronglyMeasurable V).measurable
        (measurable_const (a:=(1:ℂ)))).inter (measurableSet_eq_fun (Lp.stronglyMeasurable U).measurable
        (measurable_const (a:=(0:ℂ))))
      change AEStronglyMeasurable (fun η => if η ∈ S then (1:ℂ) else 0) _
      exact (Measurable.ite hS measurable_const measurable_const).aestronglyMeasurable
    · dsimp [g]; split <;> simp
  let Z := hg.toLp g
  have Zae : Z =ᵐ[measure R ω] g := hg.coeFn_toLp
  have hZ := project_range ω Z (Zae.mono fun η eq => by rw [eq]; unfold g; split <;> simp)
  have hDiff := project_range ω (V-Z) (by
    filter_upwards [Lp.coeFn_sub V Z,hV,Zae] with η hd hV hZ
    simp only [hd,Pi.sub_apply,hZ,g]
    rcases hV with e|e <;> simp [e] <;> split <;> simp)
  let Q := project ω Z
  have hprod : ⟪Z,U⟫_ℂ=0 := by
    rw [L2.inner_def]
    have eq : (fun η => ⟪Z η,U η⟫_ℂ) =ᵐ[measure R ω] 0 := by
      filter_upwards [Zae] with η h
      rw [h]; dsimp [g]; split <;> simp_all
    rw [integral_congr_ae eq]; simp
  have orth (Y W : Hilbert R ω) (hm : W ∈ space (A:=E) (representation R ω)) : ⟪Y-project ω Y,W⟫_ℂ=0 :=
    (Submodule.mem_orthogonal' _ _).mp ((space _).sub_starProjection_mem_orthogonal Y) W hm
  have hp := orth Z U ((space _).starProjection_apply_mem _)
  change ⟪Z-Q,U⟫_ℂ=0 at hp
  rw [inner_sub_left,hprod,zero_sub,neg_eq_zero] at hp
  have hpos : 0 ≤ (⟪Q,U-Q⟫_ℂ).re := by
    change 0 ≤ RCLike.re ⟪Q,U-Q⟫_ℂ
    rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜:=ℂ) Q (U-Q))]
    apply integral_nonneg_of_ae
    have ef : project ω (V-Z) = U-Q := map_sub _ _ _
    rw [ef] at hDiff
    filter_upwards [hZ,hDiff] with η ⟨hi,hq,hqU⟩ ⟨hdI,hd,hdU⟩
    change (project ω Z η).im=0 at hi
    change 0≤(⟪project ω Z η,(U-Q) η⟫_ℂ).re
    change 0 ≤ (((U-Q) η) * (starRingEnd ℂ) (Q η)).re
    rw [Complex.mul_re,Complex.conj_re,Complex.conj_im, show (Q η).im=0 from hi,neg_zero,mul_zero,sub_zero]
    exact mul_nonneg hd hq
  have hzero : Q=0 := by
    rw [inner_sub_right,hp,zero_sub,Complex.neg_re] at hpos
    apply norm_eq_zero.mp
    have heq : ‖Q‖^2 = (⟪Q,Q⟫_ℂ).re := norm_sq_eq_re_inner (𝕜:=ℂ) Q
    nlinarith [norm_nonneg Q]
  have h1 := orth Z (oneVector ω) (one_mem ω)
  change ⟪Z-Q,oneVector ω⟫_ℂ=0 at h1
  rw [hzero,sub_zero] at h1
  have zz : Z=0 := by
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    rw [←h1,L2.inner_def,L2.inner_def]; apply integral_congr_ae
    filter_upwards [Zae,one_ae ω] with η h he
    rw [h,he]; unfold g; split <;> simp
  rw [zz] at Zae
  filter_upwards [Zae,Lp.coeFn_zero (E:=ℂ) (p:=2) (μ:=measure R ω),hV] with η hz hz' hV hU
  rcases hV with h|h
  · exact h
  · change U η=0 at hU
    simp [g,h,hU,hz'] at hz

theorem pure_agreement (a : E) : ∀ᵐ η ∂measure R ω,
    (P ω a η=0 → η.val a=false) ∧ (P ω a η=1 → η.val a=true) := by
  let A := raw R ω
  have hA : ∀ᵐ η ∂measure R ω, A η=0 ∨ A η=1 := (raw_ae R ω).mono fun η h => by
    change raw R ω η=0 ∨ raw R ω η=1; rw [h]; cases e : η.val 0 <;> simp [rawValue,e]
  have hm0 := agree_zero ω A hA
  have hm1 := agree_zero ω (oneVector ω-A) (by
    filter_upwards [hA,one_ae ω,Lp.coeFn_sub (oneVector ω) A] with η h he hd
    rw [hd]; change oneVector ω η - A η=0 ∨ oneVector ω η - A η=1
    rcases h with h|h <;> simp [he,h])
  have ep : project ω (oneVector ω-A) = oneVector ω-proj R ω := by
    rw [map_sub]
    congr 1; exact (space _).starProjection_eq_self_iff.mpr (one_mem ω)
  rw [ep] at hm1
  have hx : ∀ᵐ η ∂measure R ω, (proj R ω η=0 → η.val 0=false) ∧ (proj R ω η=1 → η.val 0=true) := by
    filter_upwards [hm0,hm1,Lp.coeFn_sub (oneVector ω) A,Lp.coeFn_sub (oneVector ω) (proj R ω),
      one_ae ω,raw_ae R ω] with η h0 h1 hd hd' he hv
    constructor
    · intro h; have hh := h0 h
      cases e : η.val 0 <;> simp_all [A,rawValue]
    · intro h; have hh := h1 (by rw [hd']; change oneVector ω η-proj R ω η=0; rw [he,h,sub_self])
      cases e : η.val 0 <;> simp_all [A,rawValue]
  unfold P; rw [field_at,op_apply]
  filter_upwards [(trans_preserving R ω a).quasiMeasurePreserving.ae hx,
    Lp.coeFn_compMeasurePreserving (proj R ω) (trans_preserving R ω a)] with η h1 h2
  rw [h2]
  simpa only [Function.comp_apply,trans_apply,zero_add] using h1

end
end C5.Model
end
