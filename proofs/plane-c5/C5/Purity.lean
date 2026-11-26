module
public import C5.AngularTransfer

@[expose] public section
namespace C5.Model
noncomputable section
open MeasureTheory Filter Topology Set OAI OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
open OAI.EuclideanFiveColor.ContinuousVectors
open scoped InnerProductSpace

theorem binary_inj : Function.Injective binary := by
  intro a b h; cases a <;> cases b <;> simp_all [binary]
theorem omega_unit : ‖omega‖=1 := by
  rw [Complex.norm_def,Real.sqrt_eq_one]
  simp [omega,Complex.normSq_apply]; ring_nf; norm_num

variable [Carrier]
def Alternates (f : E → ℂ) := ∀ u : E, ‖(u:ℂ)‖=1 →
  ∃ b : Bool, f u = binary b ∧ f (omegaE*u) = binary (!b)

theorem twice_same {f : E → ℂ} (alt : Alternates f) (u : E) (hu : ‖(u:ℂ)‖=1) :
    f (omegaE*(omegaE*u)) = f u := by
  obtain ⟨b,he,hb⟩ := alt u hu
  obtain ⟨d,hd,hd'⟩ := alt (omegaE*u) (by simpa [omegaE,norm_mul,omega_unit] using hu)
  have ed := binary_inj (hd.symm.trans hb)
  simpa [ed,he] using hd'

theorem rot_same {f : E → ℂ} (alt : Alternates f) (u : E) (hu : ‖(u:ℂ)‖=1) (i : Fin 3) :
    f (rotE i * u) = f u := by
  have e : rotE 1 = omegaE*omegaE := Subtype.ext (by simpa [pow_two,rotE,omegaE] using omega_sq.symm)
  have e' : rotE 2 = rotE 1*rotE 1 := Subtype.ext (by simpa [pow_two,rotE] using rot_sq.symm)
  have same (v : E) (hv : ‖(v:ℂ)‖=1) : f (rotE 1*v)=f v := by rw [e,mul_assoc,twice_same alt v hv]
  fin_cases i
  · change f (1*u) = f u; simp
  · exact same u hu
  · change f (rotE 2*u)=f u
    rw [e',mul_assoc,same _ (by simp [e,omegaE,norm_mul,omega_unit,hu]),same _ hu]

/-- The two halfspaces for the root colors have no common point on the face
where the two outer triples carry opposite pure colors. -/
theorem angular_period {f : E → ℂ} (alt : Alternates f) {u : E} (hu : ‖(u:ℂ)‖=1)
    (h : ∀ s b, (fun j => f (u*offsets s j)) ∈ angularSet b) :
    f (rhoE*u)=f u := by
  obtain ⟨a,ha,-⟩ := alt u hu
  have hv : ‖((rhoE*u:E):ℂ)‖=1 := by simp [rhoE,norm_mul,norm_rho,hu]
  obtain ⟨d,hd,-⟩ := alt _ hv
  by_contra ne
  have en : d = !a := by cases a <;> cases d <;> simp_all
  have ho (i) : f (u*outerE false i)=binary a := by
    convert (rot_same alt u hu i).trans ha using 2
    simp [outerE,mul_comm]
  have ho' (i) : f (u*outerE true i)=binary (!a) := by
    rw [←en]
    convert (rot_same alt _ hv i).trans hd using 2
    simp [outerE]; ring
  have hA := h false a
  have hB := h true (!a)
  cases a <;> simp [angularSet,offsets,Fin.sum_univ_three,ho,ho',matchWeight,binary] at hA hB <;> linarith

theorem powers_approach : ∃ n : ℕ → ℤ, Tendsto (fun k => rho ^ n k) atTop (𝓝 omega) := by
  obtain ⟨s,hs,ht⟩ := mem_closure_iff_seq_limit.mp (dense_gamma tau)
  choose n hn using hs
  refine ⟨n,?_⟩
  have e (k) : direction (s k) = rho ^ n k := by
    rw [←hn k]
    change (AddCircle.toCircle (n k • gamma) : ℂ) = _
    rw [AddCircle.toCircle_zsmul,Circle.coe_zpow]; exact congrArg (· ^ n k) dir_gamma
  simpa only [Function.comp_def,e,dir_tau] using direction_continuous.continuousAt.tendsto.comp ht

def MixedOrigin (ω : Space templates) (η : Space templates) :=
  field templates ω 0 η ≠ 0 ∧ field templates ω 0 η ≠ 1

theorem binary_origin_of_alternation (ω : Space templates)
    (alt : ∀ᵐ η ∂measure templates ω, MixedOrigin ω η →
      Alternates (fun z : E => field templates ω (z:ℂ) η)) :
    ∀ᵐ η ∂measure templates ω, field templates ω 0 η = 0 ∨ field templates ω 0 η = 1 := by
  have h (u : E) (s b : Bool) : ∀ᵐ η ∂measure templates ω, ‖(u:ℂ)‖=1 →
      MixedOrigin ω η → (fun j => field templates ω ((u*offsets s j:E):ℂ) η) ∈ angularSet b := by
    by_cases hu : ‖(u:ℂ)‖=1
    · filter_upwards [angular_projection ω 0 u hu s b] with η hη _ hm
      simpa using hη (by cases b <;> simp [binary,MixedOrigin] at hm ⊢ <;> tauto)
    · exact .of_forall fun _ h => (hu h).elim
  have each := ae_all_iff.mpr fun u => ae_all_iff.mpr fun s => ae_all_iff.mpr (h u s)
  obtain ⟨n,hn⟩ := powers_approach
  have hf := (field_continuous templates ω).continuousAt.tendsto.comp hn
  obtain ⟨φ,_,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  filter_upwards [alt,each,hlim] with η ha he hlim
  by_contra! hn'
  have hm : MixedOrigin ω η := hn'
  let f := fun z : E => field templates ω (z:ℂ) η
  have ha : Alternates f := ha hm
  have per (u : E) (hu : ‖(u:ℂ)‖=1) : f (rhoE*u)=f u :=
    angular_period ha hu (fun s b => he u s b hu hm)
  have eρ : rhoE ≠ 0 := unit_ne norm_rho
  have allPowers (k : ℤ) : f (rhoE^k) = f 1 := by
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one₀ eρ,mul_comm,per _ (by simp [rhoE,norm_zpow,norm_rho]),ih]
    | pred k ih =>
      let v : ℤ := -(k:ℤ)
      have h := per (rhoE^(v-1)) (by rw [show ((rhoE^(v-1):E):ℂ) = rho^(v-1) from map_zpow₀ E.subtype rhoE _,norm_zpow,norm_rho,one_zpow])
      have eq : rhoE*rhoE^(v-1) = rhoE^v := by
        calc _ = rhoE^(1:ℤ)*rhoE^(v-1) := by rw [zpow_one]
             _ = _ := by rw [←zpow_add₀ eρ]; congr 1; ring
      rw [eq] at h
      simpa [v] using h.symm.trans ih
  have e : f 1 = f omegaE := by
    apply tendsto_nhds_unique (l := atTop) (f := fun k : ℕ => f (rhoE ^ n (φ k)))
    · exact tendsto_const_nhds.congr' (.of_forall fun _ => (allPowers _).symm)
    · have co (k : ℤ) : ((rhoE^k : E):ℂ) = rho^k := map_zpow₀ E.subtype rhoE k
      simpa only [f,co,omegaE,Function.comp_def] using hlim
  obtain ⟨b,eb,eb'⟩ := ha 1 (by simp)
  simp only [mul_one] at eb'
  have bad := binary_inj (eb.symm.trans (e.trans eb'))
  cases b <;> contradiction

def oneVector {R : Set (Fin 5 → E)} (ω : Space R) : Hilbert R ω :=
  (memLp_const (1:ℂ)).toLp (fun _ : Space R => (1:ℂ))
theorem one_ae {R} (ω : Space R) : oneVector ω =ᵐ[measure R ω] (fun _ => (1:ℂ)) := MemLp.coeFn_toLp _
theorem one_mem {R} (ω : Space R) : oneVector ω ∈ space (A := E) (representation R ω) := by
  have fixed (a : E) : op (representation R ω) a (oneVector ω) = oneVector ω := by
    rw [op_apply]
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (oneVector ω) (trans_preserving R ω a),
      (trans_preserving R ω a).quasiMeasurePreserving.ae (one_ae ω),one_ae ω] with η h1 h2 h3
    exact h1.trans (h2.trans h3.symm)
  change Tendsto _ _ _
  simpa only [fixed] using (tendsto_const_nhds : Tendsto (fun _ : E => oneVector ω) (𝓝 0) (𝓝 (oneVector ω)))

theorem residual_zero_of_binary {R} (ω : Space R)
    (h : ∀ᵐ η ∂measure R ω, proj R ω η = 0 ∨ proj R ω η = 1) : residual R ω = 0 := by
  let X := raw R ω
  let P := proj R ω
  let B := residual R ω
  have ort (V : Hilbert R ω) (hv : V ∈ space (A:=E) (representation R ω)) : ⟪V,B⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp ((space (representation R ω)).sub_starProjection_mem_orthogonal X) V hv
  have h1 := ort _ (one_mem ω)
  have hP := ort P ((space _).starProjection_apply_mem X)
  have hP' := inner_eq_zero_symm.mp hP
  have normfun (V : Hilbert R ω) (hv : ∀ᵐ η ∂measure R ω,V η = 0 ∨ V η = 1) :
      ⟪V,V⟫_ℂ = ⟪oneVector ω,V⟫_ℂ := by
    rw [L2.inner_def,L2.inner_def]; apply integral_congr_ae
    filter_upwards [hv,one_ae ω] with η hη he
    rcases hη with hη|hη <;> simp [hη,he]
  have hX := normfun X ((raw_ae R ω).mono fun η he => by rw [show X η = rawValue R η from he]; cases e : η.val 0 <;> simp [rawValue,e])
  have hPP := normfun P h
  change ⟪oneVector ω,X-P⟫_ℂ = 0 at h1
  change ⟪P,X-P⟫_ℂ=0 at hP
  change ⟪X-P,P⟫_ℂ=0 at hP'
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  change ⟪X-P,X-P⟫_ℂ=0
  rw [inner_sub_left,inner_sub_right,hP,sub_zero,hX]
  rw [inner_sub_right] at h1 hP
  rw [inner_sub_left] at hP'
  linear_combination h1 - hP' - hPP

theorem impossible_alternation (ω : Space templates)
    (h : ∀ᵐ η ∂measure templates ω, MixedOrigin ω η →
      Alternates (fun z : E => field templates ω (z:ℂ) η)) : False := by
  have hb := binary_origin_of_alternation ω h
  have e := field_at templates ω 0
  rw [op_zero (A:=E) (representation templates ω)] at e
  change field templates ω 0 = proj templates ω at e
  rw [e] at hb
  exact residual_nonzero ω (residual_zero_of_binary ω hb)

end
end C5.Model
end
