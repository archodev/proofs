import AK14.DifferentialGerms
import AK14.Parameter
import AK14.Descent

/-! Local branching is specified by an actual nonzero Taylor series of exact
order e in the indicated target chart. -/
namespace AK14.SeriesAt
open PowerSeries
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

local instance (priority := 2000) : Algebra ℤ (GermField K) := Ring.toIntAlgebra _

def targetChart (j : Fin 3) (y : GermField K) : GermField K := ![y,1-y,y⁻¹] j

def BranchGerm (f : GermField K) (j : Fin 3) (e : ℕ) : Prop :=
  ∃ P : K⟦X⟧, P ≠ 0 ∧ constantCoeff (R := K) P=0 ∧ P.order.toNat=e ∧
    f=targetChart j (embed K P)

def OrdinaryGerm (f : GermField K) : Prop :=
  ∃ P : K⟦X⟧, f=embed K P ∧ constantCoeff (R := K) P ≠ 0 ∧ constantCoeff (R := K) P ≠ 1 ∧
    constantCoeff (R := K) (derivative K P) ≠ 0

theorem embed_unit_inv {P : K⟦X⟧} (h : constantCoeff (R := K) P ≠ 0) :
    embed K P⁻¹=(embed K P)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul,PowerSeries.mul_inv_cancel _ h,map_one]

private theorem remainder_regular (j : Fin 3) (P : K⟦X⟧) (hp : constantCoeff (R := K) P=0) :
    ∃ W : K⟦X⟧, chartRemainder j (embed K P)=embed K W := by
  let v := 1-P
  have nv : constantCoeff (R := K) v ≠ 0 := by simp [v,hp]
  have iv := embed_unit_inv nv
  let den := v⁻¹^2
  have den_eq : embed K den=((1-embed K P)⁻¹)^2 := by
    rw [show den=v⁻¹^2 from rfl,map_pow,iv,show v=1-P from rfl,map_sub,map_one]
  have c (n : ℕ) : embed K (C (R := K) (1/(n:K))) = (1/(n:GermField K)) :=
    show constMap K (1/(n:K))=_ by rw [map_div₀,map_one,map_natCast]
  have c72 : embed K (C (R := K) (1/72))=(1/72:GermField K) := by simpa only [Nat.cast_ofNat] using c 72
  have c8 : embed K (C (R := K) (1/8))=(1/8:GermField K) := by simpa only [Nat.cast_ofNat] using c 8
  fin_cases j
  · refine ⟨C (R := K) (1/72)*(5*P+27)*den,?_⟩
    change (5*embed K P+27)/(72*(1-embed K P)^2)=_
    simp only [map_mul (embed K),map_add (embed K),map_ofNat (embed K),den_eq,c72]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]; ring
  · refine ⟨C (R := K) (1/8)*3*den,?_⟩
    change 3/(8*(1-embed K P)^2)=_
    simp only [map_mul (embed K),map_ofNat (embed K),den_eq,c8]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]; ring
  · refine ⟨C (R := K) (1/72)*(37-5*P)*den,?_⟩
    change (37-5*embed K P)/(72*(1-embed K P)^2)=_
    simp only [map_mul (embed K),map_sub (embed K),map_ofNat (embed K),den_eq,c72]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]; ring

private theorem connection_at_branch [IsAlgClosed K] {f : GermField K} {j : Fin 3} {e : ℕ}
    (he : 0<e) (h : BranchGerm f j e) :
    ∃ v W : K⟦X⟧, constantCoeff (R := K) v ≠ 0 ∧
      pullConnection (germDeriv K) f =
        connection (germDeriv K) (branchOrder j) (embed K W) ((embed K (X*v))^e) := by
  obtain ⟨P,hP,h0,ord,rfl⟩ := h
  obtain ⟨v,hv,ev⟩ := LocalChart.local_power_parameter P hP he ord
  obtain ⟨W,hW⟩ := remainder_regular j P h0
  have ny : embed K P ≠ 0 := (map_ne_zero_iff (embed K) (IsFractionRing.injective (PowerSeries K) (GermField K))).mpr hP
  have one : 1-embed K P ≠ 0 := by
    rw [← map_one (embed K),← map_sub]
    apply (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)).mpr
    intro z
    have hz := congrArg (constantCoeff (R := K)) z
    simp [h0] at hz
  have pe : embed K P=(embed K (X*v))^e := by rw [← map_pow,ev]
  obtain ⟨du,nu,_,_,_,_,_⟩ := LocalChart.parameter_expansions (germDeriv K) (embed K)
    (IsFractionRing.injective (PowerSeries K) _) germDeriv_embed v hv
  have dy : germDeriv K (embed K P) ≠ 0 := by
    rw [pe,(germDeriv K).leibniz_pow]
    simp only [smul_eq_mul,nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr he.ne') (mul_ne_zero (pow_ne_zero _ nu) du)
  refine ⟨v,W,hv,?_⟩
  rw [← pe,← hW]
  fin_cases j
  · exact chart_zero _ ny one
  · exact chart_one _ ny one dy
  · exact chart_infty _ ny one dy

theorem branch_coefficient [IsAlgClosed K] {f : GermField K} {j : Fin 3} {e : ℕ}
    (he : 0<e) (h : BranchGerm f j e) :
    ∃ P : K⟦X⟧, (t K)^2*pullConnection (germDeriv K) f=embed K P ∧
      constantCoeff (R := K) P=LocalChart.powerCoeff K e (branchOrder j) := by
  obtain ⟨v,W,hv,eq⟩ := connection_at_branch he h
  rw [eq]
  exact LocalChart.connection_double_coefficient _ _ (IsFractionRing.injective _ _)
    germDeriv_embed v W hv he (by fin_cases j <;> decide)

theorem branch_regular [IsAlgClosed K] {f : GermField K} {j : Fin 3}
    (h : BranchGerm f j (branchOrder j)) :
    ∃ P : K⟦X⟧, pullConnection (germDeriv K) f=embed K P := by
  have k : 2 ≤ branchOrder j := by fin_cases j <;> decide
  obtain ⟨v,W,hv,eq⟩ := connection_at_branch (by omega) h
  rw [eq]
  exact LocalChart.connection_ordinary _ _ (IsFractionRing.injective _ _) germDeriv_embed v W hv k

theorem unbranched_regular {f : GermField K} (h : OrdinaryGerm f) :
    ∃ P : K⟦X⟧, pullConnection (germDeriv K) f=embed K P := by
  obtain ⟨P,rfl,h0,h1,hd⟩ := h
  let d := derivative K
  let H := d (d P)*(d P)⁻¹
  let u := 1-P
  have cu : constantCoeff (R := K) u ≠ 0 := by
    dsimp only [u]; rw [map_sub,map_one]; exact sub_ne_zero.mpr h1.symm
  have pre : preSch (germDeriv K) (embed K P)=embed K H := by
    rw [preSch,germDeriv_embed,germDeriv_embed]
    dsimp only [H]; rw [map_mul,embed_unit_inv hd,div_eq_mul_inv]
  have c (m n : ℕ) : embed K (C (R := K) ((m:K)/n))=(m/n:GermField K) := by
    change constMap K ((m:K)/n)=_; rw [map_div₀,map_natCast,map_natCast]
  have c12 : embed K (C (R := K) (1/2))=(1/2:GermField K) := by simpa only [Nat.cast_one,Nat.cast_ofNat] using c 1 2
  have c49 : embed K (C (R := K) (4/9))=(4/9:GermField K) := by simpa only [Nat.cast_ofNat] using c 4 9
  have c38 : embed K (C (R := K) (3/8))=(3/8:GermField K) := by simpa only [Nat.cast_ofNat] using c 3 8
  let V := C (R := K) (4/9)*u⁻¹^2+C (R := K) (3/8)*P⁻¹^2*u⁻¹
  refine ⟨d H-C (R := K) (1/2)*H^2+V*(d P)^2,?_⟩
  unfold pullConnection schwarzian tetraPotential
  rw [pre,germDeriv_embed,germDeriv_embed]
  dsimp only [V]
  conv_rhs => simp only [map_add (embed K),map_sub (embed K),map_mul (embed K),map_pow (embed K),
    embed_unit_inv cu,embed_unit_inv h0,c12,c49,c38]
  simp only [d,u,map_sub (embed K),map_one (embed K),div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

end
end AK14.SeriesAt
