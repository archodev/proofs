import AK14.SeriesAt
import Mathlib.Algebra.Polynomial.Reverse

/-! Laurent expansion at infinity by x ↦ 1/t, and its connection to the degree
of an actual rational function. -/
namespace AK14.SeriesAt
open Polynomial
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

abbrev t (K : Type*) [Field K] : GermField K := embed K PowerSeries.X
abbrev constMap (K : Type*) [Field K] := (embed K).comp (PowerSeries.C (R := K))

theorem t_ne : t K ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)).mpr
  PowerSeries.X_ne_zero

theorem polynomial_at_t (p : K[X]) :
    p.eval₂ (constMap K) (t K)=embed K (p : PowerSeries K) := by
  have e : eval₂RingHom (constMap K) (t K) =
      (embed K).comp (Polynomial.coeToPowerSeries.ringHom : K[X] →+* PowerSeries K) := by
    apply Polynomial.ringHom_ext
    · intro z; simp [constMap]
    · simp [t]
  exact RingHom.congr_fun e p

def reciprocalPoly (K : Type*) [Field K] : K[X] →+* GermField K :=
  eval₂RingHom (constMap K) (t K)⁻¹

theorem reciprocalPoly_formula (p : K[X]) :
    reciprocalPoly K p=embed K (p.reverse : PowerSeries K)/(t K)^p.natDegree := by
  letI : Invertible ((t K)⁻¹) := invertibleOfNonzero (inv_ne_zero t_ne)
  have e := Polynomial.eval₂_reverse_mul_pow (constMap K) ((t K)⁻¹) p
  rw [invOf_eq_inv,inv_inv,polynomial_at_t,inv_pow] at e
  exact e.symm

theorem reciprocalPoly_injective : Function.Injective (reciprocalPoly K) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p e
  rw [reciprocalPoly_formula,_root_.div_eq_zero_iff] at e
  have h := e.resolve_right (pow_ne_zero _ t_ne)
  have hz := (map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) (GermField K))).mp h
  exact Polynomial.reverse_eq_zero.mp (Polynomial.coe_eq_zero_iff.mp hz)

def expandInf (K : Type*) [Field K] [CharZero K] : RatFunc K →+* GermField K :=
  IsFractionRing.lift (reciprocalPoly_injective (K := K))

@[simp] theorem expandInf_poly (p : K[X]) :
    expandInf K (algebraMap K[X] (RatFunc K) p)=reciprocalPoly K p :=
  IsFractionRing.lift_algebraMap _ _

/-- A double zero of the Laurent expansion at infinity is the actual growth
condition used to bound the degree of the normalized numerator. -/
theorem intDegree_of_infty_regular (r : RatFunc K)
    (reg : ∃ H : PowerSeries K, expandInf K r / (t K)^2 = embed K H) :
    r=0 ∨ r.intDegree ≤ -2 := by
  classical
  by_cases hz : r=0
  · exact Or.inl hz
  right
  obtain ⟨H,hH⟩ := reg
  let P := r.num
  let Q := r.denom
  have np := RatFunc.num_ne_zero hz
  have nq := r.denom_ne_zero
  have cq : PowerSeries.constantCoeff (R := K) (Q.reverse : PowerSeries K) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe,Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr nq
  have cp : PowerSeries.constantCoeff (R := K) (P.reverse : PowerSeries K) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe,Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr np
  have vq : embed K (Q.reverse : PowerSeries K) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)).mpr
      (fun e => cq (by simp [e]))
  have rep : expandInf K r = (embed K (P.reverse : PowerSeries K)/(t K)^P.natDegree) /
      (embed K (Q.reverse : PowerSeries K)/(t K)^Q.natDegree) := by
    conv_lhs => rw [← RatFunc.num_div_denom r]
    rw [map_div₀,expandInf_poly,expandInf_poly,reciprocalPoly_formula,reciprocalPoly_formula]
  rw [rep] at hH
  have e : embed K (P.reverse : PowerSeries K)*(t K)^Q.natDegree =
      embed K H * embed K (Q.reverse : PowerSeries K)*(t K)^(P.natDegree+2) := by
    rw [mul_assoc]
    apply (div_eq_iff (mul_ne_zero vq (pow_ne_zero _ t_ne))).mp
    rw [← hH]
    rw [pow_add]
    field_simp [vq,t_ne] <;> ring_nf <;> simp
  change (P.natDegree:ℤ)-Q.natDegree ≤ -2
  apply Classical.byContradiction
  intro high
  have lt : Q.natDegree < P.natDegree+2 := by omega
  let m := P.natDegree+2-Q.natDegree
  have hm : 0<m := by dsimp [m]; omega
  have split : P.natDegree+2=m+Q.natDegree := by dsimp [m]; omega
  rw [split,pow_add,← mul_assoc] at e
  have cancel := mul_right_cancel₀ (pow_ne_zero _ t_ne) e
  have eq : (P.reverse : PowerSeries K) = H*(Q.reverse : PowerSeries K)*PowerSeries.X^m :=
    (IsFractionRing.injective (PowerSeries K) (GermField K)) (by
      rw [map_mul,map_mul,map_pow]; exact cancel)
  apply cp
  rw [eq,map_mul (PowerSeries.constantCoeff (R := K)),map_pow (PowerSeries.constantCoeff (R := K)),
    PowerSeries.constantCoeff_X,zero_pow hm.ne',mul_zero]

/-- The quadratic coefficient is the constant term of r(1/t)/t². -/
theorem poleFraction_at_infty (P : K[X]) (hd : P.natDegree ≤ 2) :
    ∃ H : PowerSeries K, expandInf K (poleFraction P)/(t K)^2=embed K H ∧
      PowerSeries.constantCoeff (R := K) H=P.coeff 2 := by
  let V : PowerSeries K := (1-PowerSeries.X)^2
  have cv : PowerSeries.constantCoeff (R := K) V=1 := by simp [V]
  let U : PowerSeries K := PowerSeries.C (R := K) (P.coeff 0)*PowerSeries.X^2+
    PowerSeries.C (R := K) (P.coeff 1)*PowerSeries.X+PowerSeries.C (R := K) (P.coeff 2)
  refine ⟨U*V⁻¹,?_,?_⟩
  · have vi := congrArg (embed K) (PowerSeries.mul_inv_cancel V (cv ▸ one_ne_zero))
    rw [map_mul,map_one] at vi
    have vn : (1-t K)^2 ≠ 0 := by
      have vne : embed K V ≠ 0 := left_ne_zero_of_mul_eq_one vi
      simpa only [V,map_pow,map_sub,map_one,t] using vne
    have hp := P.as_sum_range' 3 (by omega)
    have exp : P = C (P.coeff 0)+C (P.coeff 1)*X+C (P.coeff 2)*X^2 := by
      simpa [Finset.sum_range_succ,← C_mul_X_pow_eq_monomial] using hp
    rw [poleFraction,map_div₀,expandInf_poly,expandInf_poly,map_mul,eq_inv_of_mul_eq_one_right vi]
    change (P.eval₂ (constMap K) (t K)⁻¹ /
      (poleDenom K).eval₂ (constMap K) (t K)⁻¹)/(t K)^2=_
    conv_lhs => rw [exp]
    simp only [poleDenom,eval₂_add,eval₂_mul,eval₂_C,eval₂_X,eval₂_pow,eval₂_sub,map_one]
    simp only [U,V,map_add,map_mul,map_pow,map_sub,map_one,RingHom.comp_apply,constMap]
    change _ = ((constMap K) (P.coeff 0)*(t K)^2+(constMap K) (P.coeff 1)*(t K)+
      (constMap K) (P.coeff 2))*((1-t K)^2)⁻¹
    have tt : (t K)⁻¹-1=(1-t K)/t K := by field_simp [t_ne]
    rw [eval₂_one,tt]
    have d : 1-t K ≠ 0 := fun z => vn (by rw [z]; norm_num)
    dsimp only [constMap,RingHom.comp_apply]
    field_simp [t_ne,d] <;> ring
  · simp [U,V,PowerSeries.constantCoeff_inv,cv]

end
end AK14.SeriesAt
