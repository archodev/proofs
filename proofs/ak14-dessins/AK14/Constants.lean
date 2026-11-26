import AK14.FractionDeriv
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Adjoin.Field

/-! Constant fields for algebraic functions of one variable in characteristic zero. -/
namespace AK14
open Polynomial

variable (K : Type*) [Field K] [CharZero K]

noncomputable section
local instance (priority := 2000) : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

noncomputable def ratDeriv : Derivation ℤ (RatFunc K) (RatFunc K) :=
  fractionDeriv (RatFunc K) ((Polynomial.derivative' : Derivation K K[X] K[X]).restrictScalars ℤ)

@[simp] theorem ratDeriv_polynomial (p : K[X]) :
    ratDeriv K (algebraMap K[X] (RatFunc K) p) = algebraMap _ _ p.derivative :=
  fractionDeriv_map _ _ _

theorem ratDeriv_constants (r : RatFunc K) :
    ratDeriv K r = 0 ↔ ∃ a : K, algebraMap K (RatFunc K) a = r := by
  letI : CharZero (RatFunc K) := charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  constructor
  · intro hr
    let P := r.num
    let Q := r.denom
    have nz : Q ≠ 0 := r.denom_ne_zero
    have mQ := RatFunc.algebraMap_ne_zero nz
    have prod : P.derivative*Q=P*Q.derivative := by
      have zero : ratDeriv K (algebraMap _ _ P/algebraMap _ _ Q)=0 := by
        change ratDeriv K (algebraMap _ _ r.num / algebraMap _ _ r.denom)=0
        rwa [RatFunc.num_div_denom]
      rw [quotient_deriv _ _ _ mQ,ratDeriv_polynomial,ratDeriv_polynomial] at zero
      have cross := (div_eq_zero_iff.mp zero).resolve_right (pow_ne_zero _ mQ)
      apply RatFunc.algebraMap_injective K
      simpa only [map_mul] using sub_eq_zero.mp cross
    have qdvd : Q ∣ Q.derivative :=
      (RatFunc.isCoprime_num_denom r).symm.dvd_of_dvd_mul_left (prod ▸ dvd_mul_left Q P.derivative)
    have dq : Q.derivative=0 := by
      by_cases hn : Q.derivative=0
      · exact hn
      · have pos : Q.natDegree ≠ 0 := fun h => hn (derivative_of_natDegree_zero h)
        exact ((Nat.not_lt_of_ge (natDegree_le_of_dvd qdvd hn)) (natDegree_derivative_lt pos)).elim
    have dp : P.derivative=0 := by
      rw [dq,mul_zero] at prod
      exact (mul_eq_zero.mp prod).resolve_right nz
    refine ⟨P.coeff 0/Q.coeff 0,?_⟩
    conv_rhs => rw [← RatFunc.num_div_denom r]
    change _ = algebraMap _ _ P/algebraMap _ _ Q
    rw [map_div₀,eq_C_of_derivative_eq_zero dp,eq_C_of_derivative_eq_zero dq]
    simp only [coeff_C_zero]
    rfl
  · rintro ⟨a,rfl⟩
    change ratDeriv K (algebraMap K[X] (RatFunc K) (C a))=0
    simp

/-- The constants of a finite algebraic function-field extension over algebraically
closed constants are the original constants. -/
theorem finite_extension_constants [IsAlgClosed K] {F L : Type*} [Field F] [Field L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    [Differential F] [Differential L] [DifferentialAlgebra F L]
    [FiniteDimensional F L]
    (base : ∀ x : F, Differential.deriv x = 0 → x ∈ (algebraMap K F).range)
    (x : L) (dx : Differential.deriv x = 0) : x ∈ (algebraMap K L).range := by
  classical
  let p := minpoly F x
  have integral : IsIntegral F x := Algebra.IsIntegral.isIntegral _
  have mon : p.Monic := minpoly.monic integral
  have ev : aeval x p=0 := minpoly.aeval F x
  have dev : aeval x (Differential.mapCoeffs p)=0 := by
    have e := Differential.deriv_aeval_eq x p
    simpa only [ev,map_zero,dx,mul_zero,add_zero] using e.symm
  have vanish : Differential.mapCoeffs p=0 := by
    by_contra hn
    have div : p ∣ Differential.mapCoeffs p := minpoly.dvd F x dev
    have smaller : (Differential.mapCoeffs p).degree < p.natDegree := by
      apply ((Differential.mapCoeffs p).degree_lt_iff_coeff_zero _).mpr
      intro j hj
      rcases eq_or_lt_of_le hj with rfl | hlt
      · rw [Differential.coeff_mapCoeffs,coeff_natDegree,mon.leadingCoeff,Differential.deriv.map_one_eq_zero]
      · rw [Differential.coeff_mapCoeffs,coeff_eq_zero_of_natDegree_lt hlt,map_zero]
    exact (Nat.not_lt_of_ge (natDegree_le_of_dvd div hn)) ((natDegree_lt_iff_degree_lt hn).mpr smaller)
  obtain ⟨q,hq⟩ := (Polynomial.mem_map_range (algebraMap K F) (p := p)).mpr (fun j => by
    apply base
    have e := congrArg (fun z : F[X] => z.coeff j) vanish
    simpa using e)
  change q.map (algebraMap K F) = p at hq
  have nq : q ≠ 0 := fun z => mon.ne_zero (by simpa [z] using hq.symm)
  have eq : aeval x q = 0 := by rwa [← hq,aeval_map_algebraMap] at ev
  have ik : IsIntegral K x := (show IsAlgebraic K x from ⟨q,nq,eq⟩).isIntegral
  exact ik.mem_range_algebraMap_of_minpoly_splits (K := K) (IsAlgClosed.splits_codomain _)

end
end AK14
