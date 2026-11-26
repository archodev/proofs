import AK14.ThreePoles
import Mathlib.FieldTheory.RatFunc.Degree

/-! Rational three-pole uniqueness on the normalized sphere, including behavior at infinity. -/
namespace AK14
open Polynomial

variable {K : Type*} [Field K]

noncomputable def poleDenom (K : Type*) [Field K] : K[X] := X^2 * (X-C 1)^2

theorem poleDenom_degree : (poleDenom K).natDegree = 4 := by
  have h : (X - C (1 : K)) ≠ 0 := (monic_X_sub_C _).ne_zero
  rw [poleDenom, natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ h), natDegree_pow,
    natDegree_pow, natDegree_X, natDegree_X_sub_C]

theorem poleDenom_ne_zero : poleDenom K ≠ 0 :=
  fun h => by have d := poleDenom_degree (K := K); rw [h,natDegree_zero] at d; contradiction

noncomputable def poleFraction (P : K[X]) : RatFunc K :=
  algebraMap _ _ P / algebraMap _ _ (poleDenom K)

theorem poleFraction_injective : Function.Injective (poleFraction (K := K)) := by
  intro P Q e
  unfold poleFraction at e
  exact RatFunc.algebraMap_injective K
    ((div_left_inj' (RatFunc.algebraMap_ne_zero poleDenom_ne_zero)).mp e)

/-- Finite-pole multiplicities and the order at infinity imply an actual quadratic
numerator over the fixed denominator. The zero function is included explicitly. -/
theorem normalized_numerator (r : RatFunc K) (finitePoles : r.denom ∣ poleDenom K)
    (atInfinity : r = 0 ∨ r.intDegree ≤ -2) :
    ∃! P : K[X], P.natDegree ≤ 2 ∧ r = poleFraction P := by
  obtain ⟨h,hh⟩ := finitePoles
  have hne : h ≠ 0 := fun z => poleDenom_ne_zero (K := K) (by rw [hh,z,mul_zero])
  let P := r.num*h
  have frac : r = poleFraction P := by
    apply (RatFunc.num_mul_eq_mul_denom_iff poleDenom_ne_zero).mp
    rw [hh]
    dsimp only [P]
    ring
  refine ⟨P,⟨?_,frac⟩,fun Q hQ => poleFraction_injective (hQ.2.symm.trans frac)⟩
  rcases atInfinity with hz | hd
  · simp [P,hz]
  · by_cases hz : r = 0
    · simp [P,hz]
    have e := RatFunc.natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hz hne
    rw [mul_comm h r.denom, ← hh, poleDenom_degree] at e
    change (r.num*h).natDegree ≤ 2
    omega

def poleCoeffs (P : K[X]) : K × K × K := (P.eval 0, P.eval 1, P.coeff 2)

theorem poleCoeffs_injective_on_quadratics {P Q : K[X]} (hP : P.natDegree ≤ 2)
    (hQ : Q.natDegree ≤ 2) (e : poleCoeffs P = poleCoeffs Q) : P = Q :=
  threePole_unique P Q hP hQ (congrArg Prod.fst e)
    (congrArg (fun z => z.2.1) e) (congrArg (fun z => z.2.2) e)

end AK14
