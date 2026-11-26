import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Partial fractions on the three-marked sphere. The common denominator is
x²(x−1)². The growth condition at infinity bounds the numerator degree by two. -/
namespace AK14
open Polynomial

variable {K : Type*} [Field K]

private theorem expand_quad (P : K[X]) (hd : P.natDegree ≤ 2) :
    P = C (P.coeff 0) + C (P.coeff 1)*X + C (P.coeff 2)*X^2 := by
  have h := P.as_sum_range' 3 (by omega)
  simpa [Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial] using h

/-- The double-pole coefficients at 0, 1, and infinity uniquely determine the
numerator. In these coordinates they are P(0), P(1), and the coefficient of X². -/
theorem threePole_numerator (P : K[X]) (hd : P.natDegree ≤ 2) :
    P = C (P.eval 0) * (X-1)^2 + C (P.eval 1)*X^2 +
      C (P.coeff 2 - P.eval 0 - P.eval 1)*X*(X-1) := by
  have h := expand_quad P hd
  have h0 : P.eval 0 = P.coeff 0 := P.coeff_zero_eq_eval_zero.symm
  have h1 : P.eval 1 = P.coeff 0 + P.coeff 1 + P.coeff 2 := by
    conv_lhs => rw [h]
    simp
  rw [h0, h1]
  conv_lhs => rw [h]
  simp only [map_add, map_sub]
  ring

theorem threePole_unique (P Q : K[X]) (hP : P.natDegree ≤ 2) (hQ : Q.natDegree ≤ 2)
    (h0 : P.eval 0 = Q.eval 0) (h1 : P.eval 1 = Q.eval 1) (hinf : P.coeff 2 = Q.coeff 2) :
    P = Q := by
  calc
    P = _ := threePole_numerator P hP
    _ = Q := by rw [h0, h1, hinf, ← threePole_numerator Q hQ]

theorem threePole_formula (P : K[X]) (hd : P.natDegree ≤ 2) (x : K) (h0 : x ≠ 0)
    (h1 : x ≠ 1) :
    P.eval x / (x^2 * (x-1)^2) =
      P.eval 0/x^2 + P.eval 1/(x-1)^2 +
      (P.coeff 2 - P.eval 0 - P.eval 1)/(x*(x-1)) := by
  conv_lhs => rw [threePole_numerator P hd]
  simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_C, eval_X, eval_one]
  have h₁ := sub_ne_zero.mpr h1
  field_simp
  <;> ring

end AK14
