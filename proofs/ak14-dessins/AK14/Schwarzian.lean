import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Schwarzian rigidity over a characteristic-zero differential field. All four Möbius
coefficients are proved constant for the given derivation. -/
namespace AK14

variable {K : Type*} [Field K] [CharZero K] (D : Derivation ℤ K K)

def preSch (f : K) : K := D (D f) / D f

def schwarzian (f : K) : K := D (preSch D f) - (preSch D f)^2 / 2

theorem schwarzian_formula (f : K) (hf : D f ≠ 0) :
    schwarzian D f = D (D (D f)) / D f - 3 / 2 * (D (D f) / D f)^2 := by
  unfold schwarzian preSch
  rw [D.leibniz_div]
  simp only [smul_eq_mul]
  field_simp
  <;> ring

theorem quotient_deriv (a b : K) (hb : b ≠ 0) :
    D (a / b) = (D a * b - a * D b) / b^2 := by
  rw [D.leibniz_div]
  simp only [smul_eq_mul]
  field_simp
  <;> ring

theorem times_deriv (a b : K) :
    D (a * b) = a * D b + b * D a := D.leibniz _ _

private theorem two_deriv : D (2 : K) = 0 := by
  simpa only [Nat.cast_ofNat] using D.map_natCast 2

/-- A nondegenerate fractional linear change with coefficients in the constant field. -/
def ConstantMobius (f g : K) : Prop :=
  ∃ a b c d : K, D a = 0 ∧ D b = 0 ∧ D c = 0 ∧ D d = 0 ∧
    a*d-b*c ≠ 0 ∧ c*f+d ≠ 0 ∧ g = (a*f+b)/(c*f+d)

theorem constantMobius_of_schwarzian_eq {f g : K} (hf : D f ≠ 0) (hg : D g ≠ 0)
    (h : schwarzian D f = schwarzian D g) : ConstantMobius D f g := by
  let L := preSch D g - preSch D f
  let r := D g / D f
  have hr : r ≠ 0 := div_ne_zero hg hf
  have dr : D r = r * L := by
    dsimp [r, L, preSch]
    rw [quotient_deriv _ _ _ hf]
    field_simp
    <;> ring
  have dL : D L = preSch D f * L + L^2 / 2 := by
    dsimp only [L]
    rw [map_sub]
    unfold schwarzian at h
    calc
      _ = (preSch D g)^2 / 2 - (preSch D f)^2 / 2 := by
        linear_combination -h
      _ = _ := by ring
  by_cases hL : L = 0
  · have hr₀ : D r = 0 := by rw [dr, hL, mul_zero]
    let b := g - r * f
    have hb : D b = 0 := by
      dsimp only [b]
      rw [map_sub, times_deriv, hr₀]
      dsimp [r]
      field_simp
      <;> ring
    refine ⟨r, b, 0, 1, hr₀, hb, map_zero _, D.map_one_eq_zero, ?_, by simp, ?_⟩
    · simpa using hr
    · simp [b]
  · let v := 2 * D f / L
    have hv : v ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hf) hL
    have dv : D v = -D f := by
      dsimp only [v]
      rw [quotient_deriv _ _ _ hL, times_deriv, two_deriv, dL]
      unfold preSch
      field_simp
      <;> ring
    let s := f + v
    have ds : D s = 0 := by simp [s, dv]
    let k := r * (v*v)
    have hk : k ≠ 0 := mul_ne_zero hr (mul_ne_zero hv hv)
    have rel : L * v = 2 * D f := by
      dsimp [v]
      field_simp
    have dk : D k = 0 := by
      change D (r * (v*v)) = 0
      rw [times_deriv, times_deriv, dr, dv]
      calc
        _ = r*v*(L*v - 2*D f) := by ring
        _ = 0 := by rw [rel]; ring
    let b := g - k/v
    have db : D b = 0 := by
      dsimp only [b]
      rw [map_sub, quotient_deriv _ _ _ hv, dk, dv]
      dsimp only [k, r]
      field_simp
      <;> ring
    refine ⟨-b, b*s+k, -1, s, by simp [db], ?_, by simp, ds, ?_, ?_, ?_⟩
    · rw [map_add, times_deriv, ds, db, dk]; ring
    · convert hk using 1 <;> ring
    · simpa [s] using hv
    · have den : (-1:K)*f+s = v := by dsimp [s]; ring
      rw [den, eq_div_iff hv]
      dsimp only [s, b]
      field_simp
      <;> ring

end AK14
