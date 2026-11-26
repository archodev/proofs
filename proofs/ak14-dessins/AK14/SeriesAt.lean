import AK14.LocalChart
import AK14.Constants
import AK14.Rational
import Mathlib.Algebra.Polynomial.Taylor

/-! Actual Taylor embeddings of rational functions at finite points. Absence of
finite poles is deduced from the expansions, using reduced numerator and denominator. -/
namespace AK14.SeriesAt
open Polynomial
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

abbrev GermField (K : Type*) [Field K] := FractionRing (PowerSeries K)
abbrev embed (K : Type*) [Field K] := algebraMap (PowerSeries K) (GermField K)

def poly (a : K) : K[X] →+* PowerSeries K :=
  Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.taylorAlgHom a).toRingHom

theorem poly_injective (a : K) : Function.Injective (poly a) :=
  (Polynomial.coe_injective K).comp (Polynomial.taylor_injective a)

@[simp] theorem poly_constant (a : K) (p : K[X]) :
    PowerSeries.constantCoeff (R := K) (poly a p) = p.eval a := by
  change PowerSeries.constantCoeff (R := K) (taylor a p : PowerSeries K)=_
  rw [Polynomial.constantCoeff_coe,Polynomial.taylor_coeff_zero]

def intoGerm (a : K) : K[X] →+* GermField K := (embed K).comp (poly a)

theorem intoGerm_injective (a : K) : Function.Injective (intoGerm a) :=
  (IsFractionRing.injective (PowerSeries K) (GermField K)).comp (poly_injective a)

def expand (a : K) : RatFunc K →+* GermField K :=
  IsFractionRing.lift (intoGerm_injective a)

@[simp] theorem expand_polynomial (a : K) (p : K[X]) :
    expand a (algebraMap K[X] (RatFunc K) p) = embed K (poly a p) :=
  IsFractionRing.lift_algebraMap _ _

theorem regular_iff (a : K) (r : RatFunc K) :
    (∃ H : PowerSeries K, expand a r = embed K H) ↔ r.denom.eval a ≠ 0 := by
  let U := poly a r.num
  let V := poly a r.denom
  have nv := (map_ne_zero_iff (intoGerm a) (intoGerm_injective a)).mpr r.denom_ne_zero
  have repr : expand a r = embed K U/embed K V := by
    conv_lhs => rw [← RatFunc.num_div_denom r]
    rw [map_div₀,expand_polynomial,expand_polynomial]
  constructor
  · rintro ⟨H,hH⟩ hv
    have e : U=H*V := (IsFractionRing.injective (PowerSeries K) (GermField K)) (by
      rw [map_mul]; exact (div_eq_iff nv).mp (repr.symm.trans hH))
    have van := congrArg (PowerSeries.constantCoeff (R := K)) e
    change PowerSeries.constantCoeff (R := K) (poly a r.num) = _ at van
    rw [map_mul,poly_constant,show V=poly a r.denom from rfl,poly_constant,hv,mul_zero] at van
    have cop := Polynomial.aeval_ne_zero_of_isCoprime (RatFunc.isCoprime_num_denom r) a
    change r.num.eval a ≠ 0 ∨ r.denom.eval a ≠ 0 at cop
    exact cop.elim (fun h => h van) (fun h => h hv)
  · intro hv
    have v0 : PowerSeries.constantCoeff (R := K) V ≠ 0 := by simpa [V] using hv
    have eq := congrArg (embed K) (PowerSeries.mul_inv_cancel V v0)
    rw [map_mul,map_one] at eq
    refine ⟨U*V⁻¹,?_⟩
    rw [repr,map_mul,eq_inv_of_mul_eq_one_right eq,div_eq_mul_inv]

theorem polynomial_of_regular_everywhere [IsAlgClosed K] (r : RatFunc K)
    (regular : ∀ a : K, ∃ H : PowerSeries K, expand a r = embed K H) :
    ∃ P : K[X], r=algebraMap K[X] (RatFunc K) P := by
  have degree : r.denom.natDegree=0 := by
    by_contra h
    obtain ⟨a,ha⟩ := IsAlgClosed.exists_root r.denom (by
      rw [degree_eq_natDegree r.denom_ne_zero]
      exact_mod_cast h)
    exact (regular_iff a r).mp (regular a) ha
  let c := r.denom.coeff 0
  have e : r.denom=C c := eq_C_of_natDegree_eq_zero degree
  have nc : c ≠ 0 := fun z => r.denom_ne_zero (by rw [e,z,map_zero])
  refine ⟨r.num*C c⁻¹,?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom r]
  rw [e,map_mul,div_eq_mul_inv]
  have ec : algebraMap K[X] (RatFunc K) (C c⁻¹) = (algebraMap K[X] (RatFunc K) (C c))⁻¹ :=
    map_inv₀ ((algebraMap K[X] (RatFunc K)).comp C) c
  rw [ec]

theorem normalized_of_local_bounds [IsAlgClosed K] (r : RatFunc K)
    (localBounds : ∀ a : K, ∃ H : PowerSeries K,
      expand a (r * algebraMap K[X] (RatFunc K) (poleDenom K)) = embed K H)
    (growth : r=0 ∨ r.intDegree ≤ -2) :
    ∃! P : K[X], P.natDegree ≤ 2 ∧ r=poleFraction P := by
  obtain ⟨P,hP⟩ := polynomial_of_regular_everywhere _ localBounds
  apply normalized_numerator _ _ growth
  apply (RatFunc.denom_dvd poleDenom_ne_zero).mpr
  exact ⟨P,(eq_div_iff (RatFunc.algebraMap_ne_zero poleDenom_ne_zero)).mpr hP⟩

end
end AK14.SeriesAt
