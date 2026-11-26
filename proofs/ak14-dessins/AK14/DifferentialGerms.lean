import AK14.Infinity
import AK14.Transport

/-! The rational derivative transported to finite Taylor charts and to the
reciprocal chart at infinity. -/
namespace AK14.SeriesAt
open Polynomial
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

local instance (priority := 2000) : Algebra ℤ (PowerSeries K) := Ring.toIntAlgebra _
local instance (priority := 2000) : Algebra ℤ (GermField K) := Ring.toIntAlgebra _
local instance (priority := 2000) : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : CharZero (PowerSeries K) := charZero_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective
instance germCharZero : CharZero (GermField K) :=
  charZero_of_injective_algebraMap (IsFractionRing.injective (PowerSeries K) (GermField K))
instance rationalCharZero : CharZero (RatFunc K) :=
  charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective

def germDeriv (K : Type*) [Field K] : Derivation ℤ (GermField K) (GermField K) :=
  fractionDeriv (R := PowerSeries K) (GermField K) ((PowerSeries.derivative K).restrictScalars ℤ)

@[simp] theorem germDeriv_embed (P : PowerSeries K) :
    germDeriv K (embed K P)=embed K (PowerSeries.derivative K P) := fractionDeriv_map _ _ _

@[simp] theorem germDeriv_t : germDeriv K (t K)=1 := by
  change germDeriv K (embed K PowerSeries.X)=_
  rw [germDeriv_embed,PowerSeries.derivative_X,map_one]

@[simp] theorem germDeriv_const (c : K) : germDeriv K (constMap K c)=0 := by
  change germDeriv K (embed K (PowerSeries.C (R := K) c))=_
  rw [germDeriv_embed,PowerSeries.derivative_C,map_zero]

private theorem compatibility_on_fractions {L : Type*} [Field L] [CharZero L]
    (E : Derivation ℤ L L) (ρ : RatFunc K →+* L)
    (h : ∀ P : K[X], E (ρ (algebraMap _ _ P)) = ρ (algebraMap _ _ P.derivative))
    (f : RatFunc K) : E (ρ f)=ρ (ratDeriv K f) := by
  have n := RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have nn := (map_ne_zero_iff ρ ρ.injective).mpr n
  rw [← RatFunc.num_div_denom f,map_div₀ ρ,quotient_deriv E _ _ nn,
    quotient_deriv (ratDeriv K) _ _ n,h,h,ratDeriv_polynomial,ratDeriv_polynomial]
  simp only [map_div₀ ρ,map_sub ρ,map_mul ρ,map_pow ρ]

theorem expand_deriv (a : K) (f : RatFunc K) :
    germDeriv K (expand a f) = expand a (ratDeriv K f) := by
  apply compatibility_on_fractions
  intro P
  rw [expand_polynomial,expand_polynomial,germDeriv_embed]
  congr 1
  change PowerSeries.derivative K (taylor a P : PowerSeries K) =
    (taylor a P.derivative : PowerSeries K)
  rw [PowerSeries.derivative_coe,taylor_apply,taylor_apply,derivative_comp]
  simp

private theorem eval_deriv {L : Type*} [Field L] (E : Derivation ℤ L L)
    (ρ : K →+* L) (constants : ∀ c, E (ρ c)=0) (y : L) (dy : E y=1) (P : K[X]) :
    E (P.eval₂ ρ y)=P.derivative.eval₂ ρ y := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => rw [eval₂_add,map_add,hp,hq,derivative_add,eval₂_add]
  | monomial n c =>
    rw [eval₂_monomial,derivative_monomial,eval₂_monomial,E.leibniz,E.leibniz_pow,constants,dy]
    simp [smul_eq_mul,nsmul_eq_mul,mul_comm,mul_assoc,mul_left_comm]

theorem expandInf_deriv (f : RatFunc K) :
    ((-(t K)^2) • germDeriv K) (expandInf K f)=expandInf K (ratDeriv K f) := by
  let E := (-(t K)^2) • germDeriv K
  apply compatibility_on_fractions
  intro P
  rw [expandInf_poly,expandInf_poly]
  apply eval_deriv
  · intro c
    change -(t K)^2*germDeriv K (constMap K c)=0
    rw [germDeriv_const,mul_zero]
  · change -(t K)^2*germDeriv K (t K)⁻¹=1
    rw [(germDeriv K).leibniz_inv,germDeriv_t]
    simp only [smul_eq_mul]
    field_simp [t_ne]

def rationalConnection (f : RatFunc K) := pullConnection (ratDeriv K) f

theorem finite_connection (a : K) (f : RatFunc K) :
    expand a (rationalConnection f)=pullConnection (germDeriv K) (expand a f) :=
  pullConnection_map _ _ _ (expand_deriv a) _

theorem infty_connection (f : RatFunc K) (hf : ratDeriv K f ≠ 0) :
    expandInf K (rationalConnection f)=(t K)^4*pullConnection (germDeriv K) (expandInf K f) := by
  have ne := (map_ne_zero_iff (expandInf K) (expandInf K).injective).mpr hf
  rw [← expandInf_deriv] at ne
  have df : germDeriv K (expandInf K f) ≠ 0 := fun z => ne (by simp [Derivation.smul_apply,z])
  exact (pullConnection_map _ _ _ expandInf_deriv _).trans
    (pullConnection_inversion_scale _ germDeriv_t df)

end
end AK14.SeriesAt
