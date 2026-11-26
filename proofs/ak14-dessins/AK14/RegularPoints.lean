import AK14.FullInverse

/-! On the complement of the three branch values, the normalized local passport
implies the usual nonvanishing rational derivative at each affine point. -/
namespace AK14.SeriesAt
open Polynomial
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def affineValue (f : RatFunc K) (x : K) : K := f.num.eval x/f.denom.eval x

def GoodPoint (f : RatFunc K) (x : K) : Prop :=
  f.denom.eval x≠0 ∧ affineValue f x≠0 ∧ affineValue f x≠1

theorem germ_cross {f : RatFunc K} {x : K} {P : PowerSeries K} (h : expand x f=embed K P) :
    poly x f.num=P*poly x f.denom := by
  have nz := (map_ne_zero_iff (intoGerm x) (intoGerm_injective x)).mpr f.denom_ne_zero
  apply (IsFractionRing.injective (PowerSeries K) (GermField K))
  rw [map_mul (embed K)]
  apply (div_eq_iff nz).mp
  conv_rhs => rw [← h,← RatFunc.num_div_denom f]
  rw [map_div₀,expand_polynomial,expand_polynomial]
  rfl

theorem germ_value {f : RatFunc K} {x : K} {P : PowerSeries K} (h : expand x f=embed K P) :
    affineValue f x=PowerSeries.constantCoeff (R := K) P := by
  have n := (regular_iff x f).mp ⟨P,h⟩
  apply (div_eq_iff n).mpr
  simpa only [map_mul,poly_constant] using congrArg (PowerSeries.constantCoeff (R := K)) (germ_cross h)

theorem good_not_branch {f : RatFunc K} {x : K} (gx : GoodPoint f x) {j : Fin 3} {e : ℕ} :
    ¬BranchGerm (expand x f) j e := by
  rintro ⟨P,np,cp,_,h⟩
  fin_cases j
  · change expand x f=embed K P at h
    exact gx.2.1 ((germ_value h).trans cp)
  · change expand x f=1-embed K P at h
    have g : expand x f=embed K (1-P) := by rw [map_sub,map_one,h]
    exact gx.2.2 ((germ_value g).trans (by simp [cp]))
  · change expand x f=(embed K P)⁻¹ at h
    obtain ⟨U,hu⟩ := (regular_iff x f).mpr gx.1
    have nz := (map_ne_zero_iff (embed K) (IsFractionRing.injective (PowerSeries K) _)).mpr np
    have inv : U*P=1 := (IsFractionRing.injective (PowerSeries K) (GermField K)) (by
      rw [map_mul (embed K),← hu,h,inv_mul_cancel₀ nz,map_one])
    have eq := congrArg (PowerSeries.constantCoeff (R := K)) inv
    simp [cp] at eq

theorem good_ordinary {p : Passport} {f : RatFunc K} (hf : NormalizedCover p f)
    {x : K} (gx : GoodPoint f x) : OrdinaryGerm (expand x f) := by
  have a : x≠0 := fun z => good_not_branch (z ▸ gx) hf.atA
  have b : x≠1 := fun z => good_not_branch (z ▸ gx) hf.atB
  rcases hf.elsewhere x a b with h | ⟨_,h⟩
  · exact h
  · exact (good_not_branch gx h).elim

theorem derivative_at_center (x : K) (p : K[X]) :
    PowerSeries.constantCoeff (R := K) (PowerSeries.derivative K (poly x p))=p.derivative.eval x := by
  change PowerSeries.constantCoeff (R := K) (PowerSeries.derivative K (taylor x p : PowerSeries K))=_
  rw [PowerSeries.derivative_coe,Polynomial.constantCoeff_coe,Polynomial.coeff_derivative]
  simpa using taylor_coeff_one x p

theorem good_deriv_ne {p : Passport} {f : RatFunc K} (hf : NormalizedCover p f) {x : K}
    (gx : GoodPoint f x) :
    (f.num.derivative.eval x*f.denom.eval x-f.num.eval x*f.denom.derivative.eval x)/
      (f.denom.eval x)^2 ≠ 0 := by
  obtain ⟨P,h,_,_,ne⟩ := good_ordinary hf gx
  have e := germ_cross h
  have v := congrArg (PowerSeries.constantCoeff (R := K)) e
  rw [poly_constant,map_mul,poly_constant] at v
  have d := congrArg (fun A : PowerSeries K => PowerSeries.constantCoeff (R := K) (PowerSeries.derivative K A)) e
  simp only [derivative_at_center,Derivation.leibniz,smul_eq_mul,map_add,map_mul,poly_constant] at d
  have z := gx.1
  have eq : (f.num.derivative.eval x*f.denom.eval x-f.num.eval x*f.denom.derivative.eval x)/
      (f.denom.eval x)^2 = PowerSeries.constantCoeff (R := K) (PowerSeries.derivative K P) := by
    apply (div_eq_iff (pow_ne_zero 2 z)).mpr
    linear_combination f.denom.eval x*d-f.denom.derivative.eval x*v
  exact eq ▸ ne

end
end AK14.SeriesAt
