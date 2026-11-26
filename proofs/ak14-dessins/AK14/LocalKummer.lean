import AK14.Normalized
import Mathlib.FieldTheory.KummerPolynomial

/-! The first (cubic) step of the explicit tetrahedral inverse is irreducible
over the rational function field for every allowed normalized map. -/
namespace AK14.SeriesAt
open Polynomial PowerSeries
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem ord_zero_of_unit {P : K⟦X⟧} (h : constantCoeff (R := K) P ≠ 0) : P.order.toNat=0 := by
  have e : P.order ≤ 0 := order_le 0 (by simpa only [coeff_zero_eq_constantCoeff] using h)
  rw [nonpos_iff_eq_zero.mp e]
  rfl

theorem power_order_divides {P Q : K⟦X⟧} (np : P ≠ 0) (nq : Q ≠ 0)
    {u : GermField K} {k : ℕ} (hk : 0<k) (eq : u^k=embed K P/embed K Q) :
    (k:ℤ) ∣ (P.order.toNat:ℤ)-Q.order.toNat := by
  obtain ⟨A,B,nb,rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries K) u
  have nB := mem_nonZeroDivisors_iff_ne_zero.mp nb
  have emb := IsFractionRing.injective (PowerSeries K) (GermField K)
  have nA : A ≠ 0 := by
    intro zero
    have ne := div_ne_zero ((map_ne_zero_iff _ emb).mpr np) ((map_ne_zero_iff _ emb).mpr nq)
    apply ne
    rw [← eq,zero,map_zero,zero_div,zero_pow hk.ne']
  have cross : A^k*Q=P*B^k := by
    apply emb
    rw [map_mul (embed K),map_mul (embed K),map_pow (embed K),map_pow (embed K)]
    rw [div_pow] at eq
    exact (div_eq_div_iff (pow_ne_zero _ ((map_ne_zero_iff _ emb).mpr nB))
      ((map_ne_zero_iff _ emb).mpr nq)).mp eq
  have o := congrArg (fun U : K⟦X⟧ => U.order) cross
  simp only [order_mul,order_pow] at o
  rw [← coe_toNat_order nA,← coe_toNat_order nB,← coe_toNat_order np,← coe_toNat_order nq] at o
  have nat : k*A.order.toNat+Q.order.toNat=P.order.toNat+k*B.order.toNat := by
    simp only [nsmul_eq_mul] at o
    exact_mod_cast o
  have ints : (k:ℤ)*A.order.toNat+Q.order.toNat=P.order.toNat+k*B.order.toNat := by exact_mod_cast nat
  refine ⟨(A.order.toNat:ℤ)-B.order.toNat,?_⟩
  linear_combination -ints

theorem cube_irreducible {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {f : RatFunc K} (hf : NormalizedCover p f) :
    Irreducible ((X : (RatFunc K)[X])^3-Polynomial.C (1-f)) := by
  apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_three).mpr
  intro u h
  have b := hf.atB
  obtain ⟨P,np,cp,ord,chart⟩ := b
  have e : ((expand 1) u)^3=1-expand 1 f := by rw [← map_pow,h,map_sub,map_one]
  apply hp.b_residue
  apply Int.natCast_dvd_natCast.mp
  cases fam : p.family with
  | split =>
    change (expand 1) f=targetChart p.bSlot _ at chart
    simp [Passport.bSlot,fam,targetChart] at chart
    have val : (expand 1 u)^3=embed K P/embed K 1 := by rw [e,chart]; simp
    have div := power_order_divides np (Q := 1) one_ne_zero (by decide : 0<3) val
    simpa [ord,PowerSeries.order_one] using div
  | together =>
    simp [Passport.bSlot,fam,targetChart] at chart
    have nz := (map_ne_zero_iff (embed K) (IsFractionRing.injective (PowerSeries K) _)).mpr np
    have c : constantCoeff (R := K) (P-1) ≠ 0 := by simp [cp]
    have nP1 : P-1 ≠ 0 := fun z => c (by simp [z])
    have val : (expand 1 u)^3=embed K (P-1)/embed K P := by
      rw [e,chart,map_sub,map_one]
      field_simp
    have d := power_order_divides nP1 np (by decide : 0<3) val
    simpa [ord,ord_zero_of_unit c] using d

end
end AK14.SeriesAt
