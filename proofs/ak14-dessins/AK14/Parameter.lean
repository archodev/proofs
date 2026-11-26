import AK14.LocalChart
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-! A power series of finite positive order e is the e-th power of a genuine
uniformizing parameter, over an algebraically closed field of characteristic zero. -/
namespace AK14.LocalChart
open PowerSeries
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

private theorem bin_nat (n : ℕ) : binomialSeries K (n:ℚ)=(1+X)^n := by
  exact binomialSeries_nat (R:=ℚ) (A:=K) n

private theorem bin_mul (r : ℚ) (n : ℕ) :
    binomialSeries K ((n:ℚ)*r)=(binomialSeries K r)^n := by
  induction n with
  | zero =>
    simpa using bin_nat (K := K) 0
  | succ n ih =>
    rw [Nat.cast_succ,add_mul,one_mul,binomialSeries_add,ih,pow_succ]

theorem one_plus_root (P : K⟦X⟧) (hc : constantCoeff (R := K) P = 0) {e : ℕ} (he : 0<e) :
    ∃ W : K⟦X⟧, W^e=1+P := by
  let a : Unit → MvPowerSeries Unit K := fun _ => P
  have h : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hc)
  let subst := MvPowerSeries.substAlgHom (R := K) h
  have eX : subst X=P := MvPowerSeries.substAlgHom_X h ()
  refine ⟨subst (binomialSeries K (1/(e:ℚ))),?_⟩
  rw [← map_pow,← bin_mul]
  have n : (e:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  rw [mul_one_div_cancel n]
  have b1 := bin_nat (K := K) 1
  simp only [Nat.cast_one,pow_one] at b1
  rw [b1,map_add,map_one,eX]

theorem unit_root [IsAlgClosed K] (P : K⟦X⟧) (hc : constantCoeff (R := K) P ≠ 0)
    {e : ℕ} (he : 0<e) : ∃ W : K⟦X⟧, W^e=P ∧ constantCoeff (R := K) W ≠ 0 := by
  let c := constantCoeff (R := K) P
  have nc : c ≠ 0 := hc
  obtain ⟨b,hb⟩ := IsAlgClosed.exists_pow_nat_eq c he
  let V := C (R := K) c⁻¹*P-1
  have z : constantCoeff (R := K) V=0 := by simp [V,← show c=constantCoeff (R := K) P from rfl,nc]
  obtain ⟨W,hW⟩ := one_plus_root V z he
  have eW : (C (R := K) b*W)^e=P := by
    rw [mul_pow,← map_pow,hb,hW]
    dsimp only [V]
    rw [add_sub_cancel,← mul_assoc,← map_mul,mul_inv_cancel₀ nc,map_one,one_mul]
  refine ⟨C (R := K) b*W,eW,?_⟩
  intro zero
  have eq := congrArg (constantCoeff (R := K)) eW
  rw [map_pow,zero,zero_pow he.ne'] at eq
  exact hc eq.symm

theorem local_power_parameter [IsAlgClosed K] (P : K⟦X⟧) (hp : P ≠ 0) {e : ℕ}
    (he : 0<e) (order : P.order.toNat=e) :
    ∃ V : K⟦X⟧, constantCoeff (R := K) V ≠ 0 ∧ (X*V)^e=P := by
  obtain ⟨V,hv,cv⟩ := unit_root (divXPowOrder P)
    (constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hp) he
  refine ⟨V,cv,?_⟩
  rw [mul_pow,hv,← order,X_pow_order_mul_divXPowOrder]

end
end AK14.LocalChart
