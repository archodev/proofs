import AK14.QuotientSphere
import AK14.DifferentialGerms
import Mathlib.FieldTheory.SplittingField.Construction

/-! Construction of simultaneous inverse tetrahedral lifts in a finite algebraic
function field. -/
namespace AK14
open Polynomial TetraQuotient
noncomputable section
variable {F L : Type*} [Field F] [CharZero F] [Field L] [CharZero L]

def liftPolynomial (s f : F) : F[X] := numerator s-C f*(quart s)^3

theorem liftPolynomial_degree {s f : F} (hs : s^2= -3) (hf : f ≠ 0) :
    (liftPolynomial s f).natDegree=12 := by
  have d : (C f*(quart s)^3).natDegree=12 := by
    rw [natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hf),natDegree_pow,degree_quart]
  rw [liftPolynomial,natDegree_sub_eq_right_of_natDegree_lt,d]
  rw [degree_numerator hs,d]; decide

theorem root_is_lift (ρ : F →+* L) {s f : F} (hs : s^2= -3) (hf : f ≠ 0)
    {z : L} (root : (liftPolynomial s f).eval₂ ρ z=0) : tetraMap (ρ s) z=ρ f := by
  have hs' : (ρ s)^2= -3 := by rw [← map_pow,hs,map_neg,map_ofNat]
  let A := quartic (ρ s) (z,1)
  let B := quartic (-(ρ s)) (z,1)
  have ev : (quart s).eval₂ ρ z=A := by simp [quart,A,quartic,map_ofNat ρ]
  have en : (numerator s).eval₂ ρ z = (qmap (ρ s) (z,1)).1 := by
    rw [quartic_difference hs']
    simp only [numerator,edgePoly,eval₂_mul,eval₂_pow,eval₂_sub,eval₂_X,eval₂_C,eval₂_one,
      map_mul ρ,map_ofNat ρ,one_pow,mul_one]
    ring
  have cross : A^3-B^3=ρ f*A^3 := by
    apply sub_eq_zero.mp
    simpa only [liftPolynomial,eval₂_sub,eval₂_mul,eval₂_C,eval₂_pow,ev,en] using root
  have good := qmap_valid hs' (P := (z,1)) (Or.inr one_ne_zero)
  have na : A ≠ 0 := by
    intro h
    have n : A^3-B^3=0 := by rw [cross,h]; simp
    change A^3-B^3 ≠ 0 ∨ A^3 ≠ 0 at good
    simp [h] at good cross
    exact good cross
  have nz : z ≠ 0 := by
    intro z0
    have one : A=1 := by simp [A,quartic,z0]
    have one' : B=1 := by simp [B,quartic,z0]
    apply (map_ne_zero_iff ρ ρ.injective).mpr hf
    simpa [one,one'] using cross.symm
  let v := z^2
  let t := v+v⁻¹
  have nv : v ≠ 0 := pow_ne_zero _ nz
  have ea : A=v*(t+2*(ρ s)) := by
    dsimp only [A,quartic,t,v]; simp only [one_pow,mul_one]; field_simp; ring
  have eb : B=v*(t-2*(ρ s)) := by
    dsimp only [B,quartic,t,v]; simp only [one_pow,mul_one]; field_simp; ring
  have ratio : contrast (2*ρ s) t=B/A := by
    rw [ea,eb,contrast,mul_div_mul_left _ _ nv]
  change 1-(contrast (2*ρ s) t)^3=ρ f
  rw [ratio,div_pow]
  field_simp [na]
  linear_combination cross

abbrev LiftField (s f g : F) := ((liftPolynomial s f)*(liftPolynomial s g)).SplittingField

theorem common_lifts {s f g : F} (hs : s^2= -3) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ z w : LiftField s f g,
      tetraMap (algebraMap F _ s) z=algebraMap F _ f ∧
      tetraMap (algebraMap F _ s) w=algebraMap F _ g := by
  let L := LiftField s f g
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  let P := liftPolynomial s f
  let Q := liftPolynomial s g
  have degP : P.natDegree=12 := liftPolynomial_degree hs hf
  have degQ : Q.natDegree=12 := liftPolynomial_degree hs hg
  have np : P ≠ 0 := fun z => by simp [z] at degP
  have nq : Q ≠ 0 := fun z => by simp [z] at degQ
  let ρ := algebraMap F L
  have pair : (P.map ρ).Splits ∧ (Q.map ρ).Splits :=
    (splits_mul_iff (Polynomial.map_ne_zero np) (Polynomial.map_ne_zero nq)).mp
      (by simpa only [Polynomial.map_mul] using SplittingField.splits (P*Q))
  obtain ⟨z,hz⟩ := pair.1.exists_eval_eq_zero (by rw [degree_map,degree_eq_natDegree np,degP]; decide)
  obtain ⟨w,hw⟩ := pair.2.exists_eval_eq_zero (by rw [degree_map,degree_eq_natDegree nq,degQ]; decide)
  exact ⟨z,w,root_is_lift ρ hs hf (by simpa only [Polynomial.eval_map] using hz),
    root_is_lift ρ hs hg (by simpa only [Polynomial.eval_map] using hw)⟩

theorem tetraMap_deriv_zero (D : Derivation ℤ L L) {s z : L} (ds : D s=0) (dz : D z=0) :
    D (tetraMap s z)=0 := by
  let v := z^2
  let t := v+v⁻¹
  have dv : D v=0 := by dsimp only [v]; rw [d_square,dz,mul_zero]
  have dt : D t=0 := by dsimp only [t]; rw [map_add,D.leibniz_inv,dv]; simp
  have d2 : D (2:L)=0 := by simpa only [Nat.cast_ofNat] using D.map_natCast 2
  have da : D (2*s)=0 := by rw [times_deriv,ds,d2]; ring
  have dh : D (contrast (2*s) t)=0 := by
    rw [contrast,D.leibniz_div,map_sub D t (2*s),map_add D t (2*s),dt,da]; simp
  change D (1-(contrast (2*s) t)^3)=0
  rw [map_sub,D.map_one_eq_zero,D.leibniz_pow,dh]; simp

end
end AK14
