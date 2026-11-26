import AK14.Schwarzian
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! Extension of a derivation to the field of fractions by the universal property
of localization, using dual numbers. -/
namespace AK14
open scoped nonZeroDivisors
open TrivSqZeroExt

variable {R : Type*} [CommRing R] [IsDomain R] (F : Type*) [Field F] [Algebra R F]
  [IsFractionRing R F] (d : Derivation ℤ R R)

private def dualRingHom : R →+* TrivSqZeroExt F F where
  toFun a := (algebraMap R F a, algebraMap R F (d a))
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul _ _ _
    · change algebraMap R F (d (a*b)) =
        algebraMap R F a * algebraMap R F (d b) + algebraMap R F (d a) * algebraMap R F b
      simp [d.leibniz,smul_eq_mul,mul_comm]

private theorem dualUnits (u : R⁰) : IsUnit (dualRingHom F d u) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  change IsUnit (algebraMap R F (u : R))
  exact IsLocalization.map_units F u

private noncomputable def dualLift : F →+* TrivSqZeroExt F F :=
  IsLocalization.lift (dualUnits F d)

private theorem dualLift_apply (a : R) :
    dualLift F d (algebraMap R F a) = dualRingHom F d a := IsLocalization.lift_eq _ _

private theorem dualLift_fst (a : F) : (dualLift F d a).fst = a := by
  let f := (TrivSqZeroExt.fstHom F F F).toRingHom.comp (dualLift F d)
  have h : f = RingHom.id F := IsLocalization.ringHom_ext R⁰ (by
    apply RingHom.ext
    intro r
    change (dualLift F d (algebraMap R F r)).fst = algebraMap R F r
    rw [dualLift_apply]
    rfl)
  exact RingHom.congr_fun h a

noncomputable def fractionDeriv : Derivation ℤ F F :=
  let f : F →+ F := {
    toFun := fun a => (dualLift F d a).snd
    map_zero' := by simp
    map_add' := by intro a b; simp }
  Derivation.mk' f.toIntLinearMap (by
    intro a b
    change (dualLift F d (a*b)).snd =
      a*(dualLift F d b).snd + b*(dualLift F d a).snd
    rw [map_mul,TrivSqZeroExt.snd_mul,dualLift_fst,dualLift_fst]
    change _ + (dualLift F d a).snd*b = _
    rw [mul_comm _ b,smul_eq_mul])

@[simp] theorem fractionDeriv_map (a : R) :
    fractionDeriv F d (algebraMap R F a) = algebraMap R F (d a) :=
  congrArg TrivSqZeroExt.snd (dualLift_apply F d a)

theorem fractionDeriv_unique (D : Derivation ℤ F F)
    (h : ∀ a, D (algebraMap R F a) = algebraMap R F (d a)) : D = fractionDeriv F d := by
  apply Derivation.ext
  intro z
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective (A := R) z
  rw [D.leibniz_div, (fractionDeriv F d).leibniz_div, h, h, fractionDeriv_map, fractionDeriv_map]

end AK14
