import AK14.GluedCovering
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Basic

/-! The double of a triangle in the complex coordinate with named values 0, 1
and infinity. Barycentric coordinates are normalized triangle inequalities for
the three side lengths |w|, |w-1|, 1. -/
namespace AK14.Gluing
open Complex Set Filter Topology
open scoped OnePoint
noncomputable section

def zeroMass (z : Triangle) : ℝ := z.val 2
def oneMass (z : Triangle) : ℝ := z.val 1
def infMass (z : Triangle) : ℝ := z.val 0
def baseMass (z : Triangle) : ℝ := zeroMass z + oneMass z

theorem masses_sum (z : Triangle) : zeroMass z+oneMass z+infMass z=1 := by
  have h := z.property.2
  rw [Fin.sum_univ_three] at h
  dsimp [zeroMass,oneMass,infMass]
  linarith

def realNum (z : Triangle) := oneMass z*baseMass z + infMass z*(oneMass z-zeroMass z)
def imagNum (z : Triangle) := 2*Real.sqrt (zeroMass z*oneMass z*infMass z)
def sideSign (b : Bool) : ℝ := if b then -1 else 1

def affinePoint (b : Bool) (z : Triangle) : ℂ :=
  ⟨realNum z / baseMass z^2, sideSign b*imagNum z / baseMass z^2⟩

private theorem num_square (z : Triangle) :
    realNum z^2+imagNum z^2=(oneMass z+infMass z)^2*baseMass z^2 := by
  have sq := Real.sq_sqrt (mul_nonneg (mul_nonneg (z.property.1 2) (z.property.1 1)) (z.property.1 0))
  change Real.sqrt (zeroMass z*oneMass z*infMass z)^2=zeroMass z*oneMass z*infMass z at sq
  have tot := masses_sum z
  dsimp only [realNum,imagNum,baseMass]
  linear_combination 4*sq - 4*zeroMass z*oneMass z*infMass z*tot

private theorem other_num_square (z : Triangle) :
    (realNum z-baseMass z^2)^2+imagNum z^2=(zeroMass z+infMass z)^2*baseMass z^2 := by
  have h := num_square z
  dsimp only [realNum,baseMass] at h ⊢
  linear_combination h

theorem baseMass_pos {z : Triangle} (h : baseMass z≠0) : 0<baseMass z :=
  lt_of_le_of_ne (add_nonneg (z.property.1 2) (z.property.1 1)) h.symm

theorem affine_norm {z : Triangle} (h : baseMass z≠0) (b : Bool) :
    ‖affinePoint b z‖=(oneMass z+infMass z)/baseMass z := by
  have nonneg : 0≤(oneMass z+infMass z)/baseMass z :=
    div_nonneg (add_nonneg (z.property.1 1) (z.property.1 0)) (baseMass_pos h).le
  apply (sq_eq_sq₀ (norm_nonneg _) nonneg).mp
  rw [Complex.sq_norm,Complex.normSq_apply]
  change _ / _ * (_ / _) + (sideSign b*imagNum z / _) * (_ / _)=_
  cases b <;> simp only [sideSign,Bool.false_eq_true,if_false,if_true,neg_one_mul,one_mul,neg_div,neg_mul_neg] <;>
    field_simp [h] <;> nlinarith only [num_square z]

theorem affine_sub_norm {z : Triangle} (h : baseMass z≠0) (b : Bool) :
    ‖affinePoint b z-1‖=(zeroMass z+infMass z)/baseMass z := by
  have nonneg : 0≤(zeroMass z+infMass z)/baseMass z :=
    div_nonneg (add_nonneg (z.property.1 2) (z.property.1 0)) (baseMass_pos h).le
  apply (sq_eq_sq₀ (norm_nonneg _) nonneg).mp
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [sub_re,sub_im,one_re,one_im,sub_zero]
  change (_ / _ - 1) * (_ / _ - 1) + (sideSign b*imagNum z / _) * (_ / _)=_
  cases b <;> simp only [sideSign,Bool.false_eq_true,if_false,if_true,neg_one_mul,one_mul,neg_div,neg_mul_neg] <;>
    field_simp [h] <;> nlinarith only [other_num_square z]

theorem inf_vertex_iff (z : Triangle) : baseMass z=0 ↔ z=vertex 2 := by
  constructor
  · intro e
    have a := z.property.1 2
    have b := z.property.1 1
    have c := masses_sum z
    dsimp [baseMass,zeroMass,oneMass,infMass] at e c
    apply Subtype.ext; funext i; fin_cases i
    · change z.val 0=1; linarith
    · change z.val 1=0; linarith
    · change z.val 2=0; linarith
  · rintro rfl; change (0:ℝ)+0=0; ring

theorem boundary_imag_zero (z : Triangle) {j : Fin 3} (h : z.val j=0) : imagNum z=0 := by
  dsimp [imagNum,zeroMass,oneMass,infMass]
  fin_cases j
  · change z.val 0=0 at h; simp [h]
  · change z.val 1=0 at h; simp [h]
  · change z.val 2=0 at h; simp [h]

theorem affine_continuousAt (b : Bool) {z : Triangle} (h : baseMass z≠0) :
    ContinuousAt (affinePoint b) z := by
  have coord (i : Fin 3) : Continuous (fun x : Triangle => x.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  have hb : Continuous baseMass := (coord 2).add (coord 1)
  have hr : Continuous realNum := ((coord 1).mul hb).add ((coord 0).mul ((coord 1).sub (coord 2)))
  have hi : Continuous imagNum := continuous_const.mul (((coord 2).mul (coord 1)).mul (coord 0)).sqrt
  exact Complex.equivRealProdCLM.symm.continuous.continuousAt.comp
    ((hr.continuousAt.div (hb.pow 2).continuousAt (pow_ne_zero _ h)).prodMk
      ((continuousAt_const.mul hi.continuousAt).div (hb.pow 2).continuousAt (pow_ne_zero _ h)))

end
end AK14.Gluing
