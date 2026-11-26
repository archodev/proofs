import AK14.SphereProjection
import AK14.StandardLoops

/-! Realization of the specific complex peripheral circles on the glued
surface, using one numbering over 1/2 and right-to-left composition. -/
namespace AK14.Gluing
open Complex Set Topology
open scoped OnePoint unitInterval
open SeriesAt (basePoint circleZero circleOne circleInfinity standardLoops)
noncomputable section

def loopSheet {n : ℕ} (T : Triple n) (i : Fin n) : Surface T := cell T (true,i) (location basePoint)

private theorem location_base_edge : (location basePoint).val 0=0 := by
  change (‖basePoint‖+‖basePoint-1‖-1)/_=0
  have h : basePoint-1= -(1/2:ℂ) := by unfold basePoint; ring
  rw [h]; norm_num [basePoint,norm_div]

private theorem circle_mid (t : I) (h : (t:ℝ)=1/2) : circleZero t= -(1/2:ℂ) := by
  change Complex.exp (((2*Real.pi*(t:ℝ):ℝ):ℂ)*Complex.I)/2=_
  rw [h,show 2*Real.pi*(1/2)=Real.pi by ring,Complex.exp_pi_mul_I]
  ring

private theorem negative_edge : (location (-(1/2:ℂ))).val 1=0 := by
  change (‖-(1/2:ℂ)‖+1-‖-(1/2:ℂ)-1‖)/_=0
  rw [show -(1/2:ℂ)-1= -(3/2:ℂ) by norm_num]
  norm_num [norm_div]

private theorem right_edge : (location (1+(1/2:ℂ))).val 2=0 := by
  change (‖1+1/2-(1:ℂ)‖+1-‖1+(1/2:ℂ)‖)/_=0
  rw [show 1+1/2-(1:ℂ)=1/2 by ring,show 1+(1/2:ℂ)=3/2 by norm_num]
  norm_num [norm_div]

private def faceTrace {n : ℕ} (T : Triple n) (q : Tri n) {x y : ℂ} (P : Path x y) : C(I,Surface T) :=
  ⟨fun t => cell T q (location (P t)),(cell_cont T q).comp (location_continuous.comp P.continuous)⟩

private theorem circle_sides (t : I) :
    ((t:ℝ)≤1/2 → 0≤(circleZero t).im) ∧ (1/2≤(t:ℝ) → (circleZero t).im≤0) := by
  let θ := 2*Real.pi*(t:ℝ)
  have im : (circleZero t).im=Real.sin θ/2 := by
    change (Complex.exp ((θ:ℂ)*Complex.I)/(2:ℂ)).im=_
    rw [Complex.exp_mul_I]
    simp [Complex.div_im,Complex.sin_ofReal_re]
  rw [im]
  have nonneg : 0≤θ := mul_nonneg (by positivity) t.property.1
  have up : θ≤2*Real.pi := by dsimp [θ]; nlinarith [mul_nonneg (Real.pi_pos.le) (sub_nonneg.mpr t.property.2)]
  constructor
  · intro m; exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi nonneg (by dsimp [θ]; nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr m)])) (by norm_num)
  · intro m
    have h : Real.pi≤θ := by dsimp [θ]; nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr m)]
    have a := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤θ-Real.pi by linarith) (show θ-Real.pi≤Real.pi by linarith)
    rw [Real.sin_sub_pi] at a
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

private theorem seam_zero {n : ℕ} (T : Triple n) (k : Fin n) :
    cell T (false,k) (location basePoint)=loopSheet T k := by
  simpa [step,crossing,loopSheet] using glue_edge T (false,k) (location basePoint) 0 location_base_edge

def standardZeroLift {n : ℕ} (T : Triple n) (i : Fin n) : Path (loopSheet T i) (loopSheet T (T 0 i)) where
  toFun t := if (t:ℝ)≤1/2 then faceTrace T (false,i) circleZero t else faceTrace T (true,T 0 i) circleZero t
  continuous_toFun := by
    apply Continuous.if_le (faceTrace T _ circleZero).continuous (faceTrace T _ circleZero).continuous
      continuous_subtype_val continuous_const
    intro t mid
    change cell T _ (location (circleZero t))=cell T _ _
    rw [circle_mid t mid]
    simpa [step,crossing] using glue_edge T (false,i) _ 1 negative_edge
  source' := by simp [faceTrace,circleZero.source,seam_zero]
  target' := by norm_num [faceTrace,circleZero.target,loopSheet]

def standardOneLift {n : ℕ} (T : Triple n) (i : Fin n) : Path (loopSheet T i) (loopSheet T (T 1 i)) where
  toFun t := if (t:ℝ)≤1/2 then faceTrace T (true,i) circleOne t else faceTrace T (false,T 1 i) circleOne t
  continuous_toFun := by
    apply Continuous.if_le (faceTrace T _ circleOne).continuous (faceTrace T _ circleOne).continuous
      continuous_subtype_val continuous_const
    intro t mid
    change cell T _ (location (1-circleZero t))=cell T _ (location (1-circleZero t))
    rw [circle_mid t mid,sub_neg_eq_add]
    simpa [step,crossing] using glue_edge T (true,i) _ 2 right_edge
  source' := by simp [faceTrace,circleOne.source,loopSheet]
  target' := by norm_num [faceTrace,circleOne.target,seam_zero]

theorem zeroLift_projects {n : ℕ} (T : Triple n) (i : Fin n) (t : I) :
    gluedMap T (standardZeroLift T i t)=(circleZero t : OnePoint ℂ) := by
  change gluedMap T (if (t:ℝ)≤1/2 then _ else _) = _
  split
  · rename_i m; exact spherePoint_location (b:=false) (by simpa [sideSign] using (circle_sides t).1 m)
  · rename_i m; exact spherePoint_location (b:=true) (by simpa [sideSign] using (circle_sides t).2 (le_of_not_ge m))

theorem oneLift_projects {n : ℕ} (T : Triple n) (i : Fin n) (t : I) :
    gluedMap T (standardOneLift T i t)=(circleOne t : OnePoint ℂ) := by
  have im : (circleOne t).im= -(circleZero t).im := by change (1-circleZero t).im=_; simp
  change gluedMap T (if (t:ℝ)≤1/2 then _ else _) = _
  split
  · rename_i m; exact spherePoint_location (b:=true) (by simpa [sideSign,im] using (circle_sides t).1 m)
  · rename_i m; exact spherePoint_location (b:=false) (by simpa [sideSign,im] using (circle_sides t).2 (le_of_not_ge m))

end
end AK14.Gluing
