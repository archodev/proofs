import AK14.SphereHomeomorph

namespace AK14.Gluing
open Complex Set Topology
open scoped OnePoint
noncomputable section

theorem location_continuous : Continuous location := by
  have cp : Continuous perimeter := (continuous_norm.add ((continuous_id.sub continuous_const).norm)).add continuous_const
  apply Continuous.subtype_mk; apply continuous_pi; intro i
  fin_cases i
  · exact ((continuous_norm.add ((continuous_id.sub continuous_const).norm)).sub continuous_const).div cp
      (fun w => (perimeter_pos w).ne')
  · exact ((continuous_norm.add continuous_const).sub ((continuous_id.sub continuous_const).norm)).div cp
      (fun w => (perimeter_pos w).ne')
  · exact ((((continuous_id.sub continuous_const).norm.add continuous_const).sub continuous_norm)).div cp
      (fun w => (perimeter_pos w).ne')

theorem spherePoint_location {w : ℂ} {b : Bool} (s : 0≤sideSign b*w.im) :
    spherePoint b (location w)=(w : OnePoint ℂ) := by
  have h : baseMass (location w)≠0 := by
    rw [location_base]; exact div_ne_zero (by norm_num) (perimeter_pos w).ne'
  simp only [spherePoint,h,if_false,OnePoint.coe_eq_coe]
  obtain ⟨ra,rb⟩ := location_norms w b
  apply determined_by_distances ra rb
  have p := chosen_side (location w) b
  cases b
  · simp [sideSign] at s p ⊢; exact mul_nonneg p s
  · simp [sideSign] at s p ⊢; exact mul_nonneg_of_nonpos_of_nonpos p s

def gluedMap {n : ℕ} (T : Triple n) (x : Surface T) : OnePoint ℂ :=
  complexTarget (coveringProjection T x)

theorem gluedMap_continuous {n : ℕ} (T : Triple n) : Continuous (gluedMap T) :=
  complexTarget.continuous.comp (projection_continuous T)

end
end AK14.Gluing
