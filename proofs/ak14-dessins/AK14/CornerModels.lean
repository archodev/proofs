import AK14.CornerCharts

namespace AK14.Gluing
open Complex Set Topology
open scoped OnePoint
noncomputable section

def branchModel (j : Fin 3) (w : ℂ) : OnePoint ℂ :=
  ![(w : OnePoint ℂ),((1-w:ℂ) : OnePoint ℂ),if w=0 then ∞ else ((w⁻¹:ℂ) : OnePoint ℂ)] j

theorem location_reflected (w : ℂ) : frame 1 (location w)=location (1-w) := by
  have oth : (1-w)-1= -w := by ring
  have per : perimeter (1-w)=perimeter w := by rw [perimeter,oth,norm_neg,norm_sub_rev]; unfold perimeter; ring
  apply Subtype.ext; funext i; fin_cases i
  · change (‖w‖+‖w-1‖-1)/_=(‖1-w‖+‖(1-w)-1‖-1)/_
    rw [per,oth,norm_neg,norm_sub_rev]; ring
  · change (‖w-1‖+1-‖w‖)/_=(‖1-w‖+1-‖(1-w)-1‖)/_
    rw [per,oth,norm_neg,norm_sub_rev]
  · change (‖w‖+1-‖w-1‖)/_=(‖(1-w)-1‖+1-‖1-w‖)/_
    rw [per,oth,norm_neg,norm_sub_rev]

theorem location_reciprocal {w : ℂ} (nz : w≠0) : frame 2 (location w)=location w⁻¹ := by
  have rn := norm_ne_zero_iff.mpr nz
  have oth : ‖w⁻¹-1‖=‖w-1‖/‖w‖ := by
    rw [←norm_sub_rev,←norm_div]; congr 1; field_simp [nz]
  have per : perimeter w⁻¹=perimeter w/‖w‖ := by
    unfold perimeter; rw [norm_inv,oth]; field_simp [rn]; ring
  have P := (perimeter_pos w).ne'
  apply Subtype.ext; funext i; fin_cases i
  · change (‖w-1‖+1-‖w‖)/_=(‖w⁻¹‖+‖w⁻¹-1‖-1)/_
    rw [per,oth,norm_inv]; field_simp [rn,P]; ring
  · change (‖w‖+1-‖w-1‖)/_=(‖w⁻¹‖+1-‖w⁻¹-1‖)/_
    rw [per,oth,norm_inv]; field_simp [rn,P]; ring
  · change (‖w‖+‖w-1‖-1)/_=(‖w⁻¹-1‖+1-‖w⁻¹‖)/_
    rw [per,oth,norm_inv]; field_simp [rn,P]; ring

theorem spherePoint_framed (j : Fin 3) (b : Bool) (w : ℂ)
    (side : 0≤sideSign (frameSide j b)*w.im) :
    spherePoint b (frame j (location w))=branchModel j w := by
  fin_cases j
  · change spherePoint b (frame 0 (location w))=(w:OnePoint ℂ)
    have a : frame 0 (location w)=location w := by apply Subtype.ext; funext i; fin_cases i <;> rfl
    rw [a]; exact spherePoint_location side
  · change spherePoint b (frame 1 (location w))=((1-w:ℂ):OnePoint ℂ)
    rw [location_reflected]; apply spherePoint_location
    cases b <;> simp [frameSide,sideSign,Fin.ext_iff] at side ⊢ <;> linarith
  · change spherePoint b (frame 2 (location w))=(if w=0 then ∞ else ((w⁻¹:ℂ) : OnePoint ℂ))
    split_ifs with zero
    · subst w
      have id : frame 2 (vertex 0)=vertex 2 := by rw [←frame_vertex 2,frame_frame]
      rw [finite_location_zero,id,spherePoint,if_pos ((inf_vertex_iff _).mpr rfl)]
    · rw [location_reciprocal zero]; apply spherePoint_location
      rw [Complex.inv_im]
      cases b <;> simp [frameSide,sideSign,Fin.ext_iff] at side ⊢
      · exact div_nonneg (neg_nonneg.mpr side) (Complex.normSq_nonneg _)
      · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr side) (Complex.normSq_nonneg _)

theorem chart_represents_projection {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n)
    {y : Surface T} (hy : y∈(cornerChart T pr j x).source) :
    gluedMap T y=branchModel j ((cornerChart T pr j x y)^(degreeAt T j x)) := by
  induction y using Quot.ind with | _ u =>
    obtain ⟨q,z⟩ := u
    change gluedMap T (cell T q z)=branchModel j ((cornerChart T pr j x (cell T q z))^(degreeAt T j x))
    rw [cornerChart_power T pr j x q z hy]
    have pos := closedSheet_star T j x (openSheet_closedSheet T j x hy)
    change 0<z.val (opposite j) at pos
    have loc := location_affine (frameSide j q.1) (frame_base_ne pos)
    have hz : frame j (location (cornerValue j q.1 z))=z := by
      change frame j (location (affinePoint _ _))=z; rw [loc,frame_frame]
    change spherePoint q.1 z=_
    conv_lhs => rw [←hz]
    exact spherePoint_framed j q.1 _ (chosen_side (frame j z) (frameSide j q.1))

end
end AK14.Gluing
