import AK14.SphereCoordinates

namespace AK14.Gluing
open Complex Set Filter Topology Bornology
open scoped OnePoint
noncomputable section

def perimeter (w : ℂ) : ℝ := ‖w‖+‖w-1‖+1

theorem perimeter_pos (w : ℂ) : 0<perimeter w := by unfold perimeter; positivity

def location (w : ℂ) : Triangle := by
  let r := ‖w‖
  let s := ‖w-1‖
  have rle : r≤s+1 := by simpa [r,s] using norm_add_le (w-1) (1:ℂ)
  have sle : s≤r+1 := by simpa [s,r] using norm_sub_le w (1:ℂ)
  have one_le : 1≤r+s := by
    have h := norm_sub_le w (w-1)
    simpa [r,s] using h
  let L := perimeter w
  have pos : 0<L := perimeter_pos w
  refine ⟨![(r+s-1)/L,(r+1-s)/L,(s+1-r)/L],?_⟩
  constructor
  · intro i; fin_cases i
    · exact div_nonneg (by linarith) pos.le
    · exact div_nonneg (by linarith) pos.le
    · exact div_nonneg (by linarith) pos.le
  · rw [Fin.sum_univ_three]
    change (r+s-1)/L+(r+1-s)/L+(s+1-r)/L=1
    field_simp [pos.ne']
    dsimp [L,perimeter,r,s]
    ring

theorem location_base (w : ℂ) : baseMass (location w)=2/perimeter w := by
  change (‖w-1‖+1-‖w‖)/_+(‖w‖+1-‖w-1‖)/_=_
  ring

theorem location_norms (w : ℂ) (b : Bool) :
    ‖affinePoint b (location w)‖=‖w‖ ∧ ‖affinePoint b (location w)-1‖=‖w-1‖ := by
  have h : baseMass (location w)≠0 := by rw [location_base]; exact div_ne_zero (by norm_num) (perimeter_pos w).ne'
  rw [affine_norm h,affine_sub_norm h,location_base]
  change ((‖w‖+1-‖w-1‖)/_+(‖w‖+‖w-1‖-1)/_)/(2/_)=_ ∧
    ((‖w-1‖+1-‖w‖)/_+(‖w‖+‖w-1‖-1)/_)/(2/_)=_
  constructor <;> field_simp [(perimeter_pos w).ne'] <;> ring

theorem location_affine (b : Bool) {z : Triangle} (h : baseMass z≠0) :
    location (affinePoint b z)=z := by
  let w := affinePoint b z
  have rw' : ‖w‖=(oneMass z+infMass z)/baseMass z := affine_norm h b
  have sw' : ‖w-1‖=(zeroMass z+infMass z)/baseMass z := affine_sub_norm h b
  have per : perimeter w=2/baseMass z := by
    rw [perimeter,rw',sw']; field_simp [h]; dsimp [baseMass]; linarith [masses_sum z]
  apply Subtype.ext; funext j; fin_cases j
  · change (‖w‖+‖w-1‖-1)/perimeter w=infMass z
    rw [per,rw',sw']; field_simp [h]; dsimp [baseMass]; ring
  · change (‖w‖+1-‖w-1‖)/perimeter w=oneMass z
    rw [per,rw',sw']; field_simp [h]; dsimp [baseMass]; ring
  · change (‖w-1‖+1-‖w‖)/perimeter w=zeroMass z
    rw [per,rw',sw']; field_simp [h]; dsimp [baseMass]; ring

theorem determined_by_distances {w u : ℂ} (h : ‖w‖=‖u‖) (g : ‖w-1‖=‖u-1‖)
    (sign : 0≤w.im*u.im) : w=u := by
  have a := congrArg (fun t : ℝ => t^2) h
  have b := congrArg (fun t : ℝ => t^2) g
  dsimp only at a b
  simp only [Complex.sq_norm,Complex.normSq_apply,sub_re,sub_im,one_re,one_im,sub_zero] at a b
  have re : w.re=u.re := by linarith only [a,b]
  apply Complex.ext re
  rw [re] at a
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show w.im^2=u.im^2 by nlinarith only [a]) with p|p
  · exact p
  · nlinarith [sq_nonneg (w.im-u.im)]

theorem chosen_side (z : Triangle) (b : Bool) :
    0≤sideSign b*(affinePoint b z).im := by
  have pos : 0 ≤ imagNum z := by unfold imagNum; positivity
  change 0≤sideSign b*(sideSign b*imagNum z/baseMass z^2)
  cases b with
  | false => simpa [sideSign] using (div_nonneg pos (sq_nonneg (baseMass z)))
  | true => simp [sideSign]; exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr pos) (sq_nonneg _)

def lowerSide (w : ℂ) : Bool := decide (w.im<0)

theorem affine_location (w : ℂ) : affinePoint (lowerSide w) (location w)=w := by
  obtain ⟨a,b⟩ := location_norms w (lowerSide w)
  apply determined_by_distances a b
  have c := chosen_side (location w) (lowerSide w)
  by_cases p : w.im<0
  · simp [lowerSide,p,sideSign] at c ⊢
    exact mul_nonneg_of_nonpos_of_nonpos c p.le
  · simp [lowerSide,p,sideSign] at c ⊢
    exact mul_nonneg c (le_of_not_gt p)

def spherePoint (b : Bool) (z : Triangle) : OnePoint ℂ :=
  if baseMass z=0 then ∞ else (affinePoint b z : OnePoint ℂ)

theorem spherePoint_boundary (q r : Bool) (z : Triangle) {j : Fin 3} (h : z.val j=0) :
    spherePoint q z=spherePoint r z := by
  by_cases nz : baseMass z=0
  · simp [spherePoint,nz]
  · simp only [spherePoint,nz,if_false,OnePoint.coe_eq_coe]
    apply Complex.ext
    · rfl
    change sideSign q*imagNum z/_=sideSign r*imagNum z/_
    simp [boundary_imag_zero z h]

def targetPoint : DoubleTriangle → OnePoint ℂ :=
  Quot.lift (fun u : Cell 1 => spherePoint u.1.1 u.2) (by
    rintro ⟨q,z⟩ ⟨r,w⟩ ⟨j,e,h,_⟩
    change z=w at e; subst w
    exact spherePoint_boundary _ _ _ h)

@[simp] theorem targetPoint_cell (b : Bool) (i : Fin 1) (z : Triangle) :
    targetPoint (cell flatTriple (b,i) z)=spherePoint b z := rfl

end
end AK14.Gluing
