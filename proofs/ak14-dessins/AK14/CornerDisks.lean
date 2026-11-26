import AK14.CornerRoot

namespace AK14.Gluing
open Complex Set Topology
noncomputable section

def radialLeft (j : Fin 3) (z : Triangle) := 2*(oneMass (frame j z)+infMass (frame j z))
def radialRight (j : Fin 3) (z : Triangle) := baseMass (frame j z)

theorem radial_forces_star {j : Fin 3} {z : Triangle} (h : radialLeft j z≤radialRight j z) : 0<z.val (opposite j) := by
  have total := masses_sum (frame j z)
  have b : 0≤oneMass (frame j z) := (frame j z).property.1 1
  have c : 0 ≤ infMass (frame j z) := (frame j z).property.1 0
  dsimp only [radialLeft,radialRight,baseMass] at h
  rw [←frame_zeroMass]; linarith

theorem radialLeft_cont (j : Fin 3) : Continuous (radialLeft j) :=
  continuous_const.mul ((coord_cont (negativeEdge j)).add (coord_cont (positiveEdge j)))
theorem radialRight_cont (j : Fin 3) : Continuous (radialRight j) := by
  change Continuous (fun z => zeroMass (frame j z)+oneMass (frame j z))
  simpa only [frame_zeroMass,frame_oneMass] using (coord_cont (opposite j)).add (coord_cont (negativeEdge j))

theorem cornerEdge_zero (j : Fin 3) : (vertex j).val (positiveEdge j)=0 := by
  exact Pi.single_eq_of_ne (by fin_cases j <;> decide : positiveEdge j≠opposite j) _

theorem anchored_index {n : ℕ} (T : Triple n) (j : Fin 3) (q : Tri n) :
    cell T q (vertex j)=cell T (true,cornerIndex T j q) (vertex j) := by
  obtain ⟨b,i⟩ := q; cases b
  · exact glue_edge T _ _ _ (cornerEdge_zero j)
  · rfl

def anchorAt {n : ℕ} (T : Triple n) (j : Fin 3) : Surface T → Option (Surface T) :=
  Quot.lift (fun u : Cell n => if 0<u.2.val (opposite j) then some (cell T u.1 (vertex j)) else none) (by
    rintro ⟨q,z⟩ ⟨r,w⟩ ⟨k,h,m,s⟩
    change z=w at h; change step T k q=r at s; change z.val k=0 at m; subst w; subst r
    dsimp only; split_ifs with pos
    · apply congrArg some
      apply glue_edge
      have ne : k≠opposite j := fun hk => pos.ne' (hk ▸ m)
      exact Pi.single_eq_of_ne ne _
    · rfl)

def closedSheet {n : ℕ} (T : Triple n) (j : Fin 3) (x : Fin n) : Set (Surface T) :=
  {y | radialLeft j (barycentric T y)≤radialRight j (barycentric T y) ∧
    anchorAt T j y=some (cell T (true,x) (vertex j))}

def openSheet {n : ℕ} (T : Triple n) (j : Fin 3) (x : Fin n) : Set (Surface T) :=
  {y | radialLeft j (barycentric T y)<radialRight j (barycentric T y) ∧
    anchorAt T j y=some (cell T (true,x) (vertex j))}

theorem anchor_cell_iff {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n)
    (q : Tri n) {z : Triangle} (pos : 0<z.val (opposite j)) :
    anchorAt T j (cell T q z)=some (cell T (true,x) (vertex j)) ↔ (T j).SameCycle x (cornerIndex T j q) := by
  change (if 0<z.val (opposite j) then some (cell T q (vertex j)) else none)=_ ↔ _
  rw [if_pos pos,Option.some.injEq,anchored_index,corner_cell_eq_iff T pr]
  exact ⟨Equiv.Perm.SameCycle.symm,Equiv.Perm.SameCycle.symm⟩

theorem closedSheet_cell {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n)
    (q : Tri n) (z : Triangle) :
    cell T q z∈closedSheet T j x ↔ radialLeft j z≤radialRight j z ∧ (T j).SameCycle x (cornerIndex T j q) := by
  change (_ ∧ _) ↔ _
  by_cases h : radialLeft j z≤radialRight j z
  · exact and_congr_right (fun _ => anchor_cell_iff T pr j x q (radial_forces_star h))
  · exact ⟨fun k => (h k.1).elim,fun k => (h k.1).elim⟩

theorem openSheet_cell {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n)
    (q : Tri n) (z : Triangle) :
    cell T q z∈openSheet T j x ↔ radialLeft j z<radialRight j z ∧ (T j).SameCycle x (cornerIndex T j q) := by
  change (_ ∧ _) ↔ _
  by_cases h : radialLeft j z<radialRight j z
  · exact and_congr_right (fun _ => anchor_cell_iff T pr j x q (radial_forces_star h.le))
  · exact ⟨fun k => (h k.1).elim,fun k => (h k.1).elim⟩

theorem closedSheet_closed {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n) :
    IsClosed (closedSheet T j x) := by
  apply isQuotientMap_quot_mk.isClosed_preimage.mp
  have eq : Quot.mk (seam T) ⁻¹' closedSheet T j x =
    Prod.snd ⁻¹' {z | radialLeft j z≤radialRight j z} ∩ Prod.fst ⁻¹' {q | (T j).SameCycle x (cornerIndex T j q)} := by
    ext ⟨q,z⟩; exact closedSheet_cell T pr j x q z
  rw [eq]
  exact ((isClosed_le (radialLeft_cont j) (radialRight_cont j)).preimage continuous_snd).inter
    ((isClosed_discrete _).preimage continuous_fst)

theorem openSheet_open {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n) :
    IsOpen (openSheet T j x) := by
  apply isQuotientMap_quot_mk.isOpen_preimage.mp
  have eq : Quot.mk (seam T) ⁻¹' openSheet T j x =
    Prod.snd ⁻¹' {z | radialLeft j z<radialRight j z} ∩ Prod.fst ⁻¹' {q | (T j).SameCycle x (cornerIndex T j q)} := by
    ext ⟨q,z⟩; exact openSheet_cell T pr j x q z
  rw [eq]
  exact ((isOpen_lt (radialLeft_cont j) (radialRight_cont j)).preimage continuous_snd).inter
    ((isOpen_discrete _).preimage continuous_fst)

theorem radius_bound {j : Fin 3} {z : Triangle} (b : Bool) (nz : baseMass (frame j z)≠0) :
    (radialLeft j z≤radialRight j z ↔ ‖cornerValue j b z‖≤1/2) ∧
    (radialLeft j z<radialRight j z ↔ ‖cornerValue j b z‖<1/2) := by
  rw [cornerValue,affine_norm nz]
  constructor
  · rw [div_le_iff₀ (baseMass_pos nz)]; unfold radialLeft radialRight; constructor <;> intro h <;> linarith
  · rw [div_lt_iff₀ (baseMass_pos nz)]; unfold radialLeft radialRight; constructor <;> intro h <;> linarith

end
end AK14.Gluing
