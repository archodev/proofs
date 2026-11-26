import AK14.CornerChartBijection
import Mathlib.Topology.OpenPartialHomeomorph

namespace AK14.Gluing
open Complex Set Topology
noncomputable section

def closedPowerDisk (d : ℕ) : Set ℂ := {z | ‖z^d‖≤1/2}
def openPowerDisk (d : ℕ) : Set ℂ := {z | ‖z^d‖<1/2}

theorem powerDisk_subset (d : ℕ) : openPowerDisk d⊆closedPowerDisk d :=
  fun _ h => (show ‖_^d‖<1/2 from h).le

theorem closedSheet_star {n : ℕ} (T : Triple n) (j : Fin 3) (x : Fin n) : closedSheet T j x⊆cornerStar T j :=
  fun _ h => radial_forces_star h.1

theorem openSheet_closedSheet {n : ℕ} (T : Triple n) (j : Fin 3) (x : Fin n) : openSheet T j x⊆closedSheet T j x :=
  fun _ h => ⟨h.1.le,h.2⟩

theorem root_power_cell {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n)
    (q : Tri n) (z : Triangle) (h : cell T q z ∈ closedSheet T j x) :
    cornerRoot T pr j x (cell T q z)^(degreeAt T j x)=cornerValue j q.1 z := by
  obtain ⟨rad,orbit⟩ := (closedSheet_cell T pr j x q z).mp h
  rw [root_cell T pr j x q (radial_forces_star rad),sector_power T j x q z orbit]

theorem root_disk {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n)
    {y : Surface T} (inside : y∈closedSheet T j x) :
    cornerRoot T pr j x y∈closedPowerDisk (degreeAt T j x) ∧
    (y∈openSheet T j x ↔ cornerRoot T pr j x y∈openPowerDisk (degreeAt T j x)) := by
  induction y using Quot.ind with | _ u =>
    obtain ⟨q,z⟩ := u
    obtain ⟨bound,orb⟩ := (closedSheet_cell T pr j x q z).mp inside
    have rad := radius_bound q.1 (frame_base_ne (radial_forces_star bound))
    change ‖cornerRoot T pr j x (cell T q z)^_‖≤_ ∧ (cell T q z∈openSheet T j x ↔ ‖cornerRoot T pr j x (cell T q z)^_‖<_)
    rw [root_power_cell T pr j x q z inside,openSheet_cell, and_iff_left orb]
    exact ⟨rad.1.mp bound,rad.2⟩
    exact pr

def closedCornerHomeo {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n) :
    closedSheet T j x ≃ₜ closedPowerDisk (degreeAt T j x) := by
  letI := surface_compact T
  letI := isCompact_iff_compactSpace.mp (closedSheet_closed T pr j x).isCompact
  let F (y : closedSheet T j x) : closedPowerDisk (degreeAt T j x) :=
    ⟨cornerRoot T pr j x y.val,(root_disk T pr j x y.property).1⟩
  let e := Equiv.ofBijective F ⟨fun a b h => Subtype.ext
    (cornerRoot_injOn T pr j x a.property b.property (congrArg Subtype.val h)),by
    rintro ⟨v,hv⟩
    obtain ⟨y,hy,eq⟩ := cornerRoot_surj T pr j x v hv
    exact ⟨⟨y,hy⟩,Subtype.ext eq⟩⟩
  exact Continuous.homeoOfEquivCompactToT2 (f:=e) (Continuous.subtype_mk
    (continuousOn_iff_continuous_restrict.mp ((cornerRoot_continuous T pr j x).mono (closedSheet_star T j x))) _)

@[simp] theorem closedCornerHomeo_val {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n)
    (y : closedSheet T j x) : (closedCornerHomeo T pr j x y).val=cornerRoot T pr j x y.val := rfl

/-- A complex coordinate on an open neighborhood of a specified cycle, in every degree. -/
def cornerChart {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n) :
    OpenPartialHomeomorph (Surface T) ℂ := by
  classical
  let E := closedCornerHomeo T pr j x
  let d := degreeAt T j x
  let back (v : ℂ) : Surface T := if h : v∈closedPowerDisk d then (E.symm ⟨v,h⟩).val else cell T (true,x) (vertex j)
  have back_eq (v : ℂ) (h : v∈closedPowerDisk d) : back v=(E.symm ⟨v,h⟩).val := dif_pos h
  have right (v : ℂ) (h : v∈closedPowerDisk d) : cornerRoot T pr j x (back v)=v := by
    rw [back_eq v h]; exact congrArg Subtype.val (E.apply_symm_apply ⟨v,h⟩)
  refine { toFun := cornerRoot T pr j x, invFun := back, source := openSheet T j x,
           target := openPowerDisk d, open_source := openSheet_open T pr j x,
           open_target := isOpen_lt (continuous_id.pow d).norm continuous_const,
           continuousOn_toFun := (cornerRoot_continuous T pr j x).mono ((openSheet_closedSheet T j x).trans (closedSheet_star T j x)),
           map_source' := fun {y} h => (root_disk T pr j x (openSheet_closedSheet T j x h)).2.mp h,
           map_target' := ?_, left_inv' := ?_, right_inv' := fun {v} h => right v (powerDisk_subset d h),
           continuousOn_invFun := ?_ }
  · intro v hv
    have hc : v∈closedPowerDisk d := powerDisk_subset d hv
    have B : back v∈closedSheet T j x := (back_eq v hc).symm ▸ (E.symm ⟨v,hc⟩).property
    exact (root_disk T pr j x B).2.mpr (by rw [right _ hc]; exact hv)
  · intro y hy
    let Y : closedSheet T j x := ⟨y,openSheet_closedSheet T j x hy⟩
    change back (E Y).val=y
    rw [back_eq _ (E Y).property]; exact congrArg Subtype.val (E.symm_apply_apply Y)
  · apply continuousOn_iff_continuous_restrict.mpr
    let inc (v : openPowerDisk d) : closedPowerDisk d := ⟨v.val,powerDisk_subset d v.property⟩
    have ci : Continuous inc := continuous_subtype_val.subtype_mk _
    have h := continuous_subtype_val.comp (E.symm.continuous.comp ci)
    exact h.congr (fun v => (back_eq v.val (inc v).property).symm)

theorem corner_mem_chart {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n) :
    cell T (true,x) (vertex j)∈(cornerChart T pr j x).source := by
  apply (openSheet_cell T pr j x _ _).mpr
  refine ⟨?_,Equiv.Perm.SameCycle.rfl⟩
  unfold radialLeft radialRight
  rw [frame_vertex]; change 2*((0:ℝ)+0)<1+0; norm_num

theorem cornerChart_power {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n)
    (q : Tri n) (z : Triangle) (h : cell T q z∈(cornerChart T pr j x).source) :
    (cornerChart T pr j x (cell T q z))^(degreeAt T j x)=cornerValue j q.1 z :=
  root_power_cell T pr j x q z (openSheet_closedSheet T j x h)

end
end AK14.Gluing
