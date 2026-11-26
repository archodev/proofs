import Mathlib.Topology.Covering.Basic
import Mathlib.Order.Filter.Finite

/-! A finite continuous system of distinct local sections exhausting each fiber
makes an actual covering map in mathlib's topological sense. -/
namespace AK14
open Filter Topology Set
open Bundle
noncomputable section
variable {X Y D : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    [TopologicalSpace D] [DiscreteTopology D] [Finite D] [Nonempty D]

theorem finite_sections_trivialization (p : X → Y) (cp : Continuous p) (V : Set Y) (op : IsOpen V)
    (s : D → Y → X) (cont : ∀ i, ContinuousOn (s i) V)
    (sect : ∀ i y, y∈V → p (s i y)=y)
    (enumerate : ∀ x, p x∈V → ∃! i, s i (p x)=x) :
    ∃ e : Trivialization D p, e.baseSet=V := by
  classical
  let label (x : X) : D := if hx : p x∈V then (enumerate x hx).choose else Classical.arbitrary D
  have lab (x : X) (hx : p x∈V) : s (label x) (p x)=x := by
    simpa only [label,dif_pos hx] using (enumerate x hx).choose_spec.1
  have uniq (x : X) (hx : p x∈V) (i : D) (hi : s i (p x)=x) : i=label x := by
    simpa only [label,dif_pos hx] using (enumerate x hx).choose_spec.2 i hi
  have continuous_label : ContinuousOn label (p ⁻¹' V) := by
    intro x hx
    have neighborhood := (op.preimage cp).mem_nhds hx
    have each (i : D) : ∀ᶠ t in 𝓝 x, i≠label x → s i (p t)≠t := by
      by_cases e : i=label x
      · exact Filter.Eventually.of_forall fun _ h => (h e).elim
      have ne : s i (p x)≠x := fun eq => e (uniq x hx i eq)
      have cs := ((cont i).continuousAt (op.mem_nhds hx)).comp cp.continuousAt
      exact ((cs.ne_iff_eventually_ne continuousAt_id).mp ne).mono fun _ h _ => h
    have all := Filter.eventually_all.mpr each
    apply ContinuousAt.continuousWithinAt
    apply (show ContinuousAt (fun _ : X => label x) x from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [neighborhood,all] with t ht h
    by_contra e
    exact h (label t) e (lab t ht)
  let e : Trivialization D p :=
    { toFun := fun x => (p x,label x)
      invFun := fun v => s v.2 v.1
      source := p ⁻¹' V
      target := V ×ˢ univ
      map_source' := fun _ h => ⟨h,trivial⟩
      map_target' := fun v hv => by change p (s v.2 v.1)∈V; rw [sect _ _ hv.1]; exact hv.1
      left_inv' := lab
      right_inv' := by
        intro v hv
        have right := sect v.2 v.1 hv.1
        apply Prod.ext right
        have mem : p (s v.2 v.1)∈V := right.symm ▸ hv.1
        exact (uniq (s v.2 v.1) mem v.2 (by rw [right])).symm
      open_source := op.preimage cp
      open_target := op.prod isOpen_univ
      continuousOn_toFun := cp.continuousOn.prodMk continuous_label
      continuousOn_invFun := by
        apply continuousOn_prod_of_discrete_right.mpr
        intro i
        simpa using cont i
      baseSet := V
      open_baseSet := op
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ => rfl }
  exact ⟨e,rfl⟩

theorem covering_of_finite_sections (p : X → Y) (cp : Continuous p)
    (charts : ∀ b : Y, ∃ V : Set Y, IsOpen V ∧ b∈V ∧ ∃ s : D → Y → X,
      (∀ i, ContinuousOn (s i) V) ∧ (∀ i y, y∈V → p (s i y)=y) ∧
      ∀ x, p x∈V → ∃! i, s i (p x)=x) : IsCoveringMap p := by
  intro b
  obtain ⟨V,op,mem,s,cont,sect,all⟩ := charts b
  obtain ⟨e,rfl⟩ := finite_sections_trivialization p cp V op s cont sect all
  exact (show IsEvenlyCovered p b D from .of_trivialization mem).to_isEvenlyCovered_preimage

end
end AK14
