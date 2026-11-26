import AK14.TriangleGluing

/-! Counts the actual corner orbits, with singleton orbits included. -/
namespace AK14.Gluing
open Equiv
noncomputable section

abbrev Corners {n : ℕ} (t : Perm (Fin n)) := Quotient (Perm.SameCycle.setoid t)
abbrev CornerLabels {n : ℕ} (t : Perm (Fin n)) := Function.fixedPoints t ⊕ ↥t.cycleFactorsFinset

private def label {n : ℕ} (t : Perm (Fin n)) (x : Fin n) : CornerLabels t := by
  classical
  exact if h : t x=x then Sum.inl ⟨x,h⟩ else
    Sum.inr ⟨t.cycleOf x,(Perm.cycleOf_mem_cycleFactorsFinset_iff).mpr (Perm.mem_support.mpr h)⟩

private theorem label_iff {n : ℕ} (t : Perm (Fin n)) (x y : Fin n) :
    label t x=label t y ↔ t.SameCycle x y := by
  classical
  by_cases hx : t x=x <;> by_cases hy : t y=y
  · simp only [label,dif_pos hx,dif_pos hy,Sum.inl.injEq,Subtype.mk.injEq]
    exact ⟨fun h => h ▸ Perm.SameCycle.refl t _,fun h => h.eq_of_left hx⟩
  · simp only [label,dif_pos hx,dif_neg hy,Sum.inl_ne_inr,false_iff]
    exact fun h => hy (h.apply_eq_self_iff.mp hx)
  · simp only [label,dif_neg hx,dif_pos hy,Sum.inr_ne_inl,false_iff]
    exact fun h => hx (h.apply_eq_self_iff.mpr hy)
  · simp only [label,dif_neg hx,dif_neg hy,Sum.inr.injEq,Subtype.mk.injEq]
    exact (Perm.sameCycle_iff_cycleOf_eq_of_mem_support (Perm.mem_support.mpr hx) (Perm.mem_support.mpr hy)).symm

def cornerEquiv {n : ℕ} (t : Perm (Fin n)) : Corners t ≃ CornerLabels t := by
  classical
  let q : Corners t → CornerLabels t := Quotient.lift (label t) (fun x y => (label_iff t x y).mpr)
  refine Equiv.ofBijective q ⟨?_,?_⟩
  · intro a b
    induction a using Quotient.inductionOn with | _ x =>
      induction b using Quotient.inductionOn with | _ y =>
        exact fun e => Quotient.sound ((label_iff t x y).mp e)
  · intro b
    rcases b with ⟨x,h⟩ | ⟨c,hc⟩
    · change t x=x at h
      exact ⟨Quotient.mk _ x,by change label t x=_; simp [label,h]⟩
    · obtain ⟨x,hx⟩ := (Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
      have e := Perm.cycle_is_cycleOf hx hc
      have nx : t x≠x := by
        intro z
        have c1 : c=1 := e.trans ((Perm.cycleOf_eq_one_iff t).mpr z)
        simp [c1] at hx
      refine ⟨Quotient.mk _ x,?_⟩
      change label t x=_
      simp [label,nx,e]

theorem vertex_count {n : ℕ} (t : Perm (Fin n)) : Nat.card (Corners t)=(fullType t).card := by
  classical
  rw [Nat.card_congr (cornerEquiv t),Nat.card_eq_fintype_card,Fintype.card_sum,
    fixedPointCount,Fintype.card_coe]
  rw [fullType,Multiset.card_add,Multiset.card_replicate,add_comm]
  congr 1
  rw [Perm.cycleType_def,Multiset.card_map]
  rfl

abbrev Vertices {n : ℕ} (T : Triple n) := Corners (T 0) ⊕ Corners (T 1) ⊕ Corners (T 2)
abbrev Edges (n : ℕ) := Fin 3 × Fin n

theorem gluing_euler {p : Passport} {n : ℕ} (hp : p.Admissible n) {T : Triple n} (hT : Realizes p T) :
    (Nat.card (Vertices T) : ℤ)-Nat.card (Edges n)+Nat.card (Tri n)=2 := by
  have hv (i : Fin 3) : Nat.card (Corners (T i))=(p.rows i).card := (vertex_count _).trans (congrArg Multiset.card (hT.cycles i))
  have h := hp.sphere
  simp only [Vertices,Edges,Tri,Nat.card_sum,Nat.card_prod,hv]
  simp only [Nat.card_eq_fintype_card,Fintype.card_fin,Fintype.card_bool]
  omega

end
end AK14.Gluing
