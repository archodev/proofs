import AK14.GluedSpace

/-! Fibers over the actual corner points of the double triangle are exactly the
cycles of the associated branch permutations. -/
namespace AK14.Gluing
open Equiv
noncomputable section

def opposite : Fin 3 → Fin 3 := ![2,1,0]
def vertex (j : Fin 3) : Triangle := ⟨Pi.single (opposite j) 1,single_mem_stdSimplex _ _⟩

theorem incident (j e : Fin 3) : (vertex j).val e=0 ↔ e=first j ∨ e=last j := by
  fin_cases j <;> fin_cases e <;> norm_num [vertex,opposite,first,last,Pi.single_apply] <;> decide

private def positiveSheet {n : ℕ} (T : Triple n) (j : Fin 3) : Tri n → Fin n
  | (true,i) => i
  | (false,i) => (crossing T (first j))⁻¹ i

private def orbitKey {n : ℕ} (T : Triple n) (j : Fin 3) (q : Tri n) : Corners (T j) :=
  Quotient.mk _ (positiveSheet T j q)

private theorem key_first {n : ℕ} (T : Triple n) (j : Fin 3) (q : Tri n) :
    orbitKey T j (step T (first j) q)=orbitKey T j q := by
  obtain ⟨b,i⟩ := q; cases b <;> simp [orbitKey,step,positiveSheet]

private theorem key_last {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (q : Tri n) :
    orbitKey T j (step T (last j) q)=orbitKey T j q := by
  have pos (i : Fin n) : orbitKey T j (step T (last j) (true,i))=orbitKey T j (true,i) := by
    let k := (T j).symm i
    have w := corner_walk T pr j k
    have ki : T j k=i := (T j).apply_symm_apply i
    rw [ki] at w
    rw [← w,step_involution,key_first,w]
    change Quotient.mk _ k=Quotient.mk _ i
    apply Quotient.sound
    exact ⟨1,by simp [ki]⟩
  obtain ⟨b,i⟩ := q
  cases b with
  | true => exact pos i
  | false =>
    let k := (crossing T (last j))⁻¹ i
    have e : step T (last j) (false,i)=(true,k) := rfl
    have r : step T (last j) (true,k)=(false,i) := e ▸ step_involution T (last j) (false,i)
    rw [e,← r]
    exact (pos k).symm

private def vertexKey {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) :
    Surface T → Option (Corners (T j)) :=
  Quot.lift (fun u => if u.2=vertex j then some (orbitKey T j u.1) else none) (by
    rintro a b ⟨e,pt,zero,st⟩
    by_cases h : a.2=vertex j
    · have h' : b.2=vertex j := pt.symm.trans h
      simp only [h,h',if_true,Option.some.injEq,← st]
      rcases (incident j e).mp (h ▸ zero) with rfl | rfl
      · exact (key_first T j a.1).symm
      · exact (key_last T pr j a.1).symm
    · have h' : b.2≠vertex j := pt ▸ h
      simp [h,h'])

theorem corner_cell_eq_iff {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x y : Fin n) :
    cell T (true,x) (vertex j)=cell T (true,y) (vertex j) ↔ (T j).SameCycle x y := by
  constructor
  · intro e
    have h := congrArg (vertexKey T pr j) e
    simp only [vertexKey,cell,Quot.lift_mk,if_true,Option.some.injEq] at h
    exact Quotient.exact h
  · intro h
    obtain ⟨k,rfl⟩ := h.exists_nat_pow_eq
    clear h
    have walk (i : Fin n) : cell T (true,i) (vertex j)=cell T (true,T j i) (vertex j) := by
      have a := glue_edge T (true,i) _ (first j) ((incident j _).mpr (Or.inl rfl))
      have b := glue_edge T (step T (first j) (true,i)) _ (last j) ((incident j _).mpr (Or.inr rfl))
      rw [corner_walk T pr j i] at b
      exact a.trans b
    induction k with
    | zero => rfl
    | succ k ih =>
      exact ih.trans (by simpa only [pow_succ',Perm.mul_apply] using walk ((T j^k) x))

def geometric_corner_fiber {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) :
    Corners (T j) ≃ {u : Surface T // coveringProjection T u=cell flatTriple (true,0) (vertex j)} := by
  let F : Corners (T j) → {u : Surface T // coveringProjection T u=cell flatTriple (true,0) (vertex j)} :=
    Quotient.lift (fun x => ⟨cell T (true,x) (vertex j),rfl⟩)
      (fun _ _ h => Subtype.ext ((corner_cell_eq_iff T pr j _ _).mpr h))
  apply Equiv.ofBijective F
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | _ a =>
      induction b using Quotient.inductionOn with | _ b =>
        exact fun eq => Quotient.sound ((corner_cell_eq_iff T pr j _ _).mp (congrArg Subtype.val eq))
  · rintro ⟨u,hu⟩
    induction u using Quot.ind with | _ a =>
      obtain ⟨⟨b,i⟩,z⟩ := a
      have w : z=vertex j := congrArg (barycentric flatTriple) hu
      subst z
      cases b with
      | true => exact ⟨Quotient.mk _ i,rfl⟩
      | false =>
        let k := (crossing T (first j))⁻¹ i
        refine ⟨Quotient.mk _ k,Subtype.ext ?_⟩
        exact (glue_edge T (false,i) _ (first j) ((incident j _).mpr (Or.inl rfl))).symm

end
end AK14.Gluing
