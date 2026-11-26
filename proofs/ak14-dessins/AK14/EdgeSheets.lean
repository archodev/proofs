import AK14.GluedConnectivity

/-! Exact sheet counts on the open edges as well as the open triangle faces.
Only the three corner fibers can have a local sheet stabilizer. -/
namespace AK14.Gluing
noncomputable section

private def edgeSheet {n : ℕ} (T : Triple n) (j : Fin 3) : Tri n → Fin n
  | (true,i) => i
  | (false,i) => (crossing T j)⁻¹ i

private theorem edgeSheet_step {n : ℕ} (T : Triple n) (j : Fin 3) (q : Tri n) :
    edgeSheet T j (step T j q)=edgeSheet T j q := by
  obtain ⟨b,i⟩ := q; cases b <;> simp [step,edgeSheet]

private def openEdgeMark {n : ℕ} (T : Triple n) (z : Triangle) (j : Fin 3)
    (h : ∀ k, z.val k=0 → k=j) : Surface T → Option (Fin n) :=
  Quot.lift (fun u => if u.2=z then some (edgeSheet T j u.1) else none) (by
    rintro a b ⟨k,pt,zero,st⟩
    by_cases e : a.2=z
    · have e' : b.2=z := pt.symm.trans e
      obtain rfl := h _ (e ▸ zero)
      simp only [e,e',if_true,Option.some.injEq,← st,edgeSheet_step]
    · have e' : b.2≠z := pt ▸ e
      simp [e,e'])

def edge_sheets {n : ℕ} (T : Triple n) (z : Triangle) (j : Fin 3) (zero : z.val j=0)
    (only : ∀ k, z.val k=0 → k=j) :
    Fin n ≃ {u : Surface T // coveringProjection T u=cell flatTriple (true,0) z} := by
  let F (i : Fin n) : {u : Surface T // coveringProjection T u=cell flatTriple (true,0) z} :=
    ⟨cell T (true,i) z,rfl⟩
  apply Equiv.ofBijective F
  constructor
  · intro i k eq
    have h := congrArg (openEdgeMark T z j only) (congrArg Subtype.val eq)
    simpa [openEdgeMark,F,cell,edgeSheet] using h
  · rintro ⟨u,hu⟩
    induction u using Quot.ind with | _ u =>
      obtain ⟨⟨b,i⟩,v⟩ := u
      have w : v=z := congrArg (barycentric flatTriple) hu
      subst v
      cases b with
      | true => exact ⟨i,rfl⟩
      | false =>
        exact ⟨(crossing T j)⁻¹ i,Subtype.ext (glue_edge T (false,i) z j zero).symm⟩

end
end AK14.Gluing
