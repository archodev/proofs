import KMO.Star
import KMO.Tree

namespace KMO
variable {n : Nat}

theorem le_total {n} (r : Fin n → Nat) (v : Fin n) : r v ≤ total n r := by
  induction n with
  | zero => exact v.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) v
    · simp [total]
    · have := ih (fun i => r i.succ) j; simp only [total]; omega

abbrev LocalRed (H : Graph n) (pivot : Fin n → Fin n) (flag : Region n) (v j : Fin n) :=
  (H.oddAt v ∨ j = pivot v) ↔ flag v

/-- Local two-coloring of a forest with one exceptional vertex s. Splitting
s into incident leaves gives the usual odd coloring of a forest. -/
theorem forest_coloring {H T : Graph n} {s : Fin n} {rank : Fin n → Nat}
    (tree : Ranked T rank) (sub : ∀ i j, i ≠ s → j ≠ s → H.adj i j → T.adj i j) :
    ∃ R : Graph n,R.Sub H ∧ ∀ v,v ≠ s →
      (R.degree v = 0 ∨ R.oddAt v) ∧ ((H.diff R).degree v = 0 ∨ (H.diff R).oddAt v) := by
  classical
  let lower := fun v j => H.adj v j ∧ v ≠ s ∧ j ≠ s ∧ rank j < rank v
  let has := fun v => ∃ j,lower v j
  let pivot v := if h : has v then Classical.choose h else if e : H.supp v then Classical.choose e else v
  have pivot_lower v (h : has v) : lower v (pivot v) := by simpa [pivot,h] using Classical.choose_spec h
  have anchor v (active : H.supp v) : H.adj v (pivot v) := by
    by_cases h : has v
    · exact (pivot_lower _ h).1
    · simpa [pivot,h,active] using Classical.choose_spec active
  have eq {v j} (l : lower v j) : pivot v = j := by
    have other := pivot_lower v ⟨j,l⟩
    exact tree.unique _ _ _ (sub _ _ other.2.1 other.2.2.1 other.1)
      (sub _ _ l.2.1 l.2.2.1 l.1) other.2.2.2 l.2.2.2
  have flags (k) : ∃ f : Region n,∀ v j,rank v < k → lower v j → (f v ↔ LocalRed H pivot f j v) := by
    induction k with
    | zero => exact ⟨fun _ => False,by intro v j h; omega⟩
    | succ k ih =>
      obtain ⟨f,valid⟩ := ih
      let f' := fun v => if rank v = k ∧ has v then LocalRed H pivot f (pivot v) v else f v
      have same i (hi : rank i < k) : f' i ↔ f i := by simp [f',Nat.ne_of_lt hi]
      refine ⟨f',?_⟩; intro v j vr lj
      have jk : rank j < k := by have := lj.2.2.2; omega
      change f' v ↔ ((H.oddAt j ∨ v = pivot j) ↔ f' j)
      rw [propext (same _ jk)]
      by_cases vk : rank v = k
      · have yes : has v := ⟨j,lj⟩; simp [f',vk,yes,eq lj]
      · exact (same _ (by omega)).trans (valid _ _ (by omega) lj)
  obtain ⟨flag,valid⟩ := flags (total n rank + 1)
  let paint := LocalRed H pivot flag
  have down {v j} (l : lower v j) : paint v j ↔ paint j v := by
    have h := valid v j (Nat.lt_succ_of_le (le_total rank v)) l
    change ((H.oddAt v ∨ j = pivot v) ↔ flag v) ↔ _
    simpa [eq l] using h
  have agree v j (vs : v ≠ s) (js : j ≠ s) (e : H.adj v j) : paint v j ↔ paint j v := by
    have neq := tree.strict _ _ (sub _ _ vs js e)
    by_cases lt : rank j < rank v
    · exact down ⟨e,vs,js,lt⟩
    · exact (down ⟨H.sym e,js,vs,by omega⟩).symm
  let R : Graph n := ⟨fun i j => H.adj i j ∧ ((i ≠ s ∧ paint i j) ∨ (j ≠ s ∧ paint j i)),
    fun h => ⟨H.sym h.1,h.2.symm⟩,fun i h => H.loopless i h.1⟩
  have rs : R.Sub H := by intro _ _ e; exact e.1
  have spec v (vs : v ≠ s) j : R.adj v j ↔ H.adj v j ∧ paint v j := by
    constructor
    · rintro ⟨e, k | k⟩
      · exact ⟨e,k.2⟩
      · exact ⟨e,(agree v j vs k.1 e).mpr k.2⟩
    · intro k; exact ⟨k.1,Or.inl ⟨vs,k.2⟩⟩
  refine ⟨R,rs,?_⟩; intro v vs
  have sum := Graph.degree_diff rs v
  by_cases active : H.supp v
  case neg =>
    have z : ¬0 < H.degree v := fun h => active (Graph.degree_pos.mp h)
    exact ⟨Or.inl (by omega),Or.inl (by omega)⟩
  have edge := anchor v active
  by_cases odd : H.oddAt v
  · by_cases color : flag v
    · have all : R.degree v = H.degree v := card_congr (fun j => by rw [spec _ vs]; simp [paint,LocalRed,odd,color] <;> exact fun _ => Or.inl odd)
      exact ⟨Or.inr (by unfold Graph.oddAt; rw [all]; exact odd),Or.inl (by omega)⟩
    · have zero : R.degree v = 0 := (card_congr (T := fun _ => False) (fun j => by
        rw [spec _ vs]; simp [paint,LocalRed,odd,color])).trans card_empty
      exact ⟨Or.inl zero,Or.inr (by unfold Graph.oddAt at *; omega)⟩
  · by_cases color : flag v
    · have anchorOnly : R.degree v = 1 := (card_congr (T := fun j => j = pivot v) (fun j => by
        rw [spec _ vs]; simp [paint,LocalRed,odd,color]; intro eqn; exact eqn ▸ edge)).trans (card_single _)
      exact ⟨Or.inr (by unfold Graph.oddAt; omega),Or.inr (by unfold Graph.oddAt at *; omega)⟩
    · have anchorOnly : (H.diff R).degree v = 1 := (card_congr (T := fun j => j = pivot v) (fun j => by
        change (H.adj v j ∧ ¬R.adj v j) ↔ _
        rw [spec _ vs]; simp only [paint,LocalRed,odd,color,false_or,iff_false]
        constructor
        · intro k; exact Classical.byContradiction (fun ne => k.2 ⟨k.1,ne⟩)
        · rintro rfl; exact ⟨edge,fun k => k.2 rfl⟩)).trans (card_single _)
      exact ⟨Or.inr (by unfold Graph.oddAt at *; omega),Or.inr (by unfold Graph.oddAt; omega)⟩

end KMO
