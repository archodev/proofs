import KMO.Trace
namespace KMO
variable {n : Nat}

structure Ranked (T : Graph n) (rank : Fin n → Nat) : Prop where
  strict : ∀ i j,T.adj i j → rank i ≠ rank j
  unique : ∀ v i j,T.adj v i → T.adj v j → rank i < rank v → rank j < rank v → i = j

/-- A rooted spanning tree with strictly decreasing ranks toward the root.
These are the two tree properties actually used in the coloring proof. -/
theorem ranked_tree {G : Graph n} {U : Region n} (conn : ConnectedOn G U)
    {root} (ur : U root) : ∃ T : Graph n,∃ rank,T.Sub (G.within U) ∧ ConnectedOn T U ∧ Ranked T rank := by
  classical
  have traces i (hi : U i) := Trace.shortest_of_reach (conn root ur i hi)
  let walk i (hi : U i) := Classical.choose (traces i hi)
  have shortest i (hi : U i) : (walk i hi).Shortest := Classical.choose_spec (traces i hi)
  let rank i := if hi : U i then (walk i hi).len else 0
  have dist i (hi : U i) : rank i = (walk i hi).len := by simp [rank,hi]
  have nearer i (hi : U i ∧ i ≠ root) : ∃ j,U j ∧ G.adj i j ∧ rank j < rank i := by
    let P := walk i hi.1
    have d : rank i = P.len := dist _ hi.1
    have pos : 0 < P.len := by
      by_cases p : P.len = 0
      · exact False.elim (hi.2 ((p ▸ P.last).symm.trans P.first))
      · omega
    let k := P.len-1
    have hk : k < P.len := by unfold k; omega
    have eq : k+1=P.len := by unfold k; omega
    have uj := P.inside k (Nat.le_of_lt hk)
    refine ⟨P.node k,uj,?_,?_⟩
    · have e := G.sym (P.step k hk); rwa [eq,P.last] at e
    · have bound := shortest _ uj (P.takePart k (Nat.le_of_lt hk))
      change (walk _ uj).len ≤ k at bound
      rw [dist _ uj,d]; omega
  let par i := if hi : U i ∧ i ≠ root then Classical.choose (nearer i hi) else i
  have spec i (hi : U i ∧ i ≠ root) : U (par i) ∧ G.adj i (par i) ∧ rank (par i) < rank i := by
    simpa [par,hi] using Classical.choose_spec (nearer i hi)
  let arc := fun i j => (U i ∧ i ≠ root) ∧ par i = j
  have desc {i j} (a : arc i j) : rank j < rank i := a.2 ▸ (spec _ a.1).2.2
  let T : Graph n := ⟨fun i j => arc i j ∨ arc j i,fun e => e.symm,by
    rintro i (e | e) <;> exact Nat.lt_irrefl _ (desc e)⟩
  refine ⟨T,rank,?_,?_,?_,?_⟩
  · rintro i j (⟨hi,rfl⟩ | ⟨hj,rfl⟩)
    · exact ⟨(spec _ hi).2.1,hi.1,(spec _ hi).1⟩
    · exact ⟨G.sym (spec _ hj).2.1,(spec _ hj).1,hj.1⟩
  · have paths : ∀ k i,rank i = k → U i → Reach T U i root := by
      intro k; induction k using Nat.strongRecOn with
      | ind k ih =>
        intro i eq ui; by_cases ir : i = root
        · subst i; exact .here ur
        · have hi := spec i ⟨ui,ir⟩
          have up := ih (rank (par i)) (eq ▸ hi.2.2) _ rfl hi.1
          exact ((Reach.here ui).next (show T.adj i (par i) from Or.inl ⟨⟨ui,ir⟩,rfl⟩) hi.1).trans up
    exact fun i ui j uj => (paths _ i rfl ui).trans (paths _ j rfl uj).reverse
  · rintro i j (a | b)
    · exact Ne.symm (Nat.ne_of_lt (desc a))
    · exact Nat.ne_of_lt (desc b)
  · rintro v i j (a|a) (b|b) iv jv
    · exact a.2.symm.trans b.2
    · have := desc b; omega
    · have := desc a; omega
    · have := desc a; omega

end KMO
