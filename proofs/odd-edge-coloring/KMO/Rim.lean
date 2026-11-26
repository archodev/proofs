import KMO.Euler

namespace KMO
variable {n : Nat}

abbrev rest (w : Fin n) (C : Region n) := fun i => i ≠ w ∧ ¬C i

/-- The induced graph on C is connected and 2-regular, so it is a cycle. -/
structure MixedCycle (G : Graph n) (w : Fin n) (C : Region n) : Prop where
  avoids : ¬C w
  regular : ∀ v, C v → (G.within C).degree v = 2
  connected : ConnectedOn G C
  exterior : ConnectedOn G (rest w C)
  meets : ∃ t, C t ∧ G.adj w t
  misses : ∃ u, C u ∧ ¬G.adj w u

theorem adj_of_degree_eq {P L : Graph n} (sub : P.Sub L) {i j}
    (eqn : P.degree i = L.degree i) (e : L.adj i j) : P.adj i j := by
  apply Classical.byContradiction; intro no
  have hd := Graph.degree_diff sub i
  have pos : 0 < (L.diff P).degree i := Graph.degree_pos.mpr ⟨j,e,no⟩
  omega

/-- In a subgraph of a cycle, when at most one odd vertex can be outside T,
every nonempty component meets T (provided the original cycle meets T). -/
theorem rim_anchor {G P : Graph n} {C T : Region n} {u : Fin n}
    (sub : P.Sub (G.within C)) (reg : ∀ v, C v → (G.within C).degree v = 2)
    (conn : ConnectedOn G C) (meets : ∃ t, C t ∧ T t)
    (ends : ∀ i, P.oddAt i → T i ∨ i = u) : Anchored P T := by
  classical
  intro v act
  apply Classical.byContradiction; intro bad
  let M := comp P v
  have noT {i} (m : M i) : ¬T i := fun t => bad ⟨i,t,m⟩
  have noOdd {i} (m : M i) : ¬P.oddAt i := by
    intro odd
    have iu := (ends i odd).resolve_left (noT m)
    have eqn : card (fun j => comp P v j ∧ P.oddAt j) = 1 := by
      rw [← card_single i]
      apply card_congr
      intro j; constructor
      · rintro ⟨mj,oj⟩; exact ((ends j oj).resolve_left (noT mj)).trans iu.symm
      · rintro rfl; exact ⟨m,odd⟩
    have hk := comp_handshake P v; omega
  obtain ⟨a,va⟩ := act
  obtain ⟨t,ct,tt⟩ := meets
  have walk := conn v (sub va).2.1 t ct
  have prop {j} (p : Reach G C v j) : M j ∧ P.supp j := by
    induction p with
    | here _ => exact ⟨.here trivial, a, va⟩
    | @next y z p e cz ih =>
      obtain ⟨mm,active⟩ := ih
      have pos := Graph.degree_pos.mpr active
      have neg := noOdd mm
      have rg := reg _ p.finish
      have hd := Graph.degree_diff sub y
      have same : P.degree y = (G.within C).degree y := by
        unfold Graph.oddAt at neg; omega
      have pe := adj_of_degree_eq sub same ⟨e,p.finish,cz⟩
      exact ⟨mm.next pe trivial,_,P.sym pe⟩
  exact noT (prop walk).1 tt

theorem exit_of_cycle {G : Graph n} {w C} (h : MixedCycle G w C)
    (deg : ∀ v, 4 ≤ G.degree v) {v} (cv : C v) : ∃ r, rest w C r ∧ G.adj v r := by
  classical
  apply Classical.byContradiction; intro bad
  have outer : ∀ j, G.adj v j ∧ ¬C j → j = w := by
    intro j hj
    exact Classical.byContradiction (fun ne => bad ⟨j,⟨ne,hj.2⟩,hj.1⟩)
  have bound := card_mono outer
  rw [card_single w] at bound
  have eqn := card_split (G.adj v) C
  have eqin : card (fun j => G.adj v j ∧ C j) = (G.within C).degree v :=
    card_congr (fun j => by simp [Graph.within,cv])
  rw [eqin,h.regular v cv] at eqn
  have low := deg v
  change 4 ≤ card (G.adj v) at low
  omega

theorem card_flag (v : Fin n) (flag : Prop) :
    card (fun i => i = v ∧ flag) = bit flag := by
  by_cases h : flag
  · rw [card_congr (fun i : Fin n => show (i = v ∧ flag) ↔ i = v by simp [h]),card_single]
    simp [bit,h]
  · rw [card_congr (fun i : Fin n => show (i = v ∧ flag) ↔ False by simp [h]),card_empty]
    simp [bit,h]

structure SwitchTips (C T : Region n) (u : Fin n) (D : Region n) : Prop where
  onC : ∀ i, D i → C i
  uniqueOutside : ∀ i, D i → ¬T i → i = u
  evenEnds : card (fun i => XorP (C i ∧ T i) (D i)) % 2 = 0
  oddSwitch : card (fun i => (C i ∧ ¬T i) ∧ ¬D i) % 2 = 1

theorem choose_tips {C T : Region n} {t u} (ct : C t) (tt : T t) (cu : C u) (nu : ¬T u) :
    ∃ D, SwitchTips C T u D := by
  classical
  let A := fun i => C i ∧ T i
  let O := fun i => C i ∧ ¬T i
  let f := card O % 2 = 0
  let U := fun i : Fin n => i = u ∧ f
  let g := (card A + bit f) % 2 = 1
  let V := fun i : Fin n => i = t ∧ g
  let D := fun i => U i ∨ V i
  have uct : u ≠ t := fun eq => nu (eq ▸ tt)
  have duv : ∀ i, U i → ¬ V i := by rintro i ⟨rfl,_⟩ ⟨eq,_⟩; exact uct eq
  have cd : card D = bit f + bit g := by
    change card (fun i => U i ∨ V i) = _; rw [card_union duv,card_flag,card_flag]
  have cfalse : card (fun i => O i ∧ D i) = bit f := by
    rw [← card_flag u f]
    apply card_congr; intro i
    change ((C i ∧ ¬T i) ∧ ((i = u ∧ f) ∨ (i = t ∧ g))) ↔ i = u ∧ f
    grind
  refine ⟨D,?_,?_,?_,?_⟩
  · rintro i (⟨rfl,_⟩ | ⟨rfl,_⟩) <;> assumption
  · rintro i (⟨rfl,_⟩ | ⟨rfl,_⟩) nt
    · rfl
    · contradiction
  · rw [card_xor,cd]; change (card A + (bit f + bit g)) % 2 = 0
    by_cases hg : g
    · have bg : bit g = 1 := by simp [bit,hg]
      rw [bg]; unfold g at hg; omega
    · have bg : bit g = 0 := by simp [bit,hg]
      rw [bg]; unfold g at hg; omega
  · have eqn := card_split O D; rw [cfalse] at eqn
    change card (fun i => O i ∧ ¬D i) % 2 = 1
    by_cases hf : f <;> simp [bit,hf] at eqn <;> dsimp [f] at hf <;> omega

end KMO
