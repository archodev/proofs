import KMO.Components
namespace KMO
variable {n : Nat}
abbrev del (U : Region n) (v : Fin n) := fun i => U i ∧ i ≠ v
abbrev del₂ (U : Region n) (a b : Fin n) := del (del U a) b
def Two (G : Graph n) (U : Region n) := ConnectedOn G U ∧ ∀ a, ConnectedOn G (del U a)
def Three (G : Graph n) (U : Region n) := Two G U ∧ ∀ a b, ConnectedOn G (del₂ U a b)

theorem conn_move {G H : Graph n} {S T : Region n} (h : ConnectedOn G S)
    (st : ∀ i, S i ↔ T i) (inc : ∀ i j, S i → S j → G.adj i j → H.adj i j) : ConnectedOn H T :=
  fun x hx y hy => (h x ((st x).mpr hx) y ((st y).mpr hy)).transport (fun i => (st i).mp) inc

theorem conn_congr {G : Graph n} {S T : Region n} (st : ∀ i, S i ↔ T i) (h : ConnectedOn G S) :
    ConnectedOn G T := conn_move h st (fun _ _ _ _ => id)

theorem Reach.preserve {G : Graph n} {S L : Region n} {x y}
    (p : Reach G S x y) (base : L x) (step : ∀ i j, L i → S j → G.adj i j → L j) : L y := by
  induction p with | here _ => exact base | next _ e h ih => exact step _ _ ih h e

theorem conn_of_cover {G : Graph n} {S : Region n}
    (h : ∀ L : Region n, (∃ i, L i) → (∀ i, L i → S i) →
      (∀ i j, L i → S j → G.adj i j → L j) → ∀ j, S j → L j) : ConnectedOn G S := by
  intro x hx y hy
  exact h (Reach G S x) ⟨x,.here hx⟩ (fun _ p => p.finish) (fun _ _ p k e => p.next e k) y hy

structure Shore (G : Graph n) (U L : Region n) : Prop where
  nonempty : ∃ i, L i
  inside : ∀ i, L i → U i
  proper : ∃ i, U i ∧ ¬L i
  closed : ∀ i j, L i → U j → G.adj i j → L j

theorem Shore.disconnected {G : Graph n} {U L : Region n} (s : Shore G U L) : ¬ConnectedOn G U := by
  rintro conn; obtain ⟨a,ha⟩ := s.nonempty; obtain ⟨b,hb,no⟩ := s.proper
  exact no ((conn a (s.inside a ha) b hb).preserve ha s.closed)

theorem shore_of_disconnected {G : Graph n} {U : Region n} (h : ¬ConnectedOn G U) :
    ∃ L, Shore G U L := by
  classical
  apply Classical.byContradiction; intro bad; apply h
  apply conn_of_cover; intro L ne sub closed i ui
  exact Classical.byContradiction (fun no => bad ⟨L,ne,sub,⟨i,ui,no⟩,closed⟩)

theorem shore_complement {G : Graph n} {U L : Region n} (s : Shore G U L) :
    Shore G U (fun i => U i ∧ ¬L i) := by
  refine ⟨s.proper,fun _ => And.left,?_,?_⟩
  · obtain ⟨i,li⟩ := s.nonempty; exact ⟨i,s.inside _ li,fun h => h.2 li⟩
  · intro i j hi uj e; exact ⟨uj,fun lj => hi.2 (s.closed j i lj hi.1 (G.sym e))⟩

theorem attach_vertices {G : Graph n} {S U : Region n} (conn : ConnectedOn G S)
    (sub : ∀ i, S i → U i)
    (attach : ∀ i, U i → ¬S i → ∃ j, S j ∧ G.adj i j) : ConnectedOn G U := by
  classical
  have toS i (ui : U i) : ∃ j, S j ∧ Reach G U i j := by
    by_cases si : S i
    · exact ⟨i,si,.here ui⟩
    · obtain ⟨j,sj,e⟩ := attach i ui si; exact ⟨j,sj,(Reach.here ui).next e (sub _ sj)⟩
  intro x hx y hy
  obtain ⟨i,si,p⟩ := toS x hx
  obtain ⟨j,sj,q⟩ := toS y hy
  exact (p.trans ((conn i si j sj).transport sub (fun _ _ _ _ => id))).trans q.reverse

theorem adjacent_across {G : Graph n} {L U : Region n} (conn : ConnectedOn G U)
    {x y} (ux : U x) (uy : U y) (lx : L x) (ly : ¬L y) :
    ∃ i j, U i ∧ U j ∧ L i ∧ ¬L j ∧ G.adj i j := by
  classical
  apply Classical.byContradiction; intro bad
  have closed (i j) (hi : U i ∧ L i) (uj : U j) (e : G.adj i j) : U j ∧ L j :=
    ⟨uj, Classical.byContradiction (fun nj => bad ⟨i,j,hi.1,uj,hi.2,nj,e⟩)⟩
  exact ly (((conn x ux y uy).preserve ⟨ux,lx⟩ closed).2)

theorem strict_card {S T : Region n} (sub : ∀ i, S i → T i) {x} (tx : T x) (sx : ¬S x) :
    card S < card T := by
  have k := card_mono (S := S) (T := del T x) (fun i si => ⟨sub _ si,fun eq => sx (eq ▸ si)⟩)
  have e := card_erase tx
  change card (del T x) + 1 = card T at e
  omega

theorem minimize {α : Type} (p : α → Prop) (size : α → Nat) (existsP : ∃ a,p a) :
    ∃ a, p a ∧ ∀ b, p b → size a ≤ size b := by
  classical
  obtain ⟨a,ha⟩ := existsP
  suffices ∀ k b, size b = k → p b → ∃ a, p a ∧ ∀ c, p c → size a ≤ size c from this _ _ rfl ha
  intro k; induction k using Nat.strongRecOn with
  | ind k ih =>
    intro b hk hb; by_cases best : ∀ c,p c → size b ≤ size c
    · exact ⟨b,hb,best⟩
    · apply Classical.byContradiction; intro no; apply best
      intro c hc; apply Nat.le_of_not_gt; intro lt
      exact no (ih (size c) (hk ▸ lt) c rfl hc)

theorem card_pair {a b : Fin n} (ne : a ≠ b) :
    card (fun i => i = a ∨ i = b) = 2 := by
  rw [card_union (S := fun i => i = a) (T := fun i => i = b) (by rintro _ rfl; exact ne),card_single,card_single]

theorem card_pair_le (a b : Fin n) : card (fun i => i = a ∨ i = b) ≤ 2 := by
  by_cases h : a = b
  · subst b; simp [card_single]
  · rw [card_pair h]; decide

theorem global_three {G : Graph n} (h : ThreeConnected G) : Three G (Full n) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply conn_congr (S := fun _ : Fin n => ¬False) (by simp [Full])
    exact h.2 _ (by rw [card_empty]; decide)
  · intro a
    apply conn_congr (S := fun i => ¬i = a) (by simp [del,Full])
    exact h.2 _ (by rw [card_single]; decide)
  · intro a b
    apply conn_congr (S := fun i => ¬(i = a ∨ i = b)) (by simp [del₂,del,Full,not_or])
    exact h.2 _ (card_pair_le _ _)

theorem two_after_delete {G : Graph n} (h : ThreeConnected G) (w) :
    Two G (fun v => v ≠ w) := by
  have h3 := global_three h
  refine ⟨conn_congr (by simp [del,Full]) (h3.1.2 w),?_⟩
  intro a; exact conn_congr (by simp [del₂,del,Full]) (h3.2 w a)

/-- Deleting the whole neighborhood isolates its center. -/
theorem degree_of_connectivity {G : Graph n} {k : Nat} (size : k < n)
    (connected : ∀ D : Region n, card D < k → ConnectedOn G (fun j => ¬D j))
    (v : Fin n) : k ≤ G.degree v := by
  apply Nat.le_of_not_gt
  intro small
  have conn := connected (G.adj v) small
  have only (j : Fin n) (hj : ¬G.adj v j) : j = v := by
    have path := conn v (G.loopless v) j hj
    apply path.preserve (L := fun i => i = v) rfl
    intro i u iv nu e
    exact False.elim (nu (iv ▸ e))
  have cover : card (fun j => G.adj v j ∨ j = v) = n := by
    refine (card_congr (T := Full n) (fun j => ⟨fun _ => trivial,fun _ => ?_⟩)).trans card_full
    by_cases e : G.adj v j
    · exact Or.inl e
    · exact Or.inr (only j e)
  have part := card_union (S := G.adj v) (T := fun j => j = v)
    (by intro j e eq; exact G.loopless v (eq ▸ e))
  rw [card_single] at part
  change card (fun j => G.adj v j ∨ j = v) = G.degree v + 1 at part
  rw [cover] at part
  omega

theorem degree_of_three {G : Graph n} (h : ThreeConnected G) (v : Fin n) :
    3 ≤ G.degree v :=
  degree_of_connectivity h.1 (fun D small => h.2 D (by omega)) v

theorem degree_sub {A G : Graph n} (h : A.Sub G) (v) : A.degree v ≤ G.degree v :=
  card_mono (fun _ e => h e)

theorem neighbors_in {G : Graph n} {U : Region n} {v} (hv : U v) :
    (G.within U).degree v = card (fun j => U j ∧ G.adj v j) :=
  card_congr (fun j => by simp [Graph.within,hv, and_comm])

end KMO
