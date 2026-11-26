import KMO.Finish

namespace KMO

/-- The graph partition theorem. All graph-theoretic dependencies, including
Tutte's peripheral-cycle theorem, are proved in the imported modules. -/
theorem conjecture_six : ConjectureSix := by
  classical
  intro n G oddOrder three minimum
  have ew : ∃ w,G.degree w % 2 = 0 := by
    apply Classical.byContradiction; intro none
    have all v : G.oddAt v := by
      have k : G.degree v % 2 ≠ 0 := fun h => none ⟨v,h⟩
      unfold Graph.oddAt; omega
    have eqn := card_congr (S := G.oddAt) (T := Full n) (fun i => ⟨fun _ => trivial,fun _ => all i⟩)
    have sizes : card (Full n) = n := card_full
    have even := handshaking G; omega
  obtain ⟨w,even⟩ := ew
  by_cases other : ∃ v,v ≠ w ∧ G.degree v % 2 = 0
  · obtain ⟨v,ne,ev⟩ := other
    exact multiple_even oddOrder three ne ev even
  · apply unique_even_of_tutte tutte_peripheral three minimum even
    intro v ne
    have k : G.degree v % 2 ≠ 0 := fun ev => other ⟨v,ne,ev⟩
    unfold Graph.oddAt; omega

/-- An undirected edge is stored once, in strictly increasing vertex order. -/
structure Edge {n : Nat} (G : Graph n) where
  lo : Fin n
  hi : Fin n
  sorted : lo < hi
  present : G.adj lo hi

def Edge.ends {n} {G : Graph n} (e : Edge G) (v u : Fin n) :=
  (e.lo = v ∧ e.hi = u) ∨ (e.lo = u ∧ e.hi = v)

theorem edge_exists {n} {G : Graph n} {v u} (h : G.adj v u) : ∃ e : Edge G,e.ends v u := by
  by_cases vu : v < u
  · exact ⟨⟨v,u,vu,h⟩,Or.inl ⟨rfl,rfl⟩⟩
  · have ne : v ≠ u := fun eq => G.loopless u (eq ▸ h)
    have uv : u < v := by omega
    exact ⟨⟨u,v,uv,G.sym h⟩,Or.inr ⟨rfl,rfl⟩⟩

theorem edge_unique {n} {G : Graph n} {v u} {e d : Edge G} (a : e.ends v u) (b : d.ends v u) : e = d := by
  cases e with | mk l h lh _ =>
    cases d with | mk l' h' lh' _ =>
      change (l=v ∧ h=u) ∨ (l=u ∧ h=v) at a
      change (l'=v ∧ h'=u) ∨ (l'=u ∧ h'=v) at b
      rcases a with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases b with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> first | rfl | omega

/-- Count the incident edges of color c, by their other endpoint. Edge uniqueness
above proves each such endpoint contributes exactly one edge. -/
noncomputable def incidentDegree {n} {G : Graph n} (paint : Edge G → Fin 3) (v : Fin n) (c : Fin 3) :=
  card (fun u => ∃ e : Edge G,e.ends v u ∧ paint e = c)

def Color.code : Color → Fin 3
  | .red => 0
  | .blue => 1
  | .green => 2

def Color.decode (c : Fin 3) : Color := if c.val = 0 then .red else if c.val = 1 then .blue else .green

theorem Color.code_decode (c : Fin 3) : (decode c).code = c := by
  unfold decode; split <;> (try split) <;> apply Fin.ext <;> simp [code] <;> omega
theorem Color.decode_code (c : Color) : decode c.code = c := by cases c <;> rfl

theorem paint_of_partition {n} {G : Graph n} (odd : OddThree G) :
    ∃ paint : Edge G → Fin 3,∀ v c,incidentDegree paint v c = 0 ∨
      ∃ k : Nat,incidentDegree paint v c = 2*k+1 := by
  classical
  obtain ⟨P,partition,disjoint,good⟩ := odd
  let pick (e : Edge G) := Classical.choose ((partition _ _).mp e.present)
  have picked (e : Edge G) : (P (pick e)).adj e.lo e.hi := Classical.choose_spec ((partition _ _).mp e.present)
  have unique (e : Edge G) (d : Color) (h : (P d).adj e.lo e.hi) : pick e = d :=
    Classical.byContradiction (fun ne => disjoint _ _ ne (picked e) h)
  let paint := fun e => (pick e).code
  refine ⟨paint,?_⟩; intro v c
  have eqn : incidentDegree paint v c = (P (Color.decode c)).degree v := by
    apply card_congr; intro u; constructor
    · rintro ⟨e,ends,eq⟩
      have pickeq : pick e = Color.decode c := by
        have p := congrArg Color.decode eq
        simpa [paint,Color.decode_code] using p
      have belongs := picked e; rw [pickeq] at belongs
      rcases ends with ⟨a,b⟩ | ⟨a,b⟩
      · simpa [a,b] using belongs
      · simpa [a,b] using (P (Color.decode c)).sym belongs
    · intro h; have g := (partition v u).mpr ⟨Color.decode c,h⟩
      obtain ⟨e,he⟩ := edge_exists g
      have belongs : (P (Color.decode c)).adj e.lo e.hi := by
        rcases he with ⟨a,b⟩ | ⟨a,b⟩
        · simpa [a,b] using h
        · simpa [a,b] using (P (Color.decode c)).sym h
      exact ⟨e,he,(congrArg Color.code (unique _ _ belongs)).trans (Color.code_decode c)⟩
  rw [eqn]; rcases good (Color.decode c) v with zero | one
  · exact Or.inl zero
  · right; refine ⟨(P (Color.decode c)).degree v / 2,?_⟩; unfold Graph.oddAt at one; omega

/-- Conjecture 6, with a single-valued color map on the actual undirected edges. -/
theorem odd_edge_coloring (n : Nat) (G : Graph n) (odd_order : n % 2 = 1)
    (three_connected : ThreeConnected G) (minimum_degree : ∀ v,4 ≤ G.degree v) :
    ∃ paint : Edge G → Fin 3,∀ v c,incidentDegree paint v c = 0 ∨
      ∃ k : Nat,incidentDegree paint v c = 2*k+1 :=
  paint_of_partition (conjecture_six n G odd_order three_connected minimum_degree)

def FourConnected {n} (G : Graph n) :=
  5 ≤ n ∧ ∀ D : Region n, card D ≤ 3 → ConnectedOn G (fun x => ¬D x)

/-- Kano–Maezawa–Ozeki, Theorem 5, as a corollary of Conjecture 6. -/
theorem four_connected_coloring {n : Nat} {G : Graph n} (order : n % 2 = 1)
    (h : FourConnected G) : OddThree G := by
  have three : ThreeConnected G :=
    ⟨Nat.le_trans (by decide : 4 ≤ 5) h.1,fun D small => h.2 D (by omega)⟩
  exact conjecture_six n G order three
    (degree_of_connectivity h.1 (fun D small => h.2 D (by omega)))

end KMO
