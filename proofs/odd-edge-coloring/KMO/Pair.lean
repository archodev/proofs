import KMO.End
namespace KMO
variable {n : Nat}

theorem avoid_one {S : Region n} (k : 2 ≤ card S) (a : Fin n) : ∃ x,S x ∧ x ≠ a := by
  classical
  apply Classical.byContradiction; intro bad
  have bound := card_mono (S := S) (T := fun x => x = a)
    (fun x sx => Classical.byContradiction (fun ne => bad ⟨x,sx,ne⟩))
  rw [card_single] at bound; omega

theorem avoid_two {S : Region n} (k : 3 ≤ card S) (a b : Fin n) : ∃ x,S x ∧ x ≠ a ∧ x ≠ b := by
  classical
  apply Classical.byContradiction; intro bad
  have bound := card_mono (S := S) (T := fun x => x = a ∨ x = b)
    (fun x sx => by by_cases xa : x = a
                    · exact Or.inl xa
                    · exact Or.inr (Classical.byContradiction (fun xb => bad ⟨x,sx,xa,xb⟩)))
  have lim := card_pair_le a b; omega

theorem pair_exhaust {S : Region n} {a b : Fin n} (ne : a ≠ b)
    (sa : S a) (sb : S b) (size : card S ≤ 2) {z} (sz : S z) : z = a ∨ z = b := by
  classical
  apply Classical.byContradiction; intro no
  have t := strict_card (S := fun i => i = a ∨ i = b) (T := S)
    (by rintro _ (rfl | rfl) <;> assumption) sz no
  rw [card_pair ne] at t; omega

theorem Sides.symm {G : Graph n} {U A B : Region n} {c} (s : Sides G U c A B) : Sides G U c B A :=
  ⟨s.pole,s.sideB,s.sideA,fun _ b a => s.disjoint _ a b,fun i ui => by have := s.cover i ui; grind⟩

theorem Sides.localEnd {G : Graph n} {U A B : Region n} {c} (s : Sides G U c A B) :
    EndAt G (plus A c) A c := ⟨Or.inr rfl,s.sideA.nonempty,
      fun _ ai => ⟨Or.inl ai,(s.sideA.inside _ ai).2⟩,fun _ _ _ uj jc _ => uj.resolve_right jc⟩

theorem Sides.local_sub {G : Graph n} {U A B : Region n} {c} (s : Sides G U c A B) :
    ∀ i,plus A c i → U i := by
  rintro i (ai | rfl)
  · exact (s.sideA.inside _ ai).1
  · exact s.pole

theorem Sides.local_degree {G : Graph n} {U A B : Region n} {c} (s : Sides G U c A B)
    {x} (ax : A x) : (G.within (plus A c)).degree x = (G.within U).degree x := by
  apply card_congr; intro j
  constructor
  · intro e; exact ⟨e.1,(s.sideA.inside _ ax).1,s.local_sub j e.2.2⟩
  · intro e; refine ⟨e.1,Or.inl ax,?_⟩; by_cases jc : j = c
    · exact Or.inr jc
    · exact Or.inl (s.sideA.closed _ _ ax e.2.2 jc e.1)

theorem Sides.cross_ne {G : Graph n} {U A B : Region n} {c} (s : Sides G U c A B)
    {x y} (ax : A x) (by' : B y) : x ≠ y ∧ ¬G.adj x y := by
  refine ⟨fun eq => s.disjoint _ (eq ▸ ax) by',?_⟩
  intro e; have k := s.sideB.inside _ by'
  exact s.disjoint _ (s.sideA.closed _ _ ax k.1 k.2 e) by'

theorem Sides.deleted_conn {G : Graph n} {U A B : Region n} {c} (s : Sides G U c A B)
    {x y} (ax : A x) (by' : B y) (hx : ConnectedOn G (del (plus A c) x))
    (hy : ConnectedOn G (del (plus B c) y)) : ConnectedOn G (del₂ U x y) := by
  have xc := (s.sideA.inside _ ax).2; have yc := (s.sideB.inside _ by').2
  have k := conn_union_at hx hy (c := c) ⟨Or.inr rfl,Ne.symm xc⟩ ⟨Or.inr rfl,Ne.symm yc⟩
  apply conn_congr _ k
  intro i; have aa := s.sideA.inside i; have bb := s.sideB.inside i
  have co := s.cover i; have dd := s.disjoint; have uc := s.pole
  unfold del₂ del plus; grind

structure PairWitness (G : Graph n) (U : Region n) (x y : Fin n) : Prop where
  first : U x
  second : U y
  different : x ≠ y
  nonedge : ¬G.adj x y
  connected : ConnectedOn G (del₂ U x y)

theorem connected_after_one {G : Graph n} {U : Region n} {x y}
    (p : PairWitness G U x y) (positive : 0 < (G.within U).degree y) : ConnectedOn G (del U x) := by
  apply attach_vertices p.connected (fun _ k => k.1)
  intro i hi missing
  have eq : i = y := Classical.byContradiction (fun iy => missing ⟨hi,iy⟩)
  subst i; obtain ⟨j,e⟩ := Graph.degree_pos.mp positive
  exact ⟨j,⟨⟨e.2.2,fun jx => p.nonedge (G.sym (jx ▸ e.1))⟩,fun jy => G.loopless y (jy ▸ e.1)⟩,e.1⟩

/-- The auxiliary graph need not have more than three vertices outside a
separating pair. Only the degree of the vertex that is added back is needed. -/
theorem pair_at_cut {G : Graph n} {U : Region n} (two : Two G U) {v c}
    (cut : ¬ConnectedOn G (del₂ U v c)) (dv : 3 ≤ (G.within U).degree v) :
    ∃ x y, PairWitness G U x y := by
  classical
  let W := del U v
  have wc := two.2 v
  obtain ⟨A,B,s⟩ := sides_of_cut wc cut
  have cs := sides_connected s wc
  have pick {A B : Region n} (s : Sides G W c A B) (cc : ConnectedOn G (plus A c)) :
      ∃ x,A x ∧ G.adj v x ∧ ConnectedOn G (del (plus A c) x) := by
    obtain ⟨p,M,e,ma,minimal⟩ := minimal_end s.localEnd
    have noC : ¬M c := fun mc => (s.sideA.inside _ (ma _ mc)).2 rfl
    have pu := s.local_sub p e.pole
    have uv : U v := by
      apply Classical.byContradiction; intro no
      have zero := outside (G := G.within U) (S := U) (by intro _ _ k; exact k.2.1) no
      omega
    obtain ⟨m,mm⟩ := e.nonempty
    have um := (s.sideA.inside _ (ma _ mm)).1
    have vm : ¬M v := fun mv => (s.sideA.inside _ (ma _ mv)).1.2 rfl
    obtain ⟨x,j,ux,uj,mx,mj,edge⟩ := adjacent_across (two.2 p)
      ⟨um.1,(e.inside _ mm).2⟩ ⟨uv,Ne.symm pu.2⟩ mm vm
    have jv : j = v := by
      apply Classical.byContradiction; intro nv
      have wj : W j := ⟨uj.1,nv⟩
      have localj : plus A c j := by
        by_cases jc : j = c
        · exact Or.inr jc
        · exact Or.inl (s.sideA.closed _ _ (ma _ mx) wj jc edge)
      exact mj (e.closed _ _ mx localj uj.2 edge)
    exact ⟨x,ma _ mx,G.sym (jv ▸ edge),removable_in_end e ma minimal cc mx⟩
  obtain ⟨x,ax,vx,cx⟩ := pick s cs.1
  obtain ⟨y,by',vy,cy⟩ := pick s.symm cs.2
  have ux := (s.sideA.inside _ ax).1; have uy := (s.sideB.inside _ by').1
  have ne := s.cross_ne ax by'
  have conn := s.deleted_conn ax by' cx cy
  refine ⟨x,y,ux.1,uy.1,ne.1,ne.2,?_⟩
  apply attach_vertices conn (by intro i hi; exact ⟨⟨hi.1.1.1,hi.1.2⟩,hi.2⟩)
  intro i hi missing
  have iv : i = v := Classical.byContradiction (fun nv => missing ⟨⟨⟨hi.1.1,nv⟩,hi.1.2⟩,hi.2⟩)
  subst i
  obtain ⟨j,e,jx,jy⟩ := avoid_two dv x y
  exact ⟨j,⟨⟨⟨e.2.2,fun jv => G.loopless _ (jv ▸ e.1)⟩,jx⟩,jy⟩,e.1⟩

/-- A 2-connected region of minimum degree at least two with a nonedge
and some degree at least three has a nonadjacent removable pair. -/
theorem nonadjacent_pair {G : Graph n} {U : Region n} (two : Two G U)
    (md : ∀ i,U i → 2 ≤ (G.within U).degree i)
    (nonclique : ∃ x y,U x ∧ U y ∧ x ≠ y ∧ ¬G.adj x y)
    (notCycle : ∃ i,U i ∧ 3 ≤ (G.within U).degree i) :
    ∃ x y, PairWitness G U x y := by
  classical
  by_cases strong : Three G U
  · obtain ⟨x,y,ux,uy,ne,no⟩ := nonclique
    exact ⟨x,y,ux,uy,ne,no,strong.2 x y⟩
  by_cases all : ∀ i,U i → 3 ≤ (G.within U).degree i
  · apply Classical.byContradiction; intro no; apply strong; refine ⟨two,?_⟩
    intro v c; apply Classical.byContradiction; intro disc
    have uv : U v := Classical.byContradiction (fun nv =>
      disc (conn_congr (fun i => by simp [del₂,del]; grind) (two.2 c)))
    exact no (pair_at_cut two disc (all _ uv))
  · obtain ⟨z,uz,high⟩ := notCycle
    have low : ∃ j,U j ∧ ¬3 ≤ (G.within U).degree j := by
      apply Classical.byContradiction; intro no; apply all
      intro j uj; exact Classical.byContradiction (fun h => no ⟨j,uj,h⟩)
    obtain ⟨k,uk,lo⟩ := low
    obtain ⟨v,s,uv,us,hv,hs,vs⟩ := adjacent_across (L := fun i => 3 ≤ (G.within U).degree i) two.1 uz uk high lo
    have sn := md _ us
    have deg2 : (G.within U).degree s = 2 := by omega
    obtain ⟨c,sc,cv⟩ := avoid_one sn v
    have sv : (G.within U).adj s v := ⟨G.sym vs,us,uv⟩
    have cs : c ≠ s := fun eq => G.loopless s (eq ▸ sc.1)
    have vsne : v ≠ s := fun eq => G.loopless s (eq ▸ vs)
    obtain ⟨j,jv,jc,js⟩ := avoid_two hv c s
    have jnv : j ≠ v := fun eq => G.loopless v (eq ▸ jv.1)
    have disc : ¬ConnectedOn G (del₂ U v c) := by
      intro conn
      have p := conn s ⟨⟨us,Ne.symm vsne⟩,Ne.symm cs⟩ j ⟨⟨jv.2.2,jnv⟩,jc⟩
      have eq := p.preserve (L := fun i => i = s) rfl (by
        rintro i k rfl hk e
        have cases := pair_exhaust cv sc sv (Nat.le_of_eq deg2) ⟨e,us,hk.1.1⟩
        exact False.elim (cases.elim hk.2 hk.1.2))
      exact js eq
    exact pair_at_cut two disc hv

end KMO
