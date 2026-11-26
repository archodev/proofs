import KMO.Connectivity
namespace KMO
variable {n : Nat}

/-- A nonempty set attached to the rest of U only at a single pole. -/
structure EndAt (G : Graph n) (U A : Region n) (p : Fin n) : Prop where
  pole : U p
  nonempty : ∃ i,A i
  inside : ∀ i,A i → U i ∧ i ≠ p
  closed : ∀ i j,A i → U j → j ≠ p → G.adj i j → A j

structure EndChoice (n : Nat) where
  pole : Fin n
  carrier : Region n

theorem minimal_end {G : Graph n} {U B : Region n} {c} (seed : EndAt G U B c) :
    ∃ p A, EndAt G U A p ∧ (∀ i,A i → B i) ∧
      (∀ q M, EndAt G U M q → (∀ i,M i → B i) → card A ≤ card M) := by
  let valid := fun k : EndChoice n => EndAt G U k.carrier k.pole ∧ ∀ i,k.carrier i → B i
  obtain ⟨k,h,hmin⟩ := minimize valid (fun k => card k.carrier) ⟨⟨c,B⟩,seed,fun _ => id⟩
  exact ⟨k.pole,k.carrier,h.1,h.2,fun q M e s => hmin ⟨q,M⟩ ⟨e,s⟩⟩

theorem EndAt.outside_path {G : Graph n} {U A : Region n} {p}
    (h : EndAt G U A p) (conn : ConnectedOn G U) {y} (uy : U y) (ny : ¬A y) :
    Reach G (fun i => U i ∧ ¬A i) p y := by
  have np : ¬A p := fun a => (h.inside p a).2 rfl
  have route {j} (walk : Reach G U p j) : ¬A j → Reach G (fun i => U i ∧ ¬A i) p j := by
    induction walk with
    | here _ => exact fun _ => .here ⟨h.pole,np⟩
    | @next i j q e uj ih =>
      intro nj; by_cases ai : A i
      · have eq : j = p := Classical.byContradiction (fun ne => nj (h.closed _ _ ai uj ne e))
        subst j; exact .here ⟨h.pole,np⟩
      · exact (ih ai).next e ⟨uj,nj⟩
  exact route (conn p h.pole y uy) ny

theorem EndAt.outside_conn {G : Graph n} {U A : Region n} {p} (h : EndAt G U A p)
    (conn : ConnectedOn G U) : ConnectedOn G (fun i => U i ∧ ¬A i) := by
  intro i hi j hj
  exact (h.outside_path conn hi.1 hi.2).reverse.trans (h.outside_path conn hj.1 hj.2)

theorem removable_in_end {G : Graph n} {U A B : Region n} {p} (h : EndAt G U A p)
    (ab : ∀ i,A i → B i) (minimal : ∀ q M,EndAt G U M q → (∀ i,M i → B i) → card A ≤ card M)
    (conn : ConnectedOn G U) {x} (ax : A x) : ConnectedOn G (del U x) := by
  classical
  apply Classical.byContradiction; intro bad
  obtain ⟨L,s⟩ := shore_of_disconnected bad
  have orient : ∃ M, Shore G (del U x) M ∧ ¬M p := by
    by_cases lp : L p
    · exact ⟨_,shore_complement s,fun k => k.2 lp⟩
    · exact ⟨L,s,lp⟩
  obtain ⟨M,ms,noP⟩ := orient
  have ma i (mi : M i) : A i := by
    apply Classical.byContradiction; intro ni
    have q := (h.outside_path conn (ms.inside _ mi).1 ni).reverse
    have lift := q.transport (T := del U x) (H := G)
      (fun j k => ⟨k.1,fun eq => k.2 (eq ▸ ax)⟩) (fun _ _ _ _ => id)
    exact noP (lift.preserve mi ms.closed)
  have newEnd : EndAt G U M x := ⟨(h.inside _ ax).1,ms.nonempty,ms.inside,fun i j mi uj jx e =>
    ms.closed i j mi ⟨uj,jx⟩ e⟩
  have lo := minimal x M newEnd (fun i mi => ab i (ma i mi))
  exact (Nat.not_le_of_lt (strict_card ma ax (fun mx => (ms.inside _ mx).2 rfl))) lo

theorem two_choices_in_end {G : Graph n} {U A : Region n} {p}
    (h : EndAt G U A p) (mindeg : ∀ v,A v → 2 ≤ (G.within U).degree v) :
    ∃ x y,A x ∧ A y ∧ x ≠ y := by
  classical
  obtain ⟨x,ax⟩ := h.nonempty
  apply Classical.byContradiction; intro no
  have only j (aj : A j) : j = x := Classical.byContradiction (fun ne => no ⟨x,j,ax,aj,Ne.symm ne⟩)
  have bound : (G.within U).degree x ≤ card (fun i => i = p) := by
    apply card_mono; intro i e
    apply Classical.byContradiction; intro ip
    have eq := only _ (h.closed x i ax e.2.2 ip e.1)
    exact G.loopless x (eq ▸ e.1)
  have d := mindeg _ ax; rw [card_single] at bound; omega

theorem noncut_on_side {G : Graph n} {U A : Region n} {c} (h : EndAt G U A c)
    (conn : ConnectedOn G U) (md : ∀ i,A i → 2 ≤ (G.within U).degree i) :
    ∃ x y,A x ∧ A y ∧ x ≠ y ∧ ConnectedOn G (del U x) ∧ ConnectedOn G (del U y) := by
  obtain ⟨p,M,e,ma,minimal⟩ := minimal_end h
  obtain ⟨x,y,mx,my,ne⟩ := two_choices_in_end e (fun i mi => md _ (ma i mi))
  exact ⟨x,y,ma _ mx,ma _ my,ne,removable_in_end e ma minimal conn mx,removable_in_end e ma minimal conn my⟩

theorem conn_union_at {G : Graph n} {U V : Region n} {c}
    (a : ConnectedOn G U) (b : ConnectedOn G V) (uc : U c) (vc : V c) :
    ConnectedOn G (fun i => U i ∨ V i) := by
  have route i (hi : U i ∨ V i) : Reach G (fun j => U j ∨ V j) i c := by
    cases hi with
    | inl h => exact (a i h c uc).transport (fun _ => Or.inl) (fun _ _ _ _ => id)
    | inr h => exact (b i h c vc).transport (fun _ => Or.inr) (fun _ _ _ _ => id)
  exact fun i hi j hj => (route i hi).trans (route j hj).reverse

/-- Both sides of a one-vertex separation, each closed up with the cut vertex. -/
structure Sides (G : Graph n) (U : Region n) (c : Fin n) (A B : Region n) : Prop where
  pole : U c
  sideA : EndAt G U A c
  sideB : EndAt G U B c
  disjoint : ∀ i,A i → ¬B i
  cover : ∀ i,U i → A i ∨ B i ∨ i = c

theorem sides_of_cut {G : Graph n} {U : Region n} {c} (conn : ConnectedOn G U)
    (cut : ¬ConnectedOn G (del U c)) : ∃ A B,Sides G U c A B := by
  classical
  have uc : U c := Classical.byContradiction (fun nc =>
    cut (conn_congr (fun i => by simp [del]; grind) conn))
  obtain ⟨A,s⟩ := shore_of_disconnected cut
  let B := fun i => del U c i ∧ ¬A i
  have s' := shore_complement s
  exact ⟨A,B,uc,⟨uc,s.nonempty,s.inside,fun i j a uj jc => s.closed i j a ⟨uj,jc⟩⟩,
    ⟨uc,s'.nonempty,s'.inside,fun i j b uj jc => s'.closed i j b ⟨uj,jc⟩⟩,
    fun _ ai bi => bi.2 ai,fun i ui => by by_cases ai : A i
                                          · exact Or.inl ai
                                          · by_cases ic : i = c
                                            · exact Or.inr (Or.inr ic)
                                            · exact Or.inr (Or.inl ⟨⟨ui,ic⟩,ai⟩)⟩

abbrev plus (A : Region n) (c : Fin n) := fun i => A i ∨ i = c

theorem sides_connected {G : Graph n} {U A B : Region n} {c} (s : Sides G U c A B)
    (conn : ConnectedOn G U) : ConnectedOn G (plus A c) ∧ ConnectedOn G (plus B c) := by
  have a' : ∀ i,(U i ∧ ¬B i) ↔ plus A c i := by
    intro i
    have aa := s.sideA.inside i; have bb := s.sideB.inside i; have cov := s.cover i
    have dd := s.disjoint i; have uc := s.pole
    unfold plus; grind
  have b' : ∀ i,(U i ∧ ¬A i) ↔ plus B c i := by
    intro i; have aa := s.sideA.inside i; have bb := s.sideB.inside i; have cov := s.cover i
    have dd := s.disjoint i; have uc := s.pole
    unfold plus; grind
  exact ⟨conn_congr a' (s.sideB.outside_conn conn),conn_congr b' (s.sideA.outside_conn conn)⟩

end KMO
