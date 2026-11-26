import KMO.Leaf

namespace KMO
variable {n : Nat}

theorem nonclique_even {G : Graph n} {U : Region n} (ne : ∃ x,U x)
    (even : card U % 2 = 0) (degrees : ∀ x,U x → (G.within U).degree x % 2 = 0) :
    ∃ x y,U x ∧ U y ∧ x ≠ y ∧ ¬G.adj x y := by
  classical
  obtain ⟨x,ux⟩ := ne
  apply Classical.byContradiction; intro bad
  have eq : (G.within U).degree x = card (del U x) := by
    apply card_congr; intro j
    constructor
    · intro e; exact ⟨e.2.2,fun eq => G.loopless x (eq ▸ e.1)⟩
    · intro dj; exact ⟨Classical.byContradiction (fun no => bad ⟨x,j,ux,dj.1,Ne.symm dj.2,no⟩),ux,dj.1⟩
  have p := card_erase ux; change card (del U x) + 1 = _ at p
  have d := degrees _ ux; omega

namespace Leaf
variable {G : Graph n} {w : Fin n} {p : Piece n}

abbrev survives (N : Region n) (x y : Fin n) := ∃ z,N z ∧ z ≠ x ∧ z ≠ y

theorem bad_pair_unique {N A B : Region n} (deg : 2 ≤ card N) (dis : ∀ i,A i → ¬B i)
    {x y x' y'} (_ax : A x) (by' : B y) (ax' : A x') (_byLast : B y')
    (a : ¬survives N x y) (b : ¬survives N x' y') : x = x' ∧ y = y' := by
  classical
  have ab z (nz : N z) : z = x ∨ z = y := by
    by_cases zx : z = x
    · exact Or.inl zx
    · exact Or.inr (Classical.byContradiction (fun zy => a ⟨z,nz,zx,zy⟩))
  have cd z (nz : N z) : z = x' ∨ z = y' := by
    by_cases zx : z = x'
    · exact Or.inl zx
    · exact Or.inr (Classical.byContradiction (fun zy => b ⟨z,nz,zx,zy⟩))
  obtain ⟨i,ni,ix⟩ := avoid_one deg x
  obtain ⟨j,nj,jy⟩ := avoid_one deg y
  have iy := (ab i ni).resolve_left ix
  have jx := (ab j nj).resolve_right jy
  have a1 := cd i ni; have b1 := cd j nj
  grind

theorem cut_star (h : Leaf G w p) {c} (cut : ¬ConnectedOn G (del p.L c)) : HasStar G w := by
  classical
  have conn := Piece.inner_conn h.piece
  obtain ⟨A,B,s⟩ := sides_of_cut conn cut
  have cc := sides_connected s conn
  obtain ⟨x,x',ax,ax',xx,cx,cx'⟩ := noncut_on_side s.localEnd cc.1
    (fun i ai => by rw [s.local_degree ai]; exact h.local_min (s.sideA.inside _ ai).1)
  obtain ⟨y,y',by',by'',yy,cy,cy'⟩ := noncut_on_side s.symm.localEnd cc.2
    (fun i bi => by rw [s.symm.local_degree bi]; exact h.local_min (s.sideB.inside _ bi).1)
  let N := poleN G p
  have da : 2 ≤ card (N p.a) := h.pole_degrees (b := p.b) (Or.inl ⟨rfl,rfl⟩)
  have db : 2 ≤ card (N p.b) := h.pole_degrees (b := p.a) (Or.inr ⟨rfl,rfl⟩)
  have solve {i j} (ai : A i) (bj : B j) (ci : ConnectedOn G (del (plus A c) i))
      (cj : ConnectedOn G (del (plus B c) j)) (sa : survives (N p.a) i j) (sb : survives (N p.b) i j) : HasStar G w := by
    have k := s.cross_ne ai bj
    apply h.take_pair (x := i) (y := j)
    · exact ⟨(s.sideA.inside _ ai).1,(s.sideB.inside _ bj).1,k.1,k.2,s.deleted_conn ai bj ci cj⟩
    · rintro z (⟨rfl,_⟩ | ⟨rfl,_⟩) <;> assumption
  apply Classical.byContradiction; intro no
  have cover {i j} (ai : A i) (bj : B j) (ci : ConnectedOn G (del (plus A c) i))
      (cj : ConnectedOn G (del (plus B c) j)) : ¬survives (N p.a) i j ∨ ¬survives (N p.b) i j := by
    by_cases aa : survives (N p.a) i j
    · exact Or.inr (fun b => no (solve ai bj ci cj aa b))
    · exact Or.inl aa
  have unique {v} (dv : 2 ≤ card (N v)) {i j i' j'} (ai : A i) (bj : B j) (ai' : A i') (bj' : B j') :=
    bad_pair_unique dv s.disjoint ai bj ai' bj'
  obtain a | a := cover ax by' cx cy <;> obtain b | b := cover ax by'' cx cy' <;>
    obtain d | d := cover ax' by' cx' cy <;>
    first | exact yy (unique da ax by' ax by'' a b).2
          | exact yy (unique db ax by' ax by'' a b).2
          | exact xx (unique da ax by' ax' by' a d).1
          | exact xx (unique db ax by' ax' by' a d).1
          | exact xx (unique da ax by'' ax' by' b d).1
          | exact xx (unique db ax by'' ax' by' b d).1

theorem common_large (h : Leaf G w p) (same : ∀ i,p.L i → (G.adj p.a i ↔ G.adj p.b i)) :
    3 ≤ card (poleN G p p.a) := by
  classical
  let N := poleN G p p.a
  have d : 2 ≤ card N := h.pole_degrees (b := p.b) (Or.inl ⟨rfl,rfl⟩)
  apply Nat.le_of_not_gt; intro small
  obtain ⟨x,nx⟩ := card_pos.mp (Nat.lt_of_lt_of_le (by decide : 0 < 2) d)
  obtain ⟨y,ny,yx⟩ := avoid_one d x
  obtain ⟨z,lz,zx,zy⟩ := avoid_two h.large x y
  have strong := Piece.torso_three h.piece h.two (outside := w) (by simp [without])
  have xx := h.piece.1.inside _ nx.1; have yy := h.piece.1.inside _ ny.1
  have zz := h.piece.1.inside _ lz
  have path := strong.2 x y p.a ⟨⟨Or.inr (Or.inl rfl),Ne.symm xx.1.2⟩,Ne.symm yy.1.2⟩ z ⟨⟨Or.inl lz,zx⟩,zy⟩
  have small' : card N ≤ 2 := Nat.le_of_lt_succ small
  have final := path.preserve (L := fun i => i = p.a ∨ i = p.b) (Or.inl rfl) (by
    intro i j pi uj e
    apply Classical.byContradiction; intro no
    have lj := uj.1.1.resolve_right no
    have nj : N j := by
      refine ⟨lj,?_⟩
      rcases e with ge | special
      · rcases pi with rfl | rfl
        · exact ge
        · exact (same j lj).mpr ge
      · change (_ = _ ∧ _ = _) ∨ (_ = _ ∧ _ = _) at special; grind
    exact (pair_exhaust yx ny nx small' nj).elim uj.2 uj.1.2)
  exact final.elim zz.1.2 zz.2

theorem has_star (h : Leaf G w p) : HasStar G w := by
  classical
  by_cases two : Two G p.L
  case neg =>
    apply Classical.byContradiction; intro no; apply two
    exact ⟨Piece.inner_conn h.piece,fun c => Classical.byContradiction (fun cut => no (h.cut_star cut))⟩
  by_cases quick : ∃ x,p.L x ∧ card (candidate G p x) % 2 = 0
  · obtain ⟨x,lx,e⟩ := quick
    exact h.candidate_star lx (fun _ => id) (fun _ => h.candidate_contains lx) e (h.candidate_conn (two.2 x))
  let M := G.within p.L
  have eqn {x} (lx : p.L x) : M.degree x % 2 = card p.L % 2 ∧
      card (ports G p x) % 2 = card p.L % 2 := by
    have bad : card (candidate G p x) % 2 ≠ 0 := fun k => quick ⟨x,lx,k⟩
    have c := h.candidate_card lx; have d := h.degree_formula lx
    have o := h.odd x (h.piece.1.inside _ lx).1.1; unfold Graph.oddAt at o
    change G.degree x = M.degree x + _ + 1 at d; omega
  have even : card p.L % 2 = 0 := by
    apply Classical.byContradiction; intro no
    have equals : card M.oddAt = card p.L := by
      apply card_congr; intro i; by_cases li : p.L i
      · have e := (eqn li).1; unfold Graph.oddAt; simp [li]; omega
      · have zero : M.degree i = 0 := outside (S := p.L) (by intro _ _ e; exact e.2.1) li
        simp [Graph.oddAt,zero,li]
    exact no (equals ▸ handshaking M)
  have equalPorts i (li : p.L i) : G.adj p.a i ↔ G.adj p.b i := by
    have k := (eqn li).2; rw [h.port_card,even] at k
    have flip (s) : G.adj s i ↔ G.adj i s := ⟨G.sym,G.sym⟩
    rw [flip,flip p.b]
    by_cases a : G.adj i p.a <;> by_cases b : G.adj i p.b <;> simp_all [bit]
  have big := h.common_large equalPorts
  have eqports : card (poleN G p p.a) = card (poleN G p p.b) :=
    card_congr (fun i => ⟨fun k => ⟨k.1,(equalPorts i k.1).mp k.2⟩,fun k => ⟨k.1,(equalPorts i k.1).mpr k.2⟩⟩)
  have nonclique := nonclique_even (G := G) h.piece.1.nonempty even (fun _ li => (eqn li).1.trans even)
  by_cases branch : ∃ x,p.L x ∧ 3 ≤ M.degree x
  · obtain ⟨x,y,pa⟩ := nonadjacent_pair two (fun _ li => h.local_min li) nonclique branch
    apply h.take_pair pa
    rintro i (⟨rfl,_⟩ | ⟨rfl,_⟩)
    · exact avoid_two big x y
    · exact avoid_two (eqports ▸ big) x y
  · have allPorts i (li : p.L i) : G.adj p.a i ∧ G.adj p.b i := by
      have max : ¬3 ≤ M.degree i := fun k => branch ⟨i,li,k⟩
      have min := h.local_min li
      have eq := h.degree_formula li; rw [h.port_card] at eq
      have o := h.odd i (h.piece.1.inside _ li).1.1; unfold Graph.oddAt at o
      have k := h.degrees i
      change G.degree i = M.degree i + _ + 1 at eq
      by_cases a : G.adj i p.a <;> by_cases b : G.adj i p.b <;> simp [bit,a,b] at eq
      · exact ⟨G.sym a,G.sym b⟩
      all_goals omega
    obtain ⟨x,y,lx,ly,xy,non⟩ := nonclique
    let V := candidate G p x
    have vy : V y := Or.inl ⟨ly,Ne.symm xy⟩
    have size := card_erase vy; change card (del V y) + 1 = card V at size
    have bad : card V % 2 ≠ 0 := fun k => quick ⟨x,lx,k⟩
    apply h.candidate_star (S := del V y) lx (fun _ k => k.1)
    · intro i e iw; exact ⟨h.candidate_contains lx e iw,fun eq => non (eq ▸ e)⟩
    · omega
    · have yy := h.piece.1.inside _ ly
      have aa : del V y p.a := ⟨Or.inr (Or.inl ⟨rfl,G.sym (allPorts x lx).1⟩),Ne.symm yy.1.2⟩
      have bb : del V y p.b := ⟨Or.inr (Or.inr ⟨rfl,G.sym (allPorts x lx).2⟩),Ne.symm yy.2⟩
      obtain ⟨z,lz,zx,zy⟩ := avoid_two h.large x y
      have visit i (vi : del V y i) : Reach G (del V y) p.a i := by
        rcases vi.1 with li | ⟨eq,_⟩ | ⟨eq,_⟩
        · exact (Reach.here aa).next (allPorts i li.1).1 vi
        · subst i; exact .here aa
        · subst i; exact ((Reach.here aa).next (allPorts z lz).1 ⟨Or.inl ⟨lz,zx⟩,zy⟩).next (G.sym (allPorts z lz).2) bb
      exact fun i hi j hj => (visit i hi).reverse.trans (visit j hj)

end Leaf
end KMO
