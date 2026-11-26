import KMO.LeafStar
namespace KMO
variable {n : Nat}

structure CycleOn (G : Graph n) (C : Region n) : Prop where
  nonempty : ∃ i,C i
  connected : ConnectedOn G C
  regular : ∀ i,C i → (G.within C).degree i = 2

/-- Tutte's peripheral cycle theorem, with both a prescribed edge and a
prescribed avoided vertex. Three is vertex connectivity on the induced domain. -/
def TuttePeripheral : Prop := ∀ {n : Nat} (G : Graph n) (U : Region n), Three G U → 4 ≤ card U →
  ∀ x y v, U x → U y → U v → G.adj x y → v ≠ x → v ≠ y →
  ∃ C : Region n, (∀ i,C i → U i) ∧ C x ∧ C y ∧ ¬C v ∧ CycleOn G C ∧
    ConnectedOn G (fun i => U i ∧ ¬C i)

namespace Piece
variable {G : Graph n} {U : Region n} {p : Piece n}

theorem large_domain {w : Fin n} (s : p.valid G (without w)) (deg : ∀ i,4 ≤ G.degree i) :
    4 ≤ card p.domain := by
  obtain ⟨x,lx⟩ := s.nonempty
  let A := fun i => (p.domain i ∧ i ≠ x)
  have sub : ∀ i,G.adj x i ∧ i ≠ w → A i := fun i e =>
    ⟨neighbor_domain s lx e.2 e.1,fun ix => G.loopless x (ix ▸ e.1)⟩
  have k := card_mono sub
  have j := card_split (G.adj x) (fun i => i = w)
  have atw := card_mono (S := fun i => G.adj x i ∧ i = w) (T := fun i => i = w) (fun _ => And.right)
  rw [card_single w] at atw
  have eq := card_erase (S := p.domain) (v := x) (Or.inl lx)
  change card A + 1 = _ at eq
  change _ + card (fun i => G.adj x i ∧ i ≠ w) = G.degree x at j
  have low := deg x; omega

theorem exterior_pole_paths (s : p.valid G U) (two : Two G U) {z} (zout : del₂ U p.a p.b z) (nz : ¬p.L z) :
    Reach G (fun i => del U p.b i ∧ ¬p.L i) p.a z ∧
    Reach G (fun i => del U p.a i ∧ ¬p.L i) p.b z := by
  obtain ⟨ua,ub,ne⟩ := poles s two
  have a : EndAt G (del U p.b) p.L p.a := ⟨⟨ua,ne⟩,s.nonempty,fun i li =>
    ⟨⟨(s.inside i li).1.1,(s.inside i li).2⟩,(s.inside i li).1.2⟩,
    fun i j li uj ja => s.closed i j li ⟨⟨uj.1,ja⟩,uj.2⟩⟩
  have b : EndAt G (del U p.a) p.L p.b := ⟨⟨ub,ne.symm⟩,s.nonempty,s.inside,
    fun i j li uj jb => s.closed i j li ⟨uj,jb⟩⟩
  exact ⟨a.outside_path (two.2 p.b) ⟨zout.1.1,zout.2⟩ nz,b.outside_path (two.2 p.a) zout.1 nz⟩

theorem lift_complement (s : p.valid G U) (two : Two G U) {C : Region n}
    (inside : ∀ i,C i → p.domain i) (avoid : ¬C p.a)
    (connected : ConnectedOn (p.torso G (poles s two).2.2) (fun i => p.domain i ∧ ¬C i)) :
    ConnectedOn G (fun i => U i ∧ ¬C i) := by
  classical
  obtain ⟨ua,ub,ne⟩ := poles s two
  let V := fun i => U i ∧ ¬C i
  have toA z (out : del₂ U p.a p.b z) (nz : ¬p.L z) : Reach G V p.a z := by
    apply (exterior_pole_paths s two out nz).1.transport _ (fun _ _ _ _ => id)
    intro i hi; refine ⟨hi.1.1,?_⟩; intro ci
    rcases inside i ci with li | eq | eq
    · exact hi.2 li
    · exact avoid (eq ▸ ci)
    · exact hi.1.2 eq
  have bridge (nb : ¬C p.b) : Reach G V p.a p.b := by
    obtain ⟨z,out,nz⟩ := s.proper
    have bz := (exterior_pole_paths s two out nz).2
    have pp : Reach G V p.b z := by
      apply bz.transport _ (fun _ _ _ _ => id)
      intro i hi; refine ⟨hi.1.1,?_⟩; intro ci
      rcases inside i ci with li | eq | eq
      · exact hi.2 li
      · exact hi.1.2 eq
      · exact nb (eq ▸ ci)
    exact (toA z out nz).trans pp.reverse
  have route (i) (hi : V i) : Reach G V p.a i := by
    by_cases di : p.domain i
    · have path := connected p.a ⟨Or.inr (Or.inl rfl),avoid⟩ i ⟨di,hi.2⟩
      induction path with
      | here _ => exact .here ⟨ua,avoid⟩
      | @next x y q e hy ih =>
        have vy : V y := ⟨domain_subset s two _ hy.1,hy.2⟩
        have vx : V x := ⟨domain_subset s two _ q.finish.1,q.finish.2⟩
        have pathx := ih vx q.finish.1
        rcases e with re | ⟨eqx,eqy⟩ | ⟨eqy,eqx⟩
        · exact pathx.next re vy
        · subst x; subst y; exact bridge hy.2
        · subst x; subst y; exact .here ⟨ua,avoid⟩
    · exact toA i ⟨⟨hi.1,fun eq => di (Or.inr (Or.inl eq))⟩,fun eq => di (Or.inr (Or.inr eq))⟩ (fun li => di (Or.inl li))
  exact fun i hi j hj => (route i hi).reverse.trans (route j hj)

theorem lift_cycle (s : p.valid G U) (two : Two G U) {C : Region n}
    (avoid : ¬C p.a) (cycle : CycleOn (p.torso G (poles s two).2.2) C) : CycleOn G C := by
  let K := p.torso G (poles s two).2.2
  have same i j (ci : C i) (cj : C j) : K.adj i j ↔ G.adj i j := by
    refine ⟨?_,Or.inl⟩; rintro (ge | ⟨e,_⟩ | ⟨e,_⟩)
    · exact ge
    · exact False.elim (avoid (e ▸ ci))
    · exact False.elim (avoid (e ▸ cj))
  refine ⟨cycle.nonempty,conn_move cycle.connected (fun _ => Iff.rfl) (fun i j ci cj => (same i j ci cj).mp),?_⟩
  intro v cv
  have e : (G.within C).degree v = (K.within C).degree v := by
    apply card_congr; intro j
    constructor
    · intro hj; exact ⟨Or.inl hj.1,hj.2⟩
    · intro hj; exact ⟨(same _ _ cv hj.2.2).mp hj.1,hj.2⟩
  exact e.trans (cycle.regular v cv)

end Piece

theorem half_degree {G : Graph n} {w} (i : Fin n) (iw : i ≠ w) :
    (G.within (without w)).degree i + bit (G.adj i w) = G.degree i := by
  have s := card_split (G.adj i) (fun j => j = w)
  have e₁ : card (fun j => G.adj i j ∧ j = w) = bit (G.adj i w) := by
    rw [← card_flag w (G.adj i w)]; apply card_congr; intro j; grind
  have e₂ : card (fun j => G.adj i j ∧ j ≠ w) = (G.within (without w)).degree i :=
    card_congr (fun j => by change (_ ∧ _) ↔ (_ ∧ i ≠ w ∧ _); simp [iw])
  rw [e₁,e₂] at s; change _ + _ = card (G.adj i); omega

theorem universal_coloring {G : Graph n} {w} (three : ThreeConnected G) (md : ∀ v,4 ≤ G.degree v)
    (ew : G.degree w % 2 = 0) (od : ∀ v,v ≠ w → G.oddAt v) (all : ∀ v,v ≠ w → G.adj w v) :
    OddThree G := by
  let U := without w
  have same := card_congr (S := G.adj w) (T := U) (fun i => ⟨fun e eq => G.loopless w (eq ▸ e),all i⟩)
  change G.degree w = card U at same
  have size : 4 ≤ card U := same ▸ md w
  have ex := card_pos.mp (Nat.lt_of_lt_of_le (by decide : 0 < 4) size)
  have even := same ▸ ew
  have facts i (ui : U i) : 3 ≤ (G.within U).degree i ∧ (G.within U).degree i % 2 = 0 := by
    have eq := half_degree (G := G) i ui; have e := G.sym (all i ui); simp [bit,e] at eq
    have oi := od i ui; unfold Graph.oddAt at oi; have k := md i
    change (G.within U).degree i + 1 = G.degree i at eq; omega
  obtain ⟨a,ua⟩ := ex
  have nc := nonclique_even ⟨a,ua⟩ even (fun i ui => (facts i ui).2)
  obtain ⟨x,y,pair⟩ := nonadjacent_pair (two_after_delete three w)
    (fun i ui => Nat.le_trans (by decide : 2 ≤ 3) (facts i ui).1) nc ⟨a,ua,(facts a ua).1⟩
  apply star_coloring ew od (x := x) (S := del₂ U x y)
  refine ⟨all x pair.first,fun k => k.1.1 rfl,fun k => k.1.2 rfl,?_,fun i k _ => all i k.1.1,?_,pair.connected⟩
  · intro i e iw; exact ⟨⟨iw,fun eq => G.loopless x (eq ▸ e)⟩,fun eq => pair.nonedge (eq ▸ e)⟩
  · have a := card_erase (S := U) (v := x) pair.first
    have b := card_erase (S := del U x) (v := y) ⟨pair.second,Ne.symm pair.different⟩
    change card (del U x) + 1 = card U at a
    change card (del₂ U x y) + 1 = card (del U x) at b
    omega

theorem unique_even_of_tutte (tutte : TuttePeripheral) {G : Graph n} {w}
    (three : ThreeConnected G) (md : ∀ v,4 ≤ G.degree v)
    (ew : G.degree w % 2 = 0) (od : ∀ v,v ≠ w → G.oddAt v) : OddThree G := by
  classical
  let U := without w
  let T := G.adj w
  by_cases universal : ∀ i,U i → T i
  · exact universal_coloring three md ew od universal
  have outside : ∃ i,U i ∧ ¬T i := by
    apply Classical.byContradiction; intro no; apply universal; intro i ui
    exact Classical.byContradiction (fun nt => no ⟨i,ui,nt⟩)
  have pos : 0 < G.degree w := by have := md w; omega
  obtain ⟨t,tt⟩ := Graph.degree_pos.mp pos
  have ut : U t := fun eq => G.loopless w (eq ▸ tt)
  have two : Two G U := two_after_delete three w
  by_cases robust : Three G U
  · obtain ⟨u,uu,nu⟩ := outside
    obtain ⟨x,y,ux,uy,tx,ny,e⟩ := adjacent_across two.1 ut uu tt nu
    have size : 4 ≤ card U := Nat.le_trans (md w) (card_mono (fun i (k : T i) => show U i from fun eq => G.loopless w (show G.adj w w by simpa [T,eq] using k)))
    obtain ⟨v,uv,vx,vy⟩ := avoid_two (Nat.le_trans (by decide : 3 ≤ 4) size) x y
    obtain ⟨C,cu,cx,cy,_,cycle,conn⟩ := tutte G U robust size x y v ux uy uv e vx vy
    apply mixed_cycle_coloring (C := C) _ md ew od
    exact ⟨fun cw => cu w cw rfl,cycle.regular,cycle.connected,conn,⟨x,cx,tx⟩,⟨y,cy,ny⟩⟩
  · obtain ⟨p,m⟩ := Piece.exists_minimal two robust
    have poles := Piece.poles m.1 two
    have touch : ∃ i,p.L i ∧ T i := by
      obtain ⟨i,li⟩ := m.1.nonempty
      have di := m.1.inside _ li
      have path := (global_three three).2 p.a p.b
      obtain ⟨j,k,_,dk,lj,nk,e⟩ := adjacent_across path (x := i) (y := w)
        ⟨⟨trivial,di.1.2⟩,di.2⟩ ⟨⟨trivial,Ne.symm poles.1⟩,Ne.symm poles.2.1⟩ li (fun lw => (m.1.inside w lw).1.1 rfl)
      have kw : k = w := Classical.byContradiction (fun kn => nk (m.1.closed _ _ lj ⟨⟨kn,dk.1.2⟩,dk.2⟩ e))
      exact ⟨j,lj,G.sym (kw ▸ e)⟩
    by_cases homogeneous : ∀ i,p.L i → T i
    · have leaf : Leaf G w p := ⟨m,two,homogeneous,md,od⟩
      obtain ⟨x,S,cert⟩ := leaf.has_star
      exact star_coloring ew od cert
    · have missed : ∃ i,p.L i ∧ ¬T i := by
        apply Classical.byContradiction; intro no; apply homogeneous; intro i li
        exact Classical.byContradiction (fun ni => no ⟨i,li,ni⟩)
      obtain ⟨i,li,ti⟩ := touch; obtain ⟨j,lj,nj⟩ := missed
      obtain ⟨x,y,lx,ly,tx,ny,edge⟩ := adjacent_across (Piece.inner_conn m) li lj ti nj
      have st := Piece.torso_three m two (outside := w) (by simp [U,without])
      obtain ⟨C,dom,cx,cy,avoid,circ,conn⟩ := tutte _ _ st (Piece.large_domain m.1 md) x y p.a
        (Or.inl lx) (Or.inl ly) (Or.inr (Or.inl rfl)) (Or.inl edge)
        (Ne.symm (m.1.inside _ lx).1.2) (Ne.symm (m.1.inside _ ly).1.2)
      have lifted := Piece.lift_cycle m.1 two avoid circ
      have connected := Piece.lift_complement m.1 two dom avoid conn
      apply mixed_cycle_coloring (C := C) _ md ew od
      exact ⟨fun cw => Piece.domain_subset m.1 two w (dom w cw) rfl,lifted.regular,lifted.connected,connected,
        ⟨x,cx,tx⟩,⟨y,cy,ny⟩⟩

end KMO
