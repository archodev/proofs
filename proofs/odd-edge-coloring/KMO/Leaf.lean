import KMO.Cycle
import KMO.Separator
import KMO.Pair
namespace KMO
variable {n : Nat}
abbrev without (w : Fin n) := fun i => i ≠ w

structure Leaf (G : Graph n) (w : Fin n) (p : Piece n) : Prop where
  piece : p.minimal G (without w)
  two : Two G (without w)
  terminal : ∀ x,p.L x → G.adj w x
  degrees : ∀ i,4 ≤ G.degree i
  odd : ∀ i,i ≠ w → G.oddAt i

namespace Leaf
variable {G : Graph n} {w : Fin n} {p : Piece n}

abbrev ports (G : Graph n) (p : Piece n) (x : Fin n) := fun i =>
  (i = p.a ∧ G.adj x p.a) ∨ (i = p.b ∧ G.adj x p.b)
abbrev candidate (G : Graph n) (p : Piece n) (x : Fin n) := fun i => del p.L x i ∨ ports G p x i

theorem port_card (h : Leaf G w p) (x) :
    card (ports G p x) = bit (G.adj x p.a) + bit (G.adj x p.b) := by
  unfold ports
  have ne := (Piece.poles h.piece.1 h.two).2.2
  rw [card_union (by rintro i ⟨rfl,_⟩ ⟨eq,_⟩; exact ne eq),card_flag,card_flag]

theorem candidate_card (h : Leaf G w p) {x} (lx : p.L x) :
    card (candidate G p x) + 1 = card p.L + card (ports G p x) := by
  have ca := card_erase lx
  change card (del p.L x) + 1 = card p.L at ca
  have dis i (li : del p.L x i) : ¬ports G p x i := by
    have e := h.piece.1.inside _ li.1
    rintro (⟨eq,_⟩ | ⟨eq,_⟩)
    · exact e.1.2 eq
    · exact e.2 eq
  have k := card_union dis; change card (candidate G p x) = _ at k; omega

theorem neighbor_cases (h : Leaf G w p) {x i} (lx : p.L x) (e : G.adj x i) :
    p.L i ∨ i = w ∨ i = p.a ∨ i = p.b := by
  by_cases iw : i = w
  · exact Or.inr (Or.inl iw)
  · rcases Piece.neighbor_domain h.piece.1 lx iw e with li | pa | pb
    · exact Or.inl li
    · exact Or.inr (Or.inr (Or.inl pa))
    · exact Or.inr (Or.inr (Or.inr pb))

theorem degree_formula (h : Leaf G w p) {x} (lx : p.L x) :
    G.degree x = (G.within p.L).degree x + card (ports G p x) + 1 := by
  let I := fun j => p.L j ∧ G.adj x j
  let P := ports G p x
  have a := Piece.poles h.piece.1 h.two
  have e : ∀ j,G.adj x j ↔ (I j ∨ P j) ∨ j = w := by
    intro j; constructor
    · intro edge; obtain lj | rfl | rfl | rfl := h.neighbor_cases lx edge
      · exact Or.inl (Or.inl ⟨lj,edge⟩)
      · exact Or.inr rfl
      · exact Or.inl (Or.inr (Or.inl ⟨rfl,edge⟩))
      · exact Or.inl (Or.inr (Or.inr ⟨rfl,edge⟩))
    · rintro ((hj | (⟨rfl,g⟩ | ⟨rfl,g⟩)) | rfl)
      · exact hj.2
      · exact g
      · exact g
      · exact G.sym (h.terminal _ lx)
  have dis i (ii : I i) : ¬P i := by
    have k := h.piece.1.inside _ ii.1
    rintro (⟨e,_⟩ | ⟨e,_⟩)
    · exact k.1.2 e
    · exact k.2 e
  have dw i (ip : I i ∨ P i) : i ≠ w := by
    rcases ip with ii | ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact (h.piece.1.inside _ ii.1).1.1
    · exact a.1
    · exact a.2.1
  change card (G.adj x) = _
  rw [card_congr e,card_union dw,card_union dis,card_single,neighbors_in lx]

theorem local_min (h : Leaf G w p) {x} (lx : p.L x) : 2 ≤ (G.within p.L).degree x := by
  have eqn := h.degree_formula lx; rw [h.port_card] at eqn
  have odd := h.odd _ (h.piece.1.inside _ lx).1.1
  have md := h.degrees x
  unfold Graph.oddAt at odd
  by_cases a : G.adj x p.a <;> by_cases b : G.adj x p.b <;> simp [bit,a,b] at eqn <;> omega

theorem large (h : Leaf G w p) : 3 ≤ card p.L := by
  obtain ⟨x,lx⟩ := h.piece.1.nonempty
  have sub : ∀ j,(G.within p.L).adj x j → del p.L x j :=
    fun j e => ⟨e.2.2,fun eq => G.loopless x (eq ▸ e.1)⟩
  have k := card_mono sub; have z := card_erase lx; have d := h.local_min lx
  change (G.within p.L).degree x ≤ card (del p.L x) at k
  change card (del p.L x) + 1 = _ at z
  omega

theorem candidate_star (h : Leaf G w p) {x S} (lx : p.L x)
    (upper : ∀ i,S i → candidate G p x i)
    (lower : ∀ i,G.adj x i → i ≠ w → S i)
    (even : card S % 2 = 0) (conn : ConnectedOn G S) : HasStar G w := by
  have poles := Piece.poles h.piece.1 h.two
  have xl := h.piece.1.inside x lx
  refine ⟨x,S,h.terminal x lx,?_,?_,lower,?_,even,conn⟩
  · intro sw; obtain l | ⟨e,_⟩ | ⟨e,_⟩ := upper w sw
    · exact (h.piece.1.inside w l.1).1.1 rfl
    · exact poles.1 e.symm
    · exact poles.2.1 e.symm
  · intro sx; obtain l | ⟨e,_⟩ | ⟨e,_⟩ := upper x sx
    · exact l.2 rfl
    · exact xl.1.2 e
    · exact xl.2 e
  · intro i si no; obtain l | ⟨rfl,e⟩ | ⟨rfl,e⟩ := upper i si
    · exact h.terminal _ l.1
    · exact False.elim (no e)
    · exact False.elim (no e)

theorem candidate_contains (h : Leaf G w p) {x i} (lx : p.L x) (e : G.adj x i) (iw : i ≠ w) :
    candidate G p x i := by
  obtain li | eq | rfl | rfl := h.neighbor_cases lx e
  · exact Or.inl ⟨li,fun eq => G.loopless _ (eq ▸ e)⟩
  · exact False.elim (iw eq)
  · exact Or.inr (Or.inl ⟨rfl,e⟩)
  · exact Or.inr (Or.inr ⟨rfl,e⟩)

abbrev poleN (G : Graph n) (p : Piece n) (a : Fin n) := fun j => p.L j ∧ G.adj a j

theorem pole_degrees (h : Leaf G w p) {a b}
    (order : (a = p.a ∧ b = p.b) ∨ (a = p.b ∧ b = p.a)) : 2 ≤ card (poleN G p a) := by
  classical
  have strong := Piece.torso_three h.piece h.two (outside := w) (by simp [without])
  have poles := Piece.poles h.piece.1 h.two
  let K := p.torso G poles.2.2
  have neighbors := Piece.neighbors_poles h.piece.1 h.two
  have one : ∃ j,poleN G p a j := by
    rcases order with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · obtain ⟨j,lj,e⟩ := neighbors.1; exact ⟨j,lj,G.sym e⟩
    · obtain ⟨j,lj,e⟩ := neighbors.2; exact ⟨j,lj,G.sym e⟩
  obtain ⟨j,jl,aj⟩ := one
  obtain ⟨z,zl,zj⟩ := avoid_one (Nat.le_trans (by decide : 2 ≤ 3) h.large) j
  have dd (i) (li : p.L i) := h.piece.1.inside i li
  have az : p.domain a ∧ a ≠ b ∧ a ≠ j := by
    rcases order with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [Piece.domain]; all_goals have := dd j jl; grind
  have zb : z ≠ b := by have := dd z zl; rcases order with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> grind
  have path := strong.2 b j a ⟨⟨az.1,az.2.1⟩,az.2.2⟩ z ⟨⟨Or.inl zl,zb⟩,zj⟩
  have cross : ∃ k,poleN G p a k ∧ k ≠ j := by
    apply Classical.byContradiction; intro no
    have endv := path.preserve (L := fun k => k = a) rfl (by
      intro i k ia hk e
      subst i
      have lk : ¬p.L k := by
        intro lk; have ak : G.adj a k := by
          rcases e with g | special
          · exact g
          · have inL := dd k lk
            change (_ = _ ∧ _ = _) ∨ (_ = _ ∧ _ = _) at special
            grind
        exact no ⟨k,⟨lk,ak⟩,hk.2⟩
      have dom := hk.1.1.resolve_left lk
      have kb := hk.1.2
      grind)
    have k := dd z zl; grind
  obtain ⟨k,hk,ne⟩ := cross
  have bound := card_mono (S := fun i => i = k ∨ i = j) (T := poleN G p a)
    (by rintro _ (rfl|rfl); exact hk; exact ⟨jl,aj⟩)
  rwa [card_pair ne] at bound

theorem candidate_conn (h : Leaf G w p) {x : Fin n} (cx : ConnectedOn G (del p.L x)) :
    ConnectedOn G (candidate G p x) := by
  apply attach_vertices cx (fun _ => Or.inl)
  intro i hi notL
  have pn := hi.resolve_left notL
  have ports2 : 2 ≤ card (poleN G p i) := by
    rcases pn with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact h.pole_degrees (b := p.b) (Or.inl ⟨rfl,rfl⟩)
    · exact h.pole_degrees (b := p.a) (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨j,⟨lj,e⟩,jx⟩ := avoid_one ports2 x; exact ⟨j,⟨lj,jx⟩,e⟩

theorem take_pair (h : Leaf G w p) {x y} (pair : PairWitness G p.L x y)
    (attach : ∀ i, ports G p x i → ∃ z,poleN G p i z ∧ z ≠ x ∧ z ≠ y) : HasStar G w := by
  let V := candidate G p x
  have cx := connected_after_one pair (Nat.lt_of_lt_of_le (by decide : 0 < 2) (h.local_min pair.second))
  by_cases even : card V % 2 = 0
  · exact h.candidate_star pair.first (fun _ => id) (fun _ => h.candidate_contains pair.first) even (h.candidate_conn cx)
  have vy : V y := Or.inl ⟨pair.second,Ne.symm pair.different⟩
  have eqn := card_erase vy
  apply h.candidate_star (S := del V y) pair.first (fun _ k => k.1)
  · intro i e iw; exact ⟨h.candidate_contains pair.first e iw,fun eq => pair.nonedge (eq ▸ e)⟩
  · change card (del V y) + 1 = card V at eqn; omega
  · apply attach_vertices pair.connected (fun _ k => ⟨Or.inl k.1,k.2⟩)
    intro i hi ni; have pn : ports G p x i := hi.1.resolve_left (fun k => ni ⟨k,hi.2⟩)
    obtain ⟨z,⟨lz,e⟩,zx,zy⟩ := attach i pn; exact ⟨z,⟨⟨lz,zx⟩,zy⟩,e⟩

end Leaf
end KMO
