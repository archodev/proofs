import KMO.Star
import KMO.Components

namespace KMO
variable {n : Nat}

theorem Reach.on_support {G : Graph n} {x y} (p : Reach G (Full n) x y)
    (hx : G.supp x) : Reach G G.supp x y := by
  induction p with
  | here => exact .here hx
  | next _ e _ ih => exact ih.next e ⟨_,G.sym e⟩

theorem euler_coloring {G K : Graph n} {w : Fin n}
    (sub : K.Sub G) (full : K.degree w = G.degree w)
    (od : ∀ v, v ≠ w → G.oddAt v) (even : ∀ v, K.degree v % 2 = 0)
    (order : card K.supp % 2 = 0) (conn : ConnectedOn K K.supp) : OddThree G := by
  obtain ⟨A,as,ap⟩ := parity_join K K.supp K.supp conn (fun _ => id) order
  have ak : A.Sub K := by intro _ _ e; exact (as e).1
  let B := K.diff A
  have bk : B.Sub K := by intro _ _ e; exact e.1
  have d : A.Disj B := by intro i j e b; exact b.2 e
  have eqn v := Graph.degree_diff ak v
  have vanish {v} (h : ¬K.supp v) : A.degree v = 0 ∧ B.degree v = 0 := by
    have hk : ¬0 < K.degree v := fun k => h (Graph.degree_pos.mp k)
    have t := eqn v
    change A.degree v + B.degree v = K.degree v at t
    omega
  apply three_from_two (by intro _ _ e; exact sub (ak e)) (by intro _ _ e; exact sub (bk e)) d
  · intro v; by_cases hv : K.supp v
    · right; simpa [bit,hv] using ap v
    · exact Or.inl (vanish hv).1
  · intro v; by_cases hv : K.supp v
    · right; have h := ap v; simp [bit,hv] at h
      have z := eqn v; have ev := even v
      change A.degree v + B.degree v = K.degree v at z
      unfold Graph.oddAt; omega
    · exact Or.inl (vanish hv).2
  · have incl : (A.union B).Sub G := by intro i j h; exact h.elim (fun e => sub (ak e)) (fun e => sub (bk e))
    intro v; have t := Graph.degree_diff incl v
    rw [Graph.degree_union d] at t
    have z := eqn v
    change A.degree v + B.degree v = K.degree v at z
    rw [z] at t
    by_cases vw : v = w
    · subst v; left; omega
    · right; have ov := od v vw; have ev := even v; unfold Graph.oddAt at *; omega

theorem odd_support_coloring {G F : Graph n} {w : Fin n}
    (sub : F.Sub (G.within (fun v => v ≠ w))) (oddSupport : card F.supp % 2 = 1)
    (bd : ∀ v, F.degree v % 2 = bit (G.adj w v)) (anchor : Anchored F (G.adj w))
    (ew : G.degree w % 2 = 0) (od : ∀ i, i ≠ w → G.oddAt i)
    (positive : 0 < G.degree w) : OddThree G := by
  let X := Graph.star w (G.adj w) (G.loopless w)
  let K := F.union X
  have xsub : X.Sub G := by
    intro i j h; rcases h with ⟨rfl,e⟩ | ⟨rfl,e⟩
    · exact e
    · exact G.sym e
  have ks : K.Sub G := by intro i j h; exact h.elim (fun k => (sub k).1) (fun k => xsub k)
  have dis : F.Disj X := by
    intro i j f e; rcases e with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact (sub f).2.1 rfl
    · exact (sub f).2.2 rfl
  have fw : F.degree w = 0 := outside (S := fun i => i ≠ w) (by intro _ _ e; exact (sub e).2.1) (by simp)
  have part v : K.degree v = F.degree v + (if v = w then G.degree w else bit (G.adj w v)) := by
    rw [Graph.degree_union dis,Graph.degree_star]; rfl
  have kw : K.degree w = G.degree w := by simpa [fw] using part w
  have sw : K.supp w := Graph.degree_pos.mp (kw ▸ positive)
  have fs (v) (t : G.adj w v) : F.supp v := by
    have h := bd v; simp [bit,t] at h
    apply Graph.degree_pos.mp; omega
  have spec (v) : K.supp v ↔ F.supp v ∨ v = w := by
    constructor
    · rintro ⟨j,e | e⟩
      · exact Or.inl ⟨j,e⟩
      · rcases e with ⟨e,_⟩ | ⟨_,t⟩
        · exact Or.inr e
        · exact Or.inl (fs _ t)
    · rintro (⟨j,e⟩ | rfl)
      · exact ⟨j,Or.inl e⟩
      · exact sw
  have count : card K.supp = card F.supp + 1 := by
    rw [card_congr spec,card_union,card_single]
    intro i h e; subst i; have := Graph.degree_pos.mpr h; omega
  apply euler_coloring ks kw od
  · intro v; by_cases vw : v = w
    · subst v; rwa [kw]
    · rw [part,if_neg vw,Nat.add_mod,bd]; by_cases t : G.adj w v <;> simp [bit,t]
  · omega
  · have toW v (active : K.supp v) : Reach K (Full n) v w := by
      rcases (spec v).mp active with f | rfl
      · obtain ⟨t,ht,p⟩ := anchor v f
        have pp := reach_full_mono (B := K) (by intro _ _ e; exact Or.inl e) p
        exact pp.next (Or.inr (Or.inr ⟨rfl,ht⟩)) trivial
      · exact .here trivial
    intro i hi j hj
    exact ((toW i hi).trans (toW j hj).reverse).on_support hi

/-- Two supports agree outside a switch region, and exactly one is active at
each member of an odd-sized region. Thus one support has odd size. -/
theorem switch_odd_support {F₀ F₁ : Graph n} {Z : Region n}
    (hz : card Z % 2 = 1) (flip : ∀ v, Z v ↔ XorP (F₀.supp v) (F₁.supp v)) :
    card F₀.supp % 2 = 1 ∨ card F₁.supp % 2 = 1 := by
  rw [card_congr flip, card_xor] at hz; omega

end KMO
