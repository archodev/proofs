import KMO.Rim
namespace KMO
variable {n : Nat}

structure Stubs (G B : Graph n) (w : Fin n) (C D : Region n) : Prop where
  sub : B.Sub G
  cross : ∀ i j, B.adj i j → (D i ∧ rest w C j) ∨ (D j ∧ rest w C i)
  count : ∀ i, C i → B.degree i = bit (D i)

theorem make_stubs {G : Graph n} {w C D u} (h : MixedCycle G w C)
    (tips : SwitchTips C (G.adj w) u D) (deg : ∀ v, 4 ≤ G.degree v) : ∃ B, Stubs G B w C D := by
  classical
  let f (i : Fin n) := if di : D i then Classical.choose (exit_of_cycle h deg (tips.onC i di)) else i
  have fprop i (di : D i) : rest w C (f i) ∧ G.adj i (f i) := by
    simpa [f,di] using Classical.choose_spec (exit_of_cycle h deg (tips.onC i di))
  let arc := fun i j => D i ∧ f i = j
  let B : Graph n := ⟨fun i j => arc i j ∨ arc j i,fun e => e.symm,by
    rintro i (⟨di,eq⟩ | ⟨di,eq⟩) <;> exact (fprop i di).1.2 (eq.symm ▸ tips.onC i di)⟩
  refine ⟨B,?_,?_,?_⟩
  · rintro i j (⟨di,rfl⟩ | ⟨dj,rfl⟩)
    · exact (fprop _ di).2
    · exact G.sym (fprop _ dj).2
  · rintro i j (⟨di,rfl⟩ | ⟨dj,rfl⟩)
    · exact Or.inl ⟨di,(fprop _ di).1⟩
    · exact Or.inr ⟨dj,(fprop _ dj).1⟩
  · intro i ci
    have inv (j) : ¬arc j i := fun a => (fprop _ a.1).1.2 (a.2 ▸ ci)
    by_cases di : D i
    · have eqn : B.degree i = card (fun j => j = f i) := card_congr (fun j => by
        change (arc i j ∨ arc j i) ↔ _; rw [or_iff_left (inv j)]; simp [arc,di,eq_comm])
      simp [eqn,card_single,bit,di]
    · have eqn : B.degree i = card (fun _ => False) := card_congr (fun j => by
        change (arc i j ∨ arc j i) ↔ _; simp [inv,arc,di])
      simp [eqn,card_empty,bit,di]

abbrev ends (C T D : Region n) := fun i => XorP (C i ∧ T i) (D i)
abbrev outerEnds (C T : Region n) (B : Graph n) := fun i => XorP (T i) (B.oddAt i) ∧ ¬C i

theorem bit_mod (d : Nat) : bit (d % 2 = 1) = d % 2 := by
  by_cases h : d % 2 = 1 <;> simp [bit,h] <;> omega

theorem outer_even {G B : Graph n} {w C D u} (tips : SwitchTips C (G.adj w) u D)
    (bs : Stubs G B w C D) (ew : G.degree w % 2 = 0) :
    card (outerEnds C (G.adj w) B) % 2 = 0 := by
  let T := G.adj w
  let H := fun i => XorP (T i) (B.oddAt i)
  have eqn := card_split H C
  have eqc : card (fun i => H i ∧ C i) = card (ends C T D) := by
    apply card_congr; intro i; by_cases ci : C i
    · have s := bs.count i ci
      by_cases di : D i <;> simp [ends,H,XorP,Graph.oddAt,s,ci,di,bit]
    · have nd : ¬D i := fun d => ci (tips.onC i d)
      simp [H,ends,XorP,ci,nd]
  rw [eqc] at eqn
  have eh := card_xor T B.oddAt; change card H % 2 = _ at eh
  have eb := handshaking B; have ee := tips.evenEnds
  change card (ends C T D) % 2 = 0 at ee
  change card T % 2 = 0 at ew
  change card (ends C T D) + card (outerEnds C T B) = card H at eqn
  change card (outerEnds C T B) % 2 = 0
  change card H % 2 = (card T + card B.oddAt) % 2 at eh
  omega

theorem stubs_off {G B : Graph n} {w C D u} (h : MixedCycle G w C)
    (tips : SwitchTips C (G.adj w) u D) (bs : Stubs G B w C D) :
    ∀ ⦃i j⦄, B.adj i j → i ≠ w := by
  intro i j e; rcases bs.cross i j e with d | d
  · exact fun eq => h.avoids (eq ▸ tips.onC i d.1)
  · exact d.2.1

theorem cycle_piece {G B J P : Graph n} {w C D u} (h : MixedCycle G w C)
    (tips : SwitchTips C (G.adj w) u D) (bs : Stubs G B w C D)
    (js : J.Sub (G.within (rest w C)))
    (jp : ∀ i, J.degree i % 2 = bit (outerEnds C (G.adj w) B i))
    (ja : Anchored J (outerEnds C (G.adj w) B))
    (ps : P.Sub (G.within C)) (pp : ∀ i, P.degree i % 2 = bit (ends C (G.adj w) D i)) :
    let F := (J.union B).union P
    F.Sub (G.within (fun i => i ≠ w)) ∧
    (∀ i, F.degree i % 2 = bit (G.adj w i)) ∧ Anchored F (G.adj w) ∧
    (∀ i, F.degree i = (J.degree i + B.degree i) + P.degree i) := by
  classical
  let T := G.adj w
  let F := (J.union B).union P
  have jb : J.Disj B := by
    intro i j e b
    obtain k | k := bs.cross i j b
    · exact (js e).2.1.2 (tips.onC _ k.1)
    · exact (js e).2.2.2 (tips.onC _ k.1)
  have jbp : (J.union B).Disj P := by
    intro i j e p
    obtain j | b := e
    · exact (js j).2.1.2 (ps p).2.1
    · obtain k | k := bs.cross _ _ b
      · exact k.2.2 (ps p).2.2
      · exact k.2.2 (ps p).2.1
  have sumF i : F.degree i = J.degree i + B.degree i + P.degree i := by
    unfold F; rw [Graph.degree_union jbp,Graph.degree_union jb]
  have incJ : J.Sub F := by intro _ _ e; exact Or.inl (Or.inl e)
  have incB : B.Sub F := by intro _ _ e; exact Or.inl (Or.inr e)
  have incP : P.Sub F := by intro _ _ e; exact Or.inr e
  have pa : Anchored P T := by
    apply rim_anchor (u := u) ps h.regular h.connected h.meets
    intro i oi
    have k := pp i
    by_cases ti : T i
    · exact Or.inl ti
    · right; apply tips.uniqueOutside i _ ti
      apply Classical.byContradiction; intro nd
      change P.degree i % 2 = bit (XorP (C i ∧ T i) (D i)) at k
      simp [XorP,ti,nd,bit] at k
      unfold Graph.oddAt at oi; omega
  let anchoredAt := fun i => ∃ t, T t ∧ Reach F (Full n) i t
  have ap i (pi : P.supp i) : anchoredAt i := by
    obtain ⟨t,tt,walk⟩ := pa i pi; exact ⟨t,tt,reach_full_mono incP walk⟩
  have ad i (di : D i) : anchoredAt i := by
    by_cases ti : T i
    · exact ⟨i,ti,.here trivial⟩
    · apply ap; apply Graph.degree_pos.mp
      have k := pp i
      change P.degree i % 2 = bit (XorP (C i ∧ T i) (D i)) at k
      simp [XorP,ti,di,bit] at k; omega
  have ab i (bi : B.supp i) : anchoredAt i := by
    obtain ⟨j,e⟩ := bi
    rcases bs.cross _ _ e with k | k
    · exact ad _ k.1
    · obtain ⟨t,tt,p⟩ := ad j k.1
      exact ⟨t,tt,((Reach.here trivial).next (incB e) trivial).trans p⟩
  refine ⟨?_,?_,?_,sumF⟩
  · intro i j e
    obtain (j | b) | p := e
    · exact ⟨(js j).1,(js j).2.1.1,(js j).2.2.1⟩
    · exact ⟨bs.sub b,stubs_off h tips bs b,stubs_off h tips bs (B.sym b)⟩
    · exact ⟨(ps p).1,fun eq => h.avoids (eq ▸ (ps p).2.1),fun eq => h.avoids (eq ▸ (ps p).2.2)⟩
  · intro i
    rw [sumF,Nat.add_mod,Nat.add_mod (J.degree i),jp,pp,← bit_mod (B.degree i)]
    change ((bit (XorP (T i) (B.oddAt i) ∧ ¬C i) + bit (B.oddAt i)) % 2 +
      bit (XorP (C i ∧ T i) (D i))) % 2 = bit (T i)
    by_cases ci : C i
    · have z := bs.count i ci
      by_cases di : D i <;> by_cases ti : T i <;> simp [Graph.oddAt,z,XorP,bit,ci,di,ti]
    · have nd : ¬D i := fun di => ci (tips.onC _ di)
      by_cases bo : B.oddAt i <;> by_cases ti : T i <;> simp [XorP,bit,ci,nd,bo,ti] <;> split <;> first | rfl | contradiction
  · rintro i ⟨j,(j' | b) | p⟩
    · obtain ⟨k,dk,walk⟩ := ja i ⟨j,j'⟩
      by_cases tk : T k
      · exact ⟨k,tk,reach_full_mono incJ walk⟩
      · have bo : B.oddAt k := by
          have e := dk.1
          change XorP (T k) (B.oddAt k) at e
          rcases e with e | e
          · exact False.elim (tk e.1)
          · exact e.1
        have pos : 0 < B.degree k := by unfold Graph.oddAt at bo; omega
        obtain ⟨t,tt,p⟩ := ab k (Graph.degree_pos.mp pos)
        exact ⟨t,tt,(reach_full_mono incJ walk).trans p⟩
    · exact ab i ⟨j,b⟩
    · exact ap i ⟨j,p⟩

theorem mixed_cycle_coloring {G : Graph n} {w C} (h : MixedCycle G w C)
    (deg : ∀ v, 4 ≤ G.degree v) (ew : G.degree w % 2 = 0) (od : ∀ i, i ≠ w → G.oddAt i) :
    OddThree G := by
  classical
  obtain ⟨t,ct,tt⟩ := h.meets
  obtain ⟨u,cu,nu⟩ := h.misses
  obtain ⟨D,tips⟩ := choose_tips ct tt cu nu
  obtain ⟨B,bs⟩ := make_stubs h tips deg
  let T := G.adj w
  have bzero : B.degree w = 0 := outside (S := fun i => i ≠ w) (stubs_off h tips bs) (by simp)
  have os : ∀ i, outerEnds C T B i → rest w C i := by
    intro i d; refine ⟨?_,d.2⟩; rintro rfl
    have k := d.1; simp [XorP,T,G.loopless,Graph.oddAt,bzero] at k
  obtain ⟨J,js,jp,ja⟩ := anchored_join G (rest w C) (outerEnds C T B) h.exterior os (outer_even tips bs ew)
  let Q := ends C T D
  have qs : ∀ i, Q i → C i := by
    rintro i (k | k)
    · exact k.1.1
    · exact tips.onC _ k.1
  obtain ⟨P,ps,pp⟩ := parity_join G C Q h.connected qs tips.evenEnds
  let L := G.within C
  let P' := L.diff P
  have ps' : P'.Sub L := by intro _ _ e; exact e.1
  have sumP i : P.degree i + P'.degree i = L.degree i := Graph.degree_diff ps i
  have zeroL {i} (nc : ¬C i) : L.degree i = 0 := outside (by intro _ _ e; exact e.2.1) nc
  have pp' i : P'.degree i % 2 = bit (Q i) := by
    have k := pp i; have s := sumP i
    by_cases ci : C i
    · have e : L.degree i = 2 := h.regular i ci; omega
    · have e := zeroL ci; omega
  obtain ⟨s₀,p₀,a₀,f₀⟩ := cycle_piece h tips bs js jp ja ps pp
  obtain ⟨s₁,p₁,a₁,f₁⟩ := cycle_piece h tips bs js jp ja ps' pp'
  let F₀ := (J.union B).union P
  let F₁ := (J.union B).union P'
  have flip (i) : ((C i ∧ ¬T i) ∧ ¬D i) ↔ XorP (F₀.supp i) (F₁.supp i) := by
    rw [← Graph.degree_pos,← Graph.degree_pos]
    change _ ↔ XorP (0 < ((J.union B).union P).degree i) (0 < ((J.union B).union P').degree i)
    rw [f₀,f₁]
    have s := sumP i
    by_cases ci : C i
    · have z : J.degree i = 0 := outside (S := fun z => ¬C z) (by intro _ _ e; exact (js e).2.1.2) (by simpa using ci)
      have r : L.degree i = 2 := h.regular i ci
      have k := pp i
      change P.degree i % 2 = bit (XorP (C i ∧ T i) (D i)) at k
      rw [z,bs.count i ci]
      by_cases ti : T i <;> by_cases di : D i <;>
        simp [XorP,bit,ti,di,ci] at k ⊢ <;> omega
    · have z := zeroL ci
      have pz : P.degree i = 0 := by omega
      have qz : P'.degree i = 0 := by omega
      simp [ci,pz,qz,XorP]; omega
  have pos : 0 < G.degree w := by have := deg w; omega
  rcases switch_odd_support tips.oddSwitch flip with odd | odd
  · exact odd_support_coloring s₀ odd p₀ a₀ ew od pos
  · exact odd_support_coloring s₁ odd p₁ a₁ ew od pos

end KMO
