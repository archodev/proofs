import KMO.Parity

namespace KMO
variable {n : Nat}

theorem three_from_two {G A B : Graph n} (sa : A.Sub G) (sb : B.Sub G)
    (dis : A.Disj B) (ga : A.good) (gb : B.good) (gc : (G.diff (A.union B)).good) :
    OddThree G := by
  let C := G.diff (A.union B)
  let P : Color → Graph n := fun | .red => C | .blue => A | .green => B
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x y
    constructor
    · intro h
      by_cases a : A.adj x y
      · exact ⟨.blue,a⟩
      by_cases b : B.adj x y
      · exact ⟨.green,b⟩
      exact ⟨.red,h,fun k => k.elim a b⟩
    · rintro ⟨c,h⟩
      cases c
      · exact h.1
      · exact sa h
      · exact sb h
  · intro c d ne x y hc hd
    cases c <;> cases d <;> simp [P,C,Graph.diff,Graph.union] at * <;> grind
  · intro c; cases c <;> assumption

structure StarAt (G : Graph n) (w x : Fin n) (S : Region n) : Prop where
  atCenter : G.adj w x
  offW : ¬ S w
  offX : ¬ S x
  neighbors : ∀ i, G.adj x i → i ≠ w → S i
  extra : ∀ i, S i → ¬ G.adj x i → G.adj w i
  even : card S % 2 = 0
  connected : ConnectedOn G S

def HasStar (G : Graph n) (w : Fin n) := ∃ x S, StarAt G w x S

theorem star_coloring {G : Graph n} {w x : Fin n} {S : Region n}
    (ew : G.degree w % 2 = 0) (od : ∀ v, v ≠ w → G.oddAt v)
    (h : StarAt G w x S) : OddThree G := by
  classical
  obtain ⟨F, fs, fp⟩ := parity_join G S S h.connected (fun _ => id) h.even
  let N := G.adj x
  let T := fun i => S i ∧ ¬N i
  have nx : ¬N x := G.loopless x
  have tw : ¬T w := fun k => h.offW k.1
  have nw : N w := G.sym h.atCenter
  have xw : x ≠ w := fun k => G.loopless w (k ▸ h.atCenter)
  let X := Graph.star x N nx
  let Y := Graph.star w T tw
  let B := X.union Y
  have sx : X.Sub G := by
    intro a b e; rcases e with ⟨rfl,ha⟩ | ⟨rfl,ha⟩
    · exact ha
    · exact G.sym ha
  have sy : Y.Sub G := by
    intro a b e; rcases e with ⟨rfl,hb⟩ | ⟨rfl,ha⟩
    · exact h.extra _ hb.1 hb.2
    · exact G.sym (h.extra _ ha.1 ha.2)
  have sb : B.Sub G := by intro i j e; exact e.elim (fun k => sx k) (fun k => sy k)
  have dxy : X.Disj Y := by
    intro i j hi hj
    change (_ ∨ _) at hi hj
    rcases hi with ⟨rfl,hi⟩ | ⟨rfl,hi⟩ <;> rcases hj with ⟨eq,hj⟩ | ⟨eq,hj⟩ <;>
      first | exact xw eq | exact h.offX hj.1
  have dbf : B.Disj F := by
    intro i j hb hf
    obtain ⟨_,si,sj⟩ := fs hf
    rcases hb with hb | hb <;> rcases hb with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;>
      first | exact h.offX si | exact h.offX sj | exact h.offW si | exact h.offW sj
  have bd (v) : B.degree v =
      (if v = x then card N else bit (N v)) + (if v = w then card T else bit (T v)) := by
    change (X.union Y).degree v = _
    rw [Graph.degree_union dxy]; unfold X Y; rw [Graph.degree_star, Graph.degree_star]
  have shared : card (fun v => S v ∧ N v) = card (fun v => N v ∧ v ≠ w) :=
    card_congr (fun v => ⟨fun k => ⟨k.2,fun e => h.offW (e ▸ k.1)⟩,fun k => ⟨h.neighbors v k.1 k.2,k.1⟩⟩)
  have hs := card_split S N
  rw [shared] at hs
  change _ + card T = card S at hs
  have hn := card_erase nw
  change _ + 1 = G.degree x at hn
  have ox := od x xw
  have es := h.even
  have bw : B.oddAt w := by
    change B.degree w % 2 = 1
    rw [bd]; simp only [if_neg (Ne.symm xw),if_pos rfl]
    have one : bit (N w) = 1 := by simp [bit,nw]
    rw [one]; simp only [ite_true]; unfold Graph.oddAt at ox; omega
  have bx : B.degree x = G.degree x := by
    rw [bd]; simp [xw,T,h.offX,bit,N,Graph.degree]
  have bi {v} (vx : v ≠ x) (vw : v ≠ w) : B.degree v = bit (S v) := by
    rw [bd,if_neg vx,if_neg vw]; by_cases nv : N v
    · simp [nv,bit,T,h.neighbors v nv vw]
    · simp [nv,bit,T]
  have fzero {v} (outside : ¬S v) : F.degree v = 0 := by
    have hn : ¬F.supp v := fun ⟨_,he⟩ => outside (fs he).2.1
    have hh : ¬ 0 < F.degree v := fun pos => hn (Graph.degree_pos.mp pos)
    omega
  apply three_from_two sb (by intro _ _ e; exact (fs e).1) dbf
  · intro v; by_cases vw : v = w
    · exact Or.inr (vw ▸ bw)
    by_cases vx : v = x
    · subst v; right; change B.degree x % 2 = 1; rwa [bx]
    · by_cases sv : S v
      · right; change B.degree v % 2 = 1; simp [bi vx vw,bit,sv]
      · left; simp [bi vx vw,bit,sv]
  · intro v; by_cases sv : S v
    · right; simpa [bit,sv] using fp v
    · exact Or.inl (fzero sv)
  · intro v
    have subu : (B.union F).Sub G := by intro i j e; exact e.elim (fun k => sb k) (fun k => (fs k).1)
    have eqn := Graph.degree_diff subu v
    rw [Graph.degree_union dbf] at eqn
    by_cases vw : v = w
    · subst v; rw [fzero h.offW] at eqn; right; unfold Graph.oddAt at *; omega
    by_cases vx : v = x
    · subst v; rw [bx] at eqn; left; omega
    have ov := od v vw
    rw [bi vx vw] at eqn
    by_cases sv : S v
    · have ff := fp v; simp [bit,sv] at ff eqn; right; unfold Graph.oddAt at *; omega
    · rw [fzero sv] at eqn; simp [bit,sv] at eqn; right; unfold Graph.oddAt at *; omega

end KMO
