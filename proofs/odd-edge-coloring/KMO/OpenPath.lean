import KMO.Tutte
namespace KMO
variable {n : Nat}

structure OpenPath (G : Graph n) (a b : Fin n) extends Trace G (Full n) a b where
  positive : 0 < len
  injective : ∀ {i j},i ≤ len → j ≤ len → node i = node j → i = j
  induced : ∀ i j,i ≤ len → j ≤ len → (G.adj (node i) (node j) ↔ j=i+1 ∨ i=j+1)

namespace OpenPath
variable {G : Graph n} {a b : Fin n}

abbrev verts (P : OpenPath G a b) := P.toTrace.image
def edges (P : OpenPath G a b) := G.within P.verts

theorem has_at (P : OpenPath G a b) {i} (hi : i ≤ P.len) : P.verts (P.node i) := ⟨i,hi,rfl⟩
theorem has_a (P : OpenPath G a b) : P.verts a := ⟨0,Nat.zero_le _,P.first⟩
theorem has_b (P : OpenPath G a b) : P.verts b := ⟨P.len,Nat.le_refl _,P.last⟩
theorem ends_ne (P : OpenPath G a b) : a ≠ b := by
  intro eq; have k := P.injective (Nat.zero_le _) (Nat.le_refl _) (P.first.trans (eq.trans P.last.symm))
  have := P.positive; omega

theorem degree_at (P : OpenPath G a b) {i} (hi : i ≤ P.len) :
    P.edges.degree (P.node i) = if i=0 ∨ i=P.len then 1 else 2 := by
  have degOne {j} (hj : j ≤ P.len) (unique : ∀ k,k ≤ P.len → (k=i+1 ∨ i=k+1 ↔ k=j)) :
      P.edges.degree (P.node i) = 1 := by
    rw [← card_single (P.node j)]
    apply card_congr; intro z; constructor
    · intro e; obtain ⟨k,hk,rfl⟩ := e.2.2
      exact congrArg P.node ((unique k hk).mp ((P.induced i k hi hk).mp e.1))
    · rintro rfl; exact ⟨(P.induced i j hi hj).mpr ((unique _ hj).mpr rfl),P.has_at hi,P.has_at hj⟩
  have pos := P.positive
  by_cases first : i=0
  · rw [if_pos (Or.inl first)]; exact degOne (j := 1) (by omega) (fun k hk => by omega)
  by_cases last : i=P.len
  · rw [if_pos (Or.inr last)]; exact degOne (j := P.len-1) (by omega) (fun k hk => by omega)
  · rw [if_neg (fun h => h.elim first last)]
    have lo : i-1 ≤ P.len := by omega
    have up : i+1 ≤ P.len := by omega
    have diff : P.node (i-1) ≠ P.node (i+1) := fun e => by have := P.injective lo up e; omega
    rw [← card_pair diff]; apply card_congr; intro z; constructor
    · intro e; obtain ⟨k,hk,rfl⟩ := e.2.2
      have loc := (P.induced i k hi hk).mp e.1
      have z : k=i-1 ∨ k=i+1 := by omega
      exact z.imp (congrArg P.node) (congrArg P.node)
    · rintro (rfl|rfl)
      · exact ⟨(P.induced i _ hi lo).mpr (by omega),P.has_at hi,P.has_at lo⟩
      · exact ⟨P.step i (by omega),P.has_at hi,P.has_at up⟩

theorem degree_a (P : OpenPath G a b) : P.edges.degree a = 1 := by
  simpa only [P.first, true_or, or_true, ite_true, eq_self] using P.degree_at (i := 0) (Nat.zero_le _)
theorem degree_b (P : OpenPath G a b) : P.edges.degree b = 1 := by
  simpa only [P.last, or_true, ite_true, eq_self] using P.degree_at (Nat.le_refl P.len)

theorem escape (P : OpenPath G a b) (md : ∀ v,3 ≤ G.degree v) {v} (hv : P.verts v) :
    ∃ j,¬P.verts j ∧ G.adj v j := by
  obtain ⟨i,hi,rfl⟩ := hv
  have de := P.degree_at hi; have high := md (P.node i)
  apply Classical.byContradiction; intro bad
  have all : G.degree (P.node i) = P.edges.degree (P.node i) :=
    card_congr (fun j => ⟨fun e => ⟨e,P.has_at hi,Classical.byContradiction (fun no => bad ⟨j,no,e⟩)⟩,And.left⟩)
  split at de <;> omega

def takeTo (P : OpenPath G a b) {k} (pk : 0 < k) (hk : k ≤ P.len) : OpenPath G a (P.node k) where
  toTrace := P.toTrace.takePart k hk
  positive := pk
  injective := fun hi hj eq => P.injective (Nat.le_trans hi hk) (Nat.le_trans hj hk) eq
  induced := fun i j hi hj => P.induced i j (Nat.le_trans hi hk) (Nat.le_trans hj hk)
end OpenPath

theorem induced_nonseparating_path {G : Graph n} {x y : Fin n} (strong : ThreeConnected G)
    (xy : x ≠ y) :
    ∃ P : OpenPath G x y,ConnectedOn G (fun i => ¬P.verts i) := by
  classical
  by_cases e : G.adj x y
  · let Q : Trace G (Full n) x y := .one trivial trivial e
    have short : Q.Shortest := by
      intro alt; change 1 ≤ alt.len
      by_cases z : alt.len = 0
      · exact False.elim (xy (alt.first.symm.trans (z ▸ alt.last)))
      · omega
    let P : OpenPath G x y := ⟨Q,by change 0 < 1; decide,fun hi hj eq => Trace.index_injective short hi hj eq,
      fun i j hi hj => ⟨Trace.step_indices short hi hj,by
        rintro (rfl | rfl); exact Q.step i (by omega); exact G.sym (Q.step j (by omega))⟩⟩
    refine ⟨P,?_⟩
    apply conn_congr _ ((global_three strong).2 x y)
    intro i
    have spec : P.verts i ↔ i = x ∨ i = y := by
      constructor
      · rintro ⟨k,hk,eq⟩
        change k ≤ 1 at hk
        have h : k = 0 ∨ k = 1 := by omega
        rcases h with rfl | rfl
        · exact Or.inl (eq.symm.trans P.first)
        · exact Or.inr (eq.symm.trans P.last)
      · rintro (rfl | rfl); exact P.has_a; exact P.has_b
    simp [del₂,del,Full,spec,not_or]
  · let K := G.union (edge xy)
    have gk : G.Sub K := by intro _ _ e; exact Or.inl e
    have lift {S : Region n} (c : ConnectedOn G S) : ConnectedOn K S :=
      conn_move c (fun _ => Iff.rfl) (fun _ _ _ _ e => gk e)
    have st := global_three strong
    have robust : Three K (Full n) := ⟨⟨lift st.1.1,fun i => lift (st.1.2 i)⟩,fun a b => lift (st.2 a b)⟩
    have size : 4 ≤ card (Full n) := by simpa [Full,card_full] using strong.1
    obtain ⟨v,_,vx,vy⟩ := avoid_two (Nat.le_trans (by decide : 3 ≤ 4) size) x y
    obtain ⟨W,T,short,_,_,conn⟩ := peripheral_trace robust size (x := x) (y := y) (v := v) trivial trivial trivial
      (Or.inr (Or.inl ⟨rfl,rfl⟩)) vx vy xy
    have back : (K.diff (edge xy)).Sub G := by intro i j k; exact k.1.resolve_right k.2
    let Q : Trace G (Full n) x y := T.transport (fun _ _ => trivial) (fun i hi => back (T.step i hi))
    have ij i j (hi : i ≤ T.len) (hj : j ≤ T.len) : G.adj (T.node i) (T.node j) ↔ j=i+1 ∨ i=j+1 := by
      constructor
      · intro ge; apply Trace.step_indices short hi hj
        refine ⟨Or.inl ge,?_⟩; rintro (⟨ix,jy⟩ | ⟨jx,iy⟩)
        · exact e (by simpa [ix,jy] using ge)
        · exact e (by simpa [jx,iy] using G.sym ge)
      · rintro (rfl|rfl); exact back (T.step i (by omega)); exact G.sym (back (T.step j (by omega)))
    have lng : 0 < T.len := by
      by_cases z : T.len = 0
      · exact False.elim (xy (T.first.symm.trans (z ▸ T.last)))
      · omega
    let P : OpenPath G x y := ⟨Q,lng,fun hi hj eq => Trace.index_injective short hi hj eq,ij⟩
    refine ⟨P,conn_move conn (fun _ => by simp [Full]; rfl) ?_⟩
    intro i j ni nj k
    rcases k with real | ⟨eq,_⟩ | ⟨eq,_⟩
    · exact real
    · exact False.elim (ni.2 (eq ▸ P.has_a))
    · exact False.elim (nj.2 (eq ▸ P.has_a))

structure Clean {n} (G : Graph n) (a b : Fin n) (P : OpenPath G a b) : Prop where
  outside : ConnectedOn G (fun i => ¬P.verts i)
  firstEven : G.degree a % 2 = 0
  lastEven : G.degree b % 2 = 0
  innerOdd : ∀ i,0 < i → i < P.len → G.oddAt (P.node i)

theorem clean_path {G : Graph n} {x y} (st : ThreeConnected G)
    (ne : x ≠ y) (ex : G.degree x % 2 = 0) (ey : G.degree y % 2 = 0) :
    ∃ a b,∃ P : OpenPath G a b,Clean G a b P := by
  obtain ⟨P,conn⟩ := induced_nonseparating_path st ne
  obtain ⟨k,⟨pk,hk,ek⟩,min⟩ := least_nat (R := fun i => 0 < i ∧ i ≤ P.len ∧ G.degree (P.node i) % 2 = 0)
    ⟨P.len,P.positive,Nat.le_refl _,by rw [P.last]; exact ey⟩
  let Q := P.takeTo pk hk
  have inc i (q : Q.verts i) : P.verts i := by obtain ⟨j,hj,eq⟩ := q; exact ⟨j,Nat.le_trans hj hk,eq⟩
  refine ⟨x,P.node k,Q,⟨?_,ex,ek,?_⟩⟩
  · apply attach_vertices conn (fun i no => fun qi => no (inc i qi))
    intro i ni pp
    have pi : P.verts i := Classical.byContradiction pp
    exact P.escape (degree_of_three st) pi
  · intro i pos hi
    change i < k at hi
    change G.degree (P.node i) % 2 = 1
    by_cases ev : G.degree (P.node i) % 2 = 0
    · have small := min i ⟨pos,by omega,ev⟩; omega
    · omega

end KMO
