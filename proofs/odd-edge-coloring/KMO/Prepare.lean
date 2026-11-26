import KMO.OpenPath
import KMO.ForestColor

namespace KMO
variable {n : Nat} {G : Graph n} {s t : Fin n}

/-- Color all edges off the reserved path. Green misses s and is odd at
every other vertex. All the residual edges at t have already been colored green. -/
theorem prepare {P : OpenPath G s t} (clean : Clean G s t P) (order : n % 2 = 1)
    (deg : ∀ i,3 ≤ G.degree i) (size : 4 ≤ n) :
    ∃ F R : Graph n, let A := G.diff P.edges; let H := A.diff F
      F.Sub A ∧ R.Sub H ∧ F.degree s = 0 ∧ (∀ i,i ≠ s → F.oddAt i) ∧ H.degree t = 0 ∧
      ∀ i,i ≠ s → (R.degree i = 0 ∨ R.oddAt i) ∧ ((H.diff R).degree i = 0 ∨ (H.diff R).oddAt i) := by
  classical
  let U := without s
  let W := fun i => U i ∧ i ≠ t
  let A := G.diff P.edges
  let J := A.within U
  have st := P.ends_ne
  have tk : U t := Ne.symm st
  have cut : P.edges.Sub G := by intro _ _ e; exact e.1
  have jrow i (e : A.adj t i) : i ≠ s := by
    rintro rfl; exact e.2 ⟨e.1,P.has_b,P.has_a⟩
  have jt : J.degree t = A.degree t := card_congr (fun i => ⟨And.left,fun e => ⟨e,tk,jrow i e⟩⟩)
  have aj := Graph.degree_diff cut t
  change P.edges.degree t + A.degree t = G.degree t at aj
  rw [P.degree_b] at aj
  have jeven := clean.lastEven
  have jtOdd : J.oddAt t := by unfold Graph.oddAt; omega
  let O := fun i => ¬P.verts i
  have ow i (oi : O i) : W i := ⟨fun eq => oi (eq ▸ P.has_a),fun eq => oi (eq ▸ P.has_b)⟩
  have toJ i j (ui : U i) (oj : O j) (e : G.adj i j) : J.adj i j :=
    ⟨⟨e,fun k => oj k.2.2⟩,ui,(ow j oj).1⟩
  have base : ConnectedOn J O := conn_move clean.outside (fun _ => Iff.rfl) (fun i j oi oj => toJ i j (ow i oi).1 oj)
  have conn : ConnectedOn J W := by
    apply attach_vertices base ow
    intro i wi no
    have pi : P.verts i := Classical.byContradiction no
    obtain ⟨j,oj,e⟩ := P.escape deg pi
    exact ⟨j,oj,toJ i j wi.1 oj e⟩
  have full : 3 ≤ card (Full n) := by rw [show card (Full n) = n from card_full]; omega
  obtain ⟨root,_,rs,rt⟩ := avoid_two full s t
  obtain ⟨T,rank,ts,tc,ranked⟩ := ranked_tree conn (root := root) ⟨rs,rt⟩
  have tj : T.Sub J := by intro _ _ e; exact (ts e).1
  let I := J.diff T
  have isub : I.Sub J := by intro _ _ e; exact e.1
  have tzero : T.degree t = 0 := outside (S := W) (by intro _ _ e; exact (ts e).2.1) (by intro k; exact k.2 rfl)
  have sumt := Graph.degree_diff tj t
  change T.degree t + I.degree t = J.degree t at sumt
  have io : I.oddAt t := by unfold Graph.oddAt at *; omega
  let D := fun i => U i ∧ ¬I.oddAt i
  have dw i (di : D i) : W i := ⟨di.1,fun eq => di.2 (eq ▸ io)⟩
  have cu : card U + 1 = n := by
    have eqn := card_erase (S := Full n) (v := s) trivial
    simpa [U,without,Full,card_full] using eqn
  have odd_inside i (oi : I.oddAt i) : U i := by
    apply Classical.byContradiction; intro no
    have zz := outside (G := I) (S := U) (by intro _ _ e; exact (isub e).2.1) no
    unfold Graph.oddAt at oi; omega
  have cI : card (fun i => U i ∧ I.oddAt i) = card I.oddAt :=
    card_congr (fun i => ⟨And.right,fun oi => ⟨odd_inside i oi,oi⟩⟩)
  have split := card_split U I.oddAt; rw [cI] at split
  change card I.oddAt + card D = card U at split
  have handshake := handshaking I
  have ev : card D % 2 = 0 := by omega
  obtain ⟨E,es,ep⟩ := parity_join T W D tc dw ev
  have et : E.Sub T := by intro _ _ e; exact (es e).1
  let F := I.union E
  have ij : I.Disj E := by intro _ _ e k; exact e.2 (et k)
  have fj : F.Sub J := by intro _ _ k; exact k.elim (fun e => isub e) (fun e => tj (et e))
  have fs : F.Sub A := by intro _ _ k; exact (fj k).1
  have fzero : F.degree s = 0 := outside (S := U) (by intro _ _ e; exact (fj e).2.1) (by simp [U,without])
  have fo i (ui : U i) : F.oddAt i := by
    change (I.union E).degree i % 2 = 1
    rw [Graph.degree_union ij,Nat.add_mod,ep]
    by_cases oi : I.oddAt i
    · simp [D,ui,oi,bit]
    · simp [D,ui,oi,bit]; unfold Graph.oddAt at oi; omega
  let H := A.diff F
  have prop : ∀ i j,i ≠ s → j ≠ s → H.adj i j → T.adj i j := by
    intro i j is js e
    exact Classical.byContradiction (fun no => e.2 (Or.inl ⟨⟨e.1,is,js⟩,no⟩))
  have emptyT : H.degree t = 0 := by
    apply outside (S := fun i => i ≠ t) (by
      intro i j e eq; subst i
      have tej := prop t j tk (jrow j e.1) e
      exact (ts tej).2.1.2 rfl) (by simp)
  obtain ⟨R,rr,valid⟩ := forest_coloring ranked prop
  exact ⟨F,R,fs,rr,fzero,fo,emptyT,valid⟩

end KMO
