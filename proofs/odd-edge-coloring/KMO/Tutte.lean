import KMO.RingIndex
namespace KMO
variable {n : Nat}

structure Avoiding (G : Graph n) (U : Region n) (x y v : Fin n) (ne : x ≠ y) (B : Region n) : Prop where
  subset : ∀ i,B i → U i
  includes : B v
  conn : ConnectedOn G B
  alternate : Reach (G.diff (edge ne)) (fun i => U i ∧ ¬B i) x y

theorem avoiding_start {G : Graph n} {U : Region n} (conn : Three G U) (size : 4 ≤ card U)
    {x y v} (ux : U x) (uy : U y) (uv : U v) (ne : x ≠ y) (vx : v ≠ x) (vy : v ≠ y) :
    Avoiding G U x y v ne (fun i => i = v) := by
  have count := card_erase uv
  change card (del U v) + 1 = card U at count
  obtain ⟨z,⟨uz,zv⟩,zx,zy⟩ := avoid_two (S := del U v) (by omega) x y
  obtain ⟨a,b,_,hb,ax,bx,ab⟩ := adjacent_across (L := fun i => i = x) (conn.2 v y)
    (x := x) (y := z) ⟨⟨ux,Ne.symm vx⟩,ne⟩ ⟨⟨uz,zv⟩,zy⟩ rfl zx
  subst a
  let H := G.diff (edge ne)
  have first : H.adj x b := ⟨ab,by rintro (⟨_,by'⟩ | ⟨_,xy⟩); exact hb.2 by'; exact ne xy⟩
  have path := conn.2 v x b ⟨hb.1,bx⟩ y ⟨⟨uy,Ne.symm vy⟩,Ne.symm ne⟩
  have q : Reach H (del U v) b y := by
    apply path.transport (fun _ => And.left)
    intro i j hi hj g; exact ⟨g,by rintro (⟨ix,_⟩ | ⟨jx,_⟩); exact hi.2 ix; exact hj.2 jx⟩
  refine ⟨fun i eq => eq ▸ uv,rfl,?_,?_⟩
  · rintro i rfl j rfl; exact .here rfl
  · exact ((Reach.here ⟨ux,Ne.symm vx⟩).next first hb.1).trans q

theorem maximal_avoiding {G : Graph n} {U : Region n} {x y v} {ne : x ≠ y}
    (seed : ∃ B,Avoiding G U x y v ne B) : ∃ B,Avoiding G U x y v ne B ∧
      ∀ D,Avoiding G U x y v ne D → card D ≤ card B := by
  obtain ⟨B,h,min⟩ := minimize (Avoiding G U x y v ne) (fun S => n-card S) seed
  have bound (S : Region n) : card S ≤ n := by
    have := card_mono (S := S) (T := Full n) (fun _ _ => trivial)
    simpa [Full,card_full] using this
  refine ⟨B,h,fun D hd => ?_⟩
  have k := min D hd; have := bound D; have := bound B; omega

theorem cannot_enlarge {G : Graph n} {U B : Region n} {x y v} {ne : x ≠ y}
    (h : Avoiding G U x y v ne B) (max : ∀ D,Avoiding G U x y v ne D → card D ≤ card B)
    {z} (uz : U z) (nz : ¬B z) (touch : ∃ b,B b ∧ G.adj z b)
    (alt : Reach (G.diff (edge ne)) (fun i => (U i ∧ ¬B i) ∧ i ≠ z) x y) : False := by
  let B' := plus B z
  have inc : ∀ i,B i → B' i := fun _ => Or.inl
  have valid : Avoiding G U x y v ne B' := by
    refine ⟨?_,Or.inl h.includes,attach_vertices h.conn inc ?_,?_⟩
    · rintro i (bi | rfl); exact h.subset _ bi; exact uz
    · intro i hi nb; have eq := hi.resolve_left nb; subst i; exact touch
    · apply alt.transport _ (fun _ _ _ _ => id)
      intro i k; exact ⟨k.1.1,fun e => e.elim k.1.2 k.2⟩
  have bigger := strict_card inc (x := z) (Or.inr rfl) nz
  exact (Nat.not_le_of_lt bigger) (max B' valid)

theorem Reach.without_closed {G : Graph n} {U B : Region n} {i j} (p : Reach G U i j)
    (closed : ∀ a b,B a → U b → G.adj a b → B b) (ni : ¬B i) :
    Reach G (fun k => U k ∧ ¬B k) i j := by
  induction p with
  | here h => exact .here ⟨h,ni⟩
  | next p e h ih => exact ih.next e ⟨h,fun bj => ih.finish.2 (closed _ _ bj p.finish (G.sym e))⟩

/-- Any component outside the rim, separated from another exterior vertex,
has an attachment avoiding two prescribed rim vertices. -/
theorem third_attachment {G : Graph n} {U C S : Region n} (three : Three G U)
    (ins : ∀ i,S i → U i ∧ ¬C i) (closed : ∀ i j,S i → (U j ∧ ¬C j) → G.adj i j → S j)
    {a b} (sa : S a) (ub : U b) (nb : ¬C b) (sb : ¬S b)
    {l r} (cl : C l) (cr : C r) :
    ∃ k,C k ∧ k ≠ l ∧ k ≠ r ∧ ∃ z,S z ∧ G.adj k z := by
  have ha := ins a sa
  have source : del₂ U l r a := ⟨⟨ha.1,fun eq => ha.2 (eq ▸ cl)⟩,fun eq => ha.2 (eq ▸ cr)⟩
  have dest : del₂ U l r b := ⟨⟨ub,fun eq => nb (eq ▸ cl)⟩,fun eq => nb (eq ▸ cr)⟩
  obtain ⟨i,j,_,dj,si,nj,e⟩ := adjacent_across (three.2 l r) source dest sa sb
  have cj : C j := Classical.byContradiction (fun no => nj (closed _ _ si ⟨dj.1.1,no⟩ e))
  exact ⟨j,cj,dj.1.2,dj.2,i,si,G.sym e⟩

theorem peripheral_trace {G : Graph n} {U : Region n} (three : Three G U) (size : 4 ≤ card U)
    {x y v} (ux : U x) (uy : U y) (uv : U v) (edgeXY : G.adj x y)
    (vx : v ≠ x) (vy : v ≠ y) (ne : x ≠ y) :
    ∃ W, ∃ P : Trace (G.diff (edge ne)) W x y, P.Shortest ∧
      (∀ i,P.image i → U i) ∧ ¬P.image v ∧ ConnectedOn G (fun i => U i ∧ ¬P.image i) := by
  classical
  let H := G.diff (edge ne)
  obtain ⟨B,valid,max⟩ := maximal_avoiding ⟨_,avoiding_start three size ux uy uv ne vx vy⟩
  obtain ⟨P,short⟩ := Trace.shortest_of_reach valid.alternate
  obtain ⟨length,around,cycle⟩ := shortest_rim edgeXY ne short
  let C := P.image
  let O := fun i => U i ∧ ¬C i
  have cin i (ci : C i) : U i ∧ ¬B i := by obtain ⟨j,hj,rfl⟩ := ci; exact P.inside _ hj
  have cx : C x := ⟨0,by omega,P.first⟩
  have cy : C y := ⟨P.len,by omega,P.last⟩
  have bin i (bi : B i) : O i := ⟨valid.subset _ bi,fun ci => (cin i ci).2 bi⟩
  have mem (i) (hi : i ≤ P.len) : C (P.node i) := ⟨i,hi,rfl⟩
  have closed i j (bi : B i) (oj : O j) (e : G.adj i j) : B j := by
    apply Classical.byContradiction; intro nj
    apply cannot_enlarge valid max oj.1 nj ⟨i,bi,G.sym e⟩
    exact (P.transport (H := H) (fun k hk => ⟨P.inside k hk,fun eq => oj.2 (eq ▸ mem k hk)⟩) P.step).reaches
  refine ⟨_,P,short,fun i ci => (cin i ci).1,(bin _ valid.includes).2,?_⟩
  suffices all : ∀ i,O i → B i by
    intro i oi j oj
    exact (valid.conn i (all i oi) j (all j oj)).transport bin (fun _ _ _ _ => id)
  intro d od
  apply Classical.byContradiction; intro nd
  let Mark := fun i => i ≤ P.len ∧ ∃ z,B z ∧ G.adj (P.node i) z
  have noBetween {i j k r s} (hi : i ≤ P.len) (hj : j ≤ P.len)
      (ik : i < k) (kj : k < j) (mk : Mark k) (er : G.adj (P.node i) r) (es : G.adj s (P.node j))
      (path : Reach G O r s) (nr : ¬B r) : False := by
    let V := fun z => (U z ∧ ¬B z) ∧ z ≠ P.node k
    have noAt {t} (ht : t ≤ P.len) (tk : t ≠ k) : V (P.node t) :=
      ⟨P.inside t ht,fun eq => tk (Trace.index_injective short ht mk.1 eq)⟩
    have left : Reach H V x (P.node i) := by
      have q : Reach H V (P.node 0) (P.node i) :=
        P.subreach (by omega) hi (fun t _ ti => noAt (by omega) (by omega)) (by intro _ _ h; exact h)
      simpa only [P.first] using q
    have right : Reach H V (P.node j) y := by
      have q : Reach H V (P.node j) (P.node P.len) :=
        P.subreach hj (Nat.le_refl _) (fun t jt tl => noAt tl (by omega)) (by intro _ _ h; exact h)
      simpa only [P.last] using q
    have noEdge {a b} (ob : O b) : ¬(edge ne).adj a b := by
      rintro (⟨_,eq⟩ | ⟨eq,_⟩)
      · exact ob.2 (eq ▸ cy)
      · exact ob.2 (eq ▸ cx)
    have exterior := path.without_closed closed nr
    have vv i (o : O i ∧ ¬B i) : V i := ⟨⟨o.1.1,o.2⟩,fun eq => o.1.2 (eq ▸ mem k mk.1)⟩
    have middle := exterior.transport (H := H) vv (fun _ _ _ b e => ⟨e,noEdge b.1⟩)
    have first := left.next (show H.adj _ _ from ⟨er,noEdge path.start⟩) middle.start
    have last := (first.trans middle).next (show H.adj _ _ from ⟨es,fun e => noEdge path.finish ((edge ne).sym e)⟩) right.start
    exact cannot_enlarge valid max (P.inside k mk.1).1 (P.inside k mk.1).2 mk.2 (last.trans right)
  let S := Reach G O d
  have ss : S d := .here od
  have ns : ¬S v := fun p => nd (p.reverse.preserve valid.includes closed)
  have attach {A : Region n} (asub : ∀ i,A i → O i)
      (acl : ∀ i j,A i → O j → G.adj i j → A j)
      {a b} (aa : A a) (ob : O b) (nab : ¬A b) (l r : Nat) (hl : l ≤ P.len) (hr : r ≤ P.len) :
      ∃ k,k ≤ P.len ∧ k ≠ l ∧ k ≠ r ∧ ∃ z,A z ∧ G.adj (P.node k) z := by
    obtain ⟨k,⟨j,hj,je⟩,kl,kr,t⟩ := third_attachment (C := C) three asub acl aa ob.1 ob.2 nab (mem l hl) (mem r hr)
    subst k
    exact ⟨j,hj,fun e => kl (congrArg P.node e),fun e => kr (congrArg P.node e),t⟩
  have attB := attach bin closed valid.includes od nd
  have attD := attach (A := S) (fun _ k => k.finish) (fun _ _ a h e => a.next e h) ss (bin _ valid.includes) ns
  obtain ⟨l,hl,_,_,bl⟩ := attB 0 0 (by omega) (by omega)
  obtain ⟨r,hr,rl,_,br⟩ := attB l l hl hl
  have distinct : ∃ i j,Mark i ∧ Mark j ∧ i ≠ j := ⟨r,l,⟨hr,br⟩,⟨hl,bl⟩,rl⟩
  have unmarked : ∃ k,k ≤ P.len ∧ ¬Mark k := by
    apply Classical.byContradiction; intro none
    have every k (hk : k ≤ P.len) : Mark k := Classical.byContradiction (fun no => none ⟨k,hk,no⟩)
    have near {i j} (hi : i ≤ P.len) (hj : j ≤ P.len) (ai : ∃ z,S z ∧ G.adj (P.node i) z)
        (aj : ∃ z,S z ∧ G.adj (P.node j) z) : j ≤ i+1 := by
      apply Nat.le_of_not_gt; intro gap
      obtain ⟨a,da,ia⟩ := ai; obtain ⟨b,db,jb⟩ := aj
      exact noBetween hi hj (Nat.lt_succ_self _) gap (every (i+1) (by omega)) ia (G.sym jb) (da.reverse.trans db)
        (fun ba => nd (da.reverse.preserve ba closed))
    obtain ⟨i,hi,_,_,ai⟩ := attD 0 0 (by omega) (by omega)
    obtain ⟨j,hj,ji,_,aj⟩ := attD i i hi hi
    obtain ⟨k,hk,ki,kj,ak⟩ := attD i j hi hj
    have := near hi hj ai aj; have := near hj hi aj ai
    have := near hi hk ai ak; have := near hk hi ak ai
    have := near hj hk aj ak; have := near hk hj ak aj
    omega
  obtain ⟨k,hk,nk⟩ := unmarked
  obtain ⟨gap⟩ := find_gap hk nk distinct (fun _ hm => hm.1)
  let In := fun z => ∃ i,i ≤ P.len ∧ gap.inside i ∧ P.node i = z
  let Tail := fun z => ∃ i,i ≤ P.len ∧ gap.inside i ∧ ∃ a,G.adj (P.node i) a ∧ Reach G O a z
  let L := fun z => In z ∨ Tail z
  have idx {i j} (hi : i ≤ P.len) (hj : j ≤ P.len) (eq : P.node i = P.node j) : i = j :=
    Trace.index_injective short hi hj eq
  have cv := (bin _ valid.includes).2
  have source : del₂ U (P.node gap.a) (P.node gap.b) (P.node k) :=
    ⟨⟨(P.inside _ hk).1,fun eq => (gap.avoids _ gap.has).1 (idx hk gap.va eq)⟩,
      fun eq => (gap.avoids _ gap.has).2 (idx hk gap.vb eq)⟩
  have dest : del₂ U (P.node gap.a) (P.node gap.b) v :=
    ⟨⟨uv,fun eq => cv (eq ▸ mem _ gap.va)⟩,fun eq => cv (eq ▸ mem _ gap.vb)⟩
  have walk := three.2 (P.node gap.a) (P.node gap.b) _ source _ dest
  have endside := walk.preserve (L := L) (Or.inl ⟨k,hk,gap.has,rfl⟩) (by
    intro z z' lz uz' e
    by_cases on : C z'
    · obtain ⟨j,hj,rfl⟩ := on
      have ja : j ≠ gap.a := fun eq => uz'.1.2 (congrArg P.node eq)
      have jb : j ≠ gap.b := fun eq => uz'.2 (congrArg P.node eq)
      refine Or.inl ⟨j,hj,?_,rfl⟩
      rcases lz with ⟨i,hi,ii,rfl⟩ | ⟨i,hi,ii,a,ia,az⟩
      · exact gap.rim_step i j hi hj ii ((around i j hi hj).mp e) ja jb
      · apply Classical.byContradiction; intro outside
        obtain ⟨t,ht,mt,ord⟩ := gap.separates i j hi hj ii outside ja jb
        have na : ¬B a := fun ba => gap.unmarked i hi ii ⟨hi,a,ba,ia⟩
        rcases ord with ⟨it,tj⟩ | ⟨jt,ti⟩
        · exact noBetween hi hj it tj mt ia e az na
        · exact noBetween hj hi jt ti mt (G.sym e) (G.sym ia) az.reverse (fun bz => na (az.reverse.preserve bz closed))
    · have oz : O z' := ⟨uz'.1.1,on⟩
      rcases lz with ⟨i,hi,ii,rfl⟩ | ⟨i,hi,ii,a,ia,az⟩
      · exact Or.inr ⟨i,hi,ii,z',e,.here oz⟩
      · exact Or.inr ⟨i,hi,ii,a,ia,az.next e oz⟩)
  rcases endside with ⟨i,hi,_,eq⟩ | ⟨i,hi,ii,a,ia,av⟩
  · exact cv ⟨i,hi,eq⟩
  · exact gap.unmarked i hi ii ⟨hi,a,av.reverse.preserve valid.includes closed,ia⟩

theorem tutte_peripheral : TuttePeripheral := by
  intro n G U three size x y v ux uy uv e vx vy
  have ne : x ≠ y := fun eq => G.loopless y (eq ▸ e)
  obtain ⟨W,P,short,sub,avoid,conn⟩ := peripheral_trace three size ux uy uv e vx vy ne
  exact ⟨P.image,sub,⟨0,Nat.zero_le _,P.first⟩,⟨P.len,Nat.le_refl _,P.last⟩,avoid,
    (shortest_rim e ne short).2.2,conn⟩

end KMO
