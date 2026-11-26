import KMO.Prepare
import KMO.PathColors

namespace KMO
variable {n : Nat}

noncomputable def pathFlags {G : Graph n} {s t} (P : OpenPath G s t) (H R : Graph n) : Nat → Bool
  | 0 => decide (R.degree s % 2 = 0)
  | i+1 => if H.degree (P.node (i+1)) = 0 then !(pathFlags P H R i) else pathFlags P H R i

theorem explicit_three {G A B F : Graph n}
    (cover : ∀ i j,G.adj i j ↔ A.adj i j ∨ B.adj i j ∨ F.adj i j)
    (ab : A.Disj B) (af : A.Disj F) (bf : B.Disj F) (a : A.good) (b : B.good) (f : F.good) :
    OddThree G := by
  let P : Color → Graph n := fun | .red => A | .blue => B | .green => F
  refine ⟨P,?_,?_,?_⟩
  · intro i j; rw [cover]; constructor
    · rintro (h | h | h)
      · exact ⟨.red,h⟩
      · exact ⟨.blue,h⟩
      · exact ⟨.green,h⟩
    · rintro ⟨c,h⟩; cases c
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · intro c d ne i j x y
    cases c <;> cases d <;> simp [P] at * <;> first | exact ab x y | exact ab y x | exact af x y | exact af y x | exact bf x y | exact bf y x
  · intro c; cases c <;> assumption

/-- Kano–Maezawa–Ozeki, Theorem 7. -/
theorem multiple_even {G : Graph n} (order : n % 2 = 1) (st : ThreeConnected G)
    {x y} (ne : x ≠ y) (ex : G.degree x % 2 = 0) (ey : G.degree y % 2 = 0) :
    OddThree G := by
  classical
  obtain ⟨s,t,P,clean⟩ := clean_path st ne ex ey
  obtain ⟨F,R,fs,rs,zeroS,oddF,zeroT,localGood⟩ := prepare clean order (degree_of_three st) st.1
  let K := P.edges
  let A := G.diff K
  let H := A.diff F
  let B := H.diff R
  let f := pathFlags P H R
  let X := P.strand f true
  let Y := P.strand f false
  have xk : X.Sub K := P.strand_sub _ _
  have yk : Y.Sub K := P.strand_sub _ _
  have kg : K.Sub G := by intro _ _ e; exact e.1
  have fsub : F.Sub A := fs
  have rsub : R.Sub H := rs
  have bsub : B.Sub H := by intro _ _ e; exact e.1
  have rx : R.Disj X := by intro i j r x; exact (rsub r).1.2 (xk x)
  have by' : B.Disj Y := by intro i j b y; exact (bsub b).1.2 (yk y)
  have sum v : K.degree v + (F.degree v + (R.degree v + B.degree v)) = G.degree v := by
    have k := Graph.degree_diff kg v; have a := Graph.degree_diff fsub v; have h := Graph.degree_diff rsub v
    change K.degree v + A.degree v = G.degree v at k
    change F.degree v + H.degree v = A.degree v at a
    change R.degree v + B.degree v = H.degree v at h
    omega
  have hn v : R.degree v + B.degree v = H.degree v := Graph.degree_diff rsub v
  have cleanR v : (R.union X).degree v = R.degree v + X.degree v := Graph.degree_union rx v
  have cleanB v : (B.union Y).degree v = B.degree v + Y.degree v := Graph.degree_union by' v
  have vertexGood v : ((R.union X).degree v = 0 ∨ (R.union X).oddAt v) ∧
      ((B.union Y).degree v = 0 ∨ (B.union Y).oddAt v) := by
    unfold Graph.oddAt; rw [cleanR,cleanB]
    by_cases vs : v = s
    · subst v
      have k := sum s; change P.edges.degree s + _ = _ at k; rw [P.degree_a,zeroS] at k
      have ev := clean.firstEven
      have xs : X.degree s = bit (f 0 = true) := P.strand_start f true
      have ys : Y.degree s = bit (f 0 = false) := P.strand_start f false
      rw [xs,ys]
      by_cases r : R.degree s % 2 = 0 <;> simp [f,pathFlags,bit,r] <;> omega
    by_cases vt : v = t
    · subst v; have eq := hn t
      change H.degree t = 0 at zeroT
      have r : R.degree t = 0 := by omega
      have b : B.degree t = 0 := by omega
      have endX : X.degree t = bit (f (P.len-1) = true) := P.strand_end f true
      have endY : Y.degree t = bit (f (P.len-1) = false) := P.strand_end f false
      rw [r,b,endX,endY]; cases e : f (P.len-1) <;> simp [bit]
    have good := localGood v vs
    change (R.degree v = 0 ∨ R.degree v % 2 = 1) ∧ (B.degree v = 0 ∨ B.degree v % 2 = 1) at good
    by_cases on : P.verts v
    case neg =>
      have zx := outside (G := X) (S := P.verts) (by intro _ _ e; exact (xk e).2.1) on
      have zy := outside (G := Y) (S := P.verts) (by intro _ _ e; exact (yk e).2.1) on
      simpa [zx,zy] using good
    obtain ⟨i,hi,rfl⟩ := on
    have ip : 0 < i := by
      by_cases z : i=0; exact False.elim (vs (z ▸ P.first)); omega
    have il : i < P.len := by
      by_cases z : i=P.len; exact False.elim (vt (z ▸ P.last)); omega
    have ig := clean.innerOdd i ip il
    have of' := oddF (P.node i) vs
    have k := sum (P.node i)
    have pd := P.degree_at hi
    have nn : ¬(i=0 ∨ i=P.len) := by omega
    rw [if_neg nn] at pd; change K.degree (P.node i) = 2 at pd
    have h := hn (P.node i)
    have xx : X.degree (P.node i) = bit (f (i-1) = true) + bit (f i = true) := by
      simpa only [ip,il,true_and] using P.strand_degree f true hi
    have yy : Y.degree (P.node i) = bit (f (i-1) = false) + bit (f i = false) := by
      simpa only [ip,il,true_and] using P.strand_degree f false hi
    rw [xx,yy]
    have seq : f i = if H.degree (P.node i) = 0 then !(f (i-1)) else f (i-1) := by
      have step := pathFlags.eq_2 P H R (i-1)
      simpa only [Nat.succ_eq_add_one,show i-1+1=i by omega] using step
    unfold Graph.oddAt at ig of'
    by_cases hz : H.degree (P.node i) = 0
    · rw [if_pos hz] at seq
      have rz : R.degree (P.node i) = 0 := by omega
      have bz : B.degree (P.node i) = 0 := by omega
      rw [rz,bz,seq]; cases prev : f (i-1) <;> simp [bit]
    · rw [if_neg hz] at seq
      have both : R.degree (P.node i) % 2 = 1 ∧ B.degree (P.node i) % 2 = 1 := by omega
      rw [seq]; cases prev : f (i-1) <;> simp [bit] <;> omega
  apply explicit_three (A := R.union X) (B := B.union Y) (F := F)
  · intro i j; constructor
    · intro g; by_cases path : K.adj i j
      · rcases P.strand_cover f path with x | y
        · exact Or.inl (Or.inr x)
        · exact Or.inr (Or.inl (Or.inr y))
      · by_cases green : F.adj i j
        · exact Or.inr (Or.inr green)
        · by_cases r : R.adj i j
          · exact Or.inl (Or.inl r)
          · exact Or.inr (Or.inl (Or.inl ⟨⟨⟨g,path⟩,green⟩,r⟩))
    · rintro ((r|x) | (b|y) | f)
      · exact (rsub r).1.1
      · exact kg (xk x)
      · exact (bsub b).1.1
      · exact kg (yk y)
      · exact (fs f).1
  · intro i j rr bb
    rcases rr with r|x <;> rcases bb with b|y
    · exact b.2 r
    · exact (rsub r).1.2 (yk y)
    · exact (bsub b).1.2 (xk x)
    · exact P.strand_disjoint f x y
  · rintro i j (r|x) green
    · exact (rsub r).2 green
    · exact (fs green).2 (xk x)
  · rintro i j (b|y) green
    · exact (bsub b).2 green
    · exact (fs green).2 (yk y)
  · exact fun v => (vertexGood v).1
  · exact fun v => (vertexGood v).2
  · intro v; by_cases vs : v = s
    · subst v; exact Or.inl zeroS
    · exact Or.inr (oddF v vs)

end KMO
