import KMO.Reduction
import KMO.Trace
namespace KMO

abbrev Around (m i j : Nat) := j = i+1 ∨ i = j+1 ∨ (i = 0 ∧ j = m) ∨ (j = 0 ∧ i = m)

def Ring.image {n} (m : Nat) (f : Nat → Fin n) := fun v => ∃ i,i ≤ m ∧ f i = v

theorem ring_regular {n} {G : Graph n} {m} {f : Nat → Fin n} (long : 2 ≤ m)
    (inj : ∀ {i j}, i ≤ m → j ≤ m → f i = f j → i = j)
    (adj : ∀ i j,i ≤ m → j ≤ m → (G.adj (f i) (f j) ↔ Around m i j)) :
    ∀ v,Ring.image m f v → (G.within (Ring.image m f)).degree v = 2 := by
  rintro _ ⟨i,hi,rfl⟩
  have two : ∃ a b,a ≤ m ∧ b ≤ m ∧ a ≠ b ∧ ∀ j,j ≤ m → (Around m i j ↔ j = a ∨ j = b) := by
    by_cases zero : i = 0
    · exact ⟨1,m,by omega,by omega,by omega,fun j hj => by unfold Around; omega⟩
    by_cases last : i = m
    · exact ⟨m-1,0,by omega,by omega,by omega,fun j hj => by unfold Around; omega⟩
    · exact ⟨i-1,i+1,by omega,by omega,by omega,fun j hj => by unfold Around; omega⟩
  obtain ⟨a,b,ha,hb,ne,spec⟩ := two
  have nodes : f a ≠ f b := fun eq => ne (inj ha hb eq)
  rw [← card_pair nodes]
  apply card_congr; intro j
  constructor
  · intro e; obtain ⟨k,hk,rfl⟩ := e.2.2
    exact ((spec k hk).mp ((adj _ _ hi hk).mp e.1)).imp (congrArg f) (congrArg f)
  · rintro (rfl | rfl)
    · exact ⟨(adj _ _ hi ha).mpr ((spec _ ha).mpr (Or.inl rfl)),⟨i,hi,rfl⟩,a,ha,rfl⟩
    · exact ⟨(adj _ _ hi hb).mpr ((spec _ hb).mpr (Or.inr rfl)),⟨i,hi,rfl⟩,b,hb,rfl⟩

theorem shortest_rim {n} {G : Graph n} {U : Region n} {x y : Fin n} (e : G.adj x y) (ne : x ≠ y)
    {P : Trace (G.diff (edge ne)) U x y} (short : P.Shortest) :
    (2 ≤ P.len) ∧ (∀ i j,i ≤ P.len → j ≤ P.len → (G.adj (P.node i) (P.node j) ↔ Around P.len i j)) ∧
    CycleOn G P.image := by
  have long : 2 ≤ P.len := by
    by_cases z : P.len = 0
    · exact False.elim (ne (P.first.symm.trans (z ▸ P.last)))
    by_cases one : P.len = 1
    · have k := P.step 0 (by omega)
      have no := k.2
      have nd : P.node 1 = y := one ▸ P.last
      exact False.elim (no (Or.inl ⟨P.first,nd⟩))
    · omega
  have inj := @Trace.index_injective _ _ _ _ _ P short
  have meta i j (hi : i ≤ P.len) (hj : j ≤ P.len) : G.adj (P.node i) (P.node j) ↔ Around P.len i j := by
    constructor
    · intro g
      by_cases cut : (edge ne).adj (P.node i) (P.node j)
      · rcases cut with ⟨ix,jy⟩ | ⟨jx,iy⟩
        · exact Or.inr (Or.inr (Or.inl ⟨inj hi (by omega) (ix.trans P.first.symm),inj hj (by omega) (jy.trans P.last.symm)⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨inj hj (by omega) (jx.trans P.first.symm),inj hi (by omega) (iy.trans P.last.symm)⟩))
      · rcases Trace.step_indices short hi hj ⟨g,cut⟩ with a | b
        · exact Or.inl a
        · exact Or.inr (Or.inl b)
    · rintro (rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact (P.step i (by omega)).1
      · exact G.sym (P.step j (by omega)).1
      · simpa [P.first,P.last] using e
      · simpa [P.first,P.last] using G.sym e
  refine ⟨long,meta,⟨_,0,by omega,rfl⟩,conn_move P.span_connected (fun _ => Iff.rfl) (fun _ _ _ _ e => e.1),?_⟩
  exact ring_regular long (fun hi hj eq => inj hi hj eq) meta

theorem least_nat {R : Nat → Prop} (h : ∃ k,R k) : ∃ k,R k ∧ ∀ j,R j → k ≤ j :=
  minimize R id h

theorem greatest_bounded {R : Nat → Prop} {m} (bound : ∀ k,R k → k ≤ m) (h : ∃ k,R k) :
    ∃ k,R k ∧ ∀ j,R j → j ≤ k := by
  obtain ⟨i,ri,min⟩ := minimize R (fun i => m-i) h
  refine ⟨i,ri,fun j rj => ?_⟩
  have b := min j rj; have := bound i ri; have := bound j rj; omega

structure Gap (m k : Nat) (marked : Nat → Prop) where
  a : Nat
  b : Nat
  inside : Nat → Prop
  va : a ≤ m
  vb : b ≤ m
  has : inside k
  unmarked : ∀ i,i ≤ m → inside i → ¬marked i
  avoids : ∀ i, inside i → i ≠ a ∧ i ≠ b
  rim_step : ∀ i j,i ≤ m → j ≤ m → inside i → Around m i j → j ≠ a → j ≠ b → inside j
  separates : ∀ i j,i ≤ m → j ≤ m → inside i → ¬inside j → j ≠ a → j ≠ b →
    ∃ t, t ≤ m ∧ marked t ∧ ((i < t ∧ t < j) ∨ (j < t ∧ t < i))

theorem find_gap {m k} {M : Nat → Prop} (_hk : k ≤ m) (nk : ¬M k)
    (distinct : ∃ i j,M i ∧ M j ∧ i ≠ j) (bound : ∀ i,M i → i ≤ m) : Nonempty (Gap m k M) := by
  classical
  obtain ⟨i,j,mi,mj,ij⟩ := distinct
  obtain ⟨lo,mlo,min⟩ := least_nat ⟨i,mi⟩
  obtain ⟨hi,mhi,max⟩ := greatest_bounded bound ⟨i,mi⟩
  have vlo := bound lo mlo; have vhi := bound hi mhi
  have lh : lo < hi := by have := min i mi; have := max i mi; have := min j mj; have := max j mj; omega
  by_cases mid : lo < k ∧ k < hi
  · obtain ⟨a,⟨ma,ak⟩,maxa⟩ := greatest_bounded (R := fun x => M x ∧ x < k) (m := m)
        (fun x h => bound _ h.1) ⟨lo,mlo,mid.1⟩
    obtain ⟨b,⟨mb,kb⟩,minb⟩ := least_nat (R := fun x => M x ∧ k < x) ⟨hi,mhi,mid.2⟩
    refine ⟨⟨a,b,fun x => a < x ∧ x < b,bound _ ma,bound _ mb,⟨ak,kb⟩,?_,?_,?_,?_⟩⟩
    · intro x _ hx mx; by_cases xk : x < k
      · have := maxa x ⟨mx,xk⟩; omega
      · by_cases kx : k < x
        · have := minb x ⟨mx,kx⟩; omega
        · have eq : x = k := by omega
          exact nk (eq ▸ mx)
    · intro x hx; omega
    · intro x y xv yv xi e ya yb; have := bound _ mb; unfold Around at e; omega
    · intro x y xv yv xi no ya yb
      by_cases yl : y < a
      · exact ⟨a,bound _ ma,ma,Or.inr ⟨yl,xi.1⟩⟩
      · exact ⟨b,bound _ mb,mb,Or.inl ⟨xi.2,by omega⟩⟩
  · have klo : k ≠ lo := fun e => nk (e ▸ mlo)
    have khi : k ≠ hi := fun e => nk (e ▸ mhi)
    refine ⟨⟨lo,hi,fun x => x < lo ∨ hi < x,vlo,vhi,by omega,?_,?_,?_,?_⟩⟩
    · intro x _ inx mx; have := min x mx; have := max x mx; omega
    · intro x hx; omega
    · intro x y xv yv xi e yl yh; unfold Around at e; omega
    · intro x y xv yv xi no yl yh
      rcases xi with left | right
      · exact ⟨lo,vlo,mlo,Or.inl ⟨left,by omega⟩⟩
      · exact ⟨hi,vhi,mhi,Or.inr ⟨by omega,right⟩⟩

end KMO
