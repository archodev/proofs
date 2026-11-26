import KMO.Pair
namespace KMO
variable {n : Nat}

/-- Only indices at most len are used. -/
structure Trace (G : Graph n) (U : Region n) (a b : Fin n) where
  len : Nat
  node : Nat → Fin n
  first : node 0 = a
  last : node len = b
  inside : ∀ i,i ≤ len → U (node i)
  step : ∀ i,i < len → G.adj (node i) (node (i+1))

namespace Trace
variable {G H : Graph n} {U V : Region n} {a b c : Fin n}

def point (ha : U a) : Trace G U a a :=
  ⟨0,fun _ => a,rfl,rfl,fun _ _ => ha,fun i h => False.elim (by omega)⟩

def one (ha : U a) (hb : U b) (e : G.adj a b) : Trace G U a b where
  len := 1
  node i := if i = 0 then a else b
  first := by simp
  last := by simp
  inside i _ := by split <;> assumption
  step i hi := by have eq : i = 0 := by omega
                  subst i; simpa using e

def append (P : Trace G U a b) (Q : Trace G U b c) : Trace G U a c where
  len := P.len + Q.len
  node i := if i ≤ P.len then P.node i else Q.node (i-P.len)
  first := by simp [P.first]
  last := by
    by_cases q : Q.len = 0
    · simp [q,P.last]; exact Q.first.symm.trans (q ▸ Q.last)
    · rw [if_neg (by omega),show P.len + Q.len - P.len = Q.len by omega,Q.last]
  inside i h := by split
                   next e => exact P.inside i e
                   next => exact Q.inside _ (by omega)
  step i h := by
    by_cases lt : i < P.len
    · rw [if_pos (by omega),if_pos (by omega)]; exact P.step i lt
    · by_cases eq : i = P.len
      · subst i; rw [if_pos (by omega),if_neg (by omega),P.last]
        have j : P.len + 1 - P.len = 0+1 := by omega
        rw [j]; simpa only [Q.first] using Q.step 0 (by omega)
      · rw [if_neg (by omega),if_neg (by omega)]
        have j : i+1-P.len = (i-P.len)+1 := by omega
        rw [j]; exact Q.step _ (by omega)

def takePart (P : Trace G U a b) (i : Nat) (h : i ≤ P.len) : Trace G U a (P.node i) :=
  ⟨i,P.node,P.first,rfl,fun _ k => P.inside _ (by omega),fun _ k => P.step _ (by omega)⟩

def suffix (P : Trace G U a b) (i : Nat) (h : i ≤ P.len) : Trace G U (P.node i) b where
  len := P.len-i
  node k := P.node (i+k)
  first := by simp
  last := by rw [show i+(P.len-i)=P.len by omega,P.last]
  inside k hk := P.inside _ (by omega)
  step k hk := P.step _ (by omega)

theorem indexed {P : Trace G U a b} (i : Nat) (hi : i ≤ P.len) : Reach G U a (P.node i) := by
  induction i with
  | zero => rw [P.first]; exact .here (P.first ▸ P.inside 0 (by omega))
  | succ i ih => exact (ih (by omega)).next (P.step i (by omega)) (P.inside _ hi)

theorem reaches (P : Trace G U a b) : Reach G U a b := P.last ▸ indexed P.len (Nat.le_refl _)

theorem of_reach (p : Reach G U a b) : Nonempty (Trace G U a b) := by
  induction p with
  | here hv => exact ⟨point hv⟩
  | next p e h ih =>
    obtain ⟨P⟩ := ih; exact ⟨P.append (one p.finish h e)⟩

def image (P : Trace G U a b) : Region n := fun v => ∃ i,i ≤ P.len ∧ P.node i = v

def transport (P : Trace G U a b) (inV : ∀ i,i ≤ P.len → V (P.node i))
    (edges : ∀ i,i < P.len → H.adj (P.node i) (P.node (i+1))) : Trace H V a b :=
  ⟨P.len,P.node,P.first,P.last,inV,edges⟩

theorem span_connected (P : Trace G U a b) : ConnectedOn G P.image := by
  let Q : Trace G P.image a b := P.transport (fun i hi => ⟨i,hi,rfl⟩) P.step
  have walk i (hi : P.image i) : Reach G P.image a i := by
    obtain ⟨k,hk,rfl⟩ := hi; exact indexed (P := Q) k hk
  exact fun i hi j hj => (walk i hi).reverse.trans (walk j hj)

def Shortest (P : Trace G U a b) := ∀ Q : Trace G U a b, P.len ≤ Q.len

theorem shortest_of_reach (p : Reach G U a b) : ∃ P : Trace G U a b,P.Shortest := by
  obtain ⟨Q⟩ := of_reach p
  obtain ⟨P,_,min⟩ := minimize (fun _ : Trace G U a b => True) (fun T => T.len) ⟨Q,trivial⟩
  exact ⟨P,fun T => min T trivial⟩

theorem splice_bound {P : Trace G U a b} (short : P.Shortest) {i j} (hi : i ≤ P.len) (hj : j ≤ P.len)
    (Q : Trace G U (P.node i) (P.node j)) : j ≤ i + Q.len := by
  have bound := short (((P.takePart i hi).append Q).append (P.suffix j hj))
  change P.len ≤ i + Q.len + (P.len-j) at bound
  omega

theorem index_injective {P : Trace G U a b} (short : P.Shortest) {i j}
    (hi : i ≤ P.len) (hj : j ≤ P.len) (eq : P.node i = P.node j) : i = j := by
  have oneWay {r s} (hr : r ≤ P.len) (hs : s ≤ P.len) (eqn : P.node r = P.node s) : s ≤ r := by
    let Q : Trace G U (P.node r) (P.node s) := ⟨0,fun _ => P.node r,rfl,eqn,fun _ _ => P.inside _ hr,fun _ k => False.elim (by omega)⟩
    have zero : Q.len = 0 := rfl
    have k := splice_bound short hr hs Q; omega
  exact Nat.le_antisymm (oneWay hj hi eq.symm) (oneWay hi hj eq)

theorem step_indices {P : Trace G U a b} (short : P.Shortest) {i j}
    (hi : i ≤ P.len) (hj : j ≤ P.len) (e : G.adj (P.node i) (P.node j)) :
    j = i+1 ∨ i = j+1 := by
  have k := splice_bound short hi hj (one (P.inside _ hi) (P.inside _ hj) e)
  have l := splice_bound short hj hi (one (P.inside _ hj) (P.inside _ hi) (G.sym e))
  change j ≤ i+1 at k; change i ≤ j+1 at l
  have ne : i ≠ j := fun eq => G.loopless _ (eq ▸ e)
  omega

theorem subreach {P : Trace G U a b} {i j} (ij : i ≤ j) (hj : j ≤ P.len)
    (inV : ∀ k,i ≤ k → k ≤ j → V (P.node k)) (sub : G.Sub H) :
    Reach H V (P.node i) (P.node j) := by
  have build (m : Nat) (le : i+m ≤ j) : Reach H V (P.node i) (P.node (i+m)) := by
    induction m with
    | zero => simpa using (Reach.here (G := H) (inV i (by omega) (by omega)))
    | succ m ih => exact (ih (by omega)).next (sub (P.step _ (by omega))) (inV _ (by omega) le)
  simpa [show i+(j-i)=j by omega] using build (j-i) (by omega)

end Trace
end KMO
