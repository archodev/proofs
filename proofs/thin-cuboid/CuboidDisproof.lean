import Std

/-!
# Two exact-degree dismantlings of cuboids

Barát and Wanless, arXiv:2603.23913, Section 6, Conjecture 2.
The finite witnesses below specialize the prior percolating constructions of
Dukes, Noel and Romer, arXiv:2209.07594, Propositions 5.4 and 5.8.
The proofs start with the full cuboid and verify deletions in the induced graph.
-/

namespace Cuboid

abbrev Cell (a b k : Nat) := Fin a × Fin b × Fin k
abbrev Position (a b k : Nat) := Cell a b k → Bool

variable {a b k : Nat}

/-- Enumerate the cuboid by taking each coordinate once in increasing order. -/
def cells (a b k : Nat) : List (Cell a b k) :=
  (List.finRange a).flatMap fun x =>
    (List.finRange b).flatMap fun y =>
      (List.finRange k).map fun z => (x, y, z)

def full : Position a b k := fun _ => true

private def consecutive (i j : Nat) : Bool :=
  (i + 1 == j) || (j + 1 == i)

/-- Face adjacency. The changed coordinate differs by one as a natural number.
    In particular there is no wraparound at the boundary. -/
def faceAdjacent (u v : Cell a b k) : Bool :=
  let (x, y, z) := u
  let (i, j, l) := v
  (consecutive x.val i.val && y == j && z == l) ||
  (x == i && consecutive y.val j.val && z == l) ||
  (x == i && y == j && consecutive z.val l.val)

def card (s : Position a b k) : Nat := (cells a b k).countP s

/-- Number of neighbors of v belonging to the current position s. -/
def degree (s : Position a b k) (v : Cell a b k) : Nat :=
  (cells a b k).countP fun u => faceAdjacent v u && s u

def erase (s : Position a b k) (v : Cell a b k) : Position a b k :=
  fun u => if u = v then false else s u

def Legal (s : Position a b k) (v : Cell a b k) : Prop :=
  s v = true ∧ degree s v = 3

instance (s : Position a b k) (v : Cell a b k) : Decidable (Legal s v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A lawful deletion path with its initial position, exact list of moves, and endpoint. -/
inductive Dismantles : Position a b k → List (Cell a b k) → Position a b k → Prop
  | stop (s) : Dismantles s [] s
  | step {s t v vs} : Legal s v → Dismantles (erase s v) vs t → Dismantles s (v :: vs) t

def Reachable (s : Position a b k) : Prop :=
  ∃ moves, Dismantles full moves s

def Independent (s : Position a b k) : Prop :=
  ∀ u, s u = true → ∀ v, s v = true → faceAdjacent u v = false

def Terminal (s : Position a b k) : Prop := ∀ v, ¬ Legal s v

private theorem terminal_of_independent {s : Position a b k} (hi : Independent s) :
    Terminal s := by
  intro v move
  obtain ⟨present, three⟩ := move
  have zero : degree s v = 0 := by
    unfold degree
    induction cells a b k with
    | nil => rfl
    | cons u us ih =>
      apply (List.countP_cons_of_neg _).trans ih
      intro edge
      obtain ⟨adjacent, alive⟩ := Bool.and_eq_true_iff.mp edge
      exact Bool.noConfusion ((hi v present u alive).symm.trans adjacent)
  exact (by decide : 0 ≠ 3) (zero.symm.trans three)

/-- The ceiling of the surface-area lower bound. -/
def lowerBound (a b k : Nat) : Nat := (a*b + a*k + b*k + 2) / 3

/-- An ordinary solution is a reachable independent position attaining the bound. -/
def HasSolution (a b k : Nat) : Prop :=
  ∃ s : Position a b k, Reachable s ∧ Independent s ∧ card s = lowerBound a b k

private instance forallCell (p : Cell a b k → Prop) [DecidablePred p] :
    Decidable (∀ u, p u) :=
  decidable_of_iff (∀ x y z, p (x, y, z))
    ⟨fun h ⟨x, y, z⟩ => h x y z, fun h x y z => h (x, y, z)⟩

private instance (s : Position a b k) : Decidable (Independent s) := by
  unfold Independent
  infer_instance

/- The list specifies which moves to try. Soundness supplies a proof of the
   inductively defined deletion relation for every accepted list. -/
private def finish (s : Position a b k) : List (Cell a b k) → Position a b k
  | [] => s
  | v :: vs => finish (erase s v) vs

private def lawful (s : Position a b k) : List (Cell a b k) → Bool
  | [] => true
  | v :: vs => decide (Legal s v) && lawful (erase s v) vs

private theorem lawful_sound (s : Position a b k) (vs : List (Cell a b k))
    (h : lawful s vs = true) : Dismantles s vs (finish s vs) := by
  induction vs generalizing s with
  | nil => exact .stop s
  | cons v vs ih =>
    obtain ⟨hv, ht⟩ := Bool.and_eq_true_iff.mp h
    exact .step (of_decide_eq_true hv) (ih (erase s v) ht)

/-- One label per vertex. Zero marks a survivor; positive labels are deleted
    from largest to smallest, with coordinate order breaking ties. -/
private abbrev Labels (a b k : Nat) := Vector (Vector (Vector Nat k) b) a

private def label (w : Labels a b k) (v : Cell a b k) : Nat :=
  w[v.1][v.2.1][v.2.2]

private def moves (w : Labels a b k) (largest : Nat) : List (Cell a b k) :=
  (List.range largest).reverse.flatMap fun n =>
    (cells a b k).filter fun v => label w v == n + 1

private def survivors (w : Labels a b k) : Position a b k :=
  fun v => label w v == 0

private def labels239 : Labels 2 3 9 := #v[
  #v[#v[0,1,0,1,2,1,0,3,0], #v[1,2,1,0,1,0,1,2,1], #v[0,3,0,1,0,1,0,1,0]],
  #v[#v[1,0,1,0,3,0,9,10,11], #v[0,3,4,5,6,7,8,3,0], #v[15,14,13,12,11,10,9,0,1]]]

private def labels336 : Labels 3 3 6 := #v[
  #v[#v[0,3,4,0,1,0], #v[1,2,0,1,0,10], #v[0,3,4,5,6,11]],
  #v[#v[1,0,5,6,7,8], #v[0,1,2,3,6,9], #v[1,2,3,4,5,0]],
  #v[#v[12,11,10,9,8,0], #v[1,0,1,0,7,10], #v[0,1,0,1,0,11]]]

/-- The mathematical statement certified by a finite trace. -/
def HasDismantling (a b k steps left : Nat) : Prop :=
  ∃ (vs : List (Cell a b k)) (s : Position a b k),
    Dismantles full vs s ∧ vs.length = steps ∧ Independent s ∧ Terminal s ∧ card s = left

private theorem certify (w : Labels a b k) (largest steps left : Nat)
    (hLaw : lawful full (moves w largest) = true)
    (hEnd : ∀ v, finish full (moves w largest) v = survivors w v)
    (hSteps : (moves w largest).length = steps) (hInd : Independent (survivors w))
    (hCard : card (survivors w) = left) :
    HasDismantling a b k steps left := by
  refine ⟨moves w largest, survivors w, ?_, hSteps, hInd, terminal_of_independent hInd, hCard⟩
  exact (funext hEnd) ▸ lawful_sound full (moves w largest) hLaw

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem dismantling_2_3_9 : HasDismantling 2 3 9 37 17 :=
  certify labels239 15 37 17 (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem dismantling_3_3_6 : HasDismantling 3 3 6 39 15 :=
  certify labels336 12 39 15 (by decide) (by decide) (by decide)
    (by decide) (by decide)

private theorem solution_of_dismantling {steps left : Nat}
    (h : HasDismantling a b k steps left) (hSize : left = lowerBound a b k) :
    HasSolution a b k := by
  obtain ⟨vs, s, path, _, independent, _, count⟩ := h
  exact ⟨s, ⟨vs, path⟩, independent, count.trans hSize⟩

theorem solution_2_3_9 : HasSolution 2 3 9 :=
  solution_of_dismantling dismantling_2_3_9 rfl

theorem solution_3_3_6 : HasSolution 3 3 6 :=
  solution_of_dismantling dismantling_3_3_6 rfl

/-- The second clause already fails on the restricted domain of lengths above three. -/
theorem not_second_clause_long :
    ¬ (∀ k : Nat, 3 < k → (HasSolution 2 3 k ↔ k = 6)) :=
  fun h => (by decide : 9 ≠ 6) ((h 9 (by decide)).mp solution_2_3_9)

theorem not_second_clause :
    ¬ (∀ k : Nat, 0 < k → (HasSolution 2 3 k ↔ k = 6)) :=
  fun h => (by decide : 9 ≠ 6) ((h 9 (by decide)).mp solution_2_3_9)

theorem not_third_clause :
    ¬ (∀ k : Nat, 0 < k → (HasSolution 3 3 k ↔ k % 2 = 1 ∨ k = 4)) :=
  fun h => (by decide : ¬ (6 % 2 = 1 ∨ 6 = 4)) ((h 6 (by decide)).mp solution_3_3_6)

#print axioms dismantling_2_3_9
#print axioms dismantling_3_3_6
#print axioms solution_2_3_9
#print axioms solution_3_3_6
#print axioms not_second_clause_long
#print axioms not_second_clause
#print axioms not_third_clause

end Cuboid
