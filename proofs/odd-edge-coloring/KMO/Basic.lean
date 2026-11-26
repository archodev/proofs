import Std

namespace KMO

abbrev Region (n : Nat) := Fin n → Prop

def total : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n+1, f => f 0 + total n (fun i => f i.succ)

noncomputable def bit (p : Prop) : Nat := by
  classical exact if p then 1 else 0

noncomputable def card {n} (S : Region n) := total n (fun x => bit (S x))

theorem total_congr {n} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    total n f = total n g := by rw [funext h]

theorem total_add {n} (f g : Fin n → Nat) :
    total n (fun i => f i + g i) = total n f + total n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total]; rw [ih]; omega

theorem total_zero (n) : total n (fun _ => 0) = 0 := by
  induction n with | zero => rfl | succ n ih => simp [total, ih]

theorem total_one (n) : total n (fun _ => 1) = n := by
  induction n with | zero => rfl | succ n ih => simp [total, ih]; omega

theorem card_congr {n} {S T : Region n} (h : ∀ i, S i ↔ T i) : card S = card T := by
  rw [funext (fun i => propext (h i))]

theorem card_empty {n} : card (fun _ : Fin n => False) = 0 := by
  simpa [card, bit] using total_zero n

theorem card_full {n} : card (fun _ : Fin n => True) = n := by
  simpa [card, bit] using total_one n

theorem card_single {n} (v : Fin n) : card (fun x => x = v) = 1 := by
  induction n with
  | zero => exact v.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) v
    · simp [card, total, bit, total_zero, Fin.succ_ne_zero]
    · change bit ((0 : Fin (n+1)) = j.succ) + card (fun i : Fin n => i.succ = j.succ) = 1
      rw [card_congr (fun i : Fin n => Fin.succ_inj)]
      simpa [bit, Ne.symm (Fin.succ_ne_zero j)] using ih j

theorem card_split {n} (S T : Region n) :
    card (fun x => S x ∧ T x) + card (fun x => S x ∧ ¬ T x) = card S := by
  unfold card
  rw [← total_add]
  apply total_congr
  intro i; by_cases h : S i <;> by_cases k : T i <;> simp [h,k,bit]

theorem card_union {n} {S T : Region n} (dis : ∀ i, S i → ¬ T i) :
    card (fun x => S x ∨ T x) = card S + card T := by
  unfold card
  rw [← total_add]
  apply total_congr
  intro i
  by_cases h : S i
  · simp [h, dis i h, bit]
  · by_cases k : T i <;> simp [h, k, bit]

theorem card_pos {n} {S : Region n} : 0 < card S ↔ ∃ i, S i := by
  induction n with
  | zero => simp [card,total]; intro x; exact x.elim0
  | succ n ih =>
    change 0 < bit (S 0) + card (fun i : Fin n => S i.succ) ↔ _
    constructor
    · intro h; by_cases h0 : S 0
      · exact ⟨0,h0⟩
      · simp [bit,h0] at h
        obtain ⟨i,hi⟩ := ih.mp h
        exact ⟨i.succ,hi⟩
    · rintro ⟨i,hi⟩
      refine Fin.cases (motive := fun i => S i → _) ?_ ?_ i hi
      · intro h0; simp [bit,h0]; omega
      · intro j hj; have h := (ih (S := fun i : Fin n => S i.succ)).mpr ⟨j,hj⟩; omega

def XorP (p q : Prop) := (p ∧ ¬q) ∨ (q ∧ ¬p)

theorem card_xor {n} (S T : Region n) :
    card (fun i => XorP (S i) (T i)) % 2 = (card S + card T) % 2 := by
  have h : card (fun i => XorP (S i) (T i)) +
      (card (fun i => S i ∧ T i) + card (fun i => S i ∧ T i)) = card S + card T := by
    unfold card
    simp only [← total_add]
    apply total_congr
    intro i; by_cases a : S i <;> by_cases b : T i <;> simp [XorP,bit,a,b]
  omega

structure Graph (n : Nat) where
  adj : Fin n → Fin n → Prop
  sym : ∀ {x y}, adj x y → adj y x
  loopless : ∀ x, ¬ adj x x

namespace Graph
variable {n : Nat}
noncomputable def degree (G : Graph n) (v : Fin n) := card (G.adj v)
abbrev Sub (A G : Graph n) := ∀ ⦃x y⦄, A.adj x y → G.adj x y
abbrev Disj (A B : Graph n) := ∀ ⦃x y⦄, A.adj x y → ¬B.adj x y
def Empty (n) : Graph n := ⟨fun _ _ => False, by simp, by simp⟩
def union (A B : Graph n) : Graph n :=
  ⟨fun x y => A.adj x y ∨ B.adj x y, fun h => h.imp A.sym B.sym, by simp [A.loopless,B.loopless]⟩
def diff (A B : Graph n) : Graph n :=
  ⟨fun x y => A.adj x y ∧ ¬B.adj x y, fun h => ⟨A.sym h.1, fun k => h.2 (B.sym k)⟩,
   fun v h => A.loopless v h.1⟩
def xor (A B : Graph n) : Graph n := (A.diff B).union (B.diff A)
def within (G : Graph n) (S : Region n) : Graph n :=
  ⟨fun x y => G.adj x y ∧ S x ∧ S y, fun h => ⟨G.sym h.1,h.2.2,h.2.1⟩,
   fun v h => G.loopless v h.1⟩
def star (v : Fin n) (S : Region n) (hv : ¬S v) : Graph n :=
  ⟨fun x y => (x = v ∧ S y) ∨ (y = v ∧ S x), fun h => h.symm, by
    intro x h; rcases h with ⟨rfl,h⟩ | ⟨rfl,h⟩ <;> exact hv h⟩
abbrev oddAt (G : Graph n) (v : Fin n) := G.degree v % 2 = 1
abbrev good (G : Graph n) := ∀ v, G.degree v = 0 ∨ G.oddAt v
def supp (G : Graph n) : Region n := fun x => ∃ y, G.adj x y

theorem degree_pos {G : Graph n} {v} : 0 < G.degree v ↔ G.supp v := card_pos

theorem degree_union {A B : Graph n} (h : A.Disj B) (v) :
    (A.union B).degree v = A.degree v + B.degree v := card_union (fun _ a => h a)
theorem degree_diff {A G : Graph n} (h : A.Sub G) (v) :
    A.degree v + (G.diff A).degree v = G.degree v := by
  have k := card_split (G.adj v) (A.adj v)
  have e : card (fun y => G.adj v y ∧ A.adj v y) = A.degree v :=
    card_congr (fun _ => ⟨And.right, fun l => ⟨h l,l⟩⟩)
  rw [e] at k; exact k
theorem degree_xor (A B : Graph n) (v) :
    (A.xor B).degree v % 2 = (A.degree v + B.degree v) % 2 := card_xor _ _
theorem degree_star (v x : Fin n) (S : Region n) (hv : ¬S v) :
    (star v S hv).degree x = (if x = v then card S else bit (S x)) := by
  by_cases he : x = v
  · subst x; simp only [if_pos rfl]
    exact card_congr (by simp [star,hv])
  · rw [if_neg he]
    by_cases hx : S x
    · simp [bit,hx]
      exact (card_congr (by simp [star,he,hx])).trans (card_single v)
    · simp [bit,hx]
      exact (card_congr (by simp [star,he,hx])).trans card_empty

end Graph

inductive Reach {n} (G : Graph n) (S : Region n) (x : Fin n) : Fin n → Prop
  | here (h : S x) : Reach G S x x
  | next {y z} (p : Reach G S x y) (e : G.adj y z) (h : S z) : Reach G S x z

def ConnectedOn {n} (G : Graph n) (S : Region n) :=
  ∀ x, S x → ∀ y, S y → Reach G S x y

def ThreeConnected {n} (G : Graph n) :=
  4 ≤ n ∧ ∀ D : Region n, card D ≤ 2 → ConnectedOn G (fun x => ¬ D x)

inductive Color | red | blue | green deriving DecidableEq, Repr

/-- A partition into three possibly empty undirected edge classes. -/
def OddThree {n} (G : Graph n) := ∃ P : Color → Graph n,
  (∀ x y, G.adj x y ↔ ∃ c, (P c).adj x y) ∧
  (∀ c d, c ≠ d → (P c).Disj (P d)) ∧ ∀ c, (P c).good

def ConjectureSix : Prop := ∀ (n : Nat) (G : Graph n), n % 2 = 1 →
  ThreeConnected G → (∀ v, 4 ≤ G.degree v) → OddThree G

end KMO
