import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Choose
import Mathlib.Tactic.ByContra

/-! Finite existentially complete triangle-free graphs. Slot addresses can refer to
every coordinate, including address and expected-value coordinates of other slots.
The sum types are named coordinates; Option.none represents the distinguished zero. -/
namespace Problem29
noncomputable section
open Finset
variable {k : ℕ}

def capacity (k : ℕ) := 3*k*(k-1)+k
abbrev S (k : ℕ) := Fin k
abbrev Row (k : ℕ) := Fin (capacity k)
abbrev Short (k : ℕ) := Unit ⊕ (S k ⊕ (S k × S k))
abbrev Key (k : ℕ) := Unit ⊕ ((S k × Short k) ⊕ ((S k × Row k) ⊕ (S k × Row k)))
abbrev Val (k : ℕ) := Option (Key k)
abbrev Raw (k : ℕ) := Key k → Val k

def root : Key k := .inl ()
def head (i : S k) (w : Short k) : Key k := .inr (.inl (i,w))
def addr (i : S k) (r : Row k) : Key k := .inr (.inr (.inl (i,r)))
def value (i : S k) (r : Row k) : Key k := .inr (.inr (.inr (i,r)))
def nilW : Short k := .inl ()
def oneW (i : S k) : Short k := .inr (.inl i)
def twoW (i j : S k) : Short k := .inr (.inr (i,j))

def top : Short k → Key k
  | .inl _ => root
  | .inr (.inl i) => head i nilW
  | .inr (.inr (i,j)) => head i (oneW j)

def Cache (x : Raw k) (i : S k) (y : Raw k) :=
  ∀ w, x (head i w) = y (top w)
def Tests (x : Raw k) (i : S k) (y : Raw k) :=
  ∀ r h, x (addr i r) = some h → x (value i r) = y h
def Slot (x : Raw k) (i : S k) (y : Raw k) :=
  x root ≠ y root ∧ Cache x i y ∧ Tests x i y
def Arc (x y : Raw k) := ∃ i, Slot x i y
def Active (x : Raw k) (i : S k) := x (head i nilW) ≠ none

def Fixed (x : Raw k) (i : S k) (d : Key k) (v : Val k) :=
  (∃ w, top w = d ∧ x (head i w) = v) ∨
  (∃ r, x (addr i r) = some d ∧ x (value i r) = v)

theorem fixed_sound {x y : Raw k} {i : S k} (s : Slot x i y) {d v}
    (h : Fixed x i d v) : y d = v := by
  obtain ⟨_, cache, tests⟩ := s
  rcases h with ⟨w, rfl, rfl⟩ | ⟨r, hr, rfl⟩
  · exact (cache w).symm
  · exact (tests r _ hr).symm

abbrev Facts (k : ℕ) := Key k → Val k → Prop
inductive Block (P Q : Facts k) (t : S k) : Prop where
  | colors {v} : P root v → Q root v → Block P Q t
  | labels {w v u} : P (head t w) v → Q (top w) u → v ≠ u → Block P Q t
  | literal {r h v u} : P (addr t r) (some h) → P (value t r) v →
      Q h u → v ≠ u → Block P Q t

theorem Block.mono {P Q P' Q' : Facts k} {t : S k} (b : Block P Q t)
    (l : ∀ d v, P d v → P' d v) (r : ∀ d v, Q d v → Q' d v) : Block P' Q' t := by
  cases b with
  | colors a b => exact .colors (l _ _ a) (r _ _ b)
  | labels a b ne => exact .labels (l _ _ a) (r _ _ b) ne
  | literal a b c ne => exact .literal (l _ _ a) (l _ _ b) (r _ _ c) ne

theorem Block.sound {P Q : Facts k} {t : S k} {x y : Raw k} (b : Block P Q t)
    (l : ∀ d v, P d v → x d = v) (r : ∀ d v, Q d v → y d = v) : ¬ Slot x t y := by
  rintro ⟨ne, cache, tests⟩
  cases b with
  | colors h j => exact ne ((l _ _ h).trans (r _ _ j).symm)
  | labels h j dif => exact dif ((l _ _ h).symm.trans ((cache _).trans (r _ _ j)))
  | literal h j m dif =>
    exact dif ((l _ _ j).symm.trans ((tests _ _ (l _ _ h)).trans (r _ _ m)))

-- Good is a predicate on raw finite records; neither it nor Slot refers to graph adjacency.
structure Good (x : Raw k) : Prop where
  positive : x root ≠ none
  fresh : ∀ i w, x root ≠ x (head i w)
  consistent : ∀ i, Active x i → ∃ y, Cache x i y ∧ Tests x i y
  blocks : ∀ i j, Active x i → Active x j → ∀ t, Block (Fixed x i) (Fixed x j) t

abbrev Vertex (k : ℕ) := {x : Raw k // Good x}
noncomputable instance vertexDecEq : DecidableEq (Vertex k) := Classical.decEq _
noncomputable instance vertexFintype : Fintype (Vertex k) := Fintype.ofFinite _

def graph (k : ℕ) : SimpleGraph (Vertex k) where
  Adj x y := Arc x.val y.val ∨ Arc y.val x.val
  symm _ _ := Or.symm
  loopless x h := by
    rcases h with ⟨i,ne,_,_⟩ | ⟨i,ne,_,_⟩ <;> exact ne rfl

theorem slot_active {x y : Raw k} {i} (s : Slot x i y) (hy : y root ≠ none) :
    Active x i := by
  exact fun h => hy ((s.2.1 nilW).symm.trans h)

theorem fork {x y z : Vertex k} (a : Arc x.val y.val) (b : Arc x.val z.val) :
    ¬ Arc y.val z.val := by
  obtain ⟨i,hi⟩ := a
  obtain ⟨j,hj⟩ := b
  rintro ⟨t,ht⟩
  exact (x.property.blocks i j (slot_active hi y.property.positive)
    (slot_active hj z.property.positive) t).sound
    (fun _ _ => fixed_sound hi) (fun _ _ => fixed_sound hj) ht

theorem no_cycle {x y z : Vertex k} (a : Arc x.val y.val) (b : Arc y.val z.val) :
    ¬ Arc z.val x.val := by
  obtain ⟨i,hi⟩ := a
  obtain ⟨j,hj⟩ := b
  rintro ⟨t,ht⟩
  apply x.property.fresh i (twoW j t)
  exact ((hi.2.1 (twoW j t)).trans ((hj.2.1 (oneW t)).trans (ht.2.1 nilW))).symm

theorem triangle_free (x y z : Vertex k) :
    (graph k).Adj x y → (graph k).Adj y z → ¬ (graph k).Adj z x := by
  rintro (a|a) (b|b) (c|c)
  · exact no_cycle a b c
  · exact fork a c b
  · exact fork c b a
  · exact fork c a b
  · exact fork b a c
  · exact fork a b c
  · exact fork b c a
  · exact no_cycle c b a

def Restrict (x : Raw k) (s : Finset (Key k)) : Facts k := fun d v => d ∈ s ∧ x d = v

-- Each failed slot needs at most two source coordinates and one target coordinate.
theorem small_block (x y : Raw k) (t : S k) (h : ¬ Slot x t y) :
    ∃ l r : Finset (Key k), l.card ≤ 2 ∧ r.card ≤ 1 ∧
      Block (Restrict x l) (Restrict y r) t := by
  classical
  by_cases hc : x root = y root
  · refine ⟨{root},{root},by simp,by simp,.colors ⟨by simp,rfl⟩ ⟨by simp,hc.symm⟩⟩
  by_cases hm : Cache x t y
  · have ht : ¬ Tests x t y := fun hh => h ⟨hc,hm,hh⟩
    unfold Tests at ht
    push_neg at ht
    obtain ⟨row,key,ha,hv⟩ := ht
    refine ⟨{addr t row,value t row},{key},?_,by simp,?_⟩
    · exact (Finset.card_insert_le _ _).trans (by simp)
    · exact .literal ⟨by simp,ha⟩ ⟨by simp,rfl⟩ ⟨by simp,rfl⟩ hv
  · unfold Cache at hm
    push_neg at hm
    obtain ⟨w,hw⟩ := hm
    exact ⟨{head t w},{top w},by simp,by simp,.labels ⟨by simp,rfl⟩ ⟨by simp,rfl⟩ hw⟩


structure Packet (k : ℕ) where
  left : Finset (Key k)
  right : Finset (Key k)
  left_le : left.card ≤ 2
  right_le : right.card ≤ 1

private theorem packet_exists (x y : Raw k) (t : S k) :
    ∃ p : Packet k, ¬Slot x t y →
      Block (Restrict x p.left) (Restrict y p.right) t := by
  classical
  by_cases h : Slot x t y
  · exact ⟨⟨∅, ∅, by simp, by simp⟩, fun hh => (hh h).elim⟩
  obtain ⟨l,r,hl,hr,hb⟩ := small_block x y t h
  exact ⟨⟨l,r,hl,hr⟩,fun _ => hb⟩

def packet (x y : Raw k) (t : S k) : Packet k := (packet_exists x y t).choose
theorem packet_spec (x y : Raw k) (t : S k) (h : ¬ Slot x t y) :
    Block (Restrict x (packet x y t).left) (Restrict y (packet x y t).right) t :=
  (packet_exists x y t).choose_spec h

def distinguish (y b : Vertex k) : Key k := by
  classical
  exact if h : ∃ d, y.val d ≠ b.val d then h.choose else root

theorem distinguish_spec {y b : Vertex k} (ne : y ≠ b) :
    y.val (distinguish y b) ≠ b.val (distinguish y b) := by
  classical
  have h : ∃ d, y.val d ≠ b.val d := by
    by_contra! eq
    exact ne (Subtype.ext (funext eq))
  simpa only [distinguish, dif_pos h] using h.choose_spec

def both (y z : Vertex k) (t : S k) : Finset (Key k) :=
  (packet y.val z.val t).left ∪ (packet z.val y.val t).right

def mask (A B : Finset (Vertex k)) (y : Vertex k) : Finset (Key k) := by
  classical
  exact ((A.erase y).biUnion (fun z => univ.biUnion (both y z))) ∪ B.image (distinguish y)

theorem mask_both {A B : Finset (Vertex k)} {y z : Vertex k}
    (hz : z ∈ A) (ne : z ≠ y) (t : S k) {d : Key k} (hd : d ∈ both y z t) :
    d ∈ mask A B y := by
  classical
  apply Finset.mem_union_left
  exact Finset.mem_biUnion.mpr ⟨z,Finset.mem_erase.mpr ⟨ne,hz⟩,
    Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,hd⟩⟩

theorem mask_dist {A B : Finset (Vertex k)} (y : Vertex k) {b} (hb : b ∈ B) :
    distinguish y b ∈ mask A B y := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)

theorem mask_card {A B : Finset (Vertex k)} {y : Vertex k} (hy : y ∈ A)
    (hk : A.card + B.card ≤ k) : (mask A B y).card ≤ capacity k := by
  classical
  have pairBound (z : Vertex k) (t : S k) : (both y z t).card ≤ 3 :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (packet y.val z.val t).left_le
      (packet z.val y.val t).right_le)
  have slotBound (z : Vertex k) : (univ.biUnion (both y z)).card ≤ k*3 := by
    simpa using Finset.card_biUnion_le_card_mul (univ : Finset (S k)) (both y z) 3
      (fun t _ => pairBound z t)
  have sumBound := Finset.card_biUnion_le_card_mul (A.erase y)
    (fun z => univ.biUnion (both y z)) (k*3) (fun z _ => slotBound z)
  rw [Finset.card_erase_of_mem hy] at sumBound
  have ha : A.card - 1 ≤ k - 1 := by omega
  have hb : B.card ≤ k := by omega
  calc
    (mask A B y).card ≤ _ := Finset.card_union_le _ _
    _ ≤ (A.card-1)*(k*3) + B.card := Nat.add_le_add sumBound Finset.card_image_le
    _ ≤ (k-1)*(k*3) + k := Nat.add_le_add (Nat.mul_le_mul_right _ ha) hb
    _ = capacity k := by simp [capacity, Nat.mul_comm, Nat.mul_left_comm]

-- A finite set of at most n items can be stored in n optional slots.
private theorem cover (α : Type) [Fintype α] (n : ℕ) (h : Fintype.card α ≤ n) :
    ∃ f : Fin n → Option α, ∀ a, ∃ i, f i = some a := by
  classical
  let e := Fintype.equivFin α
  let f (i : Fin n) := if hi : i.val < Fintype.card α then some (e.symm ⟨i.val,hi⟩) else none
  refine ⟨f, fun a => ⟨⟨(e a).val,lt_of_lt_of_le (e a).isLt h⟩,?_⟩⟩
  simp [f,(e a).isLt]

theorem short_card (k : ℕ) : Fintype.card (Short k) = 1+k+k*k := by
  simp [Short, Nat.add_assoc]

theorem key_card (k : ℕ) :
    Fintype.card (Key k) = 1+k*(1+k+k*k)+2*(k*capacity k) := by
  simp only [Key, Fintype.card_sum, Fintype.card_prod, Fintype.card_unit,
    short_card, Fintype.card_fin, S, Row, Nat.add_assoc]
  omega

/-- Numbered addresses use zero for the unused address, and 1 through M for
all fields, with no special restriction on literal fields. -/
def fieldCount (k : ℕ) := 1+k*(1+k+k*k)+2*(k*capacity k)
def fieldEquiv (k : ℕ) : Key k ≃ Fin (fieldCount k) :=
  Fintype.equivFinOfCardEq (key_card k)
def addressNumber : Val k → ℕ
  | none => 0
  | some d => (fieldEquiv k d).val + 1

theorem address_range (v : Val k) : addressNumber v ≤ fieldCount k := by
  cases v with
  | none => exact Nat.zero_le _
  | some d => exact (fieldEquiv k d).isLt

theorem address_injective : Function.Injective (addressNumber (k := k)) := by
  intro u v h
  cases u with
  | none =>
    cases v with
    | none => rfl
    | some b => simp [addressNumber] at h
  | some a =>
    cases v with
    | none => simp [addressNumber] at h
    | some b =>
      apply congrArg some
      apply (fieldEquiv k).injective
      exact Fin.ext (Nat.add_right_cancel h)

theorem address_surj (n : ℕ) (hn : n ≤ fieldCount k) :
    ∃ v : Val k, addressNumber v = n := by
  cases n with
  | zero => exact ⟨none,rfl⟩
  | succ n =>
    let i : Fin (fieldCount k) := ⟨n,hn⟩
    refine ⟨some ((fieldEquiv k).symm i),?_⟩
    simp [addressNumber,i]

set_option synthInstance.maxSize 2000 in
theorem vertex_card (k : ℕ) :
    Fintype.card (Vertex k) ≤ (fieldCount k + 1) ^ fieldCount k := by
  classical
  have h := Fintype.card_subtype_le (Good (k := k))
  change Fintype.card (Vertex k) ≤ Fintype.card (Key k → Option (Key k)) at h
  simpa only [Fintype.card_fun, Fintype.card_option, key_card, fieldCount] using h

theorem four_field_count : fieldCount 4 = 405 := by decide

set_option exponentiation.threshold 512 in
theorem four_vertex_bound : Fintype.card (Vertex 4) ≤ 406 ^ 405 := by
  exact vertex_card 4

private theorem fresh_color (A B : Finset (Vertex k)) (hk : A.card+B.card ≤ k) :
    ∃ c : Key k, ∀ y ∈ A ∪ B, ∀ w : Short k, some c ≠ y.val (top w) := by
  classical
  let f (y : Vertex k) := (univ : Finset (Short k)).image (fun w => y.val (top w))
  let bad := (A ∪ B).biUnion f
  have hf (y : Vertex k) : (f y).card ≤ 1+k+k*k := by
    simpa [f, short_card, Nat.add_assoc] using (Finset.card_image_le (s := (univ : Finset (Short k)))
      (f := fun w => y.val (top w)))
  have hb : bad.card ≤ k*(1+k+k*k) :=
    (Finset.card_biUnion_le_card_mul _ f _ (fun y _ => hf y)).trans
      (Nat.mul_le_mul_right _ ((Finset.card_union_le _ _).trans hk))
  have big : k*(1+k+k*k) < Fintype.card (Key k) := by rw [key_card]; omega
  by_contra! hall
  have sub : (univ : Finset (Key k)).image some ⊆ bad := by
    intro v hv
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,hy,w,hw⟩ := hall c
    exact Finset.mem_biUnion.mpr ⟨y,hy,Finset.mem_image.mpr ⟨w,Finset.mem_univ _,hw.symm⟩⟩
  have hh := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ (Option.some_injective _), Finset.card_univ] at hh
  omega

-- The following constructor fills one disjoint label branch and one literal block per slot.
def build {α : Type} (c : Key k) (raw : α → Raw k) (pick : S k → Option α)
    (rows : α → Row k → Option (Key k)) : Raw k
  | .inl _ => some c
  | .inr (.inl (i,w)) => (pick i).bind (fun a => raw a (top w))
  | .inr (.inr (.inl (i,r))) => (pick i).bind (fun a => rows a r)
  | .inr (.inr (.inr (i,r))) => (pick i).bind (fun a => (rows a r).bind (raw a))

section Construction
variable {α : Type} {c : Key k} {raw : α → Raw k} {pick : S k → Option α}
  {rows : α → Row k → Option (Key k)}

local notation "X" => build c raw pick rows

theorem build_cache {i : S k} {a : α} (ha : pick i = some a) : Cache X i (raw a) := by
  intro w
  simp [build, head, ha]

theorem build_tests {i : S k} {a : α} (ha : pick i = some a) : Tests X i (raw a) := by
  intro r d hd
  change (pick i).bind (fun b => rows b r) = some d at hd
  have hrow : rows a r = some d := by simpa [ha] using hd
  simp [build, value, ha, hrow]

theorem build_fixed {i : S k} {a : α} (ha : pick i = some a) {r : Row k} {d : Key k}
    (hd : rows a r = some d) : Fixed X i d (raw a d) := by
  exact Or.inr ⟨r,by simp [build, addr, ha, hd],by simp [build, value, ha, hd]⟩

theorem build_pick {i : S k} (h : Active X i) : ∃ a, pick i = some a := by
  cases eq : pick i with
  | none => exact False.elim (h (by simp [build, head, eq]))
  | some a => exact ⟨a,rfl⟩

end Construction

/-- Every independent positive set and disjoint negative set of total size at most k
admits an outside witness. The graph parameter is an ordinary Mathlib SimpleGraph. -/
def Extension (k : ℕ) {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ A B : Finset V, Disjoint A B → A.card + B.card ≤ k →
    (∀ y ∈ A, ∀ z ∈ A, y ≠ z → ¬G.Adj y z) →
    ∃ x, x ∉ A ∧ x ∉ B ∧ (∀ y ∈ A, G.Adj x y) ∧ (∀ b ∈ B, ¬G.Adj x b)

theorem extension (k : ℕ) : Extension k (graph k) := by
  classical
  intro A B disj bound indep
  obtain ⟨c,hc⟩ := fresh_color A B bound
  obtain ⟨pick,hpick⟩ := cover A k (by rw [Fintype.card_coe]; omega)
  let raw (a : ↥A) : Raw k := a.val.val
  have rowCover (a : ↥A) := cover (↥(mask A B a.val)) (capacity k)
    (by rw [Fintype.card_coe]; exact mask_card a.property bound)
  choose rowPick hit using rowCover
  let rows (a : ↥A) (r : Row k) := (rowPick a r).map Subtype.val
  have hits (a : ↥A) (d : Key k) (hd : d ∈ mask A B a.val) :
      ∃ r, rows a r = some d := by
    obtain ⟨r,hr⟩ := hit a ⟨d,hd⟩
    exact ⟨r, by simp [rows,hr]⟩
  let x := build c raw pick rows
  have cache {i a} (ha : pick i = some a) : Cache x i (raw a) := build_cache ha
  have tests {i a} (ha : pick i = some a) : Tests x i (raw a) := build_tests ha
  have written {i a} (ha : pick i = some a) {d} (hd : d ∈ mask A B a.val) :
      Fixed x i d (raw a d) := by
    obtain ⟨r,hr⟩ := hits a d hd
    exact build_fixed ha hr
  have rootFixed {i a} (ha : pick i = some a) : Fixed x i root (raw a root) :=
    Or.inl ⟨nilW,rfl,cache ha nilW⟩
  have hx : Good x := by
    constructor
    · exact Option.some_ne_none _
    · intro i w
      cases eq : pick i with
      | none => simp [x,build,root,head,eq]
      | some a =>
        simpa [x,build,root,head,eq,raw] using hc a.val (Finset.mem_union_left _ a.property) w
    · intro i h
      obtain ⟨a,ha⟩ := build_pick h
      exact ⟨raw a,cache ha,tests ha⟩
    · intro i j hi hj t
      obtain ⟨a,ha⟩ := build_pick hi
      obtain ⟨b,hb⟩ := build_pick hj
      by_cases eq : a = b
      · subst b
        exact .colors (rootFixed ha) (rootFixed hb)
      have ne : a.val ≠ b.val := fun h => eq (Subtype.ext h)
      have ns : ¬Slot a.val.val t b.val.val :=
        fun h => indep a.val a.property b.val b.property ne (Or.inl ⟨t,h⟩)
      apply (packet_spec a.val.val b.val.val t ns).mono
      · rintro d v ⟨hd,rfl⟩
        exact written ha (mask_both b.property ne.symm t (Finset.mem_union_left _ hd))
      · rintro d v ⟨hd,rfl⟩
        exact written hb (mask_both a.property ne t (Finset.mem_union_right _ hd))
  let v : Vertex k := ⟨x,hx⟩
  have outside : v ∉ A ∪ B := fun h => hc v h nilW rfl
  refine ⟨v,fun h => outside (Finset.mem_union_left _ h),
    fun h => outside (Finset.mem_union_right _ h),?_,?_⟩
  · intro y hy
    let a : ↥A := ⟨y,hy⟩
    obtain ⟨i,hi⟩ := hpick a
    exact Or.inl ⟨i,hc y (Finset.mem_union_left _ hy) nilW,cache hi,tests hi⟩
  · intro b hb
    rintro (⟨i,hi⟩ | ⟨i,hi⟩)
    · obtain ⟨a,ha⟩ := build_pick (slot_active hi b.property.positive)
      have ne : a.val ≠ b := by
        rintro eq
        exact Finset.disjoint_left.mp disj (eq ▸ a.property) hb
      exact distinguish_spec ne (fixed_sound hi (written ha (mask_dist a.val hb))).symm
    · exact hc b (Finset.mem_union_right _ hb) (oneW i) (hi.2.1 nilW).symm

def TriangleFree {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ x y z, G.Adj x y → G.Adj y z → ¬G.Adj z x

/-- Uniform finite graph theorem, including the degenerate parameter zero. -/
theorem finite_ectf (k : ℕ) : ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    TriangleFree G ∧ Extension k G :=
  ⟨Vertex k,vertexFintype,graph k,triangle_free,extension k⟩

theorem finite_4ectf : ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    TriangleFree G ∧ Extension 4 G := finite_ectf 4

#print axioms finite_ectf
#print axioms finite_4ectf
end
end Problem29
