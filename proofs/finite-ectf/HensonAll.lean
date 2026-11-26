import Problem29
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! Finite clique-free extension graphs for every forbidden clique size.
Reuses the finite record construction in Problem29; only the condition on
which active slots may be simultaneously adjacent is strengthened by a
parameter. The conclusion is combinatorial, not a model-theory encoding. -/

namespace HensonAll
open Finset Problem29
noncomputable section
variable {k r : ℕ}

def PairOn {α : Type*} (R : α → α → Prop) (C : Finset α) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, a ≠ b → R a b

def NoClique {α : Type*} (s : ℕ) (R : α → α → Prop) : Prop :=
  ∀ C : Finset α, C.card = s → PairOn R C → False

def slotAdj (x : Raw k) (i j : S k) : Prop :=
  i ≠ j ∧ ¬ (∀ t, Block (Fixed x i) (Fixed x j) t ∧ Block (Fixed x j) (Fixed x i) t)

structure GGood (r : ℕ) (x : Raw k) : Prop where
  positive : x root ≠ none
  fresh : ∀ i w, x root ≠ x (head i w)
  consistent : ∀ i, Active x i → ∃ y, Cache x i y ∧ Tests x i y
  slots : ∀ C : Finset (S k), C.card = r - 1 →
    (∀ i ∈ C, Active x i) → PairOn (slotAdj x) C → False

abbrev GVertex (k r : ℕ) := {x : Raw k // GGood r x}
noncomputable instance gDecEq : DecidableEq (GVertex k r) := Classical.decEq _
noncomputable instance gFintype : Fintype (GVertex k r) := Fintype.ofFinite _

def cliqueGraph (k r : ℕ) : SimpleGraph (GVertex k r) where
  Adj x y := Arc x.val y.val ∨ Arc y.val x.val
  symm _ _ := Or.symm
  loopless x h := by
    rcases h with ⟨i,ne,_,_⟩ | ⟨i,ne,_,_⟩ <;> exact ne rfl

private theorem freshNoCycle {x y z : GVertex k r}
    (a : Arc x.val y.val) (b : Arc y.val z.val) : ¬ Arc z.val x.val := by
  obtain ⟨i,hi⟩ := a
  obtain ⟨j,hj⟩ := b
  rintro ⟨t,ht⟩
  apply x.property.fresh i (twoW j t)
  exact ((hi.2.1 (twoW j t)).trans ((hj.2.1 (oneW t)).trans (ht.2.1 nilW))).symm

private theorem dominates {α : Type*} [DecidableEq α] (R : α → α → Prop)
    (hc : ∀ x y z, R x y → R y z → ¬ R z x) (C : Finset α) :
    C.Nonempty → PairOn (fun x y => R x y ∨ R y x) C →
      ∃ x ∈ C, ∀ y ∈ C, y ≠ x → R x y := by
  classical
  induction C using Finset.induction_on with
  | empty =>
    intro hn
    exact (Finset.not_nonempty_empty hn).elim
  | @insert a C ha ih =>
    intro _ hpair
    by_cases hC : C.Nonempty
    · obtain ⟨b,hb,hdom⟩ := ih hC
        (fun x hx y hy ne => hpair x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) ne)
      have nab : a ≠ b := fun e => ha (e.symm ▸ hb)
      by_cases hab : R a b
      · refine ⟨a, mem_insert_self _ _, ?_⟩
        intro y hy hya
        have hy' := (mem_insert.mp hy).resolve_left hya
        by_cases hyb : y = b
        · simpa [hyb] using hab
        · exact (hpair a (mem_insert_self _ _) y hy hya.symm).resolve_right
            (hc _ _ _ hab (hdom y hy' hyb))
      · refine ⟨b, mem_insert_of_mem hb, ?_⟩
        intro y hy hyb
        rcases mem_insert.mp hy with h | h
        · subst y
          exact (hpair a (mem_insert_self _ _) b (mem_insert_of_mem hb) nab).resolve_left hab
        · exact hdom y h hyb
    · refine ⟨a, mem_insert_self _ _, ?_⟩
      intro y hy hya
      exact (hC ⟨y,(mem_insert.mp hy).resolve_left hya⟩).elim

theorem noForbiddenClique (k r : ℕ) (hr : 3 ≤ r) :
    NoClique r (cliqueGraph k r).Adj := by
  classical
  intro C hC hcl
  have hn : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x,hx,hd⟩ := dominates (fun a b : GVertex k r => Arc a.val b.val)
    (fun _ _ _ => freshNoCycle) C hn hcl
  have hs (v : ↥(C.erase x)) : ∃ i, Slot x.val i v.val.val :=
    hd v.val (mem_of_mem_erase v.property) (ne_of_mem_erase v.property)
  choose pick hp using hs
  have inj : Function.Injective pick := by
    intro a b eq
    by_contra ne
    have nab : a.val ≠ b.val := fun e => ne (Subtype.ext e)
    have roots : a.val.val root = b.val.val root := by
      calc
        a.val.val root = x.val (head (pick a) nilW) := (hp a).2.1 nilW |>.symm
        _ = x.val (head (pick b) nilW) := by rw [eq]
        _ = b.val.val root := (hp b).2.1 nilW
    rcases hcl a.val (mem_of_mem_erase a.property) b.val (mem_of_mem_erase b.property) nab with ⟨t,ht⟩ | ⟨t,ht⟩
    · exact ht.1 roots
    · exact ht.1 roots.symm
  let D : Finset (S k) := univ.image pick
  have hdCard : D.card = r - 1 := by
    dsimp [D]
    rw [Finset.card_image_of_injective _ inj, Finset.card_attach,
      Finset.card_erase_of_mem hx, hC]
  refine x.property.slots D hdCard ?_ ?_
  · intro i hi
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
    exact slot_active (hp a) a.val.property.positive
  · intro i hi j hj ne
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hj
    refine ⟨ne, ?_⟩
    intro blocks
    have nab : a.val ≠ b.val := fun e => ne (congrArg pick (Subtype.ext e))
    rcases hcl a.val (mem_of_mem_erase a.property) b.val (mem_of_mem_erase b.property) nab with ⟨t,ht⟩ | ⟨t,ht⟩
    · exact (blocks t).1.sound (fun _ _ => fixed_sound (hp a)) (fun _ _ => fixed_sound (hp b)) ht
    · exact (blocks t).2.sound (fun _ _ => fixed_sound (hp b)) (fun _ _ => fixed_sound (hp a)) ht

def distinguishG (y b : GVertex k r) : Key k := by
  classical
  exact if h : ∃ d, y.val d ≠ b.val d then h.choose else root

theorem distinguishGSpec {y b : GVertex k r} (ne : y ≠ b) :
    y.val (distinguishG y b) ≠ b.val (distinguishG y b) := by
  classical
  have h : ∃ d, y.val d ≠ b.val d := by
    by_contra! eq
    exact ne (Subtype.ext (funext eq))
  simpa only [distinguishG, dif_pos h] using h.choose_spec

def bothG (y z : GVertex k r) (t : S k) : Finset (Key k) :=
  (packet y.val z.val t).left ∪ (packet z.val y.val t).right

def maskG (A B : Finset (GVertex k r)) (y : GVertex k r) : Finset (Key k) := by
  classical
  exact ((A.erase y).biUnion (fun z => univ.biUnion (bothG y z))) ∪ B.image (distinguishG y)

theorem maskGBoth {A B : Finset (GVertex k r)} {y z : GVertex k r}
    (hz : z ∈ A) (ne : z ≠ y) (t : S k) {d : Key k} (hd : d ∈ bothG y z t) :
    d ∈ maskG A B y := by
  classical
  apply Finset.mem_union_left
  exact Finset.mem_biUnion.mpr ⟨z,Finset.mem_erase.mpr ⟨ne,hz⟩,
    Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,hd⟩⟩

theorem maskGDist {A B : Finset (GVertex k r)} (y : GVertex k r) {b} (hb : b ∈ B) :
    distinguishG y b ∈ maskG A B y := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)

theorem maskGCard {A B : Finset (GVertex k r)} {y : GVertex k r} (hy : y ∈ A)
    (hk : A.card + B.card ≤ k) : (maskG A B y).card ≤ capacity k := by
  classical
  have pairBound (z : GVertex k r) (t : S k) : (bothG y z t).card ≤ 3 :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (packet y.val z.val t).left_le
      (packet z.val y.val t).right_le)
  have slotBound (z : GVertex k r) : (univ.biUnion (bothG y z)).card ≤ k*3 := by
    simpa using Finset.card_biUnion_le_card_mul (univ : Finset (S k)) (bothG y z) 3
      (fun t _ => pairBound z t)
  have sumBound := Finset.card_biUnion_le_card_mul (A.erase y)
    (fun z => univ.biUnion (bothG y z)) (k*3) (fun z _ => slotBound z)
  rw [Finset.card_erase_of_mem hy] at sumBound
  have ha : A.card - 1 ≤ k - 1 := by omega
  have hb : B.card ≤ k := by omega
  calc
    (maskG A B y).card ≤ _ := Finset.card_union_le _ _
    _ ≤ (A.card-1)*(k*3) + B.card := Nat.add_le_add sumBound Finset.card_image_le
    _ ≤ (k-1)*(k*3) + k := Nat.add_le_add (Nat.mul_le_mul_right _ ha) hb
    _ = capacity k := by simp [capacity, Nat.mul_comm, Nat.mul_left_comm]

-- A finite set of at most n items can be stored in n optional slots.
private theorem coverG (α : Type) [Fintype α] (n : ℕ) (h : Fintype.card α ≤ n) :
    ∃ f : Fin n → Option α, ∀ a, ∃ i, f i = some a := by
  classical
  let e := Fintype.equivFin α
  let f (i : Fin n) := if hi : i.val < Fintype.card α then some (e.symm ⟨i.val,hi⟩) else none
  refine ⟨f, fun a => ⟨⟨(e a).val,lt_of_lt_of_le (e a).isLt h⟩,?_⟩⟩
  simp [f,(e a).isLt]

private theorem freshColorG (A B : Finset (GVertex k r)) (hk : A.card+B.card ≤ k) :
    ∃ c : Key k, ∀ y ∈ A ∪ B, ∀ w : Short k, some c ≠ y.val (top w) := by
  classical
  let f (y : GVertex k r) := (univ : Finset (Short k)).image (fun w => y.val (top w))
  let bad := (A ∪ B).biUnion f
  have hf (y : GVertex k r) : (f y).card ≤ 1+k+k*k := by
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


/-- Positive requests need only omit a clique of size r-1. -/
def CliqueExtension (r k : ℕ) {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ A B : Finset V, Disjoint A B → A.card + B.card ≤ k →
    (∀ C : Finset V, C ⊆ A → C.card = r - 1 → PairOn G.Adj C → False) →
    ∃ x, x ∉ A ∧ x ∉ B ∧ (∀ y ∈ A, G.Adj x y) ∧ (∀ b ∈ B, ¬G.Adj x b)

theorem extensionG (k r : ℕ) : CliqueExtension r k (cliqueGraph k r) := by
  classical
  intro A B disj bound indep
  obtain ⟨c,hc⟩ := freshColorG A B bound
  obtain ⟨pick,hpick⟩ := coverG A k (by rw [Fintype.card_coe]; omega)
  let raw (a : ↥A) : Raw k := a.val.val
  have rowCover (a : ↥A) := coverG (↥(maskG A B a.val)) (capacity k)
    (by rw [Fintype.card_coe]; exact maskGCard a.property bound)
  choose rowPick hit using rowCover
  let rows (a : ↥A) (r : Row k) := (rowPick a r).map Subtype.val
  have hits (a : ↥A) (d : Key k) (hd : d ∈ maskG A B a.val) :
      ∃ r, rows a r = some d := by
    obtain ⟨r,hr⟩ := hit a ⟨d,hd⟩
    exact ⟨r, by simp [rows,hr]⟩
  let x := build c raw pick rows
  have cache {i a} (ha : pick i = some a) : Cache x i (raw a) := build_cache ha
  have tests {i a} (ha : pick i = some a) : Tests x i (raw a) := build_tests ha
  have written {i a} (ha : pick i = some a) {d} (hd : d ∈ maskG A B a.val) :
      Fixed x i d (raw a d) := by
    obtain ⟨r,hr⟩ := hits a d hd
    exact build_fixed ha hr
  have rootFixed {i a} (ha : pick i = some a) : Fixed x i root (raw a root) :=
    Or.inl ⟨nilW,rfl,cache ha nilW⟩
  have hx : GGood r x := by
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
    · intro C hC active hpair
      let chooseTarget (i : ↥C) : ↥A := (build_pick (active i.val i.property)).choose
      have findTarget (i : ↥C) : pick i.val = some (chooseTarget i) :=
        (build_pick (active i.val i.property)).choose_spec
      let target (i : ↥C) : GVertex k r := (chooseTarget i).val
      have reflect (i j : ↥C) (ne : i ≠ j) : (cliqueGraph k r).Adj (target i) (target j) := by
        have neij : i.val ≠ j.val := fun e => ne (Subtype.ext e)
        by_contra hn
        apply (hpair i.val i.property j.val j.property neij).2
        intro t
        have hblock (u v : ↥C) (h : ¬ (cliqueGraph k r).Adj (target u) (target v)) :
            Block (Fixed x u.val) (Fixed x v.val) t := by
          by_cases eq : chooseTarget u = chooseTarget v
          · exact .colors (rootFixed (findTarget u)) (eq.symm ▸ rootFixed (findTarget v))
          have neq : target u ≠ target v := fun e => eq (Subtype.ext e)
          have ns : ¬ Slot (target u).val t (target v).val :=
            fun hslot => h (Or.inl ⟨t,hslot⟩)
          apply (packet_spec (target u).val (target v).val t ns).mono
          · rintro d val ⟨hd,rfl⟩
            exact written (findTarget u)
              (maskGBoth (chooseTarget v).property neq.symm t (Finset.mem_union_left _ hd))
          · rintro d val ⟨hd,rfl⟩
            exact written (findTarget v)
              (maskGBoth (chooseTarget u).property neq t (Finset.mem_union_right _ hd))
        exact ⟨hblock i j hn, hblock j i (fun h => hn ((cliqueGraph k r).symm h))⟩
      have inj : Function.Injective target := by
        intro i j eq
        by_contra ne
        have h := reflect i j ne
        rw [eq] at h
        exact (cliqueGraph k r).loopless _ h
      let T : Finset (GVertex k r) := univ.image target
      have hT : T.card = r - 1 := by
        dsimp [T]
        rw [Finset.card_image_of_injective _ inj, Finset.card_attach, hC]
      refine indep T ?_ hT ?_
      · intro a ha
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
        exact (chooseTarget i).property
      · intro a ha b hb ne
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
        exact reflect i j (fun e => ne (congrArg target e))
  let v : GVertex k r := ⟨x,hx⟩
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
      exact distinguishGSpec ne (fixed_sound hi (written ha (maskGDist a.val hb))).symm
    · exact hc b (Finset.mem_union_right _ hb) (oneW i) (hi.2.1 nilW).symm


set_option synthInstance.maxSize 2000 in
/-- The raw-record bound is unchanged for every forbidden clique size. -/
theorem bound (k r : ℕ) :
    Fintype.card (GVertex k r) ≤ (fieldCount k + 1) ^ fieldCount k := by
  classical
  have h := Fintype.card_subtype_le (GGood (k := k) r)
  change Fintype.card (GVertex k r) ≤ Fintype.card (Key k → Option (Key k)) at h
  simpa only [Fintype.card_fun, Fintype.card_option, key_card, fieldCount] using h

theorem finite_clique_extension (r k : ℕ) (hr : 3 ≤ r) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      NoClique r G.Adj ∧ CliqueExtension r k G :=
  ⟨GVertex k r, gFintype, cliqueGraph k r, noForbiddenClique k r hr, extensionG k r⟩

/-- Standard Mathlib statement of the generalized finite graph theorem. -/
theorem finiteCliqueExtension (r k : ℕ) (hr : 3 ≤ r) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), G.CliqueFree r ∧
      ∀ A B : Finset V, Disjoint A B → A.card + B.card ≤ k →
        G.CliqueFreeOn (A : Set V) (r - 1) →
        ∃ x, x ∉ A ∧ x ∉ B ∧ (∀ y ∈ A, G.Adj x y) ∧ (∀ b ∈ B, ¬ G.Adj x b) := by
  obtain ⟨V, f, G, hc, he⟩ := finite_clique_extension r k hr
  refine ⟨V, f, G, ?_, ?_⟩
  · intro C hC
    exact hc C hC.card_eq hC.isClique
  · intro A B hd hk hA
    exact he A B hd hk (fun C hC hs hcl => hA (Finset.coe_subset.mpr hC) ⟨hcl, hs⟩)

#print axioms finiteCliqueExtension
#print axioms finite_clique_extension
#print axioms bound
end
end HensonAll
