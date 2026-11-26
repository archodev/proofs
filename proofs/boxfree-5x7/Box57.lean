import Std

/-!
# The 5 × 7 box problem

Coordinates are zero-based. A two-coloring is a total function to Bool.
The explicit lower certificate is stored transposed, with one 52-bit word
per grid cell. Bit k records that cell in layer k.
-/
namespace Box57

abbrev Coloring (h : Nat) := Fin 5 → Fin 7 → Fin h → Bool

def Rectangle {h : Nat} (f : Coloring h) (r s : Fin 5) (c d : Fin 7)
    (k : Fin h) (b : Bool) : Prop :=
  f r c k = b ∧ f r d k = b ∧ f s c k = b ∧ f s d k = b

/-- Every choice of two distinct coordinates in each axis avoids both monochromatic colors. -/
def BoxFree {h : Nat} (f : Coloring h) : Prop :=
  ∀ (r s : Fin 5) (c d : Fin 7) (k l : Fin h) (b : Bool),
    r ≠ s → c ≠ d → k ≠ l →
      ¬ (Rectangle f r s c d k b ∧ Rectangle f r s c d l b)

private def cells : Array (BitVec 52) := #[
    0xe21f108cf6cd6, 0x2ed0dfb306316, 0xc1dcec40c84a8, 0x3d13237f3b7ab, 0x966959555aa69, 0x95a9a5aa6599a, 0x596656a999955,
    0x3473b310321a8, 0xc74c8cdfcedab, 0xb84f4023f9376, 0x8b707fec09c46, 0x65a6a5aa9566a, 0x699656555aa99, 0x569959a666655,
    0x81a06dcb67d3b, 0x49149b0eb9a75, 0xd67d62f826a15, 0xe7af94c291438, 0x1e027237691c7, 0x78fb1b31967c4, 0xac53a55ccc5aa,
    0x79d798f289a45, 0xbdaf6138641c8, 0x24a0973e9d7cb, 0x16416e0be6ad5, 0xd2fe4ec469d34, 0x4b08d8cd96437, 0xa35ca553335aa,
    0x9f286f37dd684, 0x90eb60c4116b7, 0x6f829fcd77924, 0x60be9031449e7, 0x695999aaa6999, 0x965666aaa9669, 0x5aa5aa55aaa5a]

private def word (r : Fin 5) (c : Fin 7) : BitVec 52 := cells[7 * r.val + c.val]'(by change _ < 35; omega)

def witness (r : Fin 5) (c : Fin 7) (k : Fin 52) : Bool :=
  (word r c).getLsbD k.val

private def coloredWord (r : Fin 5) (c : Fin 7) (b : Bool) : BitVec 52 :=
  if b then word r c else ~~~(word r c)

private def intersection (r s : Fin 5) (c d : Fin 7) (b : Bool) : BitVec 52 :=
  coloredWord r c b &&& coloredWord r d b &&&
    coloredWord s c b &&& coloredWord s d b

private theorem colored_bit (r : Fin 5) (c : Fin 7) (k : Fin 52) (b : Bool) :
    (coloredWord r c b).getLsbD k.val = true ↔ witness r c k = b := by
  cases b <;> simp [coloredWord, witness, BitVec.getLsbD_not, k.isLt]

private theorem intersection_bit (r s : Fin 5) (c d : Fin 7) (k : Fin 52) (b : Bool) :
    (intersection r s c d b).getLsbD k.val = true ↔ Rectangle witness r s c d k b := by
  simp only [intersection, BitVec.getLsbD_and, Bool.and_eq_true, colored_bit, Rectangle, and_assoc]

private def bitIndex : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, x => if x ≤ 1 then 0 else bitIndex fuel (x / 2) + 1

/- All colored intersections for distinct rows and columns are zero or powers of two. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem intersection_certificate :
    ∀ (r s : Fin 5) (c d : Fin 7) (b : Bool), r ≠ s → c ≠ d →
      let m := (intersection r s c d b).toNat
      m = 0 ∨ m = 2 ^ bitIndex 52 m := by decide +kernel

theorem witness_boxFree : BoxFree witness := by
  intro r s c d k l b hrs hcd hkl boxes
  let m := (intersection r s c d b).toNat
  have hk : m.testBit k.val = true := (intersection_bit r s c d k b).mpr boxes.1
  have hl : m.testBit l.val = true := (intersection_bit r s c d l b).mpr boxes.2
  have h : m = 0 ∨ m = 2 ^ (bitIndex 52 m) := intersection_certificate r s c d b hrs hcd
  rcases h with hz | hp
  · simp [hz] at hk
  · have bit_index (j : Fin 52) (hj : m.testBit j.val = true) : (bitIndex 52 m) = j.val := by
      have hj' : (2 ^ (bitIndex 52 m) : Nat).testBit j.val = true := hp ▸ hj
      simpa [Nat.testBit_two_pow] using hj'
    exact hkl (Fin.ext ((bit_index k hk).symm.trans (bit_index l hl)))

/-- Original hexadecimal layers. The first of the 35 row-major binary digits is the top-left cell. -/
private def layerMasks : Array Nat := #[
  0x0d47d2d2e, 0x6a79149a9, 0x6132da778, 0x1ecd25887,
  0x6327e0725, 0x1ce9a43ba, 0x453a9bc0b, 0x5ac41dcec,
  0x2be11da9c, 0x2c2ecac63, 0x585b2cbe2, 0x4755c261d,
  0x0b39b2af2, 0x6cc748595, 0x624b4dd5c, 0x1d7496a43,
  0x4daca89f0, 0x4aa3d1697, 0x566715658, 0x5168aed47,
  0x2d65185d9, 0x2a6bb2cc6, 0x4c5694b71, 0x4b59c5d16,
  0x2cc45f8c9, 0x2b3a5b84e, 0x1c55663b1, 0x635b62336,
  0x2e9b8d8d4, 0x2994d8e53, 0x335d24ed2, 0x34538a755,
  0x6596ba91c, 0x1a99554e3, 0x353751762, 0x32c8a699d,
  0x4ea26f425, 0x49ac3f23a, 0x516ce328b, 0x5662693ec,
  0x7896ce28e, 0x079969a69, 0x35f04e6a6, 0x320f2ba39,
  0x1b5da31d4, 0x6452707d3, 0x2eca75c52, 0x29349f155,
  0x0fa25b663, 0x68ac2f89c, 0x514eea31d, 0x5671652e2]

def maskColoring (r : Fin 5) (c : Fin 7) (k : Fin 52) : Bool :=
  (layerMasks[k.val]'k.isLt).testBit (34 - (7 * r.val + c.val))

/-- Check that the transposed certificate and the original masks agree at all 1,820 cells. -/
theorem same_cells : ∀ (r : Fin 5) (c : Fin 7) (k : Fin 52),
    maskColoring r c k = witness r c k := by decide +kernel

theorem masks_boxFree : BoxFree maskColoring := by
  have eq : maskColoring = witness := funext fun r => funext fun c => funext (same_cells r c)
  exact eq ▸ witness_boxFree

/- The upper bound uses finite sums, first within a layer and then over layers. -/

private def total (xs : List α) (f : α → Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => f x + total rest f

private theorem total_le (xs : List α) {f g : α → Nat}
    (h : ∀ x ∈ xs, f x ≤ g x) : total xs f ≤ total xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

private theorem total_const (xs : List α) (c : Nat) :
    total xs (fun _ => c) = xs.length * c := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Nat.succ_mul, Nat.add_comm]

private theorem total_add (xs : List α) (f g : α → Nat) :
    total xs (fun i => f i + g i) = total xs f + total xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [total, ih]; omega

private theorem total_swap (xs : List α) (ys : List β) (f : α → β → Nat) :
    total xs (fun x => total ys (f x)) = total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [total, total_const]
  | cons x xs ih =>
    simp only [total, total_add, ih]

/-- A pair of distinct coordinates listed in increasing order. -/
private structure CoordPair (n : Nat) where
  lo : Fin n
  hi : Fin n
  ordered : lo < hi

private def rows : List (CoordPair 5) := [
  ⟨0, 1, by decide⟩, ⟨0, 2, by decide⟩, ⟨0, 3, by decide⟩,
  ⟨0, 4, by decide⟩, ⟨1, 2, by decide⟩, ⟨1, 3, by decide⟩,
  ⟨1, 4, by decide⟩, ⟨2, 3, by decide⟩, ⟨2, 4, by decide⟩,
  ⟨3, 4, by decide⟩]

private def cols : List (CoordPair 7) := [
  ⟨0, 1, by decide⟩, ⟨0, 2, by decide⟩, ⟨0, 3, by decide⟩,
  ⟨0, 4, by decide⟩, ⟨0, 5, by decide⟩, ⟨0, 6, by decide⟩,
  ⟨1, 2, by decide⟩, ⟨1, 3, by decide⟩, ⟨1, 4, by decide⟩,
  ⟨1, 5, by decide⟩, ⟨1, 6, by decide⟩, ⟨2, 3, by decide⟩,
  ⟨2, 4, by decide⟩, ⟨2, 5, by decide⟩, ⟨2, 6, by decide⟩,
  ⟨3, 4, by decide⟩, ⟨3, 5, by decide⟩, ⟨3, 6, by decide⟩,
  ⟨4, 5, by decide⟩, ⟨4, 6, by decide⟩, ⟨5, 6, by decide⟩]

private abbrev RowColor := CoordPair 5 × Bool
private def rowColors : List RowColor := rows.flatMap fun p => [(p, false), (p, true)]
private def columns : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

private def agrees (v : Fin 5 → Bool) (q : RowColor) : Bool :=
  (v q.1.lo == q.2) && (v q.1.hi == q.2)

private def singleCount (v : Fin 7 → Bool) := total columns (fun c => (v c).toNat)
private def pairCount (v : Fin 7 → Bool) :=
  total cols (fun p => (v p.lo && v p.hi).toNat)

/-- Every binary column of height five contains at least four same-color row pairs. -/
private theorem column_bound (v : Fin 5 → Bool) :
    4 ≤ total rowColors (fun q => (agrees v q).toNat) := by
  have cert : ∀ a b c d e : Bool,
      4 ≤ total rowColors (fun q => (agrees (fun i => #[a,b,c,d,e][i.val]'i.isLt) q).toNat) := by
    decide +kernel
  exact cert (v 0) (v 1) (v 2) (v 3) (v 4)

/-- Among seven flags, the number set is at most one plus the number of set pairs. -/
private theorem column_pair_bound (v : Fin 7 → Bool) : singleCount v ≤ 1 + pairCount v := by
  have cert : ∀ a b c d e f g : Bool,
      let flags := fun i : Fin 7 => #[a,b,c,d,e,f,g][i.val]'i.isLt
      singleCount flags ≤ 1 + pairCount flags := by decide +kernel
  exact cert (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)

private def mark {h : Nat} (f : Coloring h) (k : Fin h) (q : RowColor) (c : Fin 7) : Bool :=
  agrees (fun r => f r c k) q

private def hit {h : Nat} (f : Coloring h) (k : Fin h) (q : RowColor) (p : CoordPair 7) : Bool :=
  mark f k q p.lo && mark f k q p.hi

private def layerCount {h : Nat} (f : Coloring h) (k : Fin h) :=
  total rowColors (fun q => total cols (fun p => (hit f k q p).toNat))

private theorem hit_iff {h : Nat} (f : Coloring h) (k : Fin h) (q : RowColor) (p : CoordPair 7) :
    hit f k q p = true ↔ Rectangle f q.1.lo q.1.hi p.lo p.hi k q.2 := by
  simp [hit, mark, agrees, Rectangle, and_assoc, and_comm, and_left_comm]

private theorem layer_lower {h : Nat} (f : Coloring h) (k : Fin h) : 8 ≤ layerCount f k := by
  have hc : 28 ≤ total columns (fun c => total rowColors (fun q => (mark f k q c).toNat)) :=
    total_le columns (f := fun _ => 4) (fun c _ => column_bound (fun r => f r c k))
  rw [total_swap] at hc
  have hp := total_le rowColors (fun q _ => column_pair_bound (mark f k q))
  change total rowColors (fun q => total columns (fun c => (mark f k q c).toNat)) ≤
    total rowColors (fun q => 1 + total cols (fun p => (hit f k q p).toNat)) at hp
  rw [total_add, total_const] at hp
  have hn : rowColors.length = 20 := by decide
  rw [hn] at hp
  unfold layerCount
  omega

private theorem distinctLayers (h : Nat) : (List.finRange h).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij heq
  have eqv := congrArg Fin.val heq
  simp only [List.getElem_finRange] at eqv
  change i = j at eqv
  omega

private theorem atMostOne (xs : List α) (hn : xs.Nodup) (p : α → Bool)
    (unique : ∀ x y, p x = true → p y = true → x = y) :
    total xs (fun x => (p x).toNat) ≤ 1 := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := List.nodup_cons.mp hn
    cases hpa : p a with
    | false => simpa [total, hpa] using ih hxs
    | true =>
      have rest := total_le xs (f := fun x => (p x).toNat) (g := fun _ => 0) (by
        intro x hx
        cases hpx : p x with
        | false => simp [hpx]
        | true => exact False.elim (ha ((unique a x hpa hpx).symm ▸ hx)))
      simp only [total_const, Nat.mul_zero] at rest
      simp [total, hpa, Nat.eq_zero_of_le_zero rest]

private theorem slot_upper {h : Nat} {f : Coloring h} (hf : BoxFree f)
    (q : RowColor) (p : CoordPair 7) :
    total (List.finRange h) (fun k => (hit f k q p).toNat) ≤ 1 := by
  apply atMostOne _ (distinctLayers h)
  intro k l hk hl
  by_cases hkl : k = l
  · exact hkl
  · exact False.elim (hf q.1.lo q.1.hi p.lo p.hi k l q.2
      (Fin.ne_of_lt q.1.ordered) (Fin.ne_of_lt p.ordered) hkl
      ⟨(hit_iff f k q p).mp hk, (hit_iff f l q p).mp hl⟩)

/-- Double counting all layer/colored-rectangle incidences bounds every height. -/
theorem height_le {h : Nat} {f : Coloring h} (hf : BoxFree f) : h ≤ 52 := by
  let ks := List.finRange h
  have hlo : h * 8 ≤ total ks (fun k => layerCount f k) := by
    have eq : total ks (fun _ => 8) = h * 8 := by simp [ks, total_const]
    rw [← eq]
    exact total_le ks (fun k _ => layer_lower f k)
  have hhi : total ks (fun k => layerCount f k) ≤ 420 := by
    unfold layerCount
    rw [total_swap]
    have bound (q : RowColor) :
        total ks (fun k => total cols (fun p => (hit f k q p).toNat)) ≤ 21 := by
      rw [total_swap]
      exact total_le cols (g := fun _ => 1) (fun p _ => slot_upper hf q p)
    exact total_le rowColors (g := fun _ => 21) (fun q _ => bound q)
  omega

theorem no_coloring_above {h : Nat} (hh : 52 < h) : ¬ ∃ f : Coloring h, BoxFree f := by
  rintro ⟨f, hf⟩
  have := height_le hf
  omega

/-- Restrict the coloring to the first n layers. -/
def restrict {n m : Nat} (hnm : n ≤ m) (f : Coloring m) : Coloring n :=
  fun r c k => f r c (Fin.castLE hnm k)

theorem restrict_boxFree {n m : Nat} (hnm : n ≤ m) {f : Coloring m} (hf : BoxFree f) :
    BoxFree (restrict hnm f) := by
  intro r s c d k l b hrs hcd hkl box
  exact hf r s c d (Fin.castLE hnm k) (Fin.castLE hnm l) b hrs hcd
    (fun eq => hkl (Fin.ext (congrArg (fun j : Fin m => j.val) eq))) box

theorem colorable_iff (h : Nat) : (∃ f : Coloring h, BoxFree f) ↔ h ≤ 52 := by
  constructor
  · rintro ⟨f, hf⟩
    exact height_le hf
  · intro hh
    exact ⟨restrict hh maskColoring, restrict_boxFree hh masks_boxFree⟩

theorem exact_52 :
    (∃ f : Coloring 52, BoxFree f) ∧
    (∀ h : Nat, 52 < h → ¬ ∃ f : Coloring h, BoxFree f) :=
  ⟨⟨maskColoring, masks_boxFree⟩, fun _ hh => no_coloring_above hh⟩

#print axioms witness_boxFree
#print axioms same_cells
#print axioms masks_boxFree
#print axioms height_le
#print axioms no_coloring_above
#print axioms restrict_boxFree
#print axioms colorable_iff
#print axioms exact_52

end Box57
