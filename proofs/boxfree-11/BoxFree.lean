import Init

/-!
# The minimum number of monochromatic boxes in the 11-cube

Alm and Miller, arXiv:2611.19635v1, §8 Problem 1, conjectured eight.
The witness below specializes Menezes, arXiv:2609.22381v2, Construction 3.1,
to q = 2. For labels (w,e), (y,f), (z,g) in F₈ × F₂ the color is
e + f + g + Tr((w + y⁴)(y + z)³). Toggling e interchanges edges and
nonedges. Thus the prior one-class construction gives the two-color
consequence. The formal proof checks the finite table directly.
-/

namespace BoxFree

abbrev Coloring (n : Nat) := Fin n × Fin n × Fin n → Bool

/-- All four corners at height z have the specified color. -/
def Face {n : Nat} (C : Coloring n) (x X y Y z : Fin n) (b : Bool) : Prop :=
  C (x,y,z) = b ∧ C (x,Y,z) = b ∧ C (X,y,z) = b ∧ C (X,Y,z) = b

/-- A single color occurs at all eight corners. -/
def Monochromatic {n : Nat} (C : Coloring n) (x X y Y z Z : Fin n) : Prop :=
  ∃ b : Bool, Face C x X y Y z b ∧ Face C x X y Y Z b

instance {n : Nat} (C : Coloring n) (x X y Y z Z : Fin n) :
    Decidable (Monochromatic C x X y Y z Z) := by
  unfold Monochromatic Face
  infer_instance

/-- Bit z of entry (x,y) is the color of (x,y,z). In each axis, index i
encodes the pair (i / 2, i % 2) in F₈ × F₂. The polynomial is T³ + T + 1. -/
private def rows : Array (Array Nat) := #[
  #[0xaaaa, 0x5555, 0x6669, 0x9996, 0x96a5, 0x695a, 0xa599, 0x5a66, 0x6a95, 0x956a, 0x59a9, 0xa656, 0xa965, 0x569a, 0x9a59, 0x65a6],
  #[0x5555, 0xaaaa, 0x9996, 0x6669, 0x695a, 0x96a5, 0x5a66, 0xa599, 0x956a, 0x6a95, 0xa656, 0x59a9, 0x569a, 0xa965, 0x65a6, 0x9a59],
  #[0x9996, 0x6669, 0xaaaa, 0x5555, 0xa566, 0x5a99, 0x69a5, 0x965a, 0x56a6, 0xa959, 0x9a65, 0x659a, 0x6a56, 0x95a9, 0xa695, 0x596a],
  #[0x6669, 0x9996, 0x5555, 0xaaaa, 0x5a99, 0xa566, 0x965a, 0x69a5, 0xa959, 0x56a6, 0x659a, 0x9a65, 0x95a9, 0x6a56, 0x596a, 0xa695],
  #[0x956a, 0x6a95, 0xa959, 0x56a6, 0x65a9, 0x9a56, 0x599a, 0xa665, 0xaaaa, 0x5555, 0x6966, 0x9699, 0xa596, 0x5a69, 0x99a5, 0x665a],
  #[0x6a95, 0x956a, 0x56a6, 0xa959, 0x9a56, 0x65a9, 0xa665, 0x599a, 0x5555, 0xaaaa, 0x9699, 0x6966, 0x5a69, 0xa596, 0x665a, 0x99a5],
  #[0xa656, 0x59a9, 0x659a, 0x9a65, 0x566a, 0xa995, 0x95a6, 0x6a59, 0x9699, 0x6966, 0xaaaa, 0x5555, 0x66a5, 0x995a, 0xa569, 0x5a96],
  #[0x59a9, 0xa656, 0x9a65, 0x659a, 0xa995, 0x566a, 0x6a59, 0x95a6, 0x6966, 0x9699, 0x5555, 0xaaaa, 0x995a, 0x66a5, 0x5a96, 0xa569],
  #[0x569a, 0xa965, 0x95a9, 0x6a56, 0x59a6, 0xa659, 0x9a95, 0x656a, 0x5a69, 0xa596, 0x995a, 0x66a5, 0xaaaa, 0x5555, 0x9666, 0x6999],
  #[0xa965, 0x569a, 0x6a56, 0x95a9, 0xa659, 0x59a6, 0x656a, 0x9a95, 0xa596, 0x5a69, 0x66a5, 0x995a, 0x5555, 0xaaaa, 0x6999, 0x9666],
  #[0x65a6, 0x9a59, 0x596a, 0xa695, 0x6a65, 0x959a, 0x56a9, 0xa956, 0x665a, 0x99a5, 0x5a96, 0xa569, 0x6999, 0x9666, 0xaaaa, 0x5555],
  #[0x9a59, 0x65a6, 0xa695, 0x596a, 0x959a, 0x6a65, 0xa956, 0x56a9, 0x99a5, 0x665a, 0xa569, 0x5a96, 0x9666, 0x6999, 0x5555, 0xaaaa],
  #[0x695a, 0x96a5, 0x5a99, 0xa566, 0xaaaa, 0x5555, 0x6696, 0x9969, 0x9a56, 0x65a9, 0xa995, 0x566a, 0xa659, 0x59a6, 0x959a, 0x6a65],
  #[0x96a5, 0x695a, 0xa566, 0x5a99, 0x5555, 0xaaaa, 0x9969, 0x6696, 0x65a9, 0x9a56, 0x566a, 0xa995, 0x59a6, 0xa659, 0x6a65, 0x959a],
  #[0x5a66, 0xa599, 0x965a, 0x69a5, 0x9969, 0x6696, 0xaaaa, 0x5555, 0xa665, 0x599a, 0x6a59, 0x95a6, 0x656a, 0x9a95, 0xa956, 0x56a9],
  #[0xa599, 0x5a66, 0x69a5, 0x965a, 0x6696, 0x9969, 0x5555, 0xaaaa, 0x599a, 0xa665, 0x95a6, 0x6a59, 0x9a95, 0x656a, 0x56a9, 0xa956]]

private def row (x y : Fin 16) : Nat := (rows.getD x.val #[]).getD y.val 0

def color16 : Coloring 16 := fun (x,y,z) => (row x y).testBit z.val

/-- In the packed cube the coordinate strides are 1024, 32 and 1. The
padding keeps a legal displacement of at most 15 from carrying into the
next coordinate. Each bit represents one possible lower corner. -/
private def pos (x y z : Fin 16) : Nat := 1024*x.val + 32*y.val + z.val

private def pack (stride : Nat) (entries : List Nat) : Nat :=
  entries.foldr (fun entry rest => entry ||| (rest <<< stride)) 0

private def packColor (b : Bool) : Nat :=
  pack 1024 (rows.toList.map fun layer =>
    pack 32 (layer.toList.map fun r => if b then r else 0xffff ^^^ r))

private def bitmap (b : Bool) : Nat := if b then packColor true else packColor false

private def allFin {n : Nat} (p : Fin n → Bool) : Bool := (List.finRange n).all p

private theorem specialize_all {p : Fin n → Bool} (h : allFin p = true)
    (i : Fin n) : p i = true :=
  List.all_eq_true.mp h i ((List.mem_ofFn).mpr ⟨i, rfl⟩)

-- Every point lies in the bitmap selected by its actual table color.
set_option maxHeartbeats 5000000 in
private theorem covered :
    (allFin fun (x : Fin 16) => allFin fun y => allFin fun z =>
      (bitmap (color16 (x,y,z))).testBit (pos x y z)) = true := by decide +kernel

private theorem point_bit (x y z : Fin 16) {b : Bool} (h : color16 (x,y,z) = b) :
    (bitmap b).testBit (pos x y z) = true := by
  subst b
  exact specialize_all (specialize_all (specialize_all covered x) y) z

/-- Intersect a set of positions with its translate by -d. -/
private def step (s d : Nat) : Nat := s &&& (s >>> d)

private theorem step_bit {s p d : Nat} (hp : s.testBit p = true)
    (hq : s.testBit (p+d) = true) : (step s d).testBit p = true := by
  simp [step, hp, Nat.add_comm d p, hq]

private def boxMask (b : Bool) (dx dy dz : Fin 15) : Nat :=
  step (step (step (bitmap b) (1024*(dx.val+1))) (32*(dy.val+1))) (dz.val+1)

-- Each positive displacement triple is checked for both colors. The
-- bitwise operations simultaneously examine all possible lower corners.
set_option maxHeartbeats 5000000 in
private theorem certificate :
    (allFin fun dx => allFin fun dy => allFin fun dz =>
      (boxMask false dx dy dz == 0) && (boxMask true dx dy dz == 0)) = true := by
  decide +kernel

private theorem empty_mask (b : Bool) (dx dy dz : Fin 15) : boxMask b dx dy dz = 0 := by
  have h := specialize_all (specialize_all (specialize_all certificate dx) dy) dz
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  cases b
  · exact h.1
  · exact h.2

private theorem endpoints {a b : Fin 16} (h : a ≠ b) :
    ∃ lo hi : Fin 16, ∃ d : Fin 15, hi.val = lo.val + (d.val+1) ∧
      (lo = a ∨ lo = b) ∧ (hi = a ∨ hi = b) := by
  have distance (i j : Fin 16) (hlt : i < j) :
      ∃ d : Fin 15, j.val = i.val + (d.val+1) := by
    have hlt' : i.val < j.val := hlt
    refine ⟨⟨j.val - i.val - 1, by omega⟩, ?_⟩
    dsimp
    omega
  rcases Fin.lt_or_lt_of_ne h with hab | hba
  · obtain ⟨d, hd⟩ := distance a b hab
    exact ⟨a,b,d,hd,Or.inl rfl,Or.inr rfl⟩
  · obtain ⟨d, hd⟩ := distance b a hba
    exact ⟨b,a,d,hd,Or.inr rfl,Or.inl rfl⟩

/-- No monochromatic axis-aligned box in the explicit 16-cube coloring. -/
theorem noBox16 (x X y Y z Z : Fin 16) (hx : x ≠ X) (hy : y ≠ Y) (hz : z ≠ Z) :
    ¬ Monochromatic color16 x X y Y z Z := by
  rintro ⟨b, h₀, h₁⟩
  have corner (i j k) (hi : i=x ∨ i=X) (hj : j=y ∨ j=Y) (hk : k=z ∨ k=Z) :
      (bitmap b).testBit (pos i j k) = true := by
    apply point_bit
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;>
      simp_all [Face]
  obtain ⟨xl,xh,dx,ex,hxl,hxh⟩ := endpoints hx
  obtain ⟨yl,yh,dy,ey,hyl,hyh⟩ := endpoints hy
  obtain ⟨zl,zh,dz,ez,hzl,hzh⟩ := endpoints hz
  have xbit (j k) (hj : j=y ∨ j=Y) (hk : k=z ∨ k=Z) :
      (step (bitmap b) (1024*(dx.val+1))).testBit (pos xl j k) = true := by
    apply step_bit (corner xl j k hxl hj hk)
    rw [show pos xl j k + 1024*(dx.val+1) = pos xh j k by unfold pos; omega]
    exact corner xh j k hxh hj hk
  have xybit (k) (hk : k=z ∨ k=Z) :
      (step (step (bitmap b) (1024*(dx.val+1))) (32*(dy.val+1))).testBit (pos xl yl k) =
        true := by
    apply step_bit (xbit yl k hyl hk)
    rw [show pos xl yl k + 32*(dy.val+1) = pos xl yh k by unfold pos; omega]
    exact xbit yh k hyh hk
  have last : (boxMask b dx dy dz).testBit (pos xl yl zl) = true := by
    apply step_bit (xybit zl hzl)
    rw [show pos xl yl zl + (dz.val+1) = pos xl yl zh by unfold pos; omega]
    exact xybit zh hzh
  rw [empty_mask, Nat.zero_testBit] at last
  contradiction

private def embed11 (i : Fin 11) : Fin 16 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

private theorem embed_ne {i j : Fin 11} (hne : i ≠ j) : embed11 i ≠ embed11 j :=
  fun h => hne (Fin.ext (congrArg (fun p : Fin 16 => p.val) h))

def color11 : Coloring 11 := fun (x,y,z) => color16 (embed11 x, embed11 y, embed11 z)

/-- Each pair may be supplied in either order. -/
theorem noBox11 (x X y Y z Z : Fin 11) (hx : x ≠ X) (hy : y ≠ Y) (hz : z ≠ Z) :
    ¬ Monochromatic color11 x X y Y z Z :=
  noBox16 _ _ _ _ _ _ (embed_ne hx) (embed_ne hy) (embed_ne hz)

private def pairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a => (List.finRange n).map fun b => (a,b)

/-- Each geometric box is counted once by requiring increasing endpoints
on all three axes. Colorings are completely unrestricted. -/
def boxCount {n : Nat} (C : Coloring n) : Nat :=
  let ps := pairs n
  let triples := ps.flatMap fun p => ps.flatMap fun q => ps.map fun r => (p,q,r)
  triples.countP fun (p,q,r) =>
    decide (p.1 < p.2 ∧ q.1 < q.2 ∧ r.1 < r.2 ∧ Monochromatic C p.1 p.2 q.1 q.2 r.1 r.2)

private theorem count_zero_of_noBox {n : Nat} (C : Coloring n)
    (free : ∀ x X y Y z Z, x ≠ X → y ≠ Y → z ≠ Z → ¬ Monochromatic C x X y Y z Z) :
    boxCount C = 0 := by
  apply List.countP_eq_zero.mpr
  rintro ⟨⟨x,X⟩,⟨y,Y⟩,⟨z,Z⟩⟩ _ h
  obtain ⟨hx, hy, hz, hm⟩ := of_decide_eq_true h
  exact free x X y Y z Z (Fin.ne_of_lt hx) (Fin.ne_of_lt hy) (Fin.ne_of_lt hz) hm

private theorem minimum_exists (n : Nat) :
    ∃ k, (∃ C : Coloring n, boxCount C = k) ∧ ∀ C : Coloring n, k ≤ boxCount C := by
  let constant : Coloring n := fun _ => false
  suffices aux : ∀ t (C : Coloring n), boxCount C = t →
      ∃ k, (∃ D : Coloring n, boxCount D = k) ∧ ∀ D : Coloring n, k ≤ boxCount D by
    exact aux _ constant rfl
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro C hC
    by_cases lower : ∃ D : Coloring n, boxCount D < t
    · obtain ⟨D, hD⟩ := lower
      exact ih _ hD D rfl
    · exact ⟨t, ⟨C,hC⟩, fun D => Nat.le_of_not_gt (fun h => lower ⟨D,h⟩)⟩

/-- The minimum box count over all two-colorings of the n-cube. -/
noncomputable def m (n : Nat) : Nat := Classical.choose (minimum_exists n)

theorem m_spec (n : Nat) :
    (∃ C : Coloring n, boxCount C = m n) ∧ ∀ C : Coloring n, m n ≤ boxCount C :=
  Classical.choose_spec (minimum_exists n)

theorem m11_eq_zero : m 11 = 0 :=
  Nat.eq_zero_of_le_zero ((count_zero_of_noBox color11 noBox11) ▸ (m_spec 11).2 color11)

theorem m16_eq_zero : m 16 = 0 :=
  Nat.eq_zero_of_le_zero ((count_zero_of_noBox color16 noBox16) ▸ (m_spec 16).2 color16)

theorem conjecture_false : ¬ (m 11 = 8) := by rw [m11_eq_zero]; decide

#print axioms noBox11
#print axioms noBox16
#print axioms m_spec
#print axioms m11_eq_zero
#print axioms m16_eq_zero
#print axioms conjecture_false

end BoxFree
