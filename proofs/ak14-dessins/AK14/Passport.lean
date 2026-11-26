import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.FinCases

/-! Ordered, oriented branch-cycle formulation of Adrianov–Kreines, Conjecture 1.4. -/
namespace AK14

open Equiv

inductive Family | split | together
  deriving DecidableEq

structure Passport where
  family : Family
  r : ℕ
  s : ℕ
  t : ℕ
  a : ℕ
  b : ℕ
  c : ℕ

def Passport.rows (p : Passport) : Fin 3 → Multiset ℕ :=
  match p.family with
  | .split => ![Multiset.replicate p.r 2 + {p.a},
                Multiset.replicate p.s 3 + {p.b},
                Multiset.replicate p.t 3 + {p.c}]
  | .together => ![Multiset.replicate p.r 2 + {p.a},
                   Multiset.replicate p.s 3,
                   Multiset.replicate p.t 3 + {p.b, p.c}]

/-- Equal totals, three genuine branch values, and the genus-zero Riemann–Hurwitz equality. -/
structure Passport.Admissible (p : Passport) (n : ℕ) : Prop where
  a_pos : 0 < p.a
  b_pos : 0 < p.b
  c_pos : 0 < p.c
  a_odd : ¬ 2 ∣ p.a
  b_residue : ¬ 3 ∣ p.b
  c_residue : ¬ 3 ∣ p.c
  totals : ∀ j, (p.rows j).sum = n
  branched : ∀ j, p.rows j ≠ Multiset.replicate n 1
  sphere : (p.rows 0).card + (p.rows 1).card + (p.rows 2).card = n + 2

abbrev Triple (n : ℕ) := Fin 3 → Perm (Fin n)

/-- Mathlib's cycle type omits the fixed points. A passport counts each of them. -/
def fullType {n : ℕ} (g : Perm (Fin n)) : Multiset ℕ :=
  g.cycleType + Multiset.replicate (n - g.cycleType.sum) 1

theorem fullType_eq_partition {n : ℕ} (g : Perm (Fin n)) :
    fullType g = g.partition.parts := by
  simp [fullType, Perm.parts_partition, Perm.sum_cycleType]

theorem sum_nontrivial_parts {n : ℕ} (g : Perm (Fin n)) :
    ((fullType g).filter (fun k => 2 ≤ k)).sum = g.support.card := by
  rw [fullType_eq_partition, Perm.filter_parts_partition_eq_cycleType, Perm.sum_cycleType]

theorem fixedPointCount {n : ℕ} (g : Perm (Fin n)) :
    Fintype.card (Function.fixedPoints g) = n - g.cycleType.sum := by
  simpa using Equiv.Perm.card_fixedPoints g

/-- In particular a displayed exceptional part of size 1 supplies a genuine sheet. -/
theorem exists_fixed_pow_of_mem_fullType {n e : ℕ} {g : Perm (Fin n)}
    (he : e ∈ fullType g) : ∃ x : Fin n, (g ^ e) x = x := by
  rcases Multiset.mem_add.mp he with hc | hf
  · rw [Perm.cycleType_def] at hc
    obtain ⟨c, hc, he⟩ := Multiset.mem_map.mp hc
    change c ∈ g.cycleFactorsFinset at hc
    change c.support.card = e at he
    obtain ⟨x, hx⟩ := (Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
    exact ⟨x, he ▸ (Perm.isCycleOn_support_of_mem_cycleFactorsFinset hc).pow_card_apply hx⟩
  · obtain ⟨hn, rfl⟩ := Multiset.mem_replicate.mp hf
    have hp : 0 < Fintype.card (Function.fixedPoints g) := by
      rw [fixedPointCount]
      omega
    obtain ⟨⟨x, hx⟩⟩ := Fintype.card_pos_iff.mp hp
    exact ⟨x, by simpa using hx⟩

def generated {n : ℕ} (T : Triple n) := Subgroup.closure (Set.range T)

def Transitive {n : ℕ} (T : Triple n) : Prop :=
  ∀ x y : Fin n, ∃ g ∈ generated T, g x = y

structure Realizes {n : ℕ} (p : Passport) (T : Triple n) : Prop where
  product : T 0 * T 1 * T 2 = 1
  transitive : Transitive T
  cycles : ∀ i, fullType (T i) = p.rows i

def Passport.bSlot (p : Passport) : Fin 3 :=
  match p.family with | .split => 1 | .together => 2

theorem Passport.a_mem (p : Passport) : p.a ∈ p.rows 0 := by
  cases hf : p.family <;> simp [rows, hf]

theorem Passport.b_mem (p : Passport) : p.b ∈ p.rows p.bSlot := by
  cases hf : p.family <;> simp [rows, bSlot, hf]

/-- A single relabeling of the sheets, acting on each of the three named slots. -/
def SameDessin {n : ℕ} (T U : Triple n) : Prop :=
  ∃ q : Perm (Fin n), ∀ i, U i = q * T i * q⁻¹

/-- The full universal assertion, including the existence supplied by Theorem 1.3 on paper.
This declaration specifies the target proposition. -/
def Conjecture14 : Prop :=
  ∀ (p : Passport) (n : ℕ), p.Admissible n →
    ∃ T : Triple n, Realizes p T ∧ ∀ U : Triple n, Realizes p U → SameDessin T U

theorem sameDessin_equivalence (n : ℕ) : Equivalence (@SameDessin n) where
  refl T := ⟨1, by simp⟩
  symm := by
    rintro T U ⟨q, h⟩
    exact ⟨q⁻¹, fun i => by simp [h i, mul_assoc]⟩
  trans := by
    rintro T U V ⟨q, h⟩ ⟨r, k⟩
    exact ⟨r * q, fun i => by simp [k i, h i, mul_assoc]⟩

theorem Passport.degree_formula {p : Passport} {n : ℕ} (h : p.Admissible n) :
    n + 6 = 3 * p.a + 2 * p.b + 2 * p.c := by
  have h₀ := h.totals 0
  have h₁ := h.totals 1
  have h₂ := h.totals 2
  have hχ := h.sphere
  cases hf : p.family <;>
    simp [Passport.rows, hf, Multiset.sum_replicate, nsmul_eq_mul] at h₀ h₁ h₂ hχ <;>
    omega

end AK14
