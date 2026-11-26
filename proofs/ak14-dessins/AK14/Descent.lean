import AK14.Passport
import Mathlib.Algebra.Group.Subgroup.Basic

namespace AK14
open Equiv

/-- Descent of a normalizing automorphism to an orbit quotient. The fiber characterization
and surjectivity are exactly the hypotheses for q to be such a quotient of sets. -/
theorem normalizer_descends {X Y : Type*} (G : Subgroup (Perm X)) (q : X → Y)
    (onto : Function.Surjective q)
    (fiber : ∀ x y, q x = q y ↔ ∃ g ∈ G, g x = y)
    (M : Perm X) (normalizes : M ∈ Subgroup.normalizer (G : Set (Perm X))) :
    ∃! h : Perm Y, ∀ x, h (q x) = q (M x) := by
  classical
  have respect (N : Perm X) (hN : N ∈ Subgroup.normalizer (G : Set (Perm X))) {x y : X} (hxy : q x = q y) :
      q (N x) = q (N y) := by
    obtain ⟨g, hg, rfl⟩ := (fiber x y).mp hxy
    apply (fiber _ _).mpr
    refine ⟨N * g * N⁻¹, (Subgroup.mem_normalizer_iff.mp hN g).mp hg, ?_⟩
    simp
  let s : Y → X := Function.surjInv onto
  have hs : ∀ y, q (s y) = y := Function.rightInverse_surjInv onto
  let h : Y → Y := fun y => q (M (s y))
  have commutes (x : X) : h (q x) = q (M x) := respect M normalizes (hs (q x))
  have inj : Function.Injective h := by
    intro u v huv
    obtain ⟨x, rfl⟩ := onto u
    obtain ⟨y, rfl⟩ := onto v
    rw [commutes, commutes] at huv
    simpa using respect M⁻¹ ((Subgroup.normalizer (G : Set (Perm X))).inv_mem normalizes) huv
  have surj : Function.Surjective h := by
    intro v
    obtain ⟨x, rfl⟩ := onto v
    exact ⟨q (M⁻¹ x), by simp [commutes]⟩
  refine ⟨Equiv.ofBijective h ⟨inj, surj⟩, commutes, ?_⟩
  intro j hj
  ext y
  obtain ⟨x, rfl⟩ := onto y
  exact (hj x).trans (commutes x).symm

def branchOrder : Fin 3 → ℕ := ![2, 3, 3]

/-- Fixing the target of the b-point removes the order-three swap in both families. -/
theorem targetLabels_force_identity (p : Passport) (h : Perm (Fin 3))
    (weights : ∀ i, branchOrder (h i) = branchOrder i)
    (mark : h p.bSlot = p.bSlot) : h = 1 := by
  have hz : h 0 = 0 := by
    have w := weights 0
    generalize he : h 0 = i at w ⊢
    fin_cases i <;> simp_all [branchOrder]
  have fixTwo (j k : Fin 3) (hj : h j = j) (hne : k ≠ 0) (hkj : k ≠ j)
      (all : ∀ v : Fin 3, v = 0 ∨ v = j ∨ v = k) : h k = k := by
    rcases all (h k) with a | a | a
    · exact (hne (h.injective (a.trans hz.symm))).elim
    · exact (hkj (h.injective (a.trans hj.symm))).elim
    · exact a
  cases hf : p.family with
  | split =>
    have h1 : h 1 = 1 := by simpa [Passport.bSlot, hf] using mark
    have h2 := fixTwo 1 2 h1 (by decide) (by decide) (by decide)
    apply Equiv.ext; intro i; fin_cases i <;> assumption
  | together =>
    have h2 : h 2 = 2 := by simpa [Passport.bSlot, hf] using mark
    have h1 := fixTwo 2 1 h2 (by decide) (by decide) (by decide)
    apply Equiv.ext; intro i; fin_cases i <;> assumption

end AK14
