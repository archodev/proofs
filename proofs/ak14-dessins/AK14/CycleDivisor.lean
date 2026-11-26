import AK14.CornerVertices
import AK14.CycleCoordinates

namespace AK14.Gluing
open Equiv
open scoped BigOperators Classical
noncomputable section

def cornerClass {n : ℕ} (g : Perm (Fin n)) (x : Fin n) : Corners g := Quotient.mk _ x

def classDegree {n : ℕ} (g : Perm (Fin n)) (c : Corners g) : ℕ :=
  Nat.card {y : Fin n // cornerClass g y=c}

theorem classDegree_at {n : ℕ} (g : Perm (Fin n)) (x : Fin n) :
    classDegree g (cornerClass g x)=cycleDegree g x := by
  let e : {y : Fin n // g.SameCycle x y} ≃ {y : Fin n // cornerClass g y=cornerClass g x} :=
    Equiv.subtypeEquivRight (fun y => ⟨fun h => Quotient.sound h.symm,fun h => (Quotient.exact h : g.SameCycle y x).symm⟩)
  simpa [classDegree] using (Nat.card_congr ((orbitNumbering g x).trans e)).symm

theorem classDegree_sum {n : ℕ} (g : Perm (Fin n)) :
    ∑ c : Corners g, classDegree g c=n := by
  let e := Equiv.sigmaFiberEquiv (cornerClass g)
  have total := Fintype.card_congr e
  simpa [classDegree,Fintype.card_sigma,Nat.card_eq_fintype_card] using total

theorem classDegree_fixed {n : ℕ} (g : Perm (Fin n)) {x : Fin n} (h : g x=x) :
    classDegree g (cornerClass g x)=1 := by
  rw [classDegree_at,cycleDegree]
  exact (Function.minimalPeriod_eq_one_iff_isFixedPt.mpr h)

theorem classDegree_moving {n : ℕ} (g : Perm (Fin n)) {x : Fin n} (h : g x≠x) :
    classDegree g (cornerClass g x)=(g.cycleOf x).support.card := by
  let e : {y : Fin n // cornerClass g y=cornerClass g x} ≃ ↥(g.cycleOf x).support :=
    Equiv.subtypeEquivRight (fun y => ⟨fun eq => (Perm.mem_support_cycleOf_iff' h).mpr
      (Quotient.exact eq : g.SameCycle y x).symm,
      fun hy => Quotient.sound ((Perm.mem_support_cycleOf_iff' h).mp hy).symm⟩)
  simpa only [classDegree,Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_congr e

/-- The signed orders of the differential of the local power models. At a
pole of degree d the differential has order -d-1. -/
def differentialWeight (j : Fin 3) (d : ℕ) : ℤ := if j=2 then -(d:ℤ)-1 else (d:ℤ)-1

theorem class_weight_sum {n : ℕ} (g : Perm (Fin n)) (j : Fin 3) :
    ∑ c : Corners g, differentialWeight j (classDegree g c)=
      (if j=2 then -(n:ℤ) else (n:ℤ))-(Nat.card (Corners g):ℤ) := by
  have d : (∑ c : Corners g, (classDegree g c : ℤ))=(n:ℤ) := by exact_mod_cast classDegree_sum g
  by_cases h : j=2 <;> simp [differentialWeight,h,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
    Nat.card_eq_fintype_card,d]

theorem total_differential_weight {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {T : Triple n} (hT : Realizes p T) :
    (∑ c : Corners (T 0), differentialWeight 0 (classDegree (T 0) c))+
    (∑ c : Corners (T 1), differentialWeight 1 (classDegree (T 1) c))+
    (∑ c : Corners (T 2), differentialWeight 2 (classDegree (T 2) c))= -2 := by
  simp only [class_weight_sum,vertex_count,hT.cycles]
  norm_num
  have s := hp.sphere
  omega

end
end AK14.Gluing
