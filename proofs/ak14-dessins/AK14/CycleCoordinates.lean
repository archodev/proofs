import AK14.Passport
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace AK14
open Equiv Function
noncomputable section

def cycleDegree {n : ℕ} (g : Perm (Fin n)) (x : Fin n) := minimalPeriod g x

theorem cycleDegree_pos {n : ℕ} (g : Perm (Fin n)) (x : Fin n) : 0<cycleDegree g x :=
  minimalPeriod_pos_of_mem_periodicPts (g.injective.mem_periodicPts x)

theorem orbit_power_mod {n : ℕ} (g : Perm (Fin n)) (x : Fin n) (k : ℕ) :
    (g^(k%cycleDegree g x)) x=(g^k) x := by
  simp only [cycleDegree,Perm.coe_pow]
  exact iterate_mod_minimalPeriod_eq

def orbitNumbering {n : ℕ} (g : Perm (Fin n)) (x : Fin n) :
    Fin (cycleDegree g x) ≃ {y : Fin n // g.SameCycle x y} := by
  let F (k : Fin (cycleDegree g x)) : {y : Fin n // g.SameCycle x y} :=
    ⟨(g^k.val) x,Perm.sameCycle_pow_right.mpr Perm.SameCycle.rfl⟩
  apply Equiv.ofBijective F
  constructor
  · intro a b h
    apply Fin.ext
    have e : (g^a.val) x=(g^b.val) x := congrArg Subtype.val h
    simp only [Perm.coe_pow] at e
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod a.isLt b.isLt).mp e
  · rintro ⟨y,hy⟩
    obtain ⟨k,hk⟩ := hy.exists_nat_pow_eq
    exact ⟨⟨k%cycleDegree g x,Nat.mod_lt _ (cycleDegree_pos _ _)⟩,Subtype.ext ((orbit_power_mod _ _ _).trans hk)⟩

@[simp] theorem orbitNumbering_val {n : ℕ} (g : Perm (Fin n)) (x : Fin n) (k : Fin (cycleDegree g x)) :
    (orbitNumbering g x k).val=(g^k.val) x := rfl

/-- Position in the marked orbit as a root of unity. The value off this orbit is zero. -/
def orbitPhase {n : ℕ} (g : Perm (Fin n)) (x : Fin n) (ξ : ℂ) (y : Fin n) : ℂ := by
  classical
  exact if h : g.SameCycle x y then ξ^((orbitNumbering g x).symm ⟨y,h⟩).val else 0

theorem orbitPhase_pow {n : ℕ} (g : Perm (Fin n)) (x : Fin n) {ξ : ℂ}
    (prim : IsPrimitiveRoot ξ (cycleDegree g x)) (k : ℕ) : orbitPhase g x ξ ((g^k) x)=ξ^k := by
  classical
  let d := cycleDegree g x
  let i : Fin d := ⟨k%d,Nat.mod_lt _ (cycleDegree_pos _ _)⟩
  have h : g.SameCycle x ((g^k) x) := Perm.sameCycle_pow_right.mpr Perm.SameCycle.rfl
  have image : orbitNumbering g x i=⟨(g^k) x,h⟩ := Subtype.ext (orbit_power_mod g x k)
  simp only [orbitPhase,dif_pos h,← image,Equiv.symm_apply_apply]
  change ξ^(k%cycleDegree g x)=ξ^k
  rw [prim.eq_orderOf,pow_mod_orderOf]

theorem orbitPhase_self {n : ℕ} (g : Perm (Fin n)) (x : Fin n) {ξ : ℂ}
    (prim : IsPrimitiveRoot ξ (cycleDegree g x)) : orbitPhase g x ξ x=1 := by simpa using orbitPhase_pow g x prim 0

theorem orbitPhase_apply {n : ℕ} (g : Perm (Fin n)) (x : Fin n) {ξ : ℂ}
    (prim : IsPrimitiveRoot ξ (cycleDegree g x)) (y : Fin n) :
    orbitPhase g x ξ (g y)=ξ*orbitPhase g x ξ y := by
  classical
  by_cases h : g.SameCycle x y
  · obtain ⟨k,rfl⟩ := h.exists_nat_pow_eq
    rw [← show (g^(k+1)) x=g ((g^k) x) by rw [pow_succ']; rfl,orbitPhase_pow _ _ prim,orbitPhase_pow _ _ prim,pow_succ']
  · have h' : ¬g.SameCycle x (g y) := by simpa using h
    simp [orbitPhase,h,h']

theorem orbitPhase_injective {n : ℕ} (g : Perm (Fin n)) (x : Fin n) {ξ : ℂ}
    (prim : IsPrimitiveRoot ξ (cycleDegree g x)) {y z : Fin n} (hy : g.SameCycle x y)
    (hz : g.SameCycle x z) (eq : orbitPhase g x ξ y=orbitPhase g x ξ z) : y=z := by
  classical
  simp only [orbitPhase,dif_pos hy,dif_pos hz] at eq
  let E := (orbitNumbering g x).symm
  have j : E ⟨y,hy⟩=E ⟨z,hz⟩ := Fin.ext (prim.pow_inj (E _).isLt (E _).isLt eq)
  exact congrArg Subtype.val (E.injective j)

end
end AK14
