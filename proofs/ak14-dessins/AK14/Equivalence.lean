import AK14.Passport

/-! A complete simultaneous-conjugacy criterion for transitive branch-cycle triples,
with the three generators ordered and their directions fixed. -/
namespace AK14
open Equiv

def joint {n : ℕ} (T U : Triple n) : Subgroup (Perm (Fin n) × Perm (Fin n)) :=
  Subgroup.closure (Set.range fun j => (T j, U j))

private theorem joint_fst {n : ℕ} (T U : Triple n) :
    (joint T U).map (MonoidHom.fst _ _) = generated T := by
  rw [joint, generated, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨j, rfl⟩, rfl⟩

private theorem joint_snd {n : ℕ} (T U : Triple n) :
    (joint T U).map (MonoidHom.snd _ _) = generated U := by
  rw [joint, generated, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨j, rfl⟩, rfl⟩

/-- Agreement of the return words at two base sheets. -/
def SameReturns {n : ℕ} (T U : Triple n) (x y : Fin n) : Prop :=
  ∀ g ∈ joint T U, g.1 x = x ↔ g.2 y = y

theorem sameDessin_of_sameReturns {n : ℕ} {T U : Triple n}
    (ht : Transitive T) (hu : Transitive U) (x y : Fin n) (h : SameReturns T U x y) :
    SameDessin T U := by
  classical
  let J := joint T U
  have left (a : Fin n) : ∃ g : J, g.val.1 x = a := by
    obtain ⟨v, hv, hvx⟩ := ht x a
    rw [← joint_fst T U] at hv
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hv
    exact ⟨⟨g,hg⟩, hvx⟩
  have right (b : Fin n) : ∃ g : J, g.val.2 y = b := by
    obtain ⟨v, hv, hvy⟩ := hu y b
    rw [← joint_snd T U] at hv
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hv
    exact ⟨⟨g,hg⟩, hvy⟩
  have eqv (g k : J) : g.val.1 x = k.val.1 x ↔ g.val.2 y = k.val.2 y := by
    have h₀ := h _ (J.mul_mem (J.inv_mem k.property) g.property)
    change k.val.1⁻¹ (g.val.1 x) = x ↔ k.val.2⁻¹ (g.val.2 y) = y at h₀
    simpa only [Perm.inv_def, Equiv.symm_apply_eq] using h₀
  let chooseG (a : Fin n) := (left a).choose
  have chosen (a : Fin n) : (chooseG a).val.1 x = a := (left a).choose_spec
  let f (a : Fin n) := (chooseG a).val.2 y
  have eval (g : J) : f (g.val.1 x) = g.val.2 y :=
    (eqv _ g).mp (chosen (g.val.1 x))
  have inject : Function.Injective f := by
    intro a b hab
    exact (chosen a).symm.trans (((eqv (chooseG a) (chooseG b)).mpr hab).trans (chosen b))
  have surject : Function.Surjective f := by
    intro b
    obtain ⟨g, rfl⟩ := right b
    exact ⟨_, eval g⟩
  let q := Equiv.ofBijective f ⟨inject, surject⟩
  refine ⟨q, fun j => ?_⟩
  have comm (a : Fin n) : f (T j a) = U j (f a) := by
    let s : J := ⟨(T j,U j), Subgroup.subset_closure ⟨j,rfl⟩⟩
    have e := eval (s * chooseG a)
    change f (T j ((chooseG a).val.1 x)) = U j (f a) at e
    rwa [chosen] at e
  apply Equiv.ext; intro b
  have eq := comm (q.symm b)
  change q (T j (q.symm b)) = U j (q (q.symm b)) at eq
  simpa using eq.symm

private def intertwines {n : ℕ} (q : Perm (Fin n)) : Subgroup (Perm (Fin n) × Perm (Fin n)) where
  carrier := {g | g.2 = q * g.1 * q⁻¹}
  one_mem' := by simp
  mul_mem' := by
    rintro ⟨a,b⟩ ⟨c,d⟩ hb hd
    change b = q*a*q⁻¹ at hb
    change d = q*c*q⁻¹ at hd
    change b*d = q*(a*c)*q⁻¹
    simp [hb, hd, mul_assoc]
  inv_mem' := by
    rintro ⟨a,b⟩ hb
    change b = q*a*q⁻¹ at hb
    change b⁻¹ = q*a⁻¹*q⁻¹
    simp [hb, mul_assoc]

theorem sameDessin_iff_sameReturns {n : ℕ} {T U : Triple n}
    (ht : Transitive T) (hu : Transitive U) (x : Fin n) :
    SameDessin T U ↔ ∃ y, SameReturns T U x y := by
  constructor
  · rintro ⟨q, hq⟩
    have incl : joint T U ≤ intertwines q :=
      (Subgroup.closure_le _).mpr (by rintro _ ⟨j,rfl⟩; exact hq j)
    refine ⟨q x, fun g hg => ?_⟩
    have e : g.2 = q * g.1 * q⁻¹ := incl hg
    simp [e]
  · rintro ⟨y, hy⟩
    exact sameDessin_of_sameReturns ht hu x y hy

end AK14
