import AK14.Equivalence

/-! The two oriented target triangles, copied on every sheet and glued across
three labeled sides. Their positive corner walks recover the ordered input
triple. This is the finite gluing data before uniformization. -/
namespace AK14.Gluing
open Equiv
noncomputable section

abbrev Tri (n : ℕ) := Bool × Fin n

def crossing {n : ℕ} (T : Triple n) : Fin 3 → Perm (Fin n) := ![1,(T 0)⁻¹,T 1]

def step {n : ℕ} (T : Triple n) (e : Fin 3) : Tri n → Tri n
  | (true,i) => (false,crossing T e i)
  | (false,i) => (true,(crossing T e)⁻¹ i)

theorem step_involution {n : ℕ} (T : Triple n) (e : Fin 3) (x : Tri n) :
    step T e (step T e x)=x := by obtain ⟨b,i⟩ := x; cases b <;> simp [step]

def first : Fin 3 → Fin 3 := ![0,2,1]
def last : Fin 3 → Fin 3 := ![1,0,2]

theorem corner_walk {n : ℕ} (T : Triple n) (h : T 0*T 1*T 2=1) (j : Fin 3) (i : Fin n) :
    step T (last j) (step T (first j) (true,i))=(true,T j i) := by
  have third : T 2=(T 1)⁻¹*(T 0)⁻¹ := by
    have k := eq_inv_of_mul_eq_one_right h
    simpa only [mul_inv_rev] using k
  fin_cases j <;> simp [first,last,step,crossing,third,Perm.mul_apply]

def ConnectedBy {n : ℕ} (T : Triple n) : Tri n → Tri n → Prop :=
  Relation.EqvGen (fun u v => ∃ e,step T e u=v)

private theorem one_step {n : ℕ} (T : Triple n) (e : Fin 3) (x : Tri n) :
    ConnectedBy T x (step T e x) := Relation.EqvGen.rel _ _ ⟨e,rfl⟩

private def walkers {n : ℕ} (T : Triple n) : Subgroup (Perm (Fin n)) where
  carrier := {g | ∀ i, ConnectedBy T (true,i) (true,g i)}
  one_mem' := fun _ => Relation.EqvGen.refl _
  mul_mem' := by
    intro g h G H i
    exact Relation.EqvGen.trans _ _ _ (H i) (G (h i))
  inv_mem' := by
    intro g G i
    have h := Relation.EqvGen.symm _ _ (G (g.symm i))
    simpa using h

theorem triangles_connected {n : ℕ} {T : Triple n} (ht : Transitive T) (prod : T 0*T 1*T 2=1)
    (x y : Tri n) : ConnectedBy T x y := by
  have sub : generated T ≤ walkers T := by
    apply (Subgroup.closure_le (walkers T)).mpr
    rintro _ ⟨j,rfl⟩ i
    rw [← corner_walk T prod j i]
    exact Relation.EqvGen.trans _ _ _ (one_step _ _ _) (one_step _ _ _)
  have attach (v : Tri n) : ConnectedBy T v (true,v.2) := by
    obtain ⟨b,i⟩ := v
    cases b with
    | false => simpa [step,crossing] using one_step T 0 (false,i)
    | true => exact Relation.EqvGen.refl _
  obtain ⟨g,hg,e⟩ := ht x.2 y.2
  have walk : ConnectedBy T (true,x.2) (true,g x.2) := sub hg x.2
  rw [e] at walk
  exact Relation.EqvGen.trans _ _ _ (attach x)
    (Relation.EqvGen.trans _ _ _ walk (Relation.EqvGen.symm _ _ (attach y)))

/-- Face bijections that preserve the two orientations and the three distinct edge labels. -/
def Equivalent {n : ℕ} (T U : Triple n) : Prop :=
  ∃ q : Tri n ≃ Tri n, (∀ x, (q x).1=x.1) ∧ ∀ j x, q (step T j x)=step U j (q x)

theorem oriented_gluing_iff {n : ℕ} {T U : Triple n} (pT : T 0*T 1*T 2=1) (pU : U 0*U 1*U 2=1) :
    Equivalent T U ↔ SameDessin T U := by
  constructor
  · rintro ⟨F,sign,move⟩
    let f (i : Fin n) := (F (true,i)).2
    have on (i : Fin n) : F (true,i)=(true,f i) := Prod.ext (sign _) rfl
    have inj : Function.Injective f := by
      intro i j eq
      have h : F (true,i)=F (true,j) := by rw [on,on,eq]
      exact congrArg Prod.snd (F.injective h)
    let q := Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩
    have go (j : Fin 3) (i : Fin n) : q (T j i)=U j (q i) := by
      have h := congrArg F (corner_walk T pT j i)
      rw [move,move,on,corner_walk U pU,on] at h
      exact (congrArg Prod.snd h).symm
    refine ⟨q,fun j => Equiv.ext fun i => ?_⟩
    have h := go j (q.symm i)
    change U j i=q (T j (q.symm i))
    simpa only [q.apply_symm_apply] using h.symm
  · rintro ⟨q,eq⟩
    let F := Equiv.prodCongr (Equiv.refl Bool) q
    refine ⟨F,fun _ => rfl,?_⟩
    intro j x
    obtain ⟨b,i⟩ := x
    fin_cases j <;> cases b <;> simp [F,step,crossing,eq,Perm.mul_apply,mul_inv_rev]

end
end AK14.Gluing
