import AK14.CubicTower
import AK14.PencilRigidity

/-! The degree-twelve inverse tetrahedral polynomial is irreducible for every
normalized rational map with an Adrianov–Kreines passport. -/
namespace AK14.SeriesAt
open Polynomial TetraQuotient
noncomputable section
variable {E : Type*} [Field E] [CharZero E]

theorem inverse_coordinates {s f z : E} (hs : s^2= -3) (nf : f≠0)
    (eq : (1-f)*quartic s (z,1)^3-quartic (-s) (z,1)^3=0) :
    ∃ h u v : E, h^3=1-f ∧ u^2=inverseContrast s h+2 ∧ v^2=inverseContrast s h-2 := by
  let A := quartic s (z,1)
  let B := quartic (-s) (z,1)
  change (1-f)*A^3-B^3=0 at eq
  have na : A≠0 := by
    intro ha
    have b : B^3=0 := by simpa [ha] using eq
    have vr := qmap_valid hs (P := (z,1)) (Or.inr one_ne_zero)
    change A^3-B^3 ≠0 ∨ A^3≠0 at vr
    simp [ha,b] at vr
  have nz : z≠0 := by
    intro zero
    have a : A=1 := by simp [A,quartic,zero]
    have b : B=1 := by simp [B,quartic,zero]
    exact nf (by rw [a,b] at eq; linear_combination -eq)
  let h := B/A
  have h3 : h^3=1-f := by
    rw [show h=B/A from rfl,div_pow,div_eq_iff (pow_ne_zero _ na)]
    linear_combination -eq
  have nh : 1-h≠0 := by
    intro hh
    have : h=1 := (sub_eq_zero.mp hh).symm
    apply nf
    rw [this,one_pow] at h3
    linear_combination h3
  let t := z^2+(z^2)⁻¹
  have ea : A=z^2*(t+2*s) := by dsimp only [A,t,quartic]; simp only [one_pow,mul_one]; field_simp; ring
  have eb : B=z^2*(t-2*s) := by dsimp only [B,t,quartic]; simp only [one_pow,mul_one]; field_simp; ring
  have hA : h*A=B := div_mul_cancel₀ _ na
  have ht : h*(t+2*s)=t-2*s := by
    apply mul_left_cancel₀ (pow_ne_zero 2 nz)
    rw [← eb,← hA,ea]; ring
  have inv : inverseContrast s h=t := by
    rw [inverseContrast,div_eq_iff nh]
    linear_combination ht
  refine ⟨h,z+z⁻¹,z-z⁻¹,h3,?_,?_⟩ <;> rw [inv] <;>
    dsimp only [t] <;> field_simp <;> ring

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

private theorem rad_rank {R : Type*} [Field R] (d : ℕ) (q : R) (h : Irreducible (radPoly d q)) :
    Module.finrank R (Rad d q)=d := by
  rw [(AdjoinRoot.powerBasis h.ne_zero).finrank,AdjoinRoot.powerBasis_dim]
  exact natDegree_X_pow_sub_C

theorem inverse_degree_divisibility {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {f : RatFunc K} (hf : NormalizedCover p f) {s : K} (hs : s^2= -3)
    [Algebra (RatFunc K) E] (h u v : E)
    (h3 : h^3=algebraMap (RatFunc K) E (1-f))
    (u2 : u^2=inverseContrast (algebraMap (RatFunc K) E (kRat K s)) h+2)
    (v2 : v^2=inverseContrast (algebraMap (RatFunc K) E (kRat K s)) h-2) :
    12 ∣ Module.finrank (RatFunc K) E := by
  let F := RatFunc K
  let C := CubeField f
  have hC : Irreducible (radPoly 3 (1-f)) := cube_irreducible hp hf
  letI : Fact (Irreducible (radPoly 3 (1-f))) := ⟨hC⟩
  let j := radicalLift (algebraMap F E) h h3
  letI : Algebra C E := j.toAlgebra
  letI : IsScalarTower F C E := IsScalarTower.of_algebraMap_eq fun x => (radicalLift_of (algebraMap F E) h h3 x).symm
  have jt : j (cubicT s f)=inverseContrast (algebraMap F E (kRat K s)) h := by
    rw [cubicT,inverseContrast,map_div₀ j,map_mul j,map_mul j,map_add j,map_sub j,map_one j,map_ofNat j]
    simp only [j,radicalLift_of,radicalLift_root,inverseContrast]
  let q := cubicT s f+2
  let q' := cubicT s f-2
  have uq : u^2=j q := by rw [show q=cubicT s f+2 from rfl,map_add,map_ofNat,jt,u2]
  have vq : v^2=j q' := by rw [show q'=cubicT s f-2 from rfl,map_sub,map_ofNat,jt,v2]
  have hA := first_square_irreducible hp hf hs
  letI : Fact (Irreducible (radPoly 2 q)) := ⟨hA⟩
  let A := Rad 2 q
  let k := radicalLift j u uq
  letI : Algebra A E := k.toAlgebra
  letI : IsScalarTower C A E := IsScalarTower.of_algebraMap_eq fun x => (radicalLift_of j u uq x).symm
  let r := AdjoinRoot.of (radPoly 2 q) q'
  have vr : v^2=k r := by rw [show k r=j q' from radicalLift_of _ _ _ _,vq]
  have hB := second_square_irreducible hp hf hs
  letI : Fact (Irreducible (radPoly 2 r)) := ⟨hB⟩
  let B := Rad 2 r
  let l := radicalLift k v vr
  letI : Algebra B E := l.toAlgebra
  letI : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq fun x => (radicalLift_of k v vr x).symm
  have a : Module.finrank F C=3 := rad_rank 3 _ hC
  have b : Module.finrank C A=2 := rad_rank 2 _ hA
  have c : Module.finrank A B=2 := rad_rank 2 _ hB
  refine ⟨Module.finrank B E,?_⟩
  rw [← Module.finrank_mul_finrank F C E,← Module.finrank_mul_finrank C A E,
    ← Module.finrank_mul_finrank A B E,a,b,c]
  ring

theorem inverse_irreducible {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {f : RatFunc K} (hf : NormalizedCover p f) {s : K} (hs : s^2= -3) :
    Irreducible (liftPolynomial (kRat K s) f) := by
  let F := RatFunc K
  let P := liftPolynomial (kRat K s) f
  have sf : (kRat K s)^2= -3 := by rw [← map_pow,hs,map_neg,map_ofNat]
  have fn : f≠0 := fun z => hf.nonconstant (by rw [z,map_zero])
  have dp : P.natDegree=12 := liftPolynomial_degree sf fn
  have np : P≠0 := fun z => by simp [z] at dp
  have nu : ¬ IsUnit P := fun unit => by have e := natDegree_eq_zero_of_isUnit unit; omega
  obtain ⟨R,ir,dv⟩ := WfDvdMonoid.exists_irreducible_factor nu np
  letI : Fact (Irreducible R) := ⟨ir⟩
  let L := AdjoinRoot R
  let ρ := AdjoinRoot.of R
  letI : CharZero L := charZero_of_injective_algebraMap ρ.injective
  let z := AdjoinRoot.root R
  have root : aeval z P=0 := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero ρ z dv (AdjoinRoot.eval₂_root R)
  change aeval z (liftPolynomial (kRat K s) f)=0 at root
  rw [← pencil_id (kRat K) hs,pencil_root_data] at root
  simp only [middleId,map_one,map_zero,one_mul,zero_mul,zero_add,add_zero] at root
  have sl : (ρ (kRat K s))^2= -3 := by rw [← map_pow,sf,map_neg,map_ofNat]
  obtain ⟨h,u,v,h3,u2,v2⟩ := inverse_coordinates sl ((map_ne_zero_iff ρ ρ.injective).mpr fn) root
  have eq : h^3=ρ (1-f) := by rw [map_sub,map_one,h3]
  have div := inverse_degree_divisibility hp hf hs h u v eq u2 v2
  have deg : 12∣R.natDegree := by simpa only [L,(AdjoinRoot.powerBasis ir.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim] using div
  have le := natDegree_le_of_dvd dv np
  have pos := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible ir)
  exact (associated_of_dvd_of_natDegree_le dv np (dp ▸ Nat.le_of_dvd pos deg)).irreducible ir

/-- Universal normalized rational-map uniqueness, with only the source ramification
prescribed. Both passport families and all admissible degrees are included. -/
theorem normalized_rational_unique {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {f g : RatFunc K} (hf : NormalizedCover p f) (hg : NormalizedCover p g) : f=g := by
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq (-3:K) (by decide : 0<2)
  exact normalized_unique_of_irreducible hp hf hg hs (inverse_irreducible hp hf hs)

end
end AK14.SeriesAt
