import AK14.Normalized
import AK14.SplittingLifts

/-! Universally quantified lift rigidity for both rational-cover passport families,
inside a concrete finite splitting field. -/
namespace AK14.SeriesAt
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

local instance (priority := 2000) : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Differential (RatFunc K) := ⟨ratDeriv K⟩

/-- Fractional linear equivalence with coefficients in the ground field K. -/
def MobiusOver (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L] (z w : L) : Prop :=
  ∃ a b c d : K, a*d-b*c ≠ 0 ∧ algebraMap K L c*z+algebraMap K L d ≠ 0 ∧
    w=(algebraMap K L a*z+algebraMap K L b)/(algebraMap K L c*z+algebraMap K L d)

theorem common_field_rigidity {L : Type*} [Field L] [CharZero L] [Algebra (RatFunc K) L]
    [Algebra K L] [IsScalarTower K (RatFunc K) L] [FiniteDimensional (RatFunc K) L]
    [Differential L] [DifferentialAlgebra (RatFunc K) L]
    {s : K} (hs : s^2= -3) {f g : RatFunc K} {z w : L}
    (df : ratDeriv K f ≠ 0) (dg : ratDeriv K g ≠ 0)
    (F : tetraMap (algebraMap K L s) z=algebraMap (RatFunc K) L f)
    (G : tetraMap (algebraMap K L s) w=algebraMap (RatFunc K) L g)
    (same : rationalConnection f=rationalConnection g) : MobiusOver K z w := by
  let D : Derivation ℤ L L := Differential.deriv
  let ρ := algebraMap (RatFunc K) L
  let σ := algebraMap K L
  have comm (x : RatFunc K) : D (ρ x)=ρ (ratDeriv K x) := deriv_algebraMap x
  have ds : D (σ s)=0 := by
    change D (algebraMap K L s)=0
    rw [IsScalarTower.algebraMap_apply K (RatFunc K) L,comm]
    have c := (ratDeriv_constants K (algebraMap K _ s)).mpr ⟨s,rfl⟩
    rw [c,map_zero]
  have reg {v : L} {h : RatFunc K} (dh : ratDeriv K h ≠ 0)
      (e : tetraMap (σ s) v=ρ h) : D v ≠ 0 := by
    intro zero
    have eq := tetraMap_deriv_zero D ds zero
    rw [e,comm] at eq
    exact dh ((map_eq_zero_iff ρ ρ.injective).mp eq)
  have dz := reg df F
  have dw := reg dg G
  have hσ : (σ s)^2= -3 := by rw [← map_pow,hs,map_neg,map_ofNat]
  have lift {v : L} {h : RatFunc K} (dv : D v ≠ 0) (e : tetraMap (σ s) v=ρ h) :
      schwarzian D v=ρ (rationalConnection h) := by
    rw [tetraMap_schwarzian D hσ dv,e]
    exact (pullConnection_map _ _ _ comm h).symm
  have equality : schwarzian D z=schwarzian D w := by rw [lift dz F,lift dw G,same]
  obtain ⟨a,b,c,d,da,db,dc,dd,det,den,quot⟩ := constantMobius_of_schwarzian_eq D dz dw equality
  have constants (u : L) (zero : D u=0) : ∃ k : K, σ k=u :=
    finite_extension_constants K (F := RatFunc K)
      (fun x hx => (ratDeriv_constants K x).mp hx) u zero
  obtain ⟨a',rfl⟩ := constants a da
  obtain ⟨b',rfl⟩ := constants b db
  obtain ⟨c',rfl⟩ := constants c dc
  obtain ⟨d',rfl⟩ := constants d dd
  refine ⟨a',b',c',d',?_,den,quot⟩
  intro bad
  apply det
  simpa only [map_sub σ,map_mul σ,map_zero] using congrArg σ bad

abbrev ComparisonField (s : K) (f g : RatFunc K) :=
  LiftField (algebraMap K (RatFunc K) s) f g

/-- Starting from the normalized rational maps alone, build both inverse quotient
branches in the same finite splitting field and derive their ground-field Möbius relation. -/
theorem normalized_lifts_mobius {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {f g : RatFunc K} (hf : NormalizedCover p f) (hg : NormalizedCover p g)
    {s : K} (hs : s^2= -3) :
    ∃ z w : ComparisonField s f g,
      tetraMap (algebraMap K _ s) z=algebraMap (RatFunc K) _ f ∧
      tetraMap (algebraMap K _ s) w=algebraMap (RatFunc K) _ g ∧ MobiusOver K z w := by
  let L := ComparisonField s f g
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap (RatFunc K) L).injective
  letI : Differential L := Differential.differentialFiniteDimensional (RatFunc K) L
  letI : DifferentialAlgebra (RatFunc K) L := Differential.differentialAlgebraFiniteDimensional
  have sf : (algebraMap K (RatFunc K) s)^2= -3 := by rw [← map_pow,hs,map_neg,map_ofNat]
  have fn : f ≠ 0 := fun h => hf.nonconstant (by rw [h,map_zero])
  have gn : g ≠ 0 := fun h => hg.nonconstant (by rw [h,map_zero])
  obtain ⟨z,w,hz,hw⟩ := common_lifts sf fn gn
  rw [← IsScalarTower.algebraMap_apply K (RatFunc K) L] at hz hw
  exact ⟨z,w,hz,hw,common_field_rigidity hs hf.nonconstant hg.nonconstant hz hw
    (normalized_connections_equal hp hf hg)⟩

end
end AK14.SeriesAt
