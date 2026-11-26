import AK14.QuadraticGerms
import Mathlib.RingTheory.AdjoinRoot

/-! Irreducibility of all three successive radical steps (degrees 3, 2 and 2).
The two square tests use different local embeddings above the odd branch. -/
namespace AK14.SeriesAt
open Polynomial
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable {R E : Type*} [Field R] [Field E]

def radPoly (k : ℕ) (q : R) : R[X] := X^k-C q
abbrev Rad (k : ℕ) (q : R) := AdjoinRoot (radPoly k q)

def radicalLift {d : ℕ} {q : R} (ρ : R →+* E) (h : E) (eq : h^d=ρ q) :
    Rad d q →+* E :=
  AdjoinRoot.lift ρ h (by simp only [radPoly,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,eq,sub_self])

@[simp] theorem radicalLift_root {d : ℕ} {q : R} (ρ : R →+* E) (h : E) (eq : h^d=ρ q) :
    radicalLift ρ h eq (AdjoinRoot.root (radPoly d q))=h := AdjoinRoot.lift_root _

@[simp] theorem radicalLift_of {d : ℕ} {q : R} (ρ : R →+* E) (h : E) (eq : h^d=ρ q) (a : R) :
    radicalLift ρ h eq (AdjoinRoot.of (radPoly d q) a)=ρ a := AdjoinRoot.lift_of _

abbrev CubeField (f : RatFunc K) := Rad 3 (1-f)

def cubicT (s : K) (f : RatFunc K) [Fact (Irreducible (radPoly 3 (1-f)))] : CubeField f :=
  inverseContrast (AdjoinRoot.of _ (kRat K s)) (AdjoinRoot.root _)

theorem cubic_embedding {p : Passport} {f : RatFunc K} (hf : NormalizedCover p f)
    [Fact (Irreducible (radPoly 3 (1-f)))] {s b : K} (hs : s^2= -3) (hb : b^2=4) :
    ∃ (j : CubeField f →+* GermField K) (V : PowerSeries K),
      PowerSeries.constantCoeff (R := K) V=0 ∧ V≠0 ∧ V.order.toNat=p.a ∧
      j (cubicT s f)=constMap K b+embed K V := by
  obtain ⟨P,np,cp,op,e⟩ := hf.atA
  change expand 0 f=embed K P at e
  obtain ⟨H,V,hH,cv,nv,ov,iv⟩ := cubic_local_branch P np cp hs hb
  have h : (embed K H)^3=expand 0 (1-f) := by rw [← map_pow,hH,map_sub,map_sub,map_one,map_one,e]
  let j := radicalLift (expand 0) (embed K H) h
  refine ⟨j,V,cv,nv,ov.trans op,?_⟩
  rw [cubicT,inverseContrast,map_div₀ j,map_mul j,map_mul j,map_add j,map_sub j,map_one j,map_ofNat j]
  simp only [j,radicalLift_of,radicalLift_root,expand_scalar]
  exact iv

private theorem quadratic_test {q : R} (j : R →+* GermField K) {V : PowerSeries K}
    (nv : V≠0) (odd : ¬2∣V.order.toNat) (value : j q=embed K V) : Irreducible (radPoly 2 q) := by
  apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
  intro z hz
  have eq : (j z)^2=embed K V/embed K 1 := by rw [← map_pow,hz,value,map_one,div_one]
  have v := power_order_divides nv (Q := 1) one_ne_zero (by decide : 0<2) eq
  apply odd
  apply Int.natCast_dvd_natCast.mp
  simpa [PowerSeries.order_one] using v

theorem first_square_irreducible {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {f : RatFunc K} (hf : NormalizedCover p f) [Fact (Irreducible (radPoly 3 (1-f)))]
    {s : K} (hs : s^2= -3) : Irreducible (radPoly 2 (cubicT s f+2)) := by
  obtain ⟨j,V,_,nv,ov,ev⟩ := cubic_embedding hf hs (b := -2) (by norm_num)
  apply quadratic_test j nv (ov ▸ hp.a_odd)
  rw [map_add,map_ofNat,ev,map_neg,map_ofNat]
  ring

abbrev FirstSquare (s : K) (f : RatFunc K) [Fact (Irreducible (radPoly 3 (1-f)))] :=
  Rad 2 (cubicT s f+2)

theorem second_square_irreducible {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {f : RatFunc K} (hf : NormalizedCover p f) [Fact (Irreducible (radPoly 3 (1-f)))]
    {s : K} (hs : s^2= -3) [Fact (Irreducible (radPoly 2 (cubicT s f+2)))] :
    Irreducible (radPoly 2 (AdjoinRoot.of (radPoly 2 (cubicT s f+2)) (cubicT s f-2))) := by
  obtain ⟨j,V,cv,nv,ov,ev⟩ := cubic_embedding hf hs (b := 2) (by norm_num)
  have n4 : PowerSeries.constantCoeff (R := K) (V+4)≠0 := by simp only [map_add,map_ofNat,cv,zero_add]; norm_num
  obtain ⟨Y,y,_⟩ := LocalChart.unit_root (V+4) n4 (by decide : 0<2)
  have ye : (embed K Y)^2=j (cubicT s f+2) := by
    rw [← map_pow,y,map_add,map_ofNat,map_add,map_ofNat,ev,map_ofNat]
    ring
  let j₂ := radicalLift j (embed K Y) ye
  apply quadratic_test j₂ nv (ov ▸ hp.a_odd)
  rw [show j₂ _=j (cubicT s f-2) from radicalLift_of _ _ _ _,map_sub,map_ofNat,ev,map_ofNat]
  ring

end
end AK14.SeriesAt
