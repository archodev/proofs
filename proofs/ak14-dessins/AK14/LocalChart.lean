import AK14.FractionDeriv
import AK14.Ramification
import Mathlib.RingTheory.PowerSeries.Derivative

/-! The local order and the double-pole coefficient in an arbitrary regular
parameter X. Regularity is membership in the embedded power-series ring. -/
namespace AK14.LocalChart
open PowerSeries
open scoped PowerSeries
variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
noncomputable section

abbrev delta (K : Type*) [Field K] := PowerSeries.derivative K

def powerCoeff (K : Type*) [Field K] (e k : ℕ) : K := (1-((e:K)/k)^2)/2

variable (D : Derivation ℤ L L) (ι : K⟦X⟧ →+* L)
  (inj : Function.Injective ι) (comm : ∀ P, D (ι P)=ι (delta K P))

private theorem invert_image {P : K⟦X⟧} (h : constantCoeff (R := K) P ≠ 0) :
    ι P⁻¹ = (ι P)⁻¹ := by
  have e := congrArg ι (PowerSeries.mul_inv_cancel P h)
  rw [map_mul,map_one] at e
  exact (eq_inv_of_mul_eq_one_right e)

include inj comm in
theorem parameter_expansions (v : K⟦X⟧) (hv : constantCoeff (R := K) v ≠ 0) :
    let u := X*v
    D (ι u) ≠ 0 ∧ ι u ≠ 0 ∧
      ∃ H V : K⟦X⟧, schwarzian D (ι u) = ι H ∧
        ι X*(D (ι u)/ι u)=ι V ∧ constantCoeff (R := K) V=1 := by
  dsimp only
  let u : K⟦X⟧ := X*v
  let du := delta K u
  have cn : constantCoeff (R := K) du = constantCoeff (R := K) v := by
    dsimp only [du,u,delta]
    rw [(PowerSeries.derivative K).leibniz, PowerSeries.derivative_X]
    simp [smul_eq_mul]
  have hu : constantCoeff (R := K) du ≠ 0 := cn ▸ hv
  have un : v ≠ 0 := fun e => hv (by simp [e])
  have dun : du ≠ 0 := fun e => hu (by simp [e])
  have xn : ι X ≠ 0 := (map_ne_zero_iff ι inj).mpr PowerSeries.X_ne_zero
  have vn : ι v ≠ 0 := (map_ne_zero_iff ι inj).mpr un
  have vu : ι u ≠ 0 := by dsimp only [u]; rw [map_mul]; exact mul_ne_zero xn vn
  have ed : D (ι u)=ι du := comm _
  refine ⟨ed ▸ (map_ne_zero_iff ι inj).mpr dun,vu,?_⟩
  let h := delta K du*du⁻¹
  let reg := delta K h - C (R := K) (1/2)*h^2
  let V := du*v⁻¹
  have ep : preSch D (ι u)=ι h := by
    rw [preSch,ed,comm]
    dsimp only [h]
    rw [map_mul,invert_image ι hu,div_eq_mul_inv]
  have const : ι (C (R := K) (1/2)) = (1/2:L) := by
    change (ι.comp (C (R := K))) (1/2) = _
    rw [map_div₀,map_one,map_ofNat]
  refine ⟨reg,V,?_,?_,?_⟩
  · rw [schwarzian,ep,comm]
    dsimp only [reg]
    conv_rhs => simp only [map_sub ι,map_mul ι,map_pow ι,const]
    ring
  · rw [ed]
    dsimp only [u,V]; rw [map_mul,map_mul,invert_image ι hv]
    field_simp <;> ring
  · dsimp only [V]; rw [map_mul,constantCoeff_inv,cn,mul_inv_cancel₀ hv]

include inj comm in
theorem power_lift_double_coefficient (v : K⟦X⟧) (hv : constantCoeff (R := K) v ≠ 0)
    {w : L} {k e : ℕ} (hk : 0 < k) (he : 0 < e) (h : w^k=(ι (X*v))^e) :
    ∃ P : K⟦X⟧, (ι X)^2*schwarzian D w = ι P ∧
      constantCoeff (R := K) P = powerCoeff K e k := by
  obtain ⟨du,nu,H,V,hs,hv',cv⟩ := parameter_expansions D ι inj comm v hv
  have nw : w ≠ 0 := fun z => (pow_ne_zero e nu) (by rw [← h,z,zero_pow hk.ne'])
  set a := powerCoeff K e k
  have ca : ι (C (R := K) a)=powerCoeff L e k := by
    let ρ := ι.comp (C (R := K))
    change ρ ((1-((e:K)/k)^2)/2) = _
    simp only [map_div₀ ρ,map_sub ρ,map_one ρ,map_pow ρ,map_natCast ρ,map_ofNat ρ]
    rfl
  refine ⟨X^2*H+C (R := K) a*V^2,?_,?_⟩
  · rw [schwarzian_of_power_relation D nu nw du hk he h,hs]
    conv_rhs => simp only [map_add ι,map_mul ι,map_pow ι,ca]
    rw [← hv']
    unfold powerCoeff; ring
  · simp [cv]

include inj comm in
theorem ordinary_lift_regular (v : K⟦X⟧) (hv : constantCoeff (R := K) v ≠ 0)
    {w : L} {k : ℕ} (hk : 0 < k) (h : w^k=(ι (X*v))^k) :
    ∃ P : K⟦X⟧, schwarzian D w = ι P := by
  obtain ⟨du,nu,H,V,hs,_,_⟩ := parameter_expansions D ι inj comm v hv
  have nw : w ≠ 0 := fun z => (pow_ne_zero k nu) (by rw [← h,z,zero_pow hk.ne'])
  exact ⟨H,(schwarzian_regular_lift D nu nw du hk h).trans hs⟩

local instance (priority := 2000) (K : Type*) [Field K] : Algebra ℤ K⟦X⟧ := Ring.toIntAlgebra _

/-- The differential-embedding hypotheses are realized by the formal fraction field. -/
theorem fraction_chart_compatible (K : Type*) [Field K] (P : K⟦X⟧) :
    fractionDeriv (R := K⟦X⟧) (FractionRing K⟦X⟧) ((delta K).restrictScalars ℤ)
        (algebraMap K⟦X⟧ (FractionRing K⟦X⟧) P) =
      algebraMap _ (FractionRing K⟦X⟧) (delta K P) := fractionDeriv_map (R := K⟦X⟧) _ _ _

end
end AK14.LocalChart
