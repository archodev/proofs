import AK14.GermRamification

/-! Three-point Schwarzian rigidity for normalized rational covers in both families.
All local hypotheses below are conditions on the rational function itself. -/
namespace AK14.SeriesAt
open Polynomial
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

structure NormalizedCover (p : Passport) (f : RatFunc K) : Prop where
  nonconstant : ratDeriv K f ≠ 0
  atA : BranchGerm (expand (0:K) f) 0 p.a
  atB : BranchGerm (expand (1:K) f) p.bSlot p.b
  atC : BranchGerm (expandInf K f) 2 p.c
  elsewhere : ∀ x : K, x ≠ 0 → x ≠ 1 →
    OrdinaryGerm (expand x f) ∨ ∃ j, BranchGerm (expand x f) j (branchOrder j)

private theorem shiftedDenom (x : K) :
    expand x (algebraMap K[X] (RatFunc K) (poleDenom K)) =
      (t K+constMap K x)^2*(t K+constMap K x-1)^2 := by
  rw [expand_polynomial]
  change embed K (poly x (X^2*(X-C 1)^2))=_
  have ex : poly x X=PowerSeries.X+PowerSeries.C (R := K) x := by
    change (taylor x X : PowerSeries K)=_
    rw [taylor_X,Polynomial.coe_add,Polynomial.coe_X,Polynomial.coe_C]
  rw [map_mul (poly x),map_pow (poly x),map_pow (poly x),map_sub (poly x),ex]
  simp only [C_1,map_one,map_mul,map_pow,map_sub,map_add,t,constMap,RingHom.comp_apply]

private theorem finite_zero_weight {r : RatFunc K} {H : PowerSeries K}
    (e : (t K)^2 * expand 0 r = embed K H) :
    expand 0 (r*algebraMap K[X] (RatFunc K) (poleDenom K)) =
      embed K (H*(PowerSeries.X-1)^2) := by
  rw [map_mul (expand (0:K)),shiftedDenom,map_zero,add_zero,map_mul (embed K),map_pow (embed K),
    map_sub (embed K),map_one (embed K),← e]
  ring

private theorem finite_one_weight {r : RatFunc K} {H : PowerSeries K}
    (e : (t K)^2 * expand 1 r = embed K H) :
    expand 1 (r*algebraMap K[X] (RatFunc K) (poleDenom K)) =
      embed K (H*(PowerSeries.X+1)^2) := by
  rw [map_mul (expand (1:K)),shiftedDenom,map_one,add_sub_cancel_right,map_mul (embed K),
    map_pow (embed K),map_add (embed K),map_one (embed K),← e]
  ring

theorem normalized_connection_numerator {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {f : RatFunc K} (hf : NormalizedCover p f) :
    ∃ P : K[X], P.natDegree ≤ 2 ∧ rationalConnection f=poleFraction P ∧
      P.eval 0=LocalChart.powerCoeff K p.a 2 ∧
      P.eval 1=LocalChart.powerCoeff K p.b 3 ∧
      P.coeff 2=LocalChart.powerCoeff K p.c 3 := by
  let r := rationalConnection f
  obtain ⟨A,hA,cA⟩ := branch_coefficient hp.a_pos hf.atA
  obtain ⟨B,hB,cB⟩ := branch_coefficient hp.b_pos hf.atB
  obtain ⟨J,hJ,cJ⟩ := branch_coefficient hp.c_pos hf.atC
  rw [← finite_connection] at hA hB
  have h0 := finite_zero_weight hA
  have h1 := finite_one_weight hB
  have infinity : expandInf K r/(t K)^2=embed K J := by
    rw [show r=rationalConnection f from rfl,infty_connection f hf.nonconstant,← hJ]
    field_simp [t_ne]
  have allFinite (x : K) : ∃ H : PowerSeries K,
      expand x (r*algebraMap K[X] (RatFunc K) (poleDenom K))=embed K H := by
    by_cases x0 : x=0
    · subst x; exact ⟨_,h0⟩
    by_cases x1 : x=1
    · subst x; exact ⟨_,h1⟩
    have regular : ∃ U : PowerSeries K, expand x r=embed K U := by
      rw [show r=rationalConnection f from rfl,finite_connection]
      rcases hf.elsewhere x x0 x1 with h | ⟨j,h⟩
      · exact unbranched_regular h
      · exact branch_regular h
    obtain ⟨U,hU⟩ := regular
    exact ⟨U*poly x (poleDenom K),by rw [map_mul (expand x),hU,expand_polynomial,map_mul (embed K)]⟩
  obtain ⟨P,⟨dP,frac⟩,_⟩ := normalized_of_local_bounds r allFinite (intDegree_of_infty_regular r ⟨_,infinity⟩)
  have cleared := (eq_div_iff (RatFunc.algebraMap_ne_zero (poleDenom_ne_zero (K := K)))).mp frac
  change r*algebraMap K[X] (RatFunc K) (poleDenom K)=algebraMap K[X] (RatFunc K) P at cleared
  have inject := IsFractionRing.injective (PowerSeries K) (GermField K)
  have a0 : poly (0:K) P=A*(PowerSeries.X-1)^2 := inject (by rw [← expand_polynomial,← cleared]; exact h0)
  have b1 : poly (1:K) P=B*(PowerSeries.X+1)^2 := inject (by rw [← expand_polynomial,← cleared]; exact h1)
  obtain ⟨H,hH,cH⟩ := poleFraction_at_infty P dP
  have c : H=J := inject (hH.symm.trans (frac ▸ infinity))
  refine ⟨P,dP,frac,?_,?_,?_⟩
  · have e := congrArg (PowerSeries.constantCoeff (R := K)) a0
    simpa [cA,branchOrder] using e
  · have e := congrArg (PowerSeries.constantCoeff (R := K)) b1
    have slot : branchOrder p.bSlot=3 := by cases h : p.family <;> simp [Passport.bSlot,h,branchOrder]
    simpa [cB,slot] using e
  · rw [← cH,c]
    exact cJ

/-- For all degrees, two normalized rational maps with the prescribed ramification
have exactly the same pulled-back tetrahedral projective connection. -/
theorem normalized_connections_equal {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {f g : RatFunc K} (hf : NormalizedCover p f) (hg : NormalizedCover p g) :
    rationalConnection f=rationalConnection g := by
  obtain ⟨P,dP,ep,a,b,c⟩ := normalized_connection_numerator hp hf
  obtain ⟨Q,dQ,eq,u,v,w⟩ := normalized_connection_numerator hp hg
  rw [ep,eq,threePole_unique P Q dP dQ (a.trans u.symm) (b.trans v.symm) (c.trans w.symm)]

end
end AK14.SeriesAt
