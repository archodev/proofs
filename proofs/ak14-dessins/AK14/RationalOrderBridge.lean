import AK14.FactoredSphere
import AK14.Public

namespace AK14.SeriesAt
open Complex Set Filter Topology Polynomial
open scoped PowerSeries
open Gluing (exactOrder puncture_avoids)
noncomputable section

def localArgument : Option ℂ → ℂ → ℂ
  | none => Inv.inv
  | some a => fun w => w+a

def localValue (x : Option ℂ) (f : RatFunc ℂ) := affineValue f ∘ localArgument x

theorem polynomial_local_parameter (x : Option ℂ) (p : ℂ[X]) (np : p≠0) :
    ∃ (i : ℤ) (U : ℂ[X]), U.eval 0≠0 ∧
      expandAt x (algebraMap ℂ[X] (RatFunc ℂ) p)=(t ℂ)^i*embed ℂ (U : PowerSeries ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), p.eval (localArgument x z)=z^i*U.eval z := by
  cases x with
  | some a =>
    let k := p.rootMultiplicity a
    obtain ⟨q,hq,nq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd np a
    change p=(X-C a)^k*q at hq
    have nr : q.eval a≠0 := fun h => nq (dvd_iff_isRoot.mpr h)
    refine ⟨k,taylor a q,by simpa [taylor_eval] using nr,?_,?_⟩
    · change expand a (algebraMap _ _ p)=_
      rw [expand_polynomial]
      have lin : poly a (X-C a)=(PowerSeries.X : PowerSeries ℂ) := by
        change (taylor a (X-C a) : PowerSeries ℂ)=_
        simp [taylor_apply,Polynomial.sub_comp,Polynomial.X_comp,Polynomial.C_comp]
      rw [hq,map_mul (poly a),map_pow (poly a),lin,map_mul (embed ℂ),map_pow (embed ℂ),zpow_natCast]; rfl
    · filter_upwards with z
      change p.eval (z+a)=_; rw [hq]; simp [taylor_eval]
  | none =>
    refine ⟨-(p.natDegree:ℤ),p.reverse,?_,?_,?_⟩
    · rw [←coeff_zero_eq_eval_zero,coeff_zero_reverse]; exact leadingCoeff_ne_zero.mpr np
    · change expandInf ℂ (algebraMap _ _ p)=_
      rw [expandInf_poly,reciprocalPoly_formula,zpow_neg,zpow_natCast,div_eq_mul_inv,mul_comm]
    · filter_upwards [puncture_avoids 0 0] with z nz
      letI : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero nz)
      have e := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (z⁻¹) p
      simpa [localArgument,invOf_eq_inv,zpow_neg,inv_pow,mul_comm] using e.symm

theorem rational_local_parameter (x : Option ℂ) (f : RatFunc ℂ) (nf : f≠0) :
    ∃ (i : ℤ) (U : PowerSeries ℂ), PowerSeries.constantCoeff (R := ℂ) U≠0 ∧
      expandAt x f=(t ℂ)^i*embed ℂ U ∧ exactOrder (localValue x f) 0 i := by
  obtain ⟨i,A,na,ea,la⟩ := polynomial_local_parameter x f.num (RatFunc.num_ne_zero nf)
  obtain ⟨j,B,nb,eb,lb⟩ := polynomial_local_parameter x f.denom f.denom_ne_zero
  have cb : PowerSeries.constantCoeff (R := ℂ) (B : PowerSeries ℂ)≠0 := by simpa only [Polynomial.constantCoeff_coe,coeff_zero_eq_eval_zero] using nb
  have ca : PowerSeries.constantCoeff (R := ℂ) (A : PowerSeries ℂ)≠0 := by simpa only [Polynomial.constantCoeff_coe,coeff_zero_eq_eval_zero] using na
  let U : PowerSeries ℂ := (A : PowerSeries ℂ)*(B : PowerSeries ℂ)⁻¹
  refine ⟨i-j,U,?_,?_,?_⟩
  · change PowerSeries.constantCoeff (R := ℂ) (_*_)≠0
    rw [map_mul,PowerSeries.constantCoeff_inv]; exact mul_ne_zero ca (inv_ne_zero cb)
  · conv_lhs => rw [←RatFunc.num_div_denom f]
    dsimp only [U]
    rw [map_div₀,ea,eb,map_mul (embed ℂ),embed_unit_inv cb,zpow_sub₀ t_ne]
    ring
  · refine ⟨fun w => A.eval w/B.eval w,((A.differentiable : Differentiable ℂ _).analyticAt _).div ((B.differentiable : Differentiable ℂ _).analyticAt _) nb,div_ne_zero na nb,?_⟩
    filter_upwards [la,lb,puncture_avoids 0 0] with w ha hb nz
    change f.num.eval _/f.denom.eval _=_
    rw [ha,hb,sub_zero,zpow_sub₀ nz]; ring

theorem exactOrder_unique {f : ℂ → ℂ} {z : ℂ} {i j : ℤ} (a : exactOrder f z i) (b : exactOrder f z j) : i=j := by
  obtain ⟨u,au,nu,eu⟩ := a; obtain ⟨v,av,nv,ev⟩ := b
  have mf : MeromorphicAt f z := MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨i,u,au,eu⟩
  have h := (meromorphicOrderAt_eq_int_iff mf).mpr ⟨u,au,nu,eu⟩
  have k := (meromorphicOrderAt_eq_int_iff mf).mpr ⟨v,av,nv,ev⟩
  exact WithTop.coe_injective (h.symm.trans k)

theorem nonzero_of_exactOrder {z : ℂ} {i : ℤ} {f : ℂ → ℂ} (h : exactOrder f z i) :
    ¬(f=ᶠ[𝓝[≠] z] 0) := by
  obtain ⟨u,au,nu,eu⟩ := h
  intro zero
  have un : ∀ᶠ w in 𝓝[≠] z, u w≠0 := mem_nhdsWithin_of_mem_nhds (au.continuousAt.tendsto.eventually (isOpen_ne.mem_nhds nu))
  obtain ⟨w,hw,h0,nw,dw⟩ := (eu.and (zero.and (un.and (puncture_avoids z z)))).exists
  exact mul_ne_zero (zpow_ne_zero _ (sub_ne_zero.mpr dw)) nw (hw.symm.trans h0)

theorem rational_power_germ {x : Option ℂ} {f : RatFunc ℂ} {e : ℕ}
    (order : exactOrder (localValue x f) 0 e) :
    ∃ V : PowerSeries ℂ, PowerSeries.constantCoeff (R := ℂ) V≠0 ∧ expandAt x f=embed ℂ (PowerSeries.X^e*V) := by
  have nf : f≠0 := by
    intro zero; subst f
    apply nonzero_of_exactOrder order
    filter_upwards with z; simp [localValue,affineValue]
  obtain ⟨i,V,nv,eq,ix⟩ := rational_local_parameter x f nf
  rw [exactOrder_unique ix order,zpow_natCast] at eq
  exact ⟨V,nv,by simpa only [map_mul,map_pow] using eq⟩

end
end AK14.SeriesAt
