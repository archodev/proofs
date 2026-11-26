import AK14.RationalOrderBridge

namespace AK14.SeriesAt
open Complex Polynomial Filter Topology
open scoped PowerSeries
open Gluing (exactOrder puncture_avoids)
noncomputable section

def rationalTargetChart (j : Fin 3) (f : RatFunc ℂ) := ![f,1-f,f⁻¹] j
def scalarTargetChart (j : Fin 3) (z : ℂ) := ![z,1-z,z⁻¹] j

theorem localArgument_cofinite (x : Option ℂ) : Tendsto (localArgument x) (𝓝[≠] (0:ℂ)) cofinite := by
  have inj : Function.Injective (localArgument x) := by
    cases x with
    | none => exact inv_injective
    | some a => exact fun _ _ h => add_right_cancel h
  exact inj.tendsto_cofinite.mono_left (Filter.le_cofinite_iff_eventually_ne.mpr (puncture_avoids 0))

theorem denominator_cofinite (f : RatFunc ℂ) : ∀ᶠ w in cofinite, f.denom.eval w≠0 := by
  apply Filter.mem_cofinite.mpr
  simpa only [Set.compl_setOf,not_not,IsRoot] using Polynomial.finite_setOf_isRoot f.denom_ne_zero

theorem eval_affine_cofinite (a b : ℂ) (f : RatFunc ℂ) :
    affineValue (kRat ℂ a*f+kRat ℂ b)=ᶠ[cofinite] (fun w => a*affineValue f w+b) := by
  let p := f.num; let q := f.denom
  let A := C a*p+C b*q
  have nz := RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have rep : kRat ℂ a*f+kRat ℂ b=algebraMap ℂ[X] (RatFunc ℂ) A/algebraMap ℂ[X] (RatFunc ℂ) q := by
    apply (eq_div_iff nz).mpr
    change _=algebraMap _ _ (C a*f.num+C b*f.denom)
    rw [map_add,map_mul,map_mul,add_mul,mul_assoc]
    rw [(div_eq_iff nz).mp (RatFunc.num_div_denom f)]
    rfl
  have eq := Gluing.fraction_cofinite A q f.denom_ne_zero
  filter_upwards [eq,denominator_cofinite f] with w hw non
  rw [rep]; change _/_=_; rw [hw]
  change (C a*p+C b*q).eval w/q.eval w=a*(p.eval w/q.eval w)+b
  simp only [eval_add,eval_mul,eval_C]; field_simp [show q.eval w≠0 from non]

theorem eval_inverse_cofinite (f : RatFunc ℂ) :
    affineValue f⁻¹=ᶠ[cofinite] (fun w => (affineValue f w)⁻¹) := by
  by_cases zero : f=0
  · subst f; filter_upwards with w; simp [affineValue]
  · have rep : f⁻¹=algebraMap ℂ[X] (RatFunc ℂ) f.denom/algebraMap ℂ[X] (RatFunc ℂ) f.num := by
      conv_lhs => rw [←RatFunc.num_div_denom f]
      rw [inv_div]
    have eq := Gluing.fraction_cofinite f.denom f.num (RatFunc.num_ne_zero zero)
    filter_upwards [eq] with w hw
    rw [rep]; change _/_=_; rw [hw]; exact (inv_div _ _).symm

theorem localTarget_germ (x : Option ℂ) (j : Fin 3) (f : RatFunc ℂ) :
    localValue x (rationalTargetChart j f)=ᶠ[𝓝[≠] 0] scalarTargetChart j ∘ localValue x f := by
  fin_cases j
  · rfl
  · change ∀ᶠ w in 𝓝[≠] 0, affineValue (1-f) (localArgument x w)=1-affineValue f (localArgument x w)
    have eq := (localArgument_cofinite x).eventually (eval_affine_cofinite (-1) 1 f)
    simpa [sub_eq_add_neg,add_comm] using eq
  · exact (localArgument_cofinite x).eventually (eval_inverse_cofinite f)

theorem branch_of_order {x : Option ℂ} {f : RatFunc ℂ} {j : Fin 3} {e : ℕ} (pos : 0<e)
    (h : exactOrder (scalarTargetChart j ∘ localValue x f) 0 e) : BranchGerm (expandAt x f) j e := by
  obtain ⟨u,au,nu,eq⟩ := h
  obtain ⟨V,nv,exp⟩ := rational_power_germ (x:=x) (f:=rationalTargetChart j f) (e:=e)
    ⟨u,au,nu,(localTarget_germ x j f).trans eq⟩
  let P := (PowerSeries.X : PowerSeries ℂ)^e*V
  have v : V≠0 := fun zero => nv (by rw [zero,map_zero])
  have ord : P.order.toNat=e := by
    rw [show P=PowerSeries.X^e*V from rfl,PowerSeries.order_mul,PowerSeries.order_X_pow,
      PowerSeries.order_zero_of_unit ((PowerSeries.isUnit_iff_constantCoeff).mpr (isUnit_iff_ne_zero.mpr nv)),add_zero]
    simp
  have cp : PowerSeries.constantCoeff (R := ℂ) P=0 := by simp [P,pos.ne']
  refine ⟨P,mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) v,cp,ord,?_⟩
  fin_cases j
  · exact exp
  · change expandAt x (1-f)=embed ℂ P at exp
    change expandAt x f=1-embed ℂ P
    rw [map_sub,map_one] at exp; rw [←exp]; ring
  · change expandAt x f⁻¹=embed ℂ P at exp
    rw [map_inv₀] at exp; change expandAt x f=(embed ℂ P)⁻¹; rw [←exp,inv_inv]

theorem ordinary_of_order {x : Option ℂ} {f : RatFunc ℂ} {c : ℂ} (c0 : c≠0) (c1 : c≠1)
    (h : exactOrder (fun w => localValue x f w-c) 0 1) : OrdinaryGerm (expandAt x f) := by
  have ev := (localArgument_cofinite x).eventually (eval_affine_cofinite 1 (-c) f)
  have E : localValue x (f-kRat ℂ c)=ᶠ[𝓝[≠] 0] (fun w => localValue x f w-c) := by
    simpa [sub_eq_add_neg,localValue,Function.comp_def] using ev
  obtain ⟨u,au,nu,eq⟩ := h
  obtain ⟨V,nv,exp⟩ := rational_power_germ (x:=x) (f:=f-kRat ℂ c) (e:=1) ⟨u,au,nu,E.trans eq⟩
  let P := PowerSeries.X*V+PowerSeries.C (R := ℂ) c
  have co : PowerSeries.constantCoeff (R := ℂ) P=c := by simp [P]
  refine ⟨P,?_,co ▸ c0,co ▸ c1,?_⟩
  · rw [map_sub,expandAt_scalar,pow_one] at exp
    change _=embed ℂ (_+_); rw [map_add,←exp]; change _= _ - constMap ℂ c + constMap ℂ c; ring
  · simpa [P,Derivation.leibniz,smul_eq_mul] using nv

end
end AK14.SeriesAt
