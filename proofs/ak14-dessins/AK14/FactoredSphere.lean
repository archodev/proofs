import AK14.SphereDivisorRigidity
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace AK14.Gluing
open Complex Set Filter Topology Polynomial
noncomputable section

theorem exactOrder_one (z : ℂ) : exactOrder (fun _ => 1) z 0 :=
  ⟨fun _ => 1,analyticAt_const,one_ne_zero,Eventually.of_forall (fun _ => by simp)⟩

theorem exactOrder_mul {f g : ℂ → ℂ} {z : ℂ} {i j : ℤ} (hf : exactOrder f z i) (hg : exactOrder g z j) :
    exactOrder (fun w => f w*g w) z (i+j) := by
  obtain ⟨u,au,nu,eu⟩ := hf; obtain ⟨v,av,nv,ev⟩ := hg
  refine ⟨fun w => u w*v w,au.mul av,mul_ne_zero nu nv,?_⟩
  filter_upwards [eu,ev,puncture_avoids z z] with w hw hw' ne
  rw [hw,hw',zpow_add₀ (sub_ne_zero.mpr ne)]; ring

theorem linearFactor_order (a z : ℂ) (i : ℤ) :
    exactOrder (fun w => (w-a)^i) z (if a=z then i else 0) := by
  split_ifs with eq
  · subst z; exact ⟨fun _ => 1,analyticAt_const,one_ne_zero,Eventually.of_forall (fun _ => by simp)⟩
  · refine ⟨_,(analyticAt_id.sub analyticAt_const).zpow (sub_ne_zero.mpr (Ne.symm eq)),zpow_ne_zero i (sub_ne_zero.mpr (Ne.symm eq)),?_⟩
    filter_upwards with w; simp

theorem linearFactor_infty (a : ℂ) (i : ℤ) :
    exactOrder (fun w : ℂ => (w⁻¹-a)^i) 0 (-i) := by
  have nz : 1-a*(0:ℂ)≠0 := by simp
  have an : AnalyticAt ℂ (fun w : ℂ => 1-a*w) 0 := analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  refine ⟨fun w => (1-a*w)^i,an.zpow nz,zpow_ne_zero _ nz,?_⟩
  filter_upwards [puncture_avoids 0 0] with w hw
  rw [sub_zero,show w⁻¹-a=w⁻¹*(1-a*w) by field_simp [hw]]
  rw [mul_zpow,inv_zpow,zpow_neg]

def factorFunction (s : Finset ℂ) (m : ℂ → ℤ) (z : ℂ) : ℂ := ∏ a∈s,(z-a)^(m a)

theorem factor_order (s : Finset ℂ) (m : ℂ → ℤ) (z : ℂ) :
    exactOrder (factorFunction s m) z (if z∈s then m z else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [factorFunction,Finset.prod_empty,Finset.notMem_empty,if_false] using exactOrder_one z
  | @insert a s h ih =>
    change exactOrder (fun w => factorFunction (insert a s) m w) z _
    have H := exactOrder_mul (linearFactor_order a z (m a)) ih
    by_cases eq : a=z
    · subst a; simpa [factorFunction,h] using H
    · by_cases mem : z∈s <;> simpa [factorFunction,h,eq,ne_comm.mp eq,mem] using H

theorem factor_infty (s : Finset ℂ) (m : ℂ → ℤ) :
    exactOrder (factorFunction s m ∘ Inv.inv) 0 (-(∑ a∈s,m a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [factorFunction,Function.comp_def] using exactOrder_one 0
  | @insert a s h ih =>
    simpa [factorFunction,Function.comp_def,h,neg_add,add_comm] using exactOrder_mul (linearFactor_infty a (m a)) ih

def productPolynomial (s : Finset ℂ) (k : ℂ → ℕ) : ℂ[X] := ∏ a∈s,(X-C a)^(k a)

theorem productPolynomial_nonzero (s : Finset ℂ) (k : ℂ → ℕ) : productPolynomial s k≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun a _ => pow_ne_zero _ (X_sub_C_ne_zero a))

theorem productPolynomial_eval (s : Finset ℂ) (k : ℂ → ℕ) (z : ℂ) :
    (productPolynomial s k).eval z=∏ a∈s,(z-a)^(k a) := by
  simp [productPolynomial,eval_prod]

theorem factor_quotient (s : Finset ℂ) (m : ℂ → ℤ) (z : ℂ) :
    (productPolynomial s (fun a => (m a).toNat)).eval z/
    (productPolynomial s (fun a => (-(m a)).toNat)).eval z=factorFunction s m z := by
  rw [productPolynomial_eval,productPolynomial_eval,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl; intro a _
  cases eq : m a with
  | ofNat n => simp
  | negSucc n => simp [zpow_negSucc,Int.neg_negSucc]

theorem fraction_cofinite (A B : ℂ[X]) (nz : B≠0) :
    let f := (algebraMap ℂ[X] (RatFunc ℂ) A)/(algebraMap ℂ[X] (RatFunc ℂ) B)
    ∀ᶠ z in cofinite, f.num.eval z/f.denom.eval z=A.eval z/B.eval z := by
  let f := (algebraMap ℂ[X] (RatFunc ℂ) A)/(algebraMap ℂ[X] (RatFunc ℂ) B)
  have cross : f.num*B=A*f.denom := by
    apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
    rw [map_mul,map_mul]
    exact (div_eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)) (RatFunc.algebraMap_ne_zero nz)).mp (RatFunc.num_div_denom f)
  have non (P : ℂ[X]) (np : P≠0) : ∀ᶠ z in cofinite, P.eval z≠0 := by
    apply Filter.mem_cofinite.mpr
    simpa only [Set.compl_setOf,not_not,IsRoot] using P.finite_setOf_isRoot np
  filter_upwards [non _ (RatFunc.denom_ne_zero f),non B nz] with z hz bz
  change f.num.eval z/f.denom.eval z=_
  exact (div_eq_div_iff hz bz).mpr (by simpa only [eval_mul] using congrArg (Polynomial.eval z) cross)

/-- A meromorphic sphere function with a finite balanced divisor has a rational representative
at every punctured germ. The proof constructs a product of linear factors and uses Liouville. -/
theorem rational_of_balanced_divisor (f : ℂ → ℂ) (D : ℂ →₀ ℤ)
    (finite : ∀ z, exactOrder f z (D z)) (infty : exactOrder (f ∘ Inv.inv) 0 (-D.degree)) :
    ∃ r : RatFunc ℂ, ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, f w=r.num.eval w/r.denom.eval w := by
  classical
  let s := D.support
  let g := factorFunction s D
  have ordinary (z : ℂ) : exactOrder g z (D z) := by
    have h := factor_order s D z
    by_cases e : z∈s
    · simpa [e,g] using h
    · have d0 : D z=0 := by simpa [s] using e
      simpa [d0,e,g] using h
  obtain ⟨c,_,eq⟩ := sphere_functions_proportional (f:=f) (g:=g)
    (fun z => ⟨D z,finite z,ordinary z⟩) ⟨-D.degree,infty,factor_infty _ _⟩
  let A := productPolynomial s (fun a => (D a).toNat)
  let B := productPolynomial s (fun a => (-(D a)).toNat)
  let r := algebraMap ℂ[X] (RatFunc ℂ) (C c*A) / algebraMap ℂ[X] (RatFunc ℂ) B
  have co := fraction_cofinite (C c*A) B (productPolynomial_nonzero _ _)
  refine ⟨r,fun z => ?_⟩
  have le : 𝓝[≠] z ≤ cofinite := Filter.le_cofinite_iff_compl_singleton_mem.mpr (fun w => puncture_avoids z w)
  filter_upwards [eq z,co.filter_mono le] with w e h
  rw [e,h,eval_mul,eval_C,show g w=A.eval w/B.eval w from (factor_quotient s D w).symm]; ring

end
end AK14.Gluing
