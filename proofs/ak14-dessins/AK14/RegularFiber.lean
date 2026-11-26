import AK14.RegularPoints

/-! The finite fibers of the rational function at ordinary target values consist
of exactly deg(num) distinct affine points. The marked source infinity is a pole. -/
namespace AK14.SeriesAt
open Polynomial
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem normalized_pole_infty {p : Passport} {f : RatFunc K} (hf : NormalizedCover p f) :
    f.denom.natDegree<f.num.natDegree := by
  by_contra! le
  let P := f.num
  let Q := f.denom
  have cq : PowerSeries.constantCoeff (R := K) (Q.reverse : PowerSeries K)≠0 := by
    rw [Polynomial.constantCoeff_coe,coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr f.denom_ne_zero
  have nq : embed K (Q.reverse : PowerSeries K)≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)).mpr (fun z => cq (by simp [z]))
  have rep : expandInf K f=(embed K (P.reverse : PowerSeries K)/(t K)^P.natDegree)/
      (embed K (Q.reverse : PowerSeries K)/(t K)^Q.natDegree) := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [map_div₀,expandInf_poly,expandInf_poly,reciprocalPoly_formula,reciprocalPoly_formula]
  let m := Q.natDegree-P.natDegree
  have d : Q.natDegree=m+P.natDegree := (Nat.sub_add_cancel le).symm
  let W := (P.reverse : PowerSeries K)*(Q.reverse : PowerSeries K)⁻¹*PowerSeries.X^m
  have w : expandInf K f=embed K W := by
    rw [rep,d,pow_add]
    simp only [W,map_mul (embed K),map_pow (embed K),embed_unit_inv cq]
    change _=embed K (P.reverse : PowerSeries K)*(embed K (Q.reverse : PowerSeries K))⁻¹*(t K)^m
    field_simp [t_ne,nq]
  obtain ⟨V,nv,cv,_,e⟩ := hf.atC
  change expandInf K f=(embed K V)⁻¹ at e
  have vn := (map_ne_zero_iff (embed K) (IsFractionRing.injective (PowerSeries K) _)).mpr nv
  have prod : W*V=1 := (IsFractionRing.injective (PowerSeries K) (GermField K)) (by
    rw [map_mul (embed K),← w,e,inv_mul_cancel₀ vn,map_one])
  have c := congrArg (PowerSeries.constantCoeff (R := K)) prod
  simp [cv] at c

def fiberPoly (f : RatFunc K) (y : K) := f.num-C y*f.denom

abbrev AffineFiber (f : RatFunc K) (y : K) := {x : K // f.denom.eval x≠0 ∧ affineValue f x=y}

theorem fiber_roots {f : RatFunc K} {x y : K} :
    (fiberPoly f y).IsRoot x ↔ f.denom.eval x≠0 ∧ affineValue f x=y := by
  simp only [IsRoot.def,fiberPoly,eval_sub,eval_mul,eval_C,sub_eq_zero]
  constructor
  · intro e
    have n : f.denom.eval x≠0 := by
      intro z
      have cop := Polynomial.aeval_ne_zero_of_isCoprime (RatFunc.isCoprime_num_denom f) x
      change f.num.eval x≠0 ∨ f.denom.eval x≠0 at cop
      exact cop.elim (fun h => h (by rw [e,z,mul_zero])) (fun h => h z)
    exact ⟨n,(div_eq_iff n).mpr e⟩
  · rintro ⟨n,e⟩
    exact (div_eq_iff n).mp e

theorem fiber_degree {p : Passport} {f : RatFunc K} (hf : NormalizedCover p f) (y : K) :
    (fiberPoly f y).natDegree=f.num.natDegree :=
  natDegree_sub_eq_left_of_natDegree_lt (lt_of_le_of_lt (natDegree_C_mul_le _ _) (normalized_pole_infty hf))

theorem regular_sheets [IsAlgClosed K] {p : Passport} {f : RatFunc K} (hf : NormalizedCover p f)
    {y : K} (y0 : y≠0) (y1 : y≠1) : Nonempty (Fin f.num.natDegree ≃ AffineFiber f y) := by
  classical
  let P := fiberPoly f y
  have dp : P.natDegree=f.num.natDegree := fiber_degree hf y
  have d := normalized_pole_infty hf
  have np : P≠0 := by intro z; rw [z,natDegree_zero] at dp; omega
  have nd : P.roots.Nodup := by
    apply Multiset.nodup_iff_count_le_one.mpr
    intro x
    rw [count_roots]
    by_contra! m
    obtain ⟨root,r⟩ := (one_lt_rootMultiplicity_iff_isRoot np).mp m
    obtain ⟨dx,val⟩ := fiber_roots.mp root
    have no := good_deriv_ne hf (x := x) ⟨dx,val ▸ y0,val ▸ y1⟩
    apply no
    have eq : f.num.derivative.eval x-y*f.denom.derivative.eval x=0 := by
      simpa [P,fiberPoly,IsRoot.def,derivative_mul] using r
    have v := (div_eq_iff dx).mp val
    apply (_root_.div_eq_zero_iff).mpr; left
    linear_combination f.denom.eval x*eq-f.denom.derivative.eval x*v
  let roots : Finset K := ⟨P.roots,nd⟩
  have card : roots.card=f.num.natDegree := by
    have split : P.Splits := IsAlgClosed.splits _
    change P.roots.card=_
    simpa using (natDegree_eq_card_roots split).symm.trans dp
  have e : ↥roots ≃ AffineFiber f y := Equiv.subtypeEquivRight fun x => by
    change x ∈ P.roots ↔ _
    exact (mem_roots np).trans fiber_roots
  exact ⟨(Fintype.equivFinOfCardEq (show Fintype.card ↥roots=f.num.natDegree by simpa using card)).symm.trans e⟩

end
end AK14.SeriesAt
