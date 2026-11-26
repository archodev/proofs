import AK14.QuadraticGerms
import AK14.SourceFrame

/-! Changing the local parameter by t ↦ t times a unit preserves all branch
orders and preserves nonvanishing of the first ordinary derivative. -/
namespace AK14.SeriesAt
open PowerSeries
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def resub (V : K⟦X⟧) : K⟦X⟧ →ₐ[K] K⟦X⟧ :=
  MvPowerSeries.substAlgHom (R := K) (a := fun _ : Unit => X*V)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by change constantCoeff (R := K) (X*V)=0; simp))

@[simp] theorem resub_X (V : K⟦X⟧) : resub V X=X*V :=
  MvPowerSeries.substAlgHom_X _ ()

@[simp] theorem resub_C (V : K⟦X⟧) (c : K) : resub V (C (R := K) c)=C (R := K) c := (resub V).commutes c

theorem resub_const (V P : K⟦X⟧) : constantCoeff (R := K) (resub V P)=constantCoeff (R := K) P := by
  conv_lhs => rw [eq_X_mul_shift_add_const P]
  simp only [map_add,map_mul,resub_X,resub_C,constantCoeff_X,zero_mul,zero_add,constantCoeff_C]

theorem resub_factor (V P : K⟦X⟧) : resub V P=X^P.order.toNat*(V^P.order.toNat*resub V (divXPowOrder P)) := by
  conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := P)]
  rw [map_mul,map_pow,resub_X,mul_pow,mul_assoc]

theorem resub_order (V : K⟦X⟧) (nv : constantCoeff (R := K) V≠0) {P : K⟦X⟧} (np : P≠0) :
    (resub V P).order=P.order := by
  have unit : constantCoeff (R := K) (V^P.order.toNat*resub V (divXPowOrder P))≠0 := by
    rw [map_mul,map_pow,resub_const]
    exact mul_ne_zero (pow_ne_zero _ nv) (constantCoeff_divXPowOrder_eq_zero_iff.not.mpr np)
  have o : (V^P.order.toNat*resub V (divXPowOrder P)).order=0 :=
    nonpos_iff_eq_zero.mp (order_le 0 (by simpa only [coeff_zero_eq_constantCoeff] using unit))
  conv_lhs => rw [resub_factor V P,order_mul,o,add_zero,order_X_pow]
  exact coe_toNat_order np

theorem resub_injective (V : K⟦X⟧) (nv : constantCoeff (R := K) V ≠0) : Function.Injective (resub V) := by
  apply (injective_iff_map_eq_zero (resub V)).mpr
  intro P e
  by_contra n
  have h := resub_order V nv n
  rw [e,order_zero] at h
  exact n (order_eq_top.mp h.symm)

def reparam (V : K⟦X⟧) (nv : constantCoeff (R := K) V≠0) : GermField K →+* GermField K :=
  IsFractionRing.lift (g := (embed K).comp (resub V).toRingHom)
    ((IsFractionRing.injective (PowerSeries K) (GermField K)).comp (resub_injective V nv))

theorem reparam_embed (V : K⟦X⟧) (nv : constantCoeff (R := K) V≠0) (P : K⟦X⟧) :
    reparam V nv (embed K P)=embed K (resub V P) := IsFractionRing.lift_algebraMap _ _

theorem reparam_const (V : K⟦X⟧) (nv : constantCoeff (R := K) V≠0) (c : K) :
    reparam V nv (constMap K c)=constMap K c := by
  change reparam V nv (embed K (C (R := K) c))=_
  rw [reparam_embed,resub_C]; rfl

theorem reparam_t (V : K⟦X⟧) (nv : constantCoeff (R := K) V≠0) :
    reparam V nv (t K)=t K*embed K V := by
  change reparam V nv (embed K X)=_
  rw [reparam_embed,resub_X,map_mul]

theorem reparam_branch {V : K⟦X⟧} (nv : constantCoeff (R := K) V≠0) {z : GermField K} {j : Fin 3}
    {e : ℕ} (h : BranchGerm z j e) : BranchGerm (reparam V nv z) j e := by
  obtain ⟨P,np,cp,op,rfl⟩ := h
  refine ⟨resub V P,(map_ne_zero_iff _ (resub_injective V nv)).mpr np,(resub_const V P).trans cp,
    (congrArg ENat.toNat (resub_order V nv np)).trans op,?_⟩
  fin_cases j <;> simp [targetChart,reparam_embed]

theorem resub_derivative_const (V P : K⟦X⟧) :
    constantCoeff (R := K) (derivative K (resub V P))=constantCoeff (R := K) V*constantCoeff (R := K) (derivative K P) := by
  let Q : K⟦X⟧ := mk fun k => coeff (R := K) (k+1) P
  have e : P=X*Q+C (R := K) (constantCoeff (R := K) P) := eq_X_mul_shift_add_const P
  have c : constantCoeff (R := K) Q=constantCoeff (R := K) (derivative K P) := by
    simp only [← coeff_zero_eq_constantCoeff]
    simp [Q,PowerSeries.coeff_derivative]
  conv_lhs => rw [e]
  simp only [map_add,map_mul,resub_X,resub_C,derivative_C,map_zero,add_zero,
    Derivation.leibniz,smul_eq_mul,derivative_X,map_one,constantCoeff_X,zero_mul,zero_add,
    add_zero,mul_one,resub_const,c]
  ring

theorem reparam_ordinary {V : K⟦X⟧} (nv : constantCoeff (R := K) V≠0) {z : GermField K}
    (h : OrdinaryGerm z) : OrdinaryGerm (reparam V nv z) := by
  obtain ⟨P,rfl,p0,p1,pd⟩ := h
  exact ⟨resub V P,reparam_embed _ _ _,resub_const V P ▸ p0,resub_const V P ▸ p1,
    resub_derivative_const V P ▸ mul_ne_zero nv pd⟩

end
end AK14.SeriesAt
