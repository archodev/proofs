import AK14.LocalSubstitution

/-! Covariance of the affine coordinate under every nonsingular Möbius
substitution, in both the finite and infinite source chart. -/
namespace AK14.SeriesAt
open Polynomial TetraQuotient
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def expandAt (x : Option K) : RatFunc K →+* GermField K :=
  match x with | some a => expand a | none => expandInf K

abbrev variableX (K : Type*) [Field K] := algebraMap K[X] (RatFunc K) X

@[simp] theorem expandAt_scalar (x : Option K) (a : K) : expandAt x (kRat K a)=constMap K a := by
  cases x with
  | some x => exact expand_scalar a x
  | none =>
    change expandInf K (algebraMap K[X] (RatFunc K) (C a))=_
    rw [expandInf_poly]; simp [reciprocalPoly]

theorem expandAt_X (x : Option K) : expandAt x (variableX K)=
    match x with | some a => constMap K a+t K | none => (t K)⁻¹ := by
  cases x with
  | some a =>
    change expand a (algebraMap K[X] (RatFunc K) X)=_
    rw [expand_polynomial]
    change embed K (taylor a X : PowerSeries K)=_
    rw [taylor_X,Polynomial.coe_add,Polynomial.coe_X,Polynomial.coe_C,map_add]
    exact add_comm _ _
  | none =>
    change expandInf K (algebraMap K[X] (RatFunc K) X)=_
    rw [expandInf_poly]; simp [reciprocalPoly]

def coordinate (m : Matrix2 K) : RatFunc K :=
  (kRat K m.a*variableX K+kRat K m.b)/(kRat K m.c*variableX K+kRat K m.d)

def direction : Option K → Pair K | some _ => (1,0) | none => (0,1)

def linearSeries (a b : K) : PowerSeries K := PowerSeries.C (R := K) a+PowerSeries.X*PowerSeries.C (R := K) b

@[simp] theorem linear_const (a b : K) : PowerSeries.constantCoeff (R := K) (linearSeries a b)=a := by simp [linearSeries]

@[simp] theorem embed_linear (a b : K) : embed K (linearSeries a b)=constMap K a+t K*constMap K b := by
  dsimp only [linearSeries]; rw [map_add,map_mul]; rfl

theorem coordinate_expansion (x : Option K) (m : Matrix2 K) :
    expandAt x (coordinate m)=
    embed K (linearSeries (m.act (rep x)).1 (m.act (direction x)).1)/
    embed K (linearSeries (m.act (rep x)).2 (m.act (direction x)).2) := by
  simp only [coordinate,map_div₀,map_add,map_mul,expandAt_scalar,expandAt_X,embed_linear]
  cases x with
  | some a =>
    simp only [rep,direction,Matrix2.act,one_mul,mul_one,mul_zero,add_zero,map_add,map_mul]
    congr 1 <;> ring
  | none =>
    simp only [rep,direction,Matrix2.act,one_mul,mul_one,mul_zero,zero_add,add_zero]
    rw [← mul_div_mul_left _ _ (t_ne (K := K))]
    congr 1 <;> field_simp [t_ne] <;> ring

private theorem linear_coordinate {a b c d : K} (det : c*b-a*d≠0) (valid : TetraQuotient.valid (a,b)) :
    ∃ (V : PowerSeries K) (nv : PowerSeries.constantCoeff (R := K) V≠0),
    embed K (linearSeries a c)/embed K (linearSeries b d)=
      reparam V nv (expandAt (point (a,b)) (variableX K)) := by
  classical
  let ρ := constMap K
  by_cases b0 : b=0
  · subst b
    have na : a≠0 := valid.resolve_right (not_not_intro rfl)
    have nd : d≠0 := by intro z; simp [z] at det
    let L := linearSeries a c
    have nL : PowerSeries.constantCoeff (R := K) L≠0 := (linear_const a c) ▸ na
    let V := PowerSeries.C (R := K) d*L⁻¹
    have inv : (L*L⁻¹)=1 := PowerSeries.mul_inv_cancel _ nL
    have ci : PowerSeries.constantCoeff (R := K) L⁻¹≠0 := by
      intro z; have h := congrArg (PowerSeries.constantCoeff (R := K)) inv; simp [z] at h
    have nv : PowerSeries.constantCoeff (R := K) V≠0 := by simpa only [V,map_mul,PowerSeries.constantCoeff_C] using mul_ne_zero nd ci
    refine ⟨V,nv,?_⟩
    rw [show point (a,(0:K))=none by simp [point],expandAt_X,map_inv₀,reparam_t]
    rw [show V=PowerSeries.C (R := K) d*L⁻¹ from rfl,map_mul (embed K),embed_unit_inv nL]
    change embed K L/embed K (linearSeries 0 d)=(t K*(ρ d*(embed K L)⁻¹))⁻¹
    rw [embed_linear 0 d,map_zero,zero_add]
    simp only [mul_inv_rev,inv_inv,div_eq_mul_inv]
    ring
  · let L := linearSeries b d
    have nL : PowerSeries.constantCoeff (R := K) L≠0 := (linear_const b d) ▸ b0
    let v := (c*b-a*d)/b
    have v0 : v≠0 := div_ne_zero det b0
    let V := PowerSeries.C (R := K) v*L⁻¹
    have inv : L*L⁻¹=1 := PowerSeries.mul_inv_cancel _ nL
    have ci : PowerSeries.constantCoeff (R := K) L⁻¹≠0 := by
      intro z; have h := congrArg (PowerSeries.constantCoeff (R := K)) inv; simp [z] at h
    have nv : PowerSeries.constantCoeff (R := K) V≠0 := by simpa only [V,map_mul,PowerSeries.constantCoeff_C] using mul_ne_zero v0 ci
    have nl : embed K L≠0 := (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)).mpr (fun z => nL (by simp [z]))
    have nb : ρ b≠0 := (map_ne_zero_iff ρ ρ.injective).mpr b0
    refine ⟨V,nv,?_⟩
    rw [show point (a,b)=some (a/b) by simp [point,b0],expandAt_X,map_add,reparam_const,reparam_t]
    rw [show V=PowerSeries.C (R := K) v*L⁻¹ from rfl,map_mul (embed K),embed_unit_inv nL]
    change embed K (linearSeries a c)/embed K L=ρ (a/b)+t K*(ρ v*(embed K L)⁻¹)
    rw [map_div₀ ρ,show v=(c*b-a*d)/b from rfl,map_div₀ ρ,map_sub ρ,map_mul ρ,map_mul ρ]
    field_simp [nl,nb]
    simp only [L,embed_linear,ρ,constMap,RingHom.comp_apply]
    ring

theorem projective_coordinate_germ (x : Option K) (m : Matrix2 K) (nd : m.det≠0) :
    ∃ (V : PowerSeries K) (nv : PowerSeries.constantCoeff (R := K) V≠0),
      expandAt x (coordinate m)=reparam V nv (expandAt (m.onSphere x) (variableX K)) := by
  have valid := m.valid nd (rep_valid x)
  have nz : bracket (m.act (direction x)) (m.act (rep x))≠0 := by
    rw [m.bracket]
    apply mul_ne_zero nd
    cases x <;> simp [direction,rep,bracket]
  rw [coordinate_expansion]
  exact linear_coordinate (by simpa only [bracket,mul_comm] using nz) valid

end
end AK14.SeriesAt
