import AK14.Ramification
import AK14.TetraQuotient

/-! The tetrahedral projective connection, computed directly for the explicit
degree-twelve quotient. Its coefficient depends on the base function alone. -/
namespace AK14
variable {K : Type*} [Field K] [CharZero K] (D : Derivation ℤ K K)

@[local simp] private theorem d2 : D (2:K) = 0 := by simpa only [Nat.cast_ofNat] using D.map_natCast 2
@[local simp] private theorem d3 : D (3:K) = 0 := by simpa only [Nat.cast_ofNat] using D.map_natCast 3

def contrast (a x : K) := (x-a)/(x+a)

theorem contrast_mobius {a x : K} (ha : a ≠ 0) (da : D a = 0) (den : x+a ≠ 0) :
    ConstantMobius D x (contrast a x) := by
  refine ⟨1,-a,1,a,D.map_one_eq_zero,by simp [da],D.map_one_eq_zero,da,?_,by simpa using den,?_⟩
  · simp only [one_mul,mul_one,sub_neg_eq_add]
    exact fun e => ha (by have : (2:K)*a=0 := by linear_combination e
                          exact (mul_eq_zero.mp this).resolve_left (by norm_num))
  · simp [contrast,sub_eq_add_neg]

theorem contrast_deriv {a x : K} (da : D a = 0) (den : x+a ≠ 0) :
    D (contrast a x) = 2*a*D x/(x+a)^2 := by
  rw [contrast,quotient_deriv _ _ _ den,map_sub,map_add,da]
  ring

theorem d_square (x : K) : D (x^2) = 2*x*D x := by rw [pow_two,times_deriv]; ring

private theorem not_const {x c : K} (dx : D x ≠ 0) (dc : D c = 0) : x ≠ c :=
  fun e => dx (e ▸ dc)

private theorem square_root_formula {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (dy : D y ≠ 0) (e : x^2=y) :
    schwarzian D x = schwarzian D y + 3/8*(D y/y)^2 := by
  have h := schwarzian_of_power_relation (e := 1) D hy hx dy (by decide : 0 < 2)
    (by decide) (by simpa using e)
  norm_num at h ⊢
  exact h

/-- Pullback through z ↦ v=z² ↦ t=v+1/v. -/
theorem klein_schwarzian (z : K) (dz : D z ≠ 0) :
    let v := z^2
    let t := v+v⁻¹
    schwarzian D z = schwarzian D t + (3/8)*((t^2+12)/(t^2-4)^2)*(D t)^2 := by
  dsimp only
  let v := z^2
  let t := v+v⁻¹
  change schwarzian D z = schwarzian D t + _
  have nz : z ≠ 0 := not_const D dz (map_zero D)
  have nv : v ≠ 0 := pow_ne_zero _ nz
  have dv : D v ≠ 0 := by
    dsimp only [v]; rw [d_square]; exact mul_ne_zero (mul_ne_zero (by norm_num) nz) dz
  have vp : v+1 ≠ 0 := by
    intro e; apply not_const D dv (by simp : D (-1 : K)=0); linear_combination e
  have vm : v-1 ≠ 0 := sub_ne_zero.mpr (not_const D dv D.map_one_eq_zero)
  have vm2 : v^2-1 ≠ 0 := by
    rw [show v^2-1=(v-1)*(v+1) by ring]; exact mul_ne_zero vm vp
  have dt : D t = (v^2-1)/v^2*D v := by
    dsimp only [t]
    rw [map_add,D.leibniz_inv]
    simp only [smul_eq_mul]
    field_simp; ring
  have dtn : D t ≠ 0 := dt ▸ mul_ne_zero (div_ne_zero vm2 (pow_ne_zero _ nv)) dv
  have tp : t+2 ≠ 0 := by
    intro e; apply not_const D dtn (by simp : D (-2 : K)=0); linear_combination e
  have tm : t-2 ≠ 0 := sub_ne_zero.mpr (not_const D dtn (by simp))
  have tp4 : t^2-4 ≠ 0 := by
    rw [show t^2-4=(t-2)*(t+2) by ring]; exact mul_ne_zero tm tp
  let u := contrast 1 v
  let m := contrast 2 t
  have nu : u ≠ 0 := div_ne_zero vm vp
  have nm : m ≠ 0 := div_ne_zero tm tp
  have dm : D m = 4*D t/(t+2)^2 := by
    rw [show m=contrast 2 t from rfl,contrast_deriv D (by simp) tp]; ring
  have dmn : D m ≠ 0 := dm ▸ div_ne_zero (mul_ne_zero (by norm_num) dtn) (pow_ne_zero _ tp)
  have rel : u^2=m := by
    have plus : t+2=(v+1)^2/v := by dsimp [t]; field_simp; ring
    have minus : t-2=(v-1)^2/v := by dsimp [t]; field_simp; ring
    dsimp only [u,m,contrast]
    rw [plus,minus]
    field_simp
  have s1 := square_root_formula D nz nv dv (rfl : z^2=v)
  have s2 := square_root_formula D nu nm dmn rel
  have su : schwarzian D u = schwarzian D v :=
    schwarzian_eq_of_constantMobius D dv (contrast_mobius D one_ne_zero D.map_one_eq_zero vp)
  have sm : schwarzian D m = schwarzian D t :=
    schwarzian_eq_of_constantMobius D dtn (contrast_mobius D (by norm_num) (by simp) tp)
  have lg : D m/m = 4*D t/(t^2-4) := by
    rw [dm,show m=(t-2)/(t+2) from rfl]
    field_simp
    ring
  have sq : (D v/v)^2 = (D t)^2/(t^2-4) := by
    rw [dt,eq_div_iff tp4]
    dsimp only [t]
    field_simp
    ring
  rw [su,sm,lg] at s2
  rw [s1,s2,sq]
  change _ = schwarzian D t + (3/8)*((t^2+12)/(t^2-4)^2)*(D t)^2
  field_simp
  ring

/-- The coefficient for exponent differences 1/2, 1/3, 1/3 at 0,1,∞. -/
def tetraPotential (f : K) : K := 4/(9*(1-f)^2)+3/(8*f^2*(1-f))

/-- The explicit tetrahedral quotient in a generic affine chart. -/
def tetraMap (s z : K) : K :=
  let v := z^2
  1-(contrast (2*s) (v+v⁻¹))^3

theorem tetraMap_schwarzian {s z : K} (hs : s^2 = -3) (dz : D z ≠ 0) :
    schwarzian D z = schwarzian D (tetraMap s z) +
      tetraPotential (tetraMap s z) * (D (tetraMap s z))^2 := by
  have sn : s ≠ 0 := by intro e; norm_num [e] at hs
  have ds : D s = 0 := by
    have e := congrArg D hs
    rw [d_square] at e
    simp at e
    exact e.resolve_left sn
  let v := z^2
  let t := v+v⁻¹
  let h := contrast (2*s) t
  let f := tetraMap s z
  change schwarzian D z = schwarzian D f + tetraPotential f * (D f)^2
  have nz := not_const D dz (map_zero D)
  have nv : v ≠ 0 := pow_ne_zero _ nz
  have dv : D v ≠ 0 := by
    dsimp only [v]; rw [d_square]; exact mul_ne_zero (mul_ne_zero (by norm_num) nz) dz
  have dtn : D t ≠ 0 := by
    have vm := sub_ne_zero.mpr (not_const D dv D.map_one_eq_zero)
    have vp : v+1 ≠ 0 := by
      intro e; apply not_const D dv (by simp : D (-1 : K)=0); linear_combination e
    have e : D t = (v-1)*(v+1)*D v/v^2 := by
      dsimp [t]; rw [map_add,D.leibniz_inv]; simp only [smul_eq_mul]; field_simp; ring
    exact e ▸ div_ne_zero (mul_ne_zero (mul_ne_zero vm vp) dv) (pow_ne_zero _ nv)
  have d2s : D (2*s) = 0 := by rw [times_deriv,ds]; simp
  have neg : t-2*s ≠ 0 := sub_ne_zero.mpr (not_const D dtn d2s)
  have pos : t+2*s ≠ 0 := by
    intro e; apply not_const D dtn (by rw [map_neg,d2s,neg_zero] : D (-(2*s))=0); linear_combination e
  have four : t^2-4 ≠ 0 := by
    rw [show t^2-4=(t-2)*(t+2) by ring]
    apply mul_ne_zero (sub_ne_zero.mpr (not_const D dtn (by simp)))
    intro e; apply not_const D dtn (by simp : D (-2 : K)=0); linear_combination e
  have hn : h ≠ 0 := div_ne_zero neg pos
  have dh : D h = 4*s*D t/(t+2*s)^2 := by
    rw [show h=contrast (2*s) t from rfl,contrast_deriv D d2s pos]; ring
  have dhn : D h ≠ 0 := dh ▸ div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) sn) dtn)
    (pow_ne_zero _ pos)
  have df : D f = -3*h^2*D h := by
    change D (1-h^3) = _
    rw [map_sub,D.map_one_eq_zero,pow_succ h 2,times_deriv,d_square]; ring
  have dfn : D f ≠ 0 := df ▸ mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hn)) dhn
  have fn : f ≠ 0 := not_const D dfn (map_zero D)
  have fone : 1-f=h^3 := by change 1-(1-h^3)=_; ring
  have onef : 1-f ≠ 0 := fone ▸ pow_ne_zero _ hn
  have dop : D (1-f) = -D f := by rw [map_sub,D.map_one_eq_zero,zero_sub]
  have hs1 := schwarzian_of_power_relation (e := 1) D onef hn (by rw [dop]; exact neg_ne_zero.mpr dfn)
    (by decide : 0 < 3) (by decide) (by simpa using fone.symm)
  have sf : schwarzian D (1-f) = schwarzian D f := by
    convert schwarzian_affine D (-1) 1 f (by norm_num) dfn (by simp) D.map_one_eq_zero using 2 <;> ring
  rw [sf,dop] at hs1
  norm_num at hs1
  have st : schwarzian D h = schwarzian D t :=
    schwarzian_eq_of_constantMobius D dtn (contrast_mobius D (mul_ne_zero (by norm_num) sn) d2s pos)
  have fnum : f = 12*s*(t^2-4)/(t+2*s)^3 := by
    change 1-((t-2*s)/(t+2*s))^3=_
    field_simp
    linear_combination 16*s*hs
  have pair : h*(t+2*s)^2=t^2+12 := by
    change ((t-2*s)/(t+2*s))*(t+2*s)^2=_
    rw [pow_two,← mul_assoc,div_mul_cancel₀ _ pos]
    linear_combination -4*hs
  have ratio : 3*D h/f = (t+2*s)*D t/(t^2-4) := by
    rw [dh,fnum]
    field_simp
    ring
  have rewriteRatio : (D f)^2/(f^2*(1-f)) = h*(3*D h/f)^2 := by
    rw [df,fone]
    field_simp
  have weight : (t^2+12)/(t^2-4)^2*(D t)^2 = (D f)^2/(f^2*(1-f)) := by
    rw [rewriteRatio,ratio,← pair,div_pow]
    ring
  have sk := klein_schwarzian D z dz
  change schwarzian D z = schwarzian D t + (3/8)*((t^2+12)/(t^2-4)^2)*(D t)^2 at sk
  rw [mul_assoc,weight,← st,hs1] at sk
  rw [sk]
  unfold tetraPotential
  rw [add_assoc]
  congr 1
  generalize 1-f=w at onef ⊢
  field_simp [fn,onef]

end AK14
