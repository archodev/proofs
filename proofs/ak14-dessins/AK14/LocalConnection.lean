import AK14.LocalChart
import AK14.Pullback

/-! Direct computation of the marked and ordinary ramification terms for a
rational projective connection. Its target-chart remainder can have a simple pole. -/
namespace AK14
open PowerSeries
open scoped PowerSeries
noncomputable section

variable {L : Type*} [Field L] [CharZero L] (D : Derivation ℤ L L)

def connection (k : ℕ) (W y : L) : L := schwarzian D y +
    LocalChart.powerCoeff L 1 k*(D y/y)^2+W*y*(D y/y)^2

def pullConnection (f : L) : L := schwarzian D f+tetraPotential f*(D f)^2

theorem connection_power {u : L} {e k : ℕ} (nu : u ≠ 0) (du : D u ≠ 0) (he : 0<e)
    (hk : 0<k) (W : L) :
    connection D k W (u^e) = schwarzian D u +
      LocalChart.powerCoeff L e k * (D u/u)^2 + W*(e:L)^2*u^e*(D u/u)^2 := by
  have h := schwarzian_of_power_relation (w := u^e) (u := u) (e := e) (k := 1)
    D nu (pow_ne_zero _ nu) du (by decide) he (pow_one _)
  rw [connection,h,logD_pow D u nu e]
  have kn : (k:L) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  generalize D u/u=v
  unfold LocalChart.powerCoeff
  simp only [Nat.cast_one,div_one,div_pow]
  field_simp [kn]
  ring

/-- The regular part times the local target coordinate in each of the three charts. -/
def chartRemainder (j : Fin 3) (y : L) : L :=
  ![(5*y+27)/(72*(1-y)^2),3/(8*(1-y)^2),(37-5*y)/(72*(1-y)^2)] j

theorem chart_zero {y : L} (ny : y ≠ 0) (one : 1-y ≠ 0) :
    pullConnection D y = connection D 2 (chartRemainder 0 y) y := by
  unfold pullConnection connection tetraPotential LocalChart.powerCoeff
  change _ = _ + _ + ((5*y+27)/(72*(1-y)^2))*y*(D y/y)^2
  generalize D y = v
  field_simp [ny,one]
  ring

theorem chart_one {y : L} (ny : y ≠ 0) (one : 1-y ≠ 0) (dy : D y ≠ 0) :
    pullConnection D (1-y) = connection D 3 (chartRemainder 1 y) y := by
  have sf : schwarzian D (1-y) = schwarzian D y := by
    convert schwarzian_affine D (-1) 1 y (by norm_num) dy (by simp) D.map_one_eq_zero using 2 <;> ring
  unfold pullConnection connection tetraPotential LocalChart.powerCoeff
  rw [sf,map_sub,D.map_one_eq_zero,zero_sub,sub_sub_cancel]
  change _ = _ + _ + (3/(8*(1-y)^2))*y*(D y/y)^2
  generalize D y = v
  field_simp [ny,one]
  ring

theorem chart_infty {y : L} (ny : y ≠ 0) (one : 1-y ≠ 0) (dy : D y ≠ 0) :
    pullConnection D y⁻¹ = connection D 3 (chartRemainder 2 y) y := by
  have e : 1-y⁻¹= -(1-y)/y := by field_simp <;> ring
  unfold pullConnection connection tetraPotential LocalChart.powerCoeff
  rw [schwarzian_inv D y ny dy,D.leibniz_inv,e]
  simp only [smul_eq_mul]
  change _ = _ + _ + ((37-5*y)/(72*(1-y)^2))*y*(D y/y)^2
  generalize D y = v
  rw [add_assoc]
  congr 1
  simp only [Nat.cast_one, Nat.cast_ofNat,div_pow, inv_pow]
  generalize hw : 1-y=t at one ⊢
  field_simp [ny,one]
  rw [← hw]
  ring

namespace LocalChart
variable {K : Type*} [Field K] [CharZero K] (ι : K⟦X⟧ →+* L) (inj : Function.Injective ι)
    (comm : ∀ P, D (ι P)=ι (delta K P))

private theorem mapCoeff (e k : ℕ) :
    ι (C (R := K) (powerCoeff K e k)) = powerCoeff L e k := by
  let ρ := ι.comp (C (R := K))
  change ρ ((1-((e:K)/k)^2)/2)=_
  simp only [map_div₀ ρ,map_sub ρ,map_one ρ,map_pow ρ,map_natCast ρ,map_ofNat ρ]
  rfl

include inj comm in
theorem connection_double_coefficient (v W : K⟦X⟧) (hv : constantCoeff (R := K) v ≠ 0)
    {e k : ℕ} (he : 0<e) (hk : 0<k) :
    ∃ P : K⟦X⟧, (ι X)^2*connection D k (ι W) ((ι (X*v))^e)=ι P ∧
      constantCoeff (R := K) P=powerCoeff K e k := by
  obtain ⟨du,nu,H,V,hs,hv',cv⟩ := parameter_expansions D ι inj comm v hv
  refine ⟨X^2*H+C (R := K) (powerCoeff K e k)*V^2+W*(e:K⟦X⟧)^2*(X*v)^e*V^2,?_,?_⟩
  · rw [connection_power D nu du he hk,hs]
    conv_rhs => simp only [map_add ι,map_mul ι,map_pow ι,map_natCast ι,mapCoeff]
    rw [← hv',map_mul ι X v]
    ring
  · simp [cv,zero_pow he.ne']

include inj comm in
theorem connection_ordinary (v W : K⟦X⟧) (hv : constantCoeff (R := K) v ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) :
    ∃ P : K⟦X⟧, connection D k (ι W) ((ι (X*v))^k)=ι P := by
  obtain ⟨du,nu,H,V,hs,_,_⟩ := parameter_expansions D ι inj comm v hv
  have pos : 0<k := by omega
  have nk : (k:L) ≠ 0 := Nat.cast_ne_zero.mpr pos.ne'
  refine ⟨H+W*(k:K⟦X⟧)^2*(X*v)^(k-2)*(delta K (X*v))^2,?_⟩
  rw [connection_power D nu du pos pos,hs]
  simp only [powerCoeff,div_self nk,one_pow,sub_self,zero_div,zero_mul,add_zero]
  conv_rhs => simp only [map_add ι,map_mul ι,map_pow ι,map_natCast ι]
  have e : (ι (X*v))^k = (ι (X*v))^(k-2)*(ι (X*v))^2 := by
    rw [← pow_add,Nat.sub_add_cancel hk]
  rw [e,comm]
  conv_lhs => rw [map_mul ι X v]
  have nu' : ι X * ι v ≠ 0 := by simpa only [map_mul ι] using nu
  have nx := left_ne_zero_of_mul nu'
  have nv := right_ne_zero_of_mul nu'
  field_simp [nx,nv] <;> ring

end LocalChart
end
end AK14
