import AK14.LocalConnection

/-! Change of independent variable for the Schwarzian and for the tetrahedral
projective connection. Inversion has zero Schwarzian correction. -/
namespace AK14
variable {F L : Type*} [Field F] [CharZero F] [Field L] [CharZero L]
variable (D : Derivation ℤ F F)

theorem schwarzian_scaled {a f : F} (ha : a ≠ 0) (hf : D f ≠ 0) :
    schwarzian (a • D) f = a^2*schwarzian D f + a*D (D a)-(D a)^2/2 := by
  have pre : preSch (a • D) f = D a + a*preSch D f := by
    change a*D (a*D f)/(a*D f)=D a+a*(D (D f)/D f)
    rw [times_deriv]
    field_simp
    ring
  unfold schwarzian
  rw [pre,Derivation.smul_apply,smul_eq_mul,map_add,times_deriv]
  ring

theorem schwarzian_map (E : Derivation ℤ L L) (ι : F →+* L)
    (comm : ∀ x, E (ι x)=ι (D x)) (f : F) :
    ι (schwarzian D f)=schwarzian E (ι f) := by
  have pre : ι (preSch D f)=preSch E (ι f) := by
    simp only [preSch,map_div₀ ι,comm]
  unfold schwarzian
  rw [map_sub ι,map_div₀ ι,map_pow ι,map_ofNat ι,← pre,comm]

theorem pullConnection_map (E : Derivation ℤ L L) (ι : F →+* L)
    (comm : ∀ x, E (ι x)=ι (D x)) (f : F) :
    ι (pullConnection D f)=pullConnection E (ι f) := by
  unfold pullConnection tetraPotential
  simp only [map_add ι,map_mul ι,map_pow ι,map_div₀ ι,map_sub ι,map_one ι,map_ofNat ι,
    schwarzian_map D E ι comm,comm]

theorem pullConnection_inversion_scale {t f : F} (dt : D t=1) (df : D f ≠ 0) :
    pullConnection ((-t^2) • D) f = t^4*pullConnection D f := by
  have nt : t ≠ 0 := fun z => by simp [z] at dt
  have e : D (-(t^2))= -2*t := by rw [map_neg,d_square,dt]; ring
  have ee : D (D (-(t^2)))= -2 := by
    rw [e,times_deriv,dt,map_neg,show D (2:F)=0 by simpa only [Nat.cast_ofNat] using D.map_natCast 2]
    ring
  unfold pullConnection
  rw [schwarzian_scaled D (neg_ne_zero.mpr (pow_ne_zero _ nt)) df,e]
  rw [e] at ee
  rw [ee,Derivation.smul_apply,smul_eq_mul]
  ring

end AK14
