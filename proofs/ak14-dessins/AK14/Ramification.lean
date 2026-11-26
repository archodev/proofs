import AK14.Schwarzian

/-! Local power model for the tetrahedral lift. The main result starts from
the equation w^k = u^e and proves the Schwarzian correction, including e = k. -/
namespace AK14
variable {K : Type*} [Field K] [CharZero K] (D : Derivation ℤ K K)

theorem logD_pow (u : K) (hu : u ≠ 0) (e : ℕ) :
    D (u^e) / u^e = (e : K) * (D u / u) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hp := pow_ne_zero e hu
    rw [pow_succ, times_deriv, Nat.cast_succ]
    calc
      _ = D (u^e) / u^e + D u/u := by field_simp; ring
      _ = _ := by rw [ih]; ring

theorem schwarzian_of_logDeriv {u w θ : K} (hu : u ≠ 0) (hw : w ≠ 0)
    (hdu : D u ≠ 0) (hθ : θ ≠ 0) (dθ : D θ = 0)
    (h : D w / w = θ * (D u / u)) :
    schwarzian D w = schwarzian D u + (1-θ^2)/2 * (D u/u)^2 := by
  let l := D u/u
  have hl : l ≠ 0 := div_ne_zero hdu hu
  have dw : D w = θ * l * w := (div_eq_iff hw).mp h
  have dl : D l = preSch D u * l - l^2 := by
    dsimp [l, preSch]
    rw [quotient_deriv _ _ _ hu]
    field_simp
    <;> ring
  have ddw : D (D w) = θ * l * D w + w * (θ * D l) := by
    conv_lhs => rw [dw]
    rw [times_deriv, times_deriv, dθ]; ring
  have pre : preSch D w = preSch D u + (θ-1)*l := by
    change D (D w) / D w = _
    rw [ddw, dl, dw]
    field_simp
    <;> ring
  unfold schwarzian
  rw [pre, map_add, times_deriv, map_sub, dθ, D.map_one_eq_zero, dl]
  change _ = _ + (1 - θ ^ 2) / 2 * l ^ 2
  ring

theorem schwarzian_of_power_relation {u w : K} {k e : ℕ}
    (hu : u ≠ 0) (hw : w ≠ 0) (hdu : D u ≠ 0) (hk : 0 < k) (he : 0 < e)
    (hpow : w^k = u^e) :
    schwarzian D w = schwarzian D u + (1-((e:K)/k)^2)/2 * (D u/u)^2 := by
  have hk' : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have he' : (e : K) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  apply schwarzian_of_logDeriv D hu hw hdu (div_ne_zero he' hk')
  · rw [quotient_deriv _ _ _ hk', D.map_natCast, D.map_natCast]; simp
  · have h : (k:K) * (D w/w) = (e:K) * (D u/u) := by
      rw [← logD_pow D w hw k, hpow, logD_pow D u hu e]
    field_simp at h ⊢
    linear_combination h

theorem schwarzian_regular_lift {u w : K} {k : ℕ}
    (hu : u ≠ 0) (hw : w ≠ 0) (hdu : D u ≠ 0) (hk : 0 < k) (h : w^k = u^k) :
    schwarzian D w = schwarzian D u := by
  have hk' : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simpa [hk'] using schwarzian_of_power_relation D hu hw hdu hk hk h

theorem schwarzian_affine (a b u : K) (ha : a ≠ 0) (du : D u ≠ 0)
    (da : D a = 0) (db : D b = 0) :
    schwarzian D (a*u+b) = schwarzian D u := by
  have d : D (a*u+b) = a*D u := by rw [map_add, times_deriv, da, db]; ring
  have eq : preSch D (a*u+b) = preSch D u := by
    unfold preSch
    rw [d, times_deriv, da]
    field_simp
    <;> ring
  simp only [schwarzian, eq]

theorem schwarzian_inv (u : K) (hu : u ≠ 0) (du : D u ≠ 0) :
    schwarzian D u⁻¹ = schwarzian D u := by
  have h : D u⁻¹ / u⁻¹ = (-1 : K) * (D u/u) := by
    rw [D.leibniz_inv]; simp only [smul_eq_mul]
    field_simp
    <;> ring
  have e := schwarzian_of_logDeriv D hu (inv_ne_zero hu) du (by norm_num : (-1:K) ≠ 0)
    (by simp : D (-1:K) = 0) h
  simpa using e

theorem schwarzian_eq_of_constantMobius {f g : K} (hf : D f ≠ 0)
    (h : ConstantMobius D f g) : schwarzian D g = schwarzian D f := by
  obtain ⟨a,b,c,d,da,db,dc,dd,det,den,rfl⟩ := h
  by_cases hc : c = 0
  · subst c
    have hd : d ≠ 0 := by simpa using den
    have ha : a ≠ 0 := by intro z; simp [z] at det
    have dA : D (a/d) = 0 := by rw [quotient_deriv _ _ _ hd, da, dd]; simp
    have dB : D (b/d) = 0 := by rw [quotient_deriv _ _ _ hd, db, dd]; simp
    have e : (a*f+b)/(0*f+d) = (a/d)*f+b/d := by simp only [zero_mul,zero_add]; field_simp
    rw [e, schwarzian_affine D _ _ _ (div_ne_zero ha hd) hf dA dB]
  · let v := c*f+d
    have dv : D v = c*D f := by dsimp [v]; rw [map_add, times_deriv, dc, dd]; ring
    have hdv : D v ≠ 0 := dv ▸ mul_ne_zero hc hf
    have hdiv : D v⁻¹ ≠ 0 := by
      rw [D.leibniz_inv]; simp [smul_eq_mul, den, hdv, show v ≠ 0 from den]
    let A := a/c
    let B := b - A*d
    have dA : D A = 0 := by
      dsimp [A]; rw [quotient_deriv _ _ _ hc, da, dc]; simp
    have dB : D B = 0 := by dsimp only [B]; rw [map_sub, times_deriv, dA, dd, db]; ring
    have hB : B ≠ 0 := by
      intro z
      apply det
      dsimp only [B,A] at z
      field_simp at z
      linear_combination -z
    have e : (a*f+b)/(c*f+d) = B*v⁻¹ + A := by
      change (a*f+b)/v = B*v⁻¹ + A
      apply (div_eq_iff den).mpr
      rw [add_mul, mul_assoc, inv_mul_cancel₀ den]
      dsimp [B, A, v]
      field_simp
      <;> ring
    rw [e, schwarzian_affine D B A _ hB hdiv dB dA, schwarzian_inv D v den hdv]
    exact schwarzian_affine D c d f hc hf dc dd

theorem schwarzian_eq_iff_constantMobius {f g : K} (hf : D f ≠ 0) (hg : D g ≠ 0) :
    schwarzian D f = schwarzian D g ↔ ConstantMobius D f g :=
  ⟨constantMobius_of_schwarzian_eq D hf hg, fun h => (schwarzian_eq_of_constantMobius D hf h).symm⟩

end AK14
