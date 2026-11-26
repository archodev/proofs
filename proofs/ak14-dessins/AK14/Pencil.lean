import AK14.LiftRigidity
import AK14.Normalizer

/-! Specialization at the named order-three fiber of the tetrahedral pencil. -/
namespace AK14.SeriesAt
open Polynomial TetraQuotient
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

abbrev kRat (K : Type*) [Field K] := algebraMap K (RatFunc K)

def pencilVal {R : Type*} [CommRing R] (ρ : K →+* R) (t : R) (s : K) (P : Pair K) : R :=
  (1-t)*ρ ((quartic s P)^3)-ρ ((quartic (-s) P)^3)

@[simp] theorem expand_scalar (v a : K) : expand a (kRat K v)=constMap K v := by
  change expand a (algebraMap K[X] (RatFunc K) (C v))=_
  rw [expand_polynomial]
  change embed K (taylor a (C v) : PowerSeries K)=_
  rw [taylor_C,Polynomial.coe_C]
  rfl

private def markedForm (fam : Family) (s : K) (P : Pair K) : K :=
  match fam with
  | .split => -((quartic (-s) P)^3)
  | .together => -((quartic s P)^3)

/-- Each marked germ clears the pencil by one common nonzero scalar, and its
specialization is exactly one of the two tetrahedral quartics cubed. -/
private theorem marked_germ {p : Passport} {f : RatFunc K} (hf : NormalizedCover p f) (s : K) :
    ∃ d : GermField K, d ≠ 0 ∧ ∀ P : Pair K, ∃ H : PowerSeries K,
      d*expand 1 (pencilVal (kRat K) f s P)=embed K H ∧
        PowerSeries.constantCoeff (R := K) H=markedForm p.family s P := by
  obtain ⟨V,nV,cV,_,e⟩ := hf.atB
  let C' := PowerSeries.C (R := K)
  have nz : embed K V ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)).mpr nV
  cases h : p.family with
  | split =>
    simp [Passport.bSlot,h,targetChart] at e
    refine ⟨1,one_ne_zero,?_⟩
    intro P
    let A := (quartic s P)^3
    let B := (quartic (-s) P)^3
    refine ⟨V*C' A-C' B,?_,?_⟩
    · simp only [pencilVal,map_sub,map_one,map_mul,expand_scalar,e,sub_sub_cancel,one_mul]
      rfl
    · simp [C',cV,markedForm,h,B]
  | together =>
    simp [Passport.bSlot,h,targetChart] at e
    refine ⟨embed K V,nz,?_⟩
    intro P
    let A := (quartic s P)^3
    let B := (quartic (-s) P)^3
    refine ⟨(V-1)*C' A-V*C' B,?_,?_⟩
    · simp only [pencilVal,map_sub,map_one,map_mul,expand_scalar,e]
      change embed K V*((1-(embed K V)⁻¹)*constMap K A-constMap K B)=
        (embed K V-1)*constMap K A-embed K V*constMap K B
      field_simp [nz]
    · simp [C',cV,markedForm,h,A]

/-- A proportional pulled-back pencil preserves every point of the marked
quartic fiber. The polynomials and the specialization are homogeneous. -/
theorem marked_roots_of_cross {p : Passport} {s : K} {f g : RatFunc K}
    (hf : NormalizedCover p f) (hg : NormalizedCover p g) (m : Matrix2 K)
    (cross : ∀ x y : K,
      pencilVal (kRat K) g s (m.act (x,1))*pencilVal (kRat K) f s (y,1)=
      pencilVal (kRat K) g s (m.act (y,1))*pencilVal (kRat K) f s (x,1)) :
    ∀ x : K, markedForm p.family s (x,1)=0 → markedForm p.family s (m.act (x,1))=0 := by
  obtain ⟨d,_,F⟩ := marked_germ hf s
  obtain ⟨e,_,G⟩ := marked_germ hg s
  intro x hx
  obtain ⟨Fx,hFx,cFx⟩ := F (x,1)
  obtain ⟨F0,hF0,cF0⟩ := F (0,1)
  obtain ⟨Gx,hGx,cGx⟩ := G (m.act (x,1))
  obtain ⟨G0,hG0,cG0⟩ := G (m.act (0,1))
  have h := congrArg (expand (1:K)) (cross x 0)
  simp only [map_mul] at h
  have h' : Gx*F0=G0*Fx := by
    apply (IsFractionRing.injective (PowerSeries K) (GermField K))
    rw [map_mul (embed K),map_mul (embed K),← hGx,← hF0,← hG0,← hFx]
    linear_combination e*d*h
  have spec := congrArg (PowerSeries.constantCoeff (R := K)) h'
  rw [map_mul,map_mul,cGx,cF0,cG0,cFx,hx,mul_zero] at spec
  have base : markedForm p.family s (0,1) = -1 := by cases p.family <;> simp [markedForm,quartic]
  simpa [base] using spec

theorem marked_bracket_of_cross [IsAlgClosed K] {p : Passport} {s : K} (hs : s^2= -3)
    {f g : RatFunc K} (hf : NormalizedCover p f) (hg : NormalizedCover p g) (m : Matrix2 K)
    (nd : m.det ≠ 0)
    (cross : ∀ x y : K,
      pencilVal (kRat K) g s (m.act (x,1))*pencilVal (kRat K) f s (y,1)=
      pencilVal (kRat K) g s (m.act (y,1))*pencilVal (kRat K) f s (x,1)) (x : K) :
    bracket (qmap s (m.act (x,1))) (qmap s (x,1))=0 := by
  have mark := marked_roots_of_cross hf hg m cross
  cases e : p.family with
  | together =>
    simp only [e,markedForm,neg_eq_zero,pow_eq_zero_iff (by decide : (3:ℕ) ≠ 0)] at mark
    exact marked_quartic_fixes_quotient hs m nd mark x
  | split =>
    simp only [e,markedForm,neg_eq_zero,pow_eq_zero_iff (by decide : (3:ℕ) ≠ 0)] at mark
    have h := marked_quartic_fixes_quotient (s := -s) (by simpa using hs) m nd mark x
    simp only [bracket,qmap,neg_neg] at h ⊢
    linear_combination -h

end
end AK14.SeriesAt
