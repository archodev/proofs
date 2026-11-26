import AK14.ProjectiveChart
import AK14.FullInverse

/-! Rigidity for arbitrary positions of the exceptional points. Normalization is
proved by actual source Möbius substitution on rational functions and their
germs, including the reciprocal source chart. -/
namespace AK14.SeriesAt
open Polynomial TetraQuotient
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def composePoly (m : Matrix2 K) : K[X] →+* RatFunc K :=
  eval₂RingHom (kRat K) (coordinate m)

private theorem polynomial_hom_ext {L : Type*} [Field L] (ρ : RatFunc K →+* L)
    (p : K[X]) : ρ (algebraMap K[X] (RatFunc K) p)=p.eval₂ (ρ.comp (kRat K)) (ρ (variableX K)) := by
  have same : ρ.comp (algebraMap K[X] (RatFunc K))=eval₂RingHom (ρ.comp (kRat K)) (ρ (variableX K)) := by
    apply Polynomial.ringHom_ext
    · intro c
      change ρ (kRat K c)=(C c).eval₂ _ _
      rw [eval₂_C]; rfl
    · change ρ (variableX K)=(X : K[X]).eval₂ _ _
      rw [eval₂_X]
  exact RingHom.congr_fun same p

private theorem polynomial_covariance (m : Matrix2 K) (x : Option K) {V : PowerSeries K}
    (nv : PowerSeries.constantCoeff (R := K) V≠0)
    (e : expandAt x (coordinate m)=reparam V nv (expandAt (m.onSphere x) (variableX K))) (p : K[X]) :
    expandAt x (composePoly m p)=reparam V nv (expandAt (m.onSphere x) (algebraMap K[X] (RatFunc K) p)) := by
  let η := (reparam V nv).comp (expandAt (m.onSphere x))
  have c : (expandAt x).comp (kRat K)=η.comp (kRat K) := by
    ext k
    change expandAt x (kRat K k)=reparam V nv (expandAt (m.onSphere x) (kRat K k))
    rw [expandAt_scalar,expandAt_scalar,reparam_const]
  change expandAt x (p.eval₂ (kRat K) (coordinate m))=η (algebraMap _ _ p)
  rw [hom_eval₂,polynomial_hom_ext η,c,e]; rfl

theorem composePoly_injective (m : Matrix2 K) (nd : m.det≠0) : Function.Injective (composePoly m) := by
  obtain ⟨V,nv,e⟩ := projective_coordinate_germ none m nd
  apply (injective_iff_map_eq_zero _).mpr
  intro p z
  have eq := polynomial_covariance m none nv e p
  rw [z,map_zero] at eq
  exact (map_eq_zero_iff _ (RatFunc.algebraMap_injective K)).mp
    ((map_eq_zero_iff _ (expandAt (m.onSphere none)).injective).mp
      ((map_eq_zero_iff _ (reparam V nv).injective).mp eq.symm))

def precompose (m : Matrix2 K) (nd : m.det≠0) : RatFunc K →+* RatFunc K :=
  IsFractionRing.lift (composePoly_injective m nd)

theorem precompose_poly (m : Matrix2 K) (nd : m.det≠0) (p : K[X]) :
    precompose m nd (algebraMap K[X] (RatFunc K) p)=composePoly m p := IsFractionRing.lift_algebraMap _ _

theorem precompose_const (m : Matrix2 K) (nd : m.det≠0) (c : K) :
    precompose m nd (kRat K c)=kRat K c := by
  change precompose m nd (algebraMap K[X] (RatFunc K) (C c))=_
  rw [precompose_poly]; simp [composePoly]

theorem precompose_germ (m : Matrix2 K) (nd : m.det≠0) (x : Option K) :
    ∃ (V : PowerSeries K) (nv : PowerSeries.constantCoeff (R := K) V≠0), ∀ f : RatFunc K,
      expandAt x (precompose m nd f)=reparam V nv (expandAt (m.onSphere x) f) := by
  obtain ⟨V,nv,e⟩ := projective_coordinate_germ x m nd
  refine ⟨V,nv,fun f => ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom f]
  conv_rhs => rw [← RatFunc.num_div_denom f]
  rw [map_div₀,map_div₀,precompose_poly,precompose_poly,polynomial_covariance m x nv e,
    polynomial_covariance m x nv e,map_div₀,map_div₀]

/-- The source exceptional points are arbitrary and distinct. At every other
point all three special fibers have their ordinary indices 2, 3, 3, and every
point outside those fibers is unramified. -/
structure MarkedCover (p : Passport) (f : RatFunc K) (A B C : Option K) : Prop where
  nonconstant : ratDeriv K f≠0
  ab : A≠B
  bc : B≠C
  ca : C≠A
  atA : BranchGerm (expandAt A f) 0 p.a
  atB : BranchGerm (expandAt B f) p.bSlot p.b
  atC : BranchGerm (expandAt C f) 2 p.c
  elsewhere : ∀ x : Option K, x≠A → x≠B → x≠C →
    OrdinaryGerm (expandAt x f) ∨ ∃ j, BranchGerm (expandAt x f) j (branchOrder j)

theorem normalize_marked {p : Passport} {f : RatFunc K} {A B C : Option K} (hf : MarkedCover p f A B C) :
    ∃ (m : Matrix2 K) (nd : m.det≠0), m.onSphere (some 0)=A ∧ m.onSphere (some 1)=B ∧
    m.onSphere none=C ∧ NormalizedCover p (precompose m nd f) := by
  obtain ⟨m,nd,ma,mb,mc⟩ := source_frame A B C hf.ab hf.bc hf.ca
  refine ⟨m,nd,ma,mb,mc,?_⟩
  have branch (x : Option K) (j : Fin 3) (e : ℕ) (h : BranchGerm (expandAt (m.onSphere x) f) j e) :
      BranchGerm (expandAt x (precompose m nd f)) j e := by
    obtain ⟨V,nv,c⟩ := precompose_germ m nd x
    rw [c]; exact reparam_branch nv h
  constructor
  · intro d
    obtain ⟨c,hc⟩ := (ratDeriv_constants K _).mp d
    rw [← precompose_const m nd c] at hc
    apply hf.nonconstant
    exact (ratDeriv_constants K _).mpr ⟨c,(precompose m nd).injective hc⟩
  · exact branch (some 0) _ _ (ma ▸ hf.atA)
  · exact branch (some 1) _ _ (mb ▸ hf.atB)
  · exact branch none _ _ (mc ▸ hf.atC)
  · intro x x0 x1
    have inj := m.onSphere_injective nd
    have na : m.onSphere (some x)≠A := fun e => x0 (Option.some.inj (inj (e.trans ma.symm)))
    have nb : m.onSphere (some x)≠B := fun e => x1 (Option.some.inj (inj (e.trans mb.symm)))
    have nc : m.onSphere (some x)≠C := fun e => Option.some_ne_none x (inj (e.trans mc.symm))
    rcases hf.elsewhere _ na nb nc with h | ⟨j,h⟩
    · obtain ⟨V,nv,c⟩ := precompose_germ m nd (some x)
      left
      change OrdinaryGerm (expandAt (some x) (precompose m nd f))
      rw [c]; exact reparam_ordinary nv h
    · exact Or.inr ⟨_,branch (some x) _ _ h⟩

/-- Arbitrary marked rational realizations agree after genuine nonsingular
source Möbius substitutions, with all three target labels fixed. -/
theorem rational_covers_equivalent [IsAlgClosed K] {p : Passport} {n : ℕ} (hp : p.Admissible n)
    {f g : RatFunc K} {a b c u v w : Option K} (hf : MarkedCover p f a b c) (hg : MarkedCover p g u v w) :
    ∃ (m t : Matrix2 K) (dm : m.det≠0) (dt : t.det≠0),
      precompose m dm f=precompose t dt g := by
  obtain ⟨m,dm,_,_,_,F⟩ := normalize_marked hf
  obtain ⟨t,dt,_,_,_,G⟩ := normalize_marked hg
  exact ⟨m,t,dm,dt,normalized_rational_unique hp F G⟩

end
end AK14.SeriesAt
