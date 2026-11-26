import AK14.Pencil

/-! Irreducibility of the explicit degree-twelve inverse equation suffices for
normalized rational-cover uniqueness. -/
namespace AK14.SeriesAt
open Polynomial TetraQuotient
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {F L : Type*} [Field F] [Field L]

def middleId (K : Type*) [Field K] : Matrix2 K := ⟨1,0,0,1⟩

def pencilPoly (ρ : K →+* F) (h : F) (s : K) (m : Matrix2 K) : F[X] :=
  C (1-h)*((transformed s m).map ρ)^3-((transformed (-s) m).map ρ)^3

theorem pencil_degree_le (ρ : K →+* F) (h : F) (s : K) (m : Matrix2 K) :
    (pencilPoly ρ h s m).natDegree ≤ 12 := by
  unfold pencilPoly
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · apply (natDegree_C_mul_le _ _).trans
    rw [natDegree_pow]
    have h := (natDegree_map_le (f := ρ) (p := transformed s m)).trans (transformed_degree_le s m)
    omega
  · rw [natDegree_pow]
    have h := (natDegree_map_le (f := ρ) (p := transformed (-s) m)).trans (transformed_degree_le (-s) m)
    omega

theorem pencil_eval (ρ : K →+* F) (h : F) (s x : K) (m : Matrix2 K) :
    (pencilPoly ρ h s m).eval (ρ x)=pencilVal ρ h s (m.act (x,1)) := by
  simp only [pencilPoly,pencilVal,eval_sub,eval_mul,eval_C,eval_pow,eval_map,eval₂_at_apply,
    eval_transformed,map_pow]

theorem pencil_id (ρ : K →+* F) [CharZero F] {s : K} (hs : s^2= -3) (h : F) :
    pencilPoly ρ h s (middleId K)=liftPolynomial (ρ s) h := by
  letI : Infinite F := Infinite.of_injective (fun n : ℕ => (n:F)) Nat.cast_injective
  apply Polynomial.funext
  intro y
  have e : (ρ s)^2= -3 := by rw [← map_pow,hs,map_neg,map_ofNat]
  simp only [liftPolynomial,eval_sub,eval_mul,eval_C,eval_pow,eval_numerator e,eval_quart,
    pencilPoly,eval_map,transformed,middleId,eval₂_add,eval₂_pow,eval₂_mul,eval₂_ofNat,
    eval₂_C,eval₂_X,eval₂_one,eval₂_neg,map_one,map_zero,map_neg,qmap,quartic,one_mul,add_zero,zero_mul,zero_add,
    one_pow,mul_one]
  ring

private theorem scalar_of_common_root [Algebra F L] {P Q : F[X]} {z : L}
    (irr : Irreducible P) (hp : aeval z P=0) (hq : aeval z Q=0) (deg : Q.natDegree≤P.natDegree) :
    ∃ k : F, Q=C k*P := by
  have div := minpoly.dvd F z hq
  rw [← minpoly.eq_of_irreducible irr hp] at div
  obtain ⟨U,hu⟩ := (dvd_mul_right P _).trans div
  by_cases un : U=0
  · exact ⟨0,by simp [hu,un]⟩
  have du : U.natDegree=0 := by
    rw [hu,natDegree_mul irr.ne_zero un] at deg
    omega
  exact ⟨U.coeff 0,by conv_lhs => rw [hu,eq_C_of_natDegree_eq_zero du]; rw [mul_comm]⟩

theorem root_pencils_cross [CharZero F] [Algebra F L] (ρ : K →+* F) {z : L}
    {f g : F} {s : K} (hs : s^2= -3) (fn : f ≠ 0) (m : Matrix2 K)
    (irr : Irreducible (liftPolynomial (ρ s) f))
    (hf : aeval z (liftPolynomial (ρ s) f)=0)
    (hg : aeval z (pencilPoly ρ g s m)=0) (x y : K) :
    pencilVal ρ g s (m.act (x,1))*pencilVal ρ f s (y,1)=
      pencilVal ρ g s (m.act (y,1))*pencilVal ρ f s (x,1) := by
  have e : (ρ s)^2= -3 := by rw [← map_pow,hs,map_neg,map_ofNat]
  obtain ⟨k,h⟩ := scalar_of_common_root irr hf hg (by
    rw [liftPolynomial_degree e fn]; exact pencil_degree_le _ _ _ _)
  rw [← pencil_id ρ hs f] at h
  have eval (u : K) := congrArg (fun P : F[X] => P.eval (ρ u)) h
  simp only [pencil_eval,eval_mul,eval_C] at eval
  simpa only [middleId,Matrix2.act,one_mul,zero_mul,zero_add,add_zero,mul_one] using
    (show pencilVal ρ g s (m.act (x,1))*pencilVal ρ f s ((middleId K).act (y,1))=
      pencilVal ρ g s (m.act (y,1))*pencilVal ρ f s ((middleId K).act (x,1)) by
      rw [eval x,eval y]; ring)

def bracketPoly (s : K) (m : Matrix2 K) : K[X] :=
  (transformed s m)^3*(quart (-s))^3-(transformed (-s) m)^3*(quart s)^3

theorem bracketPoly_zero {p : Passport} [IsAlgClosed K] {f g : RatFunc K}
    (hf : NormalizedCover p f) (hg : NormalizedCover p g) {s : K} (hs : s^2= -3)
    (m : Matrix2 K) (nd : m.det≠0)
    (cross : ∀ x y : K, pencilVal (kRat K) g s (m.act (x,1))*pencilVal (kRat K) f s (y,1)=
      pencilVal (kRat K) g s (m.act (y,1))*pencilVal (kRat K) f s (x,1)) :
    bracketPoly s m=0 := by
  apply Polynomial.funext
  intro x
  have eq := marked_bracket_of_cross hs hf hg m nd cross x
  simp only [bracketPoly,eval_sub,eval_mul,eval_pow,eval_transformed,eval_quart,eval_zero]
  simp only [bracket,qmap] at eq
  linear_combination eq

private theorem quart_hom (s u v : L) (nv : v≠0) :
    quartic s (u,v) = v^4*quartic s (u/v,1) := by
  dsimp only [quartic]
  field_simp [nv] <;> ring

theorem eval₂_transformed (ρ : K →+* L) (s : K) (m : Matrix2 K) (z : L) :
    (transformed s m).eval₂ ρ z=
    quartic (ρ s) (ρ m.a*z+ρ m.b,ρ m.c*z+ρ m.d) := by
  simp only [transformed,quartic,eval₂_add,eval₂_mul,eval₂_pow,eval₂_ofNat,eval₂_X,eval₂_C]

private theorem eval₂_quart (ρ : K →+* L) (s : K) (z : L) :
    (quart s).eval₂ ρ z=quartic (ρ s) (z,1) := by simp [quart,quartic,map_ofNat ρ]

theorem pencil_at_mobius [Algebra F L] (ρ : K →+* F) (t : F) (s : K) (m : Matrix2 K) {z w : L}
    (nv : (algebraMap F L) (ρ m.c)*z+(algebraMap F L) (ρ m.d)≠0)
    (mw : w=((algebraMap F L) (ρ m.a)*z+(algebraMap F L) (ρ m.b))/
      ((algebraMap F L) (ρ m.c)*z+(algebraMap F L) (ρ m.d))) :
    aeval z (pencilPoly ρ t s m)=
      ((algebraMap F L) (ρ m.c)*z+(algebraMap F L) (ρ m.d))^12*
        aeval w (pencilPoly ρ t s (middleId K)) := by
  let σ := (algebraMap F L).comp ρ
  change σ m.c*z+σ m.d ≠ 0 at nv
  change w=(σ m.a*z+σ m.b)/(σ m.c*z+σ m.d) at mw
  simp only [pencilPoly,aeval_def,eval₂_sub,eval₂_mul,eval₂_C,eval₂_pow,eval₂_map,eval₂_transformed]
  change (algebraMap F L (1-t))*quartic (σ s) (σ m.a*z+σ m.b,σ m.c*z+σ m.d)^3-
      quartic (σ (-s)) (σ m.a*z+σ m.b,σ m.c*z+σ m.d)^3=_
  simp only [middleId,map_one,map_zero,one_mul,zero_mul,add_zero,zero_add]
  rw [quart_hom _ _ _ nv,quart_hom _ _ _ nv,← mw]
  change (algebraMap F L (1-t))*((σ m.c*z+σ m.d)^4*quartic (σ s) (w,1))^3-
    ((σ m.c*z+σ m.d)^4*quartic (σ (-s)) (w,1))^3=(σ m.c*z+σ m.d)^12*
      ((algebraMap F L (1-t))*quartic (σ s) (w,1)^3-quartic (σ (-s)) (w,1)^3)
  rw [mul_pow,mul_pow,← pow_mul]
  ring


theorem pencil_root_data [Algebra F L] (ρ : K →+* F) (h : F) (s : K) (m : Matrix2 K) (z : L) :
    aeval z (pencilPoly ρ h s m)=
    (1-algebraMap F L h)*quartic (((algebraMap F L).comp ρ) s)
      ((algebraMap F L) (ρ m.a)*z+(algebraMap F L) (ρ m.b),
       (algebraMap F L) (ρ m.c)*z+(algebraMap F L) (ρ m.d))^3-
    quartic (-((algebraMap F L).comp ρ) s)
      ((algebraMap F L) (ρ m.a)*z+(algebraMap F L) (ρ m.b),
       (algebraMap F L) (ρ m.c)*z+(algebraMap F L) (ρ m.d))^3 := by
  simp only [pencilPoly,aeval_def,eval₂_sub,eval₂_mul,eval₂_C,eval₂_pow,eval₂_map,
    eval₂_transformed,RingHom.comp_apply,map_neg,map_sub,map_one,eval₂_one]

theorem values_equal_of_bracket [CharZero L] (s : L) (hs : s^2= -3) (P Q : Pair L)
    (p : valid P) (q : valid Q) (f g : L)
    (F : (1-f)*quartic s P^3-quartic (-s) P^3=0)
    (G : (1-g)*quartic s Q^3-quartic (-s) Q^3=0)
    (same : quartic s Q^3*quartic (-s) P^3-quartic (-s) Q^3*quartic s P^3=0) : f=g := by
  have nz (R : Pair L) (vr : valid R) {v : L}
      (eq : (1-v)*quartic s R^3-quartic (-s) R^3=0) : quartic s R^3≠0 := by
    intro bad
    have pair := qmap_valid hs vr
    simp only [valid,qmap,bad,sub_eq_add_neg,zero_add,neg_ne_zero,ne_eq,not_true_eq_false,or_false] at pair
    exact pair (by simpa [bad] using eq)
  apply sub_eq_zero.mp
  apply mul_right_cancel₀ (mul_ne_zero (nz P p F) (nz Q q G))
  rw [zero_mul]
  linear_combination -(quartic s Q)^3*F+(quartic s P)^3*G-same

/- The geometric return-group bridge can alternatively be replaced by the
irreducibility of one explicit polynomial over the source rational function field. -/
theorem normalized_unique_of_irreducible [IsAlgClosed K] {p : Passport} {n : ℕ}
    (hp : p.Admissible n) {f g : RatFunc K} (hf : NormalizedCover p f) (hg : NormalizedCover p g)
    {s : K} (hs : s^2= -3) (irr : Irreducible (liftPolynomial (kRat K s) f)) : f=g := by
  let F := RatFunc K
  let L := ComparisonField s f g
  let ρ := kRat K
  let σ := algebraMap F L
  let τ := σ.comp ρ
  letI : CharZero L := charZero_of_injective_algebraMap σ.injective
  letI : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
  letI : Differential (RatFunc K) := ⟨ratDeriv K⟩
  letI : Differential L := Differential.differentialFiniteDimensional F L
  letI : DifferentialAlgebra F L := Differential.differentialAlgebraFiniteDimensional
  have sf : (ρ s)^2= -3 := by rw [← map_pow,hs,map_neg,map_ofNat]
  have sl : (τ s)^2= -3 := by rw [← map_pow,hs,map_neg,map_ofNat]
  have fn : f ≠ 0 := fun h => hf.nonconstant (by rw [h,map_zero])
  have gn : g ≠ 0 := fun h => hg.nonconstant (by rw [h,map_zero])
  let P := liftPolynomial (ρ s) f
  let Q := liftPolynomial (ρ s) g
  have dp : P.natDegree=12 := liftPolynomial_degree sf fn
  have dq : Q.natDegree=12 := liftPolynomial_degree sf gn
  have np : P≠0 := fun z => by simp [z] at dp
  have nq : Q≠0 := fun z => by simp [z] at dq
  have sp : (P.map σ).Splits ∧ (Q.map σ).Splits :=
    (splits_mul_iff (Polynomial.map_ne_zero np) (Polynomial.map_ne_zero nq)).mp
      (by simpa only [Polynomial.map_mul] using SplittingField.splits (P*Q))
  obtain ⟨z,rawZ⟩ := sp.1.exists_eval_eq_zero (by rw [degree_map,degree_eq_natDegree np,dp]; decide)
  obtain ⟨w,rawW⟩ := sp.2.exists_eval_eq_zero (by rw [degree_map,degree_eq_natDegree nq,dq]; decide)
  have hz : aeval z P=0 := by simpa only [Polynomial.eval_map] using rawZ
  have hw : aeval w Q=0 := by simpa only [Polynomial.eval_map] using rawW
  have eF := root_is_lift σ sf fn hz
  have eG := root_is_lift σ sf gn hw
  have tower (k : K) : σ (ρ k)=algebraMap K L k := (IsScalarTower.algebraMap_apply K F L k).symm
  rw [tower] at eF eG
  obtain ⟨a,b,c,d,nd,den,rel⟩ := common_field_rigidity hs hf.nonconstant hg.nonconstant eF eG
    (normalized_connections_equal hp hf hg)
  let m : Matrix2 K := ⟨a,b,c,d⟩
  have mg := pencil_at_mobius ρ g s m (z := z) (w := w) (by simpa only [m,tower] using den)
    (by simpa only [m,tower] using rel)
  have wz : aeval w (pencilPoly ρ g s (middleId K))=0 := by rw [pencil_id ρ hs]; exact hw
  rw [wz,mul_zero] at mg
  have cross := root_pencils_cross ρ hs fn m irr (show aeval z P=0 from hz) mg
  have bp := bracketPoly_zero hf hg hs m nd cross
  have br := congrArg (fun U : K[X] => U.eval₂ τ z) bp
  simp only [bracketPoly,eval₂_sub,eval₂_mul,eval₂_pow,eval₂_transformed,eval₂_quart,map_neg,eval₂_zero] at br
  have zz : aeval z (pencilPoly ρ f s (middleId K))=0 := by rw [pencil_id ρ hs]; exact hz
  rw [pencil_root_data] at zz mg
  simp only [middleId,map_one,map_zero,one_mul,zero_mul,zero_add,add_zero] at zz
  let M : Pair L := (τ a*z+τ b,τ c*z+τ d)
  have mvalid : valid M := Or.inr (by simpa only [τ,RingHom.comp_apply,tower] using den)
  apply σ.injective
  exact values_equal_of_bracket (τ s) sl (z,1) M (Or.inr one_ne_zero) mvalid _ _ zz mg br

end
end AK14.SeriesAt
