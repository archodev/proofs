import AK14.Normalizer
import AK14.Pencil

/-! Explicit source Möbius frames sending 0, 1, infinity to any three marked
points, with a genuine inverse on the projective line. -/
namespace AK14.TetraQuotient
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem bracket_rep_ne {x y : Option K} (h : x≠y) : bracket (rep x) (rep y)≠0 := by
  intro eq
  exact h (by simpa using (points_eq_iff (rep_valid x) (rep_valid y)).mpr eq)

theorem Matrix2.bracket (m : Matrix2 K) (P R : Pair K) :
    TetraQuotient.bracket (m.act P) (m.act R)=m.det*TetraQuotient.bracket P R := by
  dsimp [TetraQuotient.bracket,Matrix2.det,Matrix2.act]
  ring

theorem Matrix2.point_act (m : Matrix2 K) (nd : m.det≠0) {P : Pair K} (vp : TetraQuotient.valid P) :
    m.onSphere (point P)=point (m.act P) := by
  apply (points_eq_iff (m.valid nd (rep_valid _)) (m.valid nd vp)).mpr
  rw [m.bracket]
  have e : TetraQuotient.bracket (rep (point P)) P=0 := (points_eq_iff (rep_valid _) vp).mp (point_rep _)
  rw [e,mul_zero]

theorem Matrix2.onSphere_injective (m : Matrix2 K) (nd : m.det≠0) :
    Function.Injective m.onSphere := by
  intro x y h
  have e := (points_eq_iff (m.valid nd (rep_valid x)) (m.valid nd (rep_valid y))).mp h
  rw [m.bracket] at e
  simpa using (points_eq_iff (rep_valid x) (rep_valid y)).mpr ((mul_eq_zero.mp e).resolve_left nd)

def Matrix2.adj (m : Matrix2 K) : Matrix2 K := ⟨m.d,-m.b,-m.c,m.a⟩

theorem Matrix2.adj_det (m : Matrix2 K) : m.adj.det=m.det := by dsimp [Matrix2.adj,Matrix2.det]; ring

theorem Matrix2.adj_left (m : Matrix2 K) (nd : m.det≠0) (x : Option K) :
    m.adj.onSphere (m.onSphere x)=x := by
  change m.adj.onSphere (point (m.act (rep x)))=x
  rw [m.adj.point_act (m.adj_det ▸ nd) (m.valid nd (rep_valid x))]
  conv_rhs => rw [← point_rep x]
  apply (points_eq_iff (m.adj.valid (m.adj_det ▸ nd) (m.valid nd (rep_valid x))) (rep_valid x)).mpr
  simp only [Matrix2.act,Matrix2.adj,TetraQuotient.bracket]
  ring

theorem Matrix2.adj_right (m : Matrix2 K) (nd : m.det≠0) (x : Option K) :
    m.onSphere (m.adj.onSphere x)=x := by
  have e := m.adj.adj_left (m.adj_det ▸ nd) x
  simpa only [Matrix2.adj,neg_neg] using e

def Matrix2.sphereEquiv (m : Matrix2 K) (nd : m.det≠0) : Option K ≃ Option K :=
  ⟨m.onSphere,m.adj.onSphere,m.adj_left nd,m.adj_right nd⟩

theorem source_frame (A B C : Option K) (ab : A≠B) (bc : B≠C) (ca : C≠A) :
    ∃ m : Matrix2 K, m.det≠0 ∧ m.onSphere (some 0)=A ∧
      m.onSphere (some 1)=B ∧ m.onSphere none=C := by
  let U := rep A
  let V := rep B
  let W := rep C
  let l := bracket V U
  let k := bracket W V
  let m : Matrix2 K := ⟨l*W.1,k*U.1,l*W.2,k*U.2⟩
  have nl : l≠0 := bracket_rep_ne ab.symm
  have nk : k≠0 := bracket_rep_ne bc.symm
  have det : m.det=l*k*bracket W U := by dsimp [m,Matrix2.det,bracket]; ring
  have nd : m.det≠0 := det ▸ mul_ne_zero (mul_ne_zero nl nk) (bracket_rep_ne ca)
  have goal (x y : Option K) (e : bracket (m.act (rep x)) (rep y)=0) : m.onSphere x=y := by
    simpa only [point_rep] using (points_eq_iff (m.valid nd (rep_valid x)) (rep_valid y)).mpr e
  refine ⟨m,nd,goal _ _ ?_,goal _ _ ?_,goal _ _ ?_⟩
  · change bracket (m.act (0,1)) U=0
    dsimp only [bracket,Matrix2.act,m]; ring
  · change bracket (m.act (1,1)) V=0
    dsimp only [bracket,Matrix2.act,m,l,k]; ring
  · change bracket (m.act (1,0)) W=0
    dsimp only [bracket,Matrix2.act,m]; ring

end
end AK14.TetraQuotient
