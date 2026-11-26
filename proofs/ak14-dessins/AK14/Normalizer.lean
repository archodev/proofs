import AK14.MarkedDescent
import AK14.Passport

/-! On the explicit quotient, preservation of tetrahedral orbits and agreement at
one point over the named order-three value imply identity on the entire quotient. -/
namespace AK14.TetraQuotient
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem rep_scaled {P : Pair K} (h : valid P) :
    ∃ c : K, c ≠ 0 ∧ rep (point P) = (c*P.1,c*P.2) := by
  classical
  obtain ⟨x,y⟩ := P
  change x ≠ 0 ∨ y ≠ 0 at h
  by_cases hy : y=0
  · subst y
    have hx := h.resolve_right (by simp)
    exact ⟨x⁻¹,inv_ne_zero hx,by simp [rep,point,hx]⟩
  · exact ⟨y⁻¹,inv_ne_zero hy,by simp [rep,point,hy,div_eq_mul_inv,mul_comm]⟩

theorem sphereMap_point {P : Pair K} (s : K) (h : valid P) :
    sphereMap s (point P)=point (qmap s P) := by
  classical
  obtain ⟨c,hc,eq⟩ := rep_scaled h
  rw [sphereMap,eq,qmap_scale]
  simp only [point]
  by_cases d : (qmap s P).2=0
  · simp [d]
  · simp [d,hc]
    exact mul_div_mul_left _ _ (pow_ne_zero _ hc)

theorem Matrix2.valid {m : Matrix2 K} (nd : m.det ≠ 0) {P : Pair K} (hp : valid P) :
    valid (m.act P) := by
  by_contra hn
  simp only [TetraQuotient.valid,Matrix2.act,not_or,not_not] at hn
  have l : m.det*P.1=0 := by unfold Matrix2.det; linear_combination m.d*hn.1-m.b*hn.2
  have r : m.det*P.2=0 := by unfold Matrix2.det; linear_combination m.a*hn.2-m.c*hn.1
  exact hp.elim (fun h => h ((mul_eq_zero.mp l).resolve_left nd))
    (fun h => h ((mul_eq_zero.mp r).resolve_left nd))

def Matrix2.onSphere (m : Matrix2 K) (z : Option K) := point (m.act (rep z))

theorem Matrix2.after_quotient (m : Matrix2 K) (nd : m.det ≠ 0) (s : K) (z : Option K) :
    sphereMap s (m.onSphere z) = point (qmap s (m.act (rep z))) :=
  sphereMap_point _ (m.valid nd (rep_valid z))

theorem fiber_infty {s : K} (P : Pair K) :
    point (qmap s P)=none ↔ quartic s P=0 := by
  classical
  by_cases z : quartic s P=0 <;> simp [point,qmap,z]

theorem fiber_one {s : K} (hs : s^2= -3) {P : Pair K} (hp : valid P) :
    point (qmap s P)=some 1 ↔ quartic (-s) P=0 := by
  rw [← point_rep (some 1),points_eq_iff (qmap_valid hs hp) (rep_valid _)]
  simp [bracket,rep,qmap]

def bValue (p : Passport) : Option K :=
  match p.family with | .split => some 1 | .together => none

/-- No assumption about an induced Möbius map on the target is needed. -/
theorem marked_orbit_descent [IsAlgClosed K] {s i : K} (hs : s^2= -3) (hi : i^2= -1)
    (m : Matrix2 K) (nd : m.det ≠ 0) (p : Passport)
    (pres : ∀ x y : Option K, tetraRelated i (rep x) (rep y) →
      tetraRelated i (rep (m.onSphere x)) (rep (m.onSphere y)))
    (z : Option K) (hz : sphereMap s z=bValue p) (hmz : sphereMap s (m.onSphere z)=bValue p) :
    ∀ x : Option K, sphereMap s (m.onSphere x)=sphereMap s x := by
  have respect {x y : Option K} (e : sphereMap s x=sphereMap s y) :
      sphereMap s (m.onSphere x)=sphereMap s (m.onSphere y) :=
    (sphereMap_fibers hs hi _ _).mpr (pres x y ((sphereMap_fibers hs hi _ _).mp e))
  have mark (x : Option K) (hx : sphereMap s x=bValue p) :
      sphereMap s (m.onSphere x)=bValue p := (respect (hx.trans hz.symm)).trans hmz
  have finite (x : K) : sphereMap s (m.onSphere (some x))=sphereMap s (some x) := by
    rw [m.after_quotient nd]
    change point (qmap s (m.act (x,1)))=point (qmap s (x,1))
    have vx : valid (x,(1:K)) := Or.inr one_ne_zero
    apply (points_eq_iff (qmap_valid hs (m.valid nd vx)) (qmap_valid hs vx)).mpr
    cases e : p.family with
    | together =>
      apply marked_quartic_fixes_quotient hs m nd _ x
      intro y hy
      have b : bValue (K := K) p=none := by simp [bValue,e]
      have hx : sphereMap s (some y)=bValue p := b.symm ▸ (fiber_infty _).mpr hy
      have mm := mark (some y) hx
      rw [m.after_quotient nd,b] at mm
      exact (fiber_infty _).mp mm
    | split =>
      have rs (y : K) (hy : quartic (-s) (y,1)=0) : quartic (-s) (m.act (y,1))=0 := by
        have b : bValue (K := K) p=some 1 := by simp [bValue,e]
        have vy : valid (y,(1:K)) := Or.inr one_ne_zero
        have hx : sphereMap s (some y)=bValue p := b.symm ▸ (fiber_one hs vy).mpr hy
        have mm := mark (some y) hx
        rw [m.after_quotient nd,b] at mm
        exact (fiber_one hs (m.valid nd vy)).mp mm
      have eq := marked_quartic_fixes_quotient (s := -s) (by simpa using hs) m nd rs x
      simp only [bracket,qmap,neg_neg] at eq ⊢
      linear_combination -eq
  intro x
  cases x with
  | some y => exact finite y
  | none =>
    have same : sphereMap s none = sphereMap s (some 0) := by simp [sphereMap,rep,point,qmap,quartic]
    exact (respect same).trans ((finite 0).trans same.symm)

end
end AK14.TetraQuotient
