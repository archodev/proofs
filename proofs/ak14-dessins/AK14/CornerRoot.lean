import AK14.CornerFrames
import AK14.CycleCoordinates
import AK14.SectorRoots

namespace AK14.Gluing
open Complex Set Topology
noncomputable section

abbrev degreeAt {n : ℕ} (T : Triple n) (j : Fin 3) (x : Fin n) := cycleDegree (T j) x

theorem degreeAt_ne {n : ℕ} (T : Triple n) (j : Fin 3) (x : Fin n) : degreeAt T j x≠0 :=
  (cycleDegree_pos _ _).ne'

def sectorValue {n : ℕ} (T : Triple n) (j : Fin 3) (x : Fin n) (q : Tri n) (z : Triangle) :=
  orbitPhase (T j) x (Polar.phase (degreeAt T j x)) (cornerIndex T j q) *
    Polar.halfRoot (degreeAt T j x) (isUpper j q.1) (cornerValue j q.1 z)

theorem sector_neg_upper {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3)
    (x : Fin n) (q : Tri n) {z : Triangle} (zero : z.val (negativeEdge j)=0) (upper : isUpper j q.1=true) :
    sectorValue T j x q z=sectorValue T j x (step T (negativeEdge j) q) z := by
  have ray := corner_neg_ray zero q.1
  unfold sectorValue
  rw [index_negative T pr j q upper,orbitPhase_apply _ _ (Polar.primitive (degreeAt_ne T j x)),
    upper_step,upper,← corner_same zero q.1 (step T (negativeEdge j) q).1]
  rw [Polar.negative_seam (degreeAt_ne T j x) ray.1 ray.2]
  simp only [Bool.not_true]; ring

theorem sector_on_seam {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j k : Fin 3)
    (x : Fin n) (q : Tri n) {z : Triangle} (zero : z.val k=0) (pos : 0<z.val (opposite j)) :
    sectorValue T j x q z=sectorValue T j x (step T k q) z := by
  rcases edge_trichotomy j k with rfl|rfl|rfl
  · have ray := corner_pos_ray zero q.1
    unfold sectorValue
    rw [index_positive,upper_step,← corner_same zero q.1 (step T (positiveEdge j) q).1]
    congr 1
    cases isUpper j q.1
    · exact (Polar.positive_seam _ ray.1 ray.2).symm
    · exact Polar.positive_seam _ ray.1 ray.2
  · cases b : isUpper j q.1 with
    | true => exact sector_neg_upper T pr j x q zero b
    | false =>
      have h := sector_neg_upper T pr j x (step T (negativeEdge j) q) zero (by simp [upper_step,b])
      simpa [step_involution] using h.symm
  · exact False.elim (pos.ne' zero)

def cornerRoot {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n) : Surface T → ℂ :=
  Quot.lift (fun u : Cell n => if 0<u.2.val (opposite j) then sectorValue T j x u.1 u.2 else 0) (by
    rintro ⟨q,z⟩ ⟨r,w⟩ ⟨k,h,m,s⟩
    change z=w at h; change step T k q=r at s; subst w; subst r
    dsimp only; split_ifs with hz
    · exact sector_on_seam T pr j k x q m hz
    · rfl)

theorem root_cell {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n)
    (q : Tri n) {z : Triangle} (pos : 0<z.val (opposite j)) :
    cornerRoot T pr j x (cell T q z)=sectorValue T j x q z := if_pos pos

def cornerStar {n : ℕ} (T : Triple n) (j : Fin 3) : Set (Surface T) := {y | 0<(barycentric T y).val (opposite j)}

theorem star_open {n : ℕ} (T : Triple n) (j : Fin 3) : IsOpen (cornerStar T j) :=
  isOpen_lt continuous_const ((coord_cont _).comp (continuous_barycentric T))

theorem frame_base_ne {j : Fin 3} {z : Triangle} (pos : 0<z.val (opposite j)) : baseMass (frame j z)≠0 := by
  unfold baseMass
  exact (add_pos_of_pos_of_nonneg (by simpa using pos) ((frame j z).property.1 1)).ne'

theorem cornerRoot_continuous {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n) :
    ContinuousOn (cornerRoot T pr j x) (cornerStar T j) := by
  apply (isQuotientMap_quot_mk.continuousOn_isOpen_iff (star_open T j)).mpr
  apply continuousOn_prod_of_discrete_left.mpr
  intro q
  intro z hz
  change 0<z.val (opposite j) at hz
  have c : ContinuousAt (sectorValue T j x q) z := continuousAt_const.mul
    ((Polar.halfRoot_continuous (degreeAt_ne T j x) _).continuousAt.comp
      ((affine_continuousAt (frameSide j q.1) (frame_base_ne hz)).comp (frame_continuous j).continuousAt))
  apply c.continuousWithinAt.congr
  · intro w hw
    exact root_cell T pr j x q hw
  · exact root_cell T pr j x q hz

theorem sector_power {n : ℕ} (T : Triple n) (j : Fin 3) (x : Fin n) (q : Tri n) (z : Triangle)
    (inside : (T j).SameCycle x (cornerIndex T j q)) :
    (sectorValue T j x q z)^(degreeAt T j x)=cornerValue j q.1 z := by
  obtain ⟨k,hk⟩ := inside.exists_nat_pow_eq
  rw [sectorValue,mul_pow,←hk,orbitPhase_pow _ _ (Polar.primitive (degreeAt_ne T j x)),← pow_mul,
    Nat.mul_comm,pow_mul,(Polar.primitive (degreeAt_ne T j x)).pow_eq_one,one_pow,one_mul]
  cases h : isUpper j q.1
  · exact Polar.lower_power (degreeAt_ne T j x) (lower_sign h z)
  · exact Polar.upper_power (degreeAt_ne T j x) (upper_sign h z)

end
end AK14.Gluing
