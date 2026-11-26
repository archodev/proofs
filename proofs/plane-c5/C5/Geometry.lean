module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

namespace C5

noncomputable section

/-- The order is cyclic. No condition is imposed on the five chords. -/
structure Pentagon (p : Fin 5 → ℂ) : Prop where
  distinct : Function.Injective p
  edges : ∀ i : Fin 5, dist (p i) (p (i+1)) = 1

def HasMono (c : ℂ → Bool) : Prop :=
  ∃ p : Fin 5 → ℂ, Pentagon p ∧ ∀ i, c (p i) = c (p 0)

def omega : ℂ := ⟨1/2, Real.sqrt 3/2⟩
def rho : ℂ := ⟨-5/6, Real.sqrt 11/6⟩
def rot : Fin 3 → ℂ := ![1, ⟨-1/2, Real.sqrt 3/2⟩, ⟨-1/2, -Real.sqrt 3/2⟩]

local macro "coords" : tactic =>
  `(tactic| (simp [rot, omega, rho, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;>
    ring_nf <;> norm_num))

theorem rotation_unit (i : Fin 3) : Complex.normSq (rot i) = 1 := by
  fin_cases i <;> coords

theorem rotation_chords (i j : Fin 3) (h : i ≠ j) :
    Complex.normSq (rot i - rot j) = 3 := by
  fin_cases i <;> fin_cases j <;> first | exact (h rfl).elim | coords

theorem rho_unit : Complex.normSq rho = 1 := by coords
theorem inner_radius : Complex.normSq (1 + rho) = 1/3 := by coords
theorem omega_sq : omega ^ 2 = rot 1 := by
  apply Complex.ext <;> simp [omega, rot, pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num
theorem rot_sq : rot 1 ^ 2 = rot 2 := by
  apply Complex.ext <;> simp [rot, pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num

def outer (b : Bool) (i : Fin 3) : ℂ := rot i * (if b then rho else 1)
def inner (i : Fin 3) : ℂ := rot i * (1 + rho)

theorem outer_radius (b : Bool) (i : Fin 3) : Complex.normSq (outer b i) = 1 := by
  cases b <;> simp [outer, Complex.normSq_mul, rotation_unit, rho_unit]

theorem inner_radius_sq (i : Fin 3) : Complex.normSq (inner i) = 1/3 := by
  simp [inner, Complex.normSq_mul, rotation_unit, inner_radius]

theorem inner_chord (i j : Fin 3) (h : i ≠ j) :
    Complex.normSq (inner i - inner j) = 1 := by
  rw [inner, inner, ← sub_mul, Complex.normSq_mul, rotation_chords i j h, inner_radius]
  norm_num

theorem radial_edge (b : Bool) (i : Fin 3) :
    Complex.normSq (inner i - outer b i) = 1 := by
  unfold inner outer
  rw [← mul_sub, Complex.normSq_mul, rotation_unit]
  cases b <;> simp [rho_unit]

private theorem near_ne {v w : ℂ} (h : Complex.normSq v ≠ Complex.normSq w) : v ≠ w :=
  fun e => h (congrArg Complex.normSq e)

private theorem unit_of_sq {v w : ℂ} (h : Complex.normSq (v-w) = 1) : dist v w = 1 := by
  simpa [dist_eq_norm, Complex.norm_def, h]

private theorem outer_ne (b : Bool) {i j : Fin 3} (h : i ≠ j) : outer b i ≠ outer b j := by
  have hr : rot i ≠ rot j := by
    intro e
    have := rotation_chords i j h
    simp [e] at this
  have hn : rho ≠ 0 := near_ne (by rw [rho_unit]; norm_num)
  cases b <;> simp [outer, hr, hn]

def pattern (b : Bool) (i j : Fin 3) : Fin 5 → ℂ :=
  ![0, outer b i, inner i, inner j, outer b j]

theorem base_pentagon (b : Bool) {i j : Fin 3} (h : i ≠ j) : Pentagon (pattern b i j) := by
  have ho (k : Fin 3) : outer b k ≠ 0 := near_ne (by rw [outer_radius]; norm_num)
  have hi (k : Fin 3) : inner k ≠ 0 := near_ne (by rw [inner_radius_sq]; norm_num)
  have hoi (k l : Fin 3) : outer b k ≠ inner l :=
    near_ne (by rw [outer_radius, inner_radius_sq]; norm_num)
  have hii : inner i ≠ inner j := by
    intro e
    have := inner_chord i j h
    simp [e] at this
  have hoo := outer_ne b h
  constructor
  · intro k l he
    fin_cases k <;> fin_cases l <;> simp_all [pattern, Ne.symm]
  · have uo (k : Fin 3) : dist (outer b k) 0 = 1 :=
      unit_of_sq (by rw [sub_zero, outer_radius])
    have ur (k : Fin 3) := unit_of_sq (radial_edge b k)
    have uz := unit_of_sq (inner_chord i j h)
    intro k
    fin_cases k <;> first | exact uo _ | exact ur _ | exact uz |
      exact (dist_comm _ _).trans (uo _) | exact (dist_comm _ _).trans (ur _)

def place (x u z : ℂ) : ℂ := x + u*z

theorem dist_place (x : ℂ) {u : ℂ} (hu : ‖u‖ = 1) (v w : ℂ) :
    dist (place x u v) (place x u w) = dist v w := by
  simp [place, dist_eq_norm, ← mul_sub, norm_mul, hu]

theorem Pentagon.place {p : Fin 5 → ℂ} (hp : Pentagon p) (x : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    Pentagon (fun k => C5.place x u (p k)) := by
  have hu' : u ≠ 0 := by intro e; simp [e] at hu
  exact ⟨fun _ _ e => hp.distinct (by simpa [C5.place, hu'] using e),
    fun i => (dist_place x hu _ _).trans (hp.edges i)⟩

theorem two_circles (x : ℂ) {u : ℂ} (hu : ‖u‖ = 1) (b : Bool)
    {i j : Fin 3} (h : i ≠ j) :
    Pentagon (fun k => place x u (pattern b i j k)) :=
  (base_pentagon b h).place x hu

theorem inner_triangle (x : ℂ) {u : ℂ} (hu : ‖u‖ = 1) {i j : Fin 3} (h : i ≠ j) :
    dist (place x u (inner i)) (place x u (inner j)) = 1 :=
  (dist_place x hu _ _).trans (unit_of_sq (inner_chord i j h))

end
end C5

end
