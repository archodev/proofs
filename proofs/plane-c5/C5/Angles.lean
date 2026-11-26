module
public import C5.Geometry
public import Erdos173.Basic
public import Mathlib.NumberTheory.Niven
public import Mathlib.Dynamics.Ergodic.Action.OfMinimal
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

@[expose] public section
namespace C5
open Erdos173 OAI.EuclideanFiveColor MeasureTheory Filter Set
noncomputable section

def tau : Angles := ((Real.pi/3 : ℝ) : Angles)
def gamma : Angles := (Complex.arg rho : Angles)
def phase : Fin 3 → Angles := ![0,tau+tau,(tau+tau)+(tau+tau)]

theorem dir_tau : direction tau = omega := by
  rw [tau,direction_real,Circle.coe_exp]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re,Real.cos_pi_div_three]; rfl
  · rw [Complex.exp_ofReal_mul_I_im,Real.sin_pi_div_three]; rfl

theorem dir_phase (i : Fin 3) : direction (phase i) = rot i := by
  have h : omega*omega = rot 1 := by simpa [pow_two] using omega_sq
  have h' : rot 1*rot 1 = rot 2 := by simpa [pow_two] using rot_sq
  fin_cases i
  · simp [phase,direction,rot]
  · exact (direction_add tau tau).trans (by rw [dir_tau,h]; rfl)
  · change direction ((tau+tau)+(tau+tau)) = rot 2
    rw [direction_add,direction_add,dir_tau,h,h']

theorem norm_rho : ‖rho‖ = 1 := by rw [Complex.norm_def,rho_unit,Real.sqrt_one]
theorem dir_gamma : direction gamma = rho := by
  rw [gamma,direction_real,Circle.coe_exp]
  simpa only [norm_rho,Complex.ofReal_one,one_mul] using Complex.norm_mul_exp_arg_mul_I rho

theorem dense_gamma : DenseRange (fun n : ℤ => n • gamma) := by
  rw [gamma,AddCircle.denseRange_zsmul_coe_iff]
  have hn : rho ≠ 0 := by intro h; simpa [h] using norm_rho
  have hcos : Real.cos (Complex.arg rho) = -5/6 := by rw [Complex.cos_arg hn,norm_rho,div_one]; rfl
  rintro ⟨q,hq⟩
  have eq : Complex.arg rho = ((2*q : ℚ) : ℝ)*Real.pi := by
    push_cast
    field_simp [Real.pi_ne_zero] at hq
    linarith
  have N := niven ⟨2*q,eq⟩ ⟨(-5/6 : ℚ), by push_cast; exact hcos⟩
  rw [hcos] at N
  norm_num at N

theorem shift_ae {P : Angles → Prop} (h : ∀ᵐ t ∂angularMeasure, P t) (a : Angles) :
    ∀ᵐ t ∂angularMeasure, P (t+a) :=
  (measurePreserving_add_right angularMeasure a).quasiMeasurePreserving.ae h

theorem twice_period {f : Angles → Bool}
    (h : ∀ᵐ t ∂angularMeasure, f (t+tau) = !(f t)) :
    ∀ᵐ t ∂angularMeasure, ∀ i : Fin 3, f (t+phase i) = f t := by
  have h₂ : ∀ᵐ t ∂angularMeasure, f (t+(tau+tau)) = f t := by
    filter_upwards [h,shift_ae h tau] with t ht h'
    rw [← add_assoc,h',ht,Bool.not_not]
  filter_upwards [h₂,shift_ae h₂ (tau+tau)] with t ht h'
  intro i
  fin_cases i
  · simp [phase]
  · exact ht
  · simpa [phase,← add_assoc] using h'.trans ht

theorem no_alternating_period (f : Angles → Bool) (hm : MeasurableSet {t | f t = true})
    (ha : ∀ᵐ t ∂angularMeasure, f (t+tau) = !(f t))
    (hg : ∀ᵐ t ∂angularMeasure, f (t+gamma) = f t) : False := by
  let R := {t | f t = true}
  have hinv : (fun t => gamma+t) ⁻¹' R =ᵐ[angularMeasure] R := by
    filter_upwards [hg] with t ht
    change (f (gamma+t) = true) = (f t = true)
    rw [add_comm gamma,ht]
  have he := ergodic_add_left_of_denseRange_zsmul dense_gamma angularMeasure
  rcases he.ae_empty_or_univ_of_preimage_ae_le hm.nullMeasurableSet hinv.le with hz|hz
  · have hf : ∀ᵐ t ∂angularMeasure, f t = false := by
      filter_upwards [hz] with t ht
      change (f t = true) = False at ht
      cases e : f t <;> simp_all
    obtain ⟨t,ht,h',h''⟩ := (ha.and (hf.and (shift_ae hf tau))).exists
    simp_all
  · have hf : ∀ᵐ t ∂angularMeasure, f t = true := by
      filter_upwards [hz] with t ht
      change (f t = true) = True at ht
      exact of_eq_true ht
    obtain ⟨t,ht,h',h''⟩ := (ha.and (hf.and (shift_ae hf tau))).exists
    simp_all

end
end C5
end
