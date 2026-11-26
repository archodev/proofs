import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A continuous choice of an e-th root on each closed half-plane. On the
negative axis the two choices differ by one primitive root of unity. -/
namespace AK14.Polar
open Complex Real Filter Topology Set
noncomputable section

def phase (e : ℕ) : ℂ := exp (2*(Real.pi:ℂ)*Complex.I/(e:ℂ))

theorem primitive {e : ℕ} (h : e≠0) : IsPrimitiveRoot (phase e) e := Complex.isPrimitiveRoot_exp e h

def turn (e : ℕ) (θ : ℝ) : ℂ := Complex.exp (((θ/(e:ℝ):ℝ):ℂ)*Complex.I)

theorem turn_norm (e : ℕ) (θ : ℝ) : ‖turn e θ‖=1 := Complex.norm_exp_ofReal_mul_I _

theorem turn_power {e : ℕ} (h : e≠0) (θ : ℝ) : turn e θ^e=Complex.exp ((θ:ℂ)*Complex.I) := by
  unfold turn
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp [show (e:ℂ)≠0 by exact_mod_cast h]

theorem turn_full (e : ℕ) : turn e (2*Real.pi)=phase e := by
  unfold turn phase; congr 1; push_cast; ring

theorem turn_add (e : ℕ) (u v : ℝ) : turn e (u+v)=turn e u*turn e v := by
  unfold turn
  rw [← Complex.exp_add]
  congr 1; push_cast; ring

def amplitude (e : ℕ) (w : ℂ) := ‖w‖ ^ ((e:ℝ)⁻¹)
def angle (w : ℂ) : ℝ := Real.arccos (w.re / ‖w‖)
def halfRoot (e : ℕ) (upper : Bool) (w : ℂ) : ℂ :=
  (amplitude e w : ℂ) * turn e (if upper then angle w else -angle w)

theorem halfRoot_norm (e : ℕ) (u : Bool) (w : ℂ) : ‖halfRoot e u w‖=amplitude e w := by
  rw [halfRoot,norm_mul,turn_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem halfRoot_zero {e : ℕ} (h : e≠0) (u : Bool) : halfRoot e u 0=0 := by
  apply norm_eq_zero.mp
  rw [halfRoot_norm,amplitude,norm_zero,Real.zero_rpow]
  exact inv_ne_zero (by exact_mod_cast h)

theorem halfRoot_continuous {e : ℕ} (h : e≠0) (u : Bool) : Continuous (halfRoot e u) := by
  have pe : 0≤(e:ℝ)⁻¹ := by positivity
  have ca : Continuous (amplitude e) := continuous_norm.rpow_const (fun _ => Or.inr pe)
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases z : w=0
  · subst w
    change Tendsto _ _ _
    rw [halfRoot_zero h,tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [halfRoot_norm]
    have a : amplitude e 0=0 := by rw [← halfRoot_norm e u,halfRoot_zero h,norm_zero]
    exact a ▸ ca.continuousAt
  · have theta : ContinuousAt angle w :=
      Real.continuous_arccos.continuousAt.comp (Complex.continuous_re.continuousAt.div continuous_norm.continuousAt (norm_ne_zero_iff.mpr z))
    have tu (f : ℂ → ℝ) (H : ContinuousAt f w) : ContinuousAt (fun x => turn e (f x)) w :=
      Complex.continuous_exp.continuousAt.comp ((Complex.continuous_ofReal.continuousAt.comp (H.div_const _)).mul continuousAt_const)
    cases u
    · exact (Complex.continuous_ofReal.continuousAt.comp ca.continuousAt).mul (tu _ theta.neg)
    · exact (Complex.continuous_ofReal.continuousAt.comp ca.continuousAt).mul (tu _ theta)

theorem upper_power {e : ℕ} (h : e≠0) {w : ℂ} (im : 0≤w.im) : (halfRoot e true w)^e=w := by
  by_cases z : w=0
  · subst w; simp [halfRoot_zero h,zero_pow h]
  · rw [halfRoot,mul_pow,turn_power h,← Complex.ofReal_pow]
    simp only [if_true,Bool.true_eq]
    rw [amplitude,Real.rpow_inv_natCast_pow (norm_nonneg _) h]
    change _*Complex.exp ((angle w:ℂ)*Complex.I)=w
    rw [show angle w=w.arg from (Complex.arg_of_im_nonneg_of_ne_zero im z).symm]
    exact Complex.norm_mul_exp_arg_mul_I _

theorem lower_power {e : ℕ} (h : e≠0) {w : ℂ} (im : w.im≤0) : (halfRoot e false w)^e=w := by
  have pos : 0≤(starRingEnd ℂ w).im := by simpa using im
  have eq := congrArg (starRingEnd ℂ) (upper_power h pos)
  rw [map_pow] at eq
  simp only [starRingEnd_self_apply] at eq
  convert eq using 2
  simp [halfRoot,amplitude,angle,turn,← Complex.exp_conj,Complex.conj_ofReal]
  left; congr 1; ring

theorem positive_seam (e : ℕ) {w : ℂ} (real : w.im=0) (pos : 0≤w.re) :
    halfRoot e true w=halfRoot e false w := by
  by_cases zero : w=0
  · subst w; by_cases h : e=0
    · subst e; simp [halfRoot,turn]
    · simp [halfRoot_zero h]
  · have a : angle w=0 := by
      rw [show angle w=w.arg from (Complex.arg_of_im_nonneg_of_ne_zero (by linarith) zero).symm]
      exact Complex.arg_eq_zero_iff.mpr ⟨pos,real⟩
    simp [halfRoot,a]

theorem negative_seam {e : ℕ} (h : e≠0) {w : ℂ} (real : w.im=0) (neg : w.re≤0) :
    halfRoot e true w=phase e*halfRoot e false w := by
  by_cases zero : w=0
  · subst w; simp [halfRoot_zero h]
  · have n : w.re<0 := lt_of_le_of_ne neg (fun e => zero (Complex.ext (by simpa using e) (by simpa using real)))
    have a : angle w=Real.pi := by
      rw [show angle w=w.arg from (Complex.arg_of_im_nonneg_of_ne_zero (by linarith) zero).symm]
      exact Complex.arg_eq_pi_iff.mpr ⟨n,real⟩
    simp only [halfRoot,if_true,Bool.false_eq_true,if_false,a]
    have step : turn e Real.pi=phase e*turn e (-Real.pi) := calc
      _ = turn e (2*Real.pi + (-Real.pi)) := congrArg (turn e) (by ring)
      _ = _ := by rw [turn_add,turn_full]
    rw [step]; ring

end
end AK14.Polar
