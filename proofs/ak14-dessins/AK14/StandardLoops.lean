import AK14.LoopData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Counterclockwise based circles about 0 and 1 and the reverse composite
about infinity, with right-to-left permutation multiplication. -/
namespace AK14.SeriesAt
open Complex
open scoped unitInterval
noncomputable section

def basePoint : ℂ := 1/2

def circleZero : Path basePoint basePoint where
  toFun t := Complex.exp (((2*Real.pi*(t:ℝ) : ℝ) : ℂ)*Complex.I)/2
  continuous_toFun := by fun_prop
  source' := by simp [basePoint]
  target' := by simp [basePoint,Complex.exp_two_pi_mul_I]

def circleOne : Path basePoint basePoint where
  toFun t := 1-circleZero t
  continuous_toFun := continuous_const.sub circleZero.continuous
  source' := by rw [circleZero.source]; norm_num [basePoint]
  target' := by rw [circleZero.target]; norm_num [basePoint]

def circleInfinity : Path basePoint basePoint := (circleOne.trans circleZero).symm

private theorem circle_norm (t : unitInterval) : ‖circleZero t‖=(1/2:ℝ) := by
  change ‖Complex.exp (((2*Real.pi*(t:ℝ) : ℝ) : ℂ)*Complex.I)/2‖=_
  rw [norm_div,Complex.norm_exp_ofReal_mul_I]
  norm_num

private theorem zero_avoid (t : unitInterval) : circleZero t ≠0 ∧ circleZero t≠1 := by
  have h := circle_norm t
  constructor <;> intro e <;> norm_num [e] at h

private theorem one_avoid (t : unitInterval) : circleOne t≠0 ∧ circleOne t≠1 := by
  obtain ⟨a,b⟩ := zero_avoid t
  change 1-circleZero t≠0 ∧ 1-circleZero t≠1
  exact ⟨fun e => b (sub_eq_zero.mp e).symm,fun e => a (by linear_combination -e)⟩

private theorem infinity_avoid (t : unitInterval) : circleInfinity t≠0 ∧ circleInfinity t≠1 := by
  have h : circleInfinity t∈Set.range (fun t => circleInfinity t) := ⟨t,rfl⟩
  change circleInfinity t∈Set.range (circleOne.trans circleZero).symm at h
  rw [Path.symm_range,Path.trans_range] at h
  rcases h with ⟨u,e⟩ | ⟨u,e⟩
  · exact e ▸ one_avoid u
  · exact e ▸ zero_avoid u

def standardLoops : LoopSystem ℂ where
  base := basePoint
  loop := ![circleZero.toContinuousMap,circleOne.toContinuousMap,circleInfinity.toContinuousMap]
  start := by intro j; fin_cases j <;> exact Path.source _
  finish := by intro j; fin_cases j <;> exact Path.target _
  avoid := by intro j t; fin_cases j
              · exact zero_avoid t
              · exact one_avoid t
              · exact infinity_avoid t

end
end AK14.SeriesAt
