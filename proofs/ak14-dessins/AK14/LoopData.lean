import AK14.RegularFiber
import Mathlib.Topology.Path

namespace AK14.SeriesAt
open scoped unitInterval
noncomputable section
variable {K : Type*} [Field K] [CharZero K] [TopologicalSpace K]

/-- Three named loops with a common base point and prescribed directions. -/
structure LoopSystem (K : Type*) [TopologicalSpace K] [Zero K] [One K] where
  base : K
  loop : Fin 3 → C(I,K)
  start : ∀ j, loop j 0=base
  finish : ∀ j, loop j 1=base
  avoid : ∀ j t, loop j t≠0 ∧ loop j t≠1

/-- A sheet numbering and continuous root paths for the affine fiber polynomials.
This definition contains no uniqueness or equivalence hypothesis. -/
def Carries {n : ℕ} (f : RatFunc K) (loops : LoopSystem K) (T : Triple n) : Prop :=
  ∃ lab : Fin n ≃ AffineFiber f loops.base, ∀ (j : Fin 3) (i : Fin n), ∃ lift : C(I,K),
    lift 0=(lab i).val ∧ lift 1=(lab (T j i)).val ∧
      ∀ t, (fiberPoly f (loops.loop j t)).IsRoot (lift t)


end
end AK14.SeriesAt
