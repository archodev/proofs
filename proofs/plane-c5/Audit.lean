import C5

open MeasureTheory

-- This includes the closing edge from the last vertex to the first.
example : (List.finRange 5).map (fun i : Fin 5 => i + 1) =
    ([1, 2, 3, 4, 0] : List (Fin 5)) := by decide

-- Restate the requested theorem independently of the project's abbreviations.
example (c : EuclideanSpace ℝ (Fin 2) → Bool) :
    ∃ p : Fin 5 → EuclideanSpace ℝ (Fin 2), Function.Injective p ∧
      (∀ i : Fin 5, dist (p i) (p (i + 1)) = 1) ∧
      ∀ i : Fin 5, c (p i) = c (p 0) :=
  C5.plane_C5 c

example (c : EuclideanSpace ℝ (Fin 2) → Bool)
    (hc : NullMeasurableSet {x | c x = true} volume) :
    ∃ p : Fin 5 → EuclideanSpace ℝ (Fin 2), Function.Injective p ∧
      (∀ i : Fin 5, dist (p i) (p (i + 1)) = 1) ∧
      ∀ i : Fin 5, c (p i) = c (p 0) :=
  C5.measurable_plane_C5 c hc

#print C5.PlaneMono
#check C5.plane_C5
#check C5.measurable_plane_C5
#print axioms C5.plane_C5
#print axioms C5.unrestricted_C5
#print axioms C5.measurable_plane_C5
#print axioms C5.measurable_C5
#print axioms C5.two_circles
#print axioms C5.angular_four
#print axioms C5.density_transfer
#print axioms C5.ae_density
#print axioms C5.measurable_core
#print axioms OAI.PlaneFiveColor.Spectral.finite_wild_fourier
#print axioms C5.Model.residual_correlation
#print axioms C5.carrier_shapes_dense
#print axioms C5.Model.residual_nonzero
#print axioms C5.Model.triangle_needed
#print axioms C5.Model.triangle_classification
#print axioms C5.Model.prism_law
#print axioms C5.Model.no_avoiding_law
