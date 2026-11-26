import AK14.GluedRiemannSurface

namespace AK14.Gluing
open Complex Set Filter Topology
open scoped OnePoint Manifold
noncomputable section

def sphereArgument : OnePoint ℂ → ℂ → OnePoint ℂ
  | none,w => if w=0 then ∞ else ((w⁻¹:ℂ):OnePoint ℂ)
  | some a,w => ((w+a:ℂ):OnePoint ℂ)

def readChart {n : ℕ} [NeZero n] (T : Triple n) (pr : T 0*T 1*T 2=1)
    (φ : OnePoint ℂ ≃ₜ Surface T) (x : OnePoint ℂ) (w : ℂ) : ℂ :=
  letI := surfaceAtlas T pr
  chartAt ℂ (φ x) (φ (sphereArgument x w))

/-- A nonsingular holomorphic sphere parameter, before choosing three marks. -/
structure SphereParameter {n : ℕ} [NeZero n] {T : Triple n} (pr : T 0*T 1*T 2=1) where
  phi : OnePoint ℂ ≃ₜ Surface T
  analytic : ∀ x, AnalyticAt ℂ (readChart T pr phi x) 0
  nonsingular : ∀ x, deriv (readChart T pr phi x) 0≠0

/-- Ordinary unmarked conformal uniformization of the glued genus-zero surfaces. -/
def GluedSphereUniformization : Prop :=
  ∀ (p : Passport) (n : ℕ) [NeZero n], p.Admissible n → ∀ (T : Triple n) (ht : Realizes p T),
    Nonempty (SphereParameter ht.product)

end
end AK14.Gluing
