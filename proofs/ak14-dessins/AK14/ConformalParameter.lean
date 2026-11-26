import AK14.SphereParameterData
import AK14.ExceptionalSites
import AK14.FormalBranchTransfer

namespace AK14.Gluing
open Complex Set Filter Topology
open scoped OnePoint Manifold
noncomputable section

@[simp] theorem sphereArgument_zero (x : OnePoint ℂ) : sphereArgument x 0=x := by cases x <;> simp [sphereArgument]

theorem sphereArgument_neighborhood (x : OnePoint ℂ) : Tendsto (sphereArgument x) (𝓝 0) (𝓝 x) := by
  cases x with
  | coe a =>
    change Tendsto (fun w : ℂ => ((w+a:ℂ):OnePoint ℂ)) (𝓝 0) (𝓝 (a:OnePoint ℂ))
    simpa only [Function.comp_apply,Function.comp_def,Pi.add_apply,id_eq,zero_add] using
      (OnePoint.continuous_coe.comp (continuous_id.add (continuous_const (y:=a)))).continuousAt.tendsto (x:=0)
  | infty =>
    suffices c : ContinuousAt (sphereArgument ∞) 0 by simpa [ContinuousAt] using c
    rw [←continuousWithinAt_compl_self]
    change Tendsto _ _ (𝓝 (sphereArgument ∞ 0))
    rw [sphereArgument_zero]
    have inv := tendsto_inv₀_nhdsWithin_ne_zero (α:=ℂ)
    rw [Metric.cobounded_eq_cocompact,←Filter.coclosedCompact_eq_cocompact] at inv
    apply (OnePoint.tendsto_coe_infty.comp inv).congr'
    filter_upwards [puncture_avoids 0 0] with w hw; simp [sphereArgument,OnePoint.infty,hw]

theorem sphereArgument_punctured (x : OnePoint ℂ) :
    ∀ᶠ w in 𝓝[≠] (0:ℂ), sphereArgument x w=(SeriesAt.localArgument x w : OnePoint ℂ) := by
  cases x with
  | coe a => exact Eventually.of_forall fun _ => rfl
  | infty => filter_upwards [puncture_avoids 0 0] with w hw; simp [sphereArgument,SeriesAt.localArgument,hw]

/-- An analytic sphere parameter normalized at the three distinguished points.
The derivative and analyticity concern the specific chosen complex chart. -/
structure ConformalParameter {n : ℕ} [NeZero n] {p : Passport} {T : Triple n} (pr : T 0*T 1*T 2=1)
    (M : Marking T p) where
  phi : OnePoint ℂ ≃ₜ Surface T
  atA : phi (0:ℂ)=sitePoint T pr M.A
  atB : phi (1:ℂ)=sitePoint T pr M.B
  atC : phi ∞=sitePoint T pr M.C
  analytic : ∀ x, AnalyticAt ℂ (readChart T pr phi x) 0
  nonsingular : ∀ x, deriv (readChart T pr phi x) 0≠0

theorem nonzero_deriv_order_one {g : ℂ → ℂ} (ag : AnalyticAt ℂ g 0) (dg : deriv g 0≠0) :
    exactOrder (fun w => g w-g 0) 0 1 := by
  obtain ⟨U,mem,op,all⟩ := mem_nhds_iff.mp (Complex.analyticAt_iff_eventually_differentiableAt.mp ag)
  have hd : DifferentiableOn ℂ g U := fun w hw => (mem hw).differentiableWithinAt
  have D := (Complex.differentiableOn_dslope (op.mem_nhds all)).mpr hd
  have a := (Complex.analyticOnNhd_iff_differentiableOn op).mpr D 0 all
  exact ⟨dslope g 0,a,by simpa using dg,Eventually.of_forall (fun w => by simpa using (sub_smul_dslope g 0 w).symm)⟩

def pulledScalar {n : ℕ} (T : Triple n) (φ : OnePoint ℂ ≃ₜ Surface T) (z : ℂ) :=
  surfaceFunction T (φ (z : OnePoint ℂ))

theorem preferred_corner_unique {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) {j : Fin 3} {x : Fin n}
    {s : CornerSite T} (eq : cell T (true,x) (vertex j)=sitePoint T pr s) : (⟨j,cornerClass (T j) x⟩ : CornerSite T)=s :=
  sitePoint_injective T pr eq

def analyticScalar {n : ℕ} (T : Triple n) (φ : OnePoint ℂ ≃ₜ Surface T) (x : OnePoint ℂ) (w : ℂ) :=
  pulledScalar T φ (SeriesAt.localArgument x w)

theorem analyticScalar_chart {n : ℕ} [NeZero n] (T : Triple n) (pr : T 0*T 1*T 2=1)
    (φ : OnePoint ℂ ≃ₜ Surface T) (x : OnePoint ℂ) :
    letI := surfaceAtlas T pr
    let g := readChart T pr φ x
    ((coveringProjection T (φ x)∈awayFromCorners ∧ analyticScalar T φ x=ᶠ[𝓝[≠] 0] g ∧
        (g 0≠0 ∧ g 0≠1)) ∨
      ∃ (j : Fin 3) (i : Fin n), cell T (true,i) (vertex j)=φ x ∧ g 0=0 ∧
        analyticScalar T φ x=ᶠ[𝓝[≠] 0] (fun w => scalarModel j (degreeAt T j i) (g w))) := by
  letI := surfaceAtlas T pr
  let e := chartAt ℂ (φ x)
  let g := readChart T pr φ x
  have base : g 0=e (φ x) := by simp [g,readChart,e]
  have hφ := φ.continuous.continuousAt.tendsto.comp (sphereArgument_neighborhood x)
  have dom : ∀ᶠ w in 𝓝[≠] (0:ℂ), φ (sphereArgument x w)∈e.source :=
    mem_nhdsWithin_of_mem_nhds (hφ.eventually (e.open_source.mem_nhds (mem_chart_source ℂ (φ x))))
  have pref : preferred T pr (φ x) e := (preferred_charts_cover T pr _).choose_spec.2
  rcases pref with ⟨reg,rep⟩|⟨j,i,center,ce⟩
  · left
    refine ⟨reg,?_,?_⟩
    · filter_upwards [dom,sphereArgument_punctured x] with w hw eq
      change planeValue (gluedMap T (φ (SeriesAt.localArgument x w : OnePoint ℂ)))=_
      rw [←eq,rep _ hw]; rfl
    · have avoids := (away_iff_avoids_vertices _).mp reg
      have val := rep (φ x) (mem_chart_source ℂ (φ x))
      change g 0≠0 ∧ g 0≠1
      rw [base]
      constructor
      · intro zero; rw [zero] at val
        exact avoids 0 (complexTarget.injective (val.trans complexTarget_zero.symm))
      · intro one; rw [one] at val
        exact avoids 1 (complexTarget.injective (val.trans complexTarget_one.symm))
  · right
    refine ⟨j,i,center,?_,?_⟩
    · change g 0=0; rw [base,ce,←center,cornerChart_center]
    · filter_upwards [dom,sphereArgument_punctured x] with w hw eq
      rw [ce] at hw
      change planeValue (gluedMap T (φ (SeriesAt.localArgument x w : OnePoint ℂ)))=_
      rw [←eq,chart_represents_projection T pr j i hw,plane_branch]
      change _=scalarModel j _ (e _); rw [ce]

end
end AK14.Gluing
