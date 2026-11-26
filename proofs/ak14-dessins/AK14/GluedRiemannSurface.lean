import AK14.AtlasAnalytic

namespace AK14.Gluing
open Complex Set Topology
open scoped OnePoint Manifold
noncomputable section

def affineInclusion : OpenPartialHomeomorph ℂ (OnePoint ℂ) :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph _

theorem ordinary_chart_exact {n : ℕ} [NeZero n] (T : Triple n) {y : Surface T}
    (hy : coveringProjection T y∈awayFromCorners) :
    ∃ e : OpenPartialHomeomorph (Surface T) ℂ, y∈e.source ∧ ∀ v∈e.source, gluedMap T v=(e v : OnePoint ℂ) := by
  obtain ⟨s,hs,rep⟩ := (glued_covering_away_from_corners T).isLocalHomeomorphOn y hy
  let u := s.transHomeomorph complexTarget
  let e := u.trans affineInclusion.symm
  have hx : gluedMap T y≠∞ := by
    intro inf
    exact (away_iff_avoids_vertices _).mp hy 2 (complexTarget.injective (inf.trans complexTarget_infty.symm))
  have ur (v : Surface T) : u v=gluedMap T v := congrArg complexTarget ((congrFun rep v).symm)
  have adom (v : OnePoint ℂ) : v∈affineInclusion.target ↔ v≠∞ := by
    rw [affineInclusion,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact OnePoint.ne_infty_iff_exists.symm
  refine ⟨e,⟨hs,(adom _).mpr ((ur y).symm ▸ hx)⟩,?_⟩
  intro v hv
  rw [←ur v]
  exact (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_right_inv _ ((adom _).mp hv.2 |> OnePoint.ne_infty_iff_exists.mp)).symm

/-- Information retained about the preferred chart at a point. -/
def preferred {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (y : Surface T)
    (e : OpenPartialHomeomorph (Surface T) ℂ) : Prop :=
  (coveringProjection T y∈awayFromCorners ∧ ∀ v∈e.source, gluedMap T v=(e v : OnePoint ℂ)) ∨
    ∃ (j : Fin 3) (x : Fin n), cell T (true,x) (vertex j)=y ∧ e=cornerChart T pr j x

theorem preferred_charts_cover {n : ℕ} [NeZero n] (T : Triple n) (pr : T 0*T 1*T 2=1) (y : Surface T) :
    ∃ e : OpenPartialHomeomorph (Surface T) ℂ, y∈e.source ∧ preferred T pr y e := by
  classical
  by_cases regular : coveringProjection T y∈awayFromCorners
  · obtain ⟨e,dom,rep⟩ := ordinary_chart_exact T regular
    exact ⟨e,dom,Or.inl ⟨regular,rep⟩⟩
  · rw [away_iff_avoids_vertices] at regular; push_neg at regular
    obtain ⟨j,hj⟩ := regular
    let Y := geometric_corner_fiber T pr j
    obtain ⟨c,eq⟩ := Y.surjective ⟨y,hj⟩
    induction c using Quotient.inductionOn with | _ x =>
      have pt : cell T (true,x) (vertex j)=y := congrArg Subtype.val eq
      exact ⟨cornerChart T pr j x,pt ▸ corner_mem_chart T pr j x,Or.inr ⟨j,x,pt,rfl⟩⟩

theorem preferred_adapted {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) {y : Surface T}
    {e : OpenPartialHomeomorph (Surface T) ℂ} (h : preferred T pr y e) : adapted (gluedMap T) e := by
  rcases h with ⟨_,rep⟩|⟨j,x,_,rfl⟩
  · exact ⟨0,1,one_ne_zero,fun v hv => by simpa [branchModel] using rep v hv⟩
  · exact ⟨j,degreeAt T j x,degreeAt_ne T j x,fun _ hv => chart_represents_projection T pr j x hv⟩

/-- The atlas of all local power presentations of the actual marked projection. -/
def surfaceAtlas {n : ℕ} [NeZero n] (T : Triple n) (pr : T 0*T 1*T 2=1) : ChartedSpace ℂ (Surface T) where
  atlas := {e | adapted (gluedMap T) e}
  chartAt y := (preferred_charts_cover T pr y).choose
  mem_chart_source y := (preferred_charts_cover T pr y).choose_spec.1
  chart_mem_atlas y := preferred_adapted T pr (preferred_charts_cover T pr y).choose_spec.2

theorem surface_analytic {n : ℕ} [NeZero n] (T : Triple n) (pr : T 0*T 1*T 2=1) :
    letI := surfaceAtlas T pr
    IsManifold 𝓘(ℂ) ⊤ (Surface T) := by
  letI := surfaceAtlas T pr
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have H := (adapted_transition (F:=gluedMap T) he he').contDiffOn_of_completeSpace (n:=⊤)
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
    Function.comp_id,Set.preimage_id_eq,Set.range_id,Set.inter_univ] using H

end
end AK14.Gluing
