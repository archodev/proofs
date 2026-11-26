import AK14.ParameterFibers

namespace AK14.Gluing
open Set Filter Topology
open scoped OnePoint unitInterval
open SeriesAt (affineValue fiberPoly AffineFiber basePoint standardLoops Carries)
noncomputable section

/-- A marked conformal parameter transports each actual lifted loop through the
same affine coordinate and the same numbering of the whole base fiber. -/
theorem parameter_carries {n : ℕ} [NeZero n] {p : Passport} {T : Triple n} {pr : T 0*T 1*T 2=1}
    {M : Marking T p} (N : ConformalParameter pr M) {f : RatFunc ℂ}
    (eq : ∀ z : ℂ, pulledScalar T N.phi=ᶠ[𝓝[≠] z] affineValue f) : Carries f standardLoops T := by
  have pole : gluedMap T (N.phi ∞)=∞ := by rw [N.atC,site_value,M.rowC]; rfl
  let get (y : Surface T) : ℂ := affineInclusion.symm (N.phi.symm y)
  have dom {y : Surface T} {u : ℂ} (hy : gluedMap T y=(u : OnePoint ℂ)) :
      N.phi.symm y∈affineInclusion.target := by
    rw [affineInclusion,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    apply OnePoint.ne_infty_iff_exists.mp
    intro e
    have same := congrArg N.phi e
    rw [N.phi.apply_symm_apply] at same
    exact OnePoint.coe_ne_infty u (hy.symm.trans (same ▸ pole))
  have back {y : Surface T} {u : ℂ} (hy : gluedMap T y=(u : OnePoint ℂ)) :
      N.phi (get y : OnePoint ℂ)=y := by
    have lift : (get y : OnePoint ℂ)=N.phi.symm y := affineInclusion.right_inv (dom hy)
    rw [lift,N.phi.apply_symm_apply]
  have forward (z : ℂ) : get (N.phi (z : OnePoint ℂ))=z := by
    change affineInclusion.symm (N.phi.symm (N.phi (z : OnePoint ℂ)))=z
    rw [N.phi.symm_apply_apply]
    exact OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv _
  let E : {y : Surface T // gluedMap T y=(basePoint : OnePoint ℂ)} ≃ AffineFiber f basePoint :=
    { toFun := fun y => ⟨get y.val,SeriesAt.fiber_roots.mp ((affine_fiber_iff T pr N.phi eq _ _).mp ((back y.property).symm ▸ y.property))⟩
      invFun := fun z => ⟨N.phi (z.val : OnePoint ℂ),(affine_fiber_iff T pr N.phi eq _ _).mpr (SeriesAt.fiber_roots.mpr z.property)⟩
      left_inv := fun y => Subtype.ext (back y.property)
      right_inv := fun z => Subtype.ext (forward z.val) }
  obtain ⟨lab,lifts⟩ := glued_standard_realization T pr
  refine ⟨lab.trans E,?_⟩
  intro j i
  obtain ⟨L,proj⟩ := lifts j i
  let lift : C(I,ℂ) := ⟨fun t => get (L t),continuous_iff_continuousAt.mpr (fun t =>
    ContinuousAt.comp (g:=affineInclusion.symm) (f:=fun s : I => N.phi.symm (L s)) (affineInclusion.symm.continuousAt (dom (proj t)))
      ((N.phi.symm.continuous.comp L.continuous).continuousAt (x:=t)))⟩
  refine ⟨lift,congrArg get L.source,congrArg get L.target,?_⟩
  intro t
  exact (affine_fiber_iff T pr N.phi eq _ _).mp ((back (proj t)).symm ▸ proj t)

end
end AK14.Gluing

