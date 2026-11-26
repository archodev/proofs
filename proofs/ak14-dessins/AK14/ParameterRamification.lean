import AK14.ParameterDivisor
import AK14.ParameterFibers

namespace AK14.Gluing
open Complex Set Filter Topology
open scoped OnePoint PowerSeries
open SeriesAt (localValue affineValue BranchGerm NormalizedCover OrdinaryGerm expandAt)
noncomputable section

theorem transported_branch {n : ℕ} [NeZero n] {p : Passport} {T : Triple n} {pr : T 0*T 1*T 2=1}
    {M : Marking T p} (N : ConformalParameter pr M) {f : RatFunc ℂ}
    (agree : pulledScalar T N.phi=ᶠ[cofinite] affineValue f) (s : CornerSite T) (x : OnePoint ℂ)
    (pt : N.phi x=sitePoint T pr s) :
    BranchGerm (expandAt x f) s.1 (classDegree (T s.1) s.2) := by
  have loc : localValue x f=ᶠ[𝓝[≠] 0] analyticScalar T N.phi x := (SeriesAt.localArgument_cofinite x).eventually agree.symm
  rcases analyticScalar_chart T pr N.phi x with ⟨reg,_,_⟩|⟨j,i,mark,center,eq⟩
  · have proj := (geometric_corner_fiber T pr s.1 s.2).property
    exact False.elim ((away_iff_avoids_vertices _).mp reg s.1 (pt ▸ proj))
  · have si := preferred_corner_unique T pr (mark.trans pt)
    subst s
    change BranchGerm _ j (classDegree (T j) (cornerClass (T j) i))
    rw [classDegree_at]
    apply SeriesAt.branch_of_order (cycleDegree_pos _ _)
    have comp := (loc.trans eq).fun_comp (SeriesAt.scalarTargetChart j)
    have red (z : ℂ) : SeriesAt.scalarTargetChart j (scalarModel j (degreeAt T j i) z)=z^(degreeAt T j i) := by
      fin_cases j <;> simp [SeriesAt.scalarTargetChart,scalarModel]
    apply exactOrder_punctured (g:=fun w => (readChart T pr N.phi x w)^(degreeAt T j i))
    · exact comp.trans (Eventually.of_forall (fun w => red _))
    · simpa only [zpow_natCast] using simple_coordinate_power (N.analytic x) (N.nonsingular x) center ((degreeAt T j i):ℤ)

set_option maxHeartbeats 500000 in
theorem deriv_nonzero_of_zero_branch {f : RatFunc ℂ} {d : ℕ}
    (h : BranchGerm (SeriesAt.expand 0 f) 0 d) : ratDeriv ℂ f≠0 := by
  intro zero
  obtain ⟨c,eq⟩ := (ratDeriv_constants ℂ f).mp zero
  obtain ⟨V,nv,vc,_,ex⟩ := h
  change SeriesAt.expand 0 f=SeriesAt.embed ℂ V at ex
  rw [←eq] at ex
  change SeriesAt.expandAt (some 0) (SeriesAt.kRat ℂ c)=_ at ex
  rw [SeriesAt.expandAt_scalar] at ex
  have same : PowerSeries.C (R := ℂ) c=V := IsFractionRing.injective (PowerSeries ℂ) (SeriesAt.GermField ℂ) ex
  have cz := congrArg (PowerSeries.constantCoeff (R := ℂ)) same
  simp only [PowerSeries.constantCoeff_C,vc] at cz
  exact nv (by rw [←same,cz,map_zero])

theorem parameter_normalized {n : ℕ} [NeZero n] {p : Passport} {T : Triple n} {pr : T 0*T 1*T 2=1}
    {M : Marking T p} (N : ConformalParameter pr M) {f : RatFunc ℂ}
    (agree : pulledScalar T N.phi=ᶠ[cofinite] affineValue f) : NormalizedCover p f := by
  have A := transported_branch N agree M.A _ N.atA
  have B := transported_branch N agree M.B _ N.atB
  have C := transported_branch N agree M.C _ N.atC
  rw [M.degreeA,M.rowA] at A; rw [M.degreeB,M.rowB] at B; rw [M.degreeC,M.rowC] at C
  refine ⟨deriv_nonzero_of_zero_branch A,A,B,C,?_⟩
  intro z nz no
  let x : OnePoint ℂ := z
  have loc : localValue x f=ᶠ[𝓝[≠] 0] analyticScalar T N.phi x := (SeriesAt.localArgument_cofinite x).eventually agree.symm
  rcases analyticScalar_chart T pr N.phi x with ⟨_,rep,c0,c1⟩|⟨j,i,pt,_,_⟩
  · left
    apply SeriesAt.ordinary_of_order (x:=x) c0 c1
    apply exactOrder_punctured ((loc.trans rep).sub (EventuallyEq.rfl (f:=fun _ => readChart T pr N.phi x 0)))
    exact nonzero_deriv_order_one (N.analytic x) (N.nonsingular x)
  · right
    let s : CornerSite T := ⟨j,cornerClass (T j) i⟩
    have spt : N.phi x=sitePoint T pr s := pt.symm
    have nA : s≠M.A := fun eq => nz (OnePoint.coe_injective (N.phi.injective (spt.trans (eq ▸ N.atA.symm))))
    have nB : s≠M.B := fun eq => no (OnePoint.coe_injective (N.phi.injective (spt.trans (eq ▸ N.atB.symm))))
    have nC : s≠M.C := fun eq => OnePoint.coe_ne_infty z (N.phi.injective (spt.trans (eq ▸ N.atC.symm)))
    exact ⟨s.1,(M.others s nA nB nC) ▸ transported_branch N agree s x spt⟩

end
end AK14.Gluing
