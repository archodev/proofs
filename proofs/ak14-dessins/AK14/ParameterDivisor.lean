import AK14.ConformalParameter

namespace AK14.Gluing
open Complex Set Filter Topology
open scoped OnePoint BigOperators Classical
noncomputable section

def zeroPoleWeight (j : Fin 3) (d : ℕ) : ℤ := ![(d:ℤ),0,-(d:ℤ)] j

def parameterDivisor {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (φ : OnePoint ℂ ≃ₜ Surface T) : Option ℂ →₀ ℤ :=
  ∑ i : CornerSite T, Finsupp.single (φ.symm (sitePoint T pr i)) (zeroPoleWeight i.1 (classDegree (T i.1) i.2))

theorem paramDivisor_site {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (φ : OnePoint ℂ ≃ₜ Surface T) (s : CornerSite T) :
    parameterDivisor T pr φ (φ.symm (sitePoint T pr s))=zeroPoleWeight s.1 (classDegree (T s.1) s.2) := by
  unfold parameterDivisor
  rw [Finset.sum_apply',Finset.sum_eq_single s]
  · exact Finsupp.single_eq_same
  · intro b _ ne; exact Finsupp.single_eq_of_ne (φ.symm.injective.ne ((sitePoint_injective T pr).ne ne.symm))
  · simp

theorem paramDivisor_regular {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (φ : OnePoint ℂ ≃ₜ Surface T)
    (x : OnePoint ℂ) (h : coveringProjection T (φ x)∈awayFromCorners) : parameterDivisor T pr φ x=0 := by
  unfold parameterDivisor; rw [Finset.sum_apply']; apply Finset.sum_eq_zero
  intro i _; apply Finsupp.single_eq_of_ne
  intro eq; have y : sitePoint T pr i=φ x := by rw [eq,φ.apply_symm_apply]
  exact (away_iff_avoids_vertices _).mp h i.1 (y ▸ (geometric_corner_fiber T pr i.1 i.2).property)

theorem parameter_degree_zero {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (φ : OnePoint ℂ ≃ₜ Surface T) :
    (parameterDivisor T pr φ).degree=0 := by
  unfold parameterDivisor; rw [Finsupp.degree_eq_weight_one,map_sum]
  simp only [←Finsupp.degree_eq_weight_one,Finsupp.degree_single]
  rw [Fintype.sum_sigma,Fin.sum_univ_three]
  change (∑ c : Corners (T 0), (classDegree (T 0) c : ℤ))+(∑ _ : Corners (T 1), (0:ℤ))+
    (∑ c : Corners (T 2), -(classDegree (T 2) c : ℤ))=0
  have H (j : Fin 3) : (∑ c : Corners (T j), (classDegree (T j) c : ℤ))=n := by exact_mod_cast classDegree_sum (T j)
  simp [Finset.sum_neg_distrib,H]

theorem simple_coordinate_power {g : ℂ → ℂ} (ag : AnalyticAt ℂ g 0) (dg : deriv g 0≠0) (center : g 0=0) (k : ℤ) :
    exactOrder (fun z => (g z)^k) 0 k := by
  obtain ⟨u,au,nu,eq⟩ := nonzero_deriv_order_one ag dg
  refine ⟨fun z => (u z)^k,au.zpow nu,zpow_ne_zero k nu,?_⟩
  filter_upwards [eq] with z hz
  simp only [center,sub_zero,zpow_one] at hz
  simp only [sub_zero,hz,mul_zpow]

theorem scalar_model_order (j : Fin 3) (d : ℕ) (dn : d≠0) {g : ℂ → ℂ}
    (ag : AnalyticAt ℂ g 0) (dg : deriv g 0≠0) (center : g 0=0) :
    exactOrder (fun w => scalarModel j d (g w)) 0 (zeroPoleWeight j d) := by
  fin_cases j
  · simpa only [zpow_natCast] using simple_coordinate_power ag dg center (d:ℤ)
  · change exactOrder (fun w => 1-(g w)^d) 0 0
    exact ⟨fun w => 1-(g w)^d,analyticAt_const.sub (ag.pow d),by simp [center,zero_pow dn],Eventually.of_forall (fun _ => by simp)⟩
  · simpa only [zpow_neg,zpow_natCast] using simple_coordinate_power ag dg center (-(d:ℤ))

theorem exactOrder_punctured {f g : ℂ → ℂ} {x : ℂ} {i : ℤ} (eq : f=ᶠ[𝓝[≠] x] g) (h : exactOrder g x i) :
    exactOrder f x i := by obtain ⟨u,a,n,rep⟩ := h; exact ⟨u,a,n,eq.trans rep⟩

theorem param_scalar_order {n : ℕ} [NeZero n] {p : Passport} {T : Triple n} {pr : T 0*T 1*T 2=1}
    {M : Marking T p} (N : ConformalParameter pr M) (x : OnePoint ℂ) :
    exactOrder (analyticScalar T N.phi x) 0 (parameterDivisor T pr N.phi x) := by
  rcases analyticScalar_chart T pr N.phi x with ⟨reg,rep,n0,_⟩|⟨j,i,pt,center,rep⟩
  · rw [paramDivisor_regular T pr N.phi x reg]
    apply exactOrder_punctured rep
    exact ⟨_,N.analytic x,n0,Eventually.of_forall (fun w => by simp)⟩
  · have loc : N.phi.symm (sitePoint T pr ⟨j,cornerClass (T j) i⟩)=x := N.phi.symm_apply_eq.mpr pt
    have val := paramDivisor_site T pr N.phi ⟨j,cornerClass (T j) i⟩
    rw [loc] at val
    change parameterDivisor T pr N.phi x=zeroPoleWeight j (classDegree (T j) (cornerClass (T j) i)) at val
    rw [val,classDegree_at]
    exact exactOrder_punctured rep (scalar_model_order j _ (degreeAt_ne T j i) (N.analytic x) (N.nonsingular x) center)

theorem uncenter_order {f : ℂ → ℂ} {a : ℂ} {m : ℤ} (h : exactOrder (fun w => f (w+a)) 0 m) : exactOrder f a m := by
  obtain ⟨u,au,nu,rep⟩ := h
  have an : AnalyticAt ℂ (fun w : ℂ => w-a) a := analyticAt_id.sub analyticAt_const
  have comp : AnalyticAt ℂ (fun w : ℂ => u (w-a)) a := (by simpa using au : AnalyticAt ℂ u (a-a)).comp (f:=fun w : ℂ => w-a) an
  refine ⟨_,comp,by simpa using nu,?_⟩
  have tend : Tendsto (fun w : ℂ => w-a) (𝓝[≠] a) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa using an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [puncture_avoids a a] with w hw using sub_ne_zero.mpr hw
  simpa using tend.eventually rep

theorem parameter_rational {n : ℕ} [NeZero n] {p : Passport} {T : Triple n} {pr : T 0*T 1*T 2=1}
    {M : Marking T p} (N : ConformalParameter pr M) :
    ∃ f : RatFunc ℂ, ∀ z : ℂ, pulledScalar T N.phi=ᶠ[𝓝[≠] z] SeriesAt.affineValue f := by
  let D := parameterDivisor T pr N.phi
  have total := parameter_degree_zero T pr N.phi
  have split : D.degree=D none+D.some.degree := D.sum_option_index (fun _ i => i) (by simp) (by simp)
  have atInfinity : D none= -D.some.degree := by change D.degree=0 at total; omega
  apply rational_of_balanced_divisor (pulledScalar T N.phi) D.some
  · intro z; exact uncenter_order (param_scalar_order N (z : OnePoint ℂ))
  · exact atInfinity ▸ param_scalar_order N ∞

end
end AK14.Gluing
