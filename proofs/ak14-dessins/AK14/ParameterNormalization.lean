import AK14.SphereChanges
import AK14.UniformizationReduction

namespace AK14.Gluing
open Complex Set Filter Topology
open scoped OnePoint Manifold
noncomputable section

theorem change_with_infinity (c : OnePoint ℂ) : ∃ C : SphereChange, C.map ∞=c := by
  cases c with
  | infty => exact ⟨sphereIdentity,rfl⟩
  | coe c =>
    refine ⟨reciprocalChange.trans (affineChange c 1 one_ne_zero),?_⟩
    change (((1:ℂ)*0+c : ℂ):OnePoint ℂ)=(c : OnePoint ℂ)
    simp

/-- Three-point interpolation by an orientation-preserving analytic sphere automorphism. -/
theorem sphere_three_points (a b c : OnePoint ℂ) (ab : a≠b) (bc : b≠c) (ac : a≠c) :
    ∃ M : SphereChange, M.map (0:ℂ)=a ∧ M.map (1:ℂ)=b ∧ M.map ∞=c := by
  obtain ⟨C,cc⟩ := change_with_infinity c
  have finite (x : OnePoint ℂ) (h : x≠c) : ∃ z : ℂ, (z : OnePoint ℂ)=C.map.symm x := by
    apply OnePoint.ne_infty_iff_exists.mp
    exact fun eq => h ((C.map.symm_apply_eq.mp eq).trans cc)
  obtain ⟨u,uu⟩ := finite a ac
  obtain ⟨v,vv⟩ := finite b bc
  have ua : C.map (u : OnePoint ℂ)=a := C.map.apply_eq_iff_eq_symm_apply.mpr uu
  have vb : C.map (v : OnePoint ℂ)=b := C.map.apply_eq_iff_eq_symm_apply.mpr vv
  have ne : v-u≠0 := sub_ne_zero.mpr (fun eq => ab (ua.symm.trans (eq ▸ vb)))
  refine ⟨(affineChange u (v-u) ne).trans C,?_,?_,cc⟩
  · change C.map (((v-u)*0+u:ℂ):OnePoint ℂ)=a; simpa using ua
  · change C.map (((v-u)*1+u:ℂ):OnePoint ℂ)=b; simpa using vb

/-- The centered expression for an analytic parameter composed with a sphere change. -/
theorem SphereParameter.precompose {n : ℕ} [NeZero n] {T : Triple n} {pr : T 0*T 1*T 2=1}
    (P : SphereParameter pr) (M : SphereChange) :
    ∀ x, AnalyticAt ℂ (readChart T pr (M.map.trans P.phi) x) 0 ∧
      deriv (readChart T pr (M.map.trans P.phi) x) 0≠0 := by
  intro x
  obtain ⟨g,c,g0,ag,dg,nc,eq⟩ := M.germ x
  let F := readChart T pr P.phi (M.map x)
  have rep : readChart T pr (M.map.trans P.phi) x=ᶠ[𝓝 0] (F ∘ g) := by
    letI := surfaceAtlas T pr
    filter_upwards [eq] with w hw
    exact congrArg (fun q => chartAt ℂ (P.phi (M.map x)) (P.phi q)) hw
  have af : AnalyticAt ℂ F (g 0) := by rw [g0]; exact P.analytic _
  have df := af.differentiableAt.hasDerivAt.comp 0 dg
  refine ⟨(af.comp ag).congr rep.symm,?_⟩
  rw [rep.deriv_eq,df.deriv,g0]
  exact mul_ne_zero (P.nonsingular _) nc

theorem normalized_parameter_of_parameter {n : ℕ} [NeZero n] {p : Passport} {T : Triple n}
    {pr : T 0*T 1*T 2=1} (P : SphereParameter pr) (L : Marking T p) : Nonempty (ConformalParameter pr L) := by
  let value (s : CornerSite T) := P.phi.symm (sitePoint T pr s)
  have inj : Function.Injective value := P.phi.symm.injective.comp (sitePoint_injective T pr)
  obtain ⟨M,A,B,C⟩ := sphere_three_points (value L.A) (value L.B) (value L.C) (inj.ne L.ab) (inj.ne L.bc) (inj.ne L.ca.symm)
  refine ⟨⟨M.map.trans P.phi,?_,?_,?_,fun x => (P.precompose M x).1,fun x => (P.precompose M x).2⟩⟩
  · exact P.phi.apply_eq_iff_eq_symm_apply.mpr A
  · exact P.phi.apply_eq_iff_eq_symm_apply.mpr B
  · exact P.phi.apply_eq_iff_eq_symm_apply.mpr C

theorem marked_uniformization_of_unmarked (u : GluedSphereUniformization) : MarkedSphereUniformization := by
  intro p n inst hp T ht
  obtain ⟨M⟩ := marking_exists ht
  obtain ⟨P⟩ := u p n hp T ht
  exact ⟨M,normalized_parameter_of_parameter P M⟩

end
end AK14.Gluing

namespace AK14
/-- Both families, arbitrary degree, simultaneous conjugacy of ordered oriented
transitive triples. Only ordinary genus-zero uniformization is an input. -/
theorem oriented_uniqueness_of_unmarked_uniformization (u : Gluing.GluedSphereUniformization) :
    OrientedUniqueness :=
  oriented_uniqueness_of_uniformization (Gluing.marked_uniformization_of_unmarked u)

theorem exactly_one_of_unmarked_uniformization_and_existence (u : Gluing.GluedSphereUniformization)
    (ex : Theorem13Existence) : Conjecture14 :=
  conjecture14_iff_existence_and_uniqueness.mpr ⟨ex,oriented_uniqueness_of_unmarked_uniformization u⟩
end AK14

