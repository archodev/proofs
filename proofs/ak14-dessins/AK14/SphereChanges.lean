import AK14.ConformalParameter

namespace AK14.Gluing
open Complex Set Filter Topology Bornology
open scoped OnePoint
noncomputable section

/-- A complex coordinate change of the sphere with an explicit local germ. -/
structure SphereChange where
  map : OnePoint ℂ ≃ₜ OnePoint ℂ
  germ : ∀ x, ∃ (g : ℂ → ℂ) (c : ℂ), g 0=0 ∧ AnalyticAt ℂ g 0 ∧ HasDerivAt g c 0 ∧ c≠0 ∧
    ∀ᶠ w in 𝓝 0, map (sphereArgument x w)=sphereArgument (map x) (g w)

def SphereChange.trans (A B : SphereChange) : SphereChange where
  map := A.map.trans B.map
  germ x := by
    obtain ⟨g,c,g0,ag,dg,nc,eq⟩ := A.germ x
    obtain ⟨h,d,h0,ah,dh,nd,eq'⟩ := B.germ (A.map x)
    have cont : Tendsto g (𝓝 0) (𝓝 0) := by simpa only [g0] using ag.continuousAt.tendsto
    refine ⟨h ∘ g,d*c,by simp [g0,h0],(g0 ▸ ah).comp ag,(g0 ▸ dh).comp 0 dg,mul_ne_zero nd nc,?_⟩
    filter_upwards [eq,cont.eventually eq'] with w hw hw' using (congrArg B.map hw).trans hw'

def sphereIdentity : SphereChange where
  map := Homeomorph.refl _
  germ _ := ⟨id,1,rfl,analyticAt_id,hasDerivAt_id _,one_ne_zero,Eventually.of_forall fun _ => rfl⟩

def affineHomeo (a b : ℂ) (hb : b≠0) : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  Homeomorph.onePointCongr ({
    toFun := fun z : ℂ => b*z+a
    invFun := fun z => (z-a)/b
    left_inv := fun z => by field_simp <;> ring
    right_inv := fun z => by field_simp <;> ring
    continuous_toFun := (continuous_const.mul continuous_id).add continuous_const
    continuous_invFun := (continuous_id.sub continuous_const).div_const b } : ℂ ≃ₜ ℂ)

def affineChange (a b : ℂ) (hb : b≠0) : SphereChange where
  map := affineHomeo a b hb
  germ x := by
    cases x with
    | coe x =>
      refine ⟨fun w => b*w,b,by simp,analyticAt_const.mul analyticAt_id,?_,hb,?_⟩
      · simpa using (hasDerivAt_id (𝕜:=ℂ) 0).const_mul b
      · apply Eventually.of_forall; intro w; apply congrArg OnePoint.some; change b*(w+x)+a=b*w+(b*x+a); ring
    | infty =>
      let g (w : ℂ) := w/(b+a*w)
      have q : b+a*0≠0 := by simpa using hb
      have da : HasDerivAt (fun w : ℂ => b+a*w) a 0 := by simpa using ((hasDerivAt_id (𝕜:=ℂ) 0).const_mul a).const_add b
      have dg := (hasDerivAt_id (𝕜:=ℂ) 0).div da q
      have nc : (1*(b+a*0)-0*a)/(b+a*0)^2≠0 := by simp [hb]
      refine ⟨g,_,by simp [g],analyticAt_id.div (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) q,dg,nc,?_⟩
      have near : ∀ᶠ w : ℂ in 𝓝 0, b+a*w≠0 := da.continuousAt.tendsto.eventually (isOpen_ne.mem_nhds q)
      filter_upwards [near] with w hw
      change affineHomeo a b hb (sphereArgument ∞ w)=sphereArgument ∞ (g w)
      by_cases z : w=0
      · subst w; simp [g]; rfl
      · have gn : g w≠0 := div_ne_zero z hw
        simp only [sphereArgument,OnePoint.infty,z,if_false,gn]
        apply congrArg OnePoint.some; change b*w⁻¹+a=(w/(b+a*w))⁻¹
        field_simp

def sphereReciprocal : OnePoint ℂ → OnePoint ℂ
  | none => ((0:ℂ):OnePoint ℂ)
  | some w => sphereArgument ∞ w

theorem reciprocal_involutive : Function.Involutive sphereReciprocal := by
  intro x; cases x with
  | infty => simp [sphereReciprocal,sphereArgument,OnePoint.infty]
  | coe w =>
    by_cases h : w=0
    · subst w; simp [sphereReciprocal,sphereArgument,OnePoint.infty,OnePoint.some]
    · simp [sphereReciprocal,sphereArgument,OnePoint.infty,h,inv_ne_zero h,OnePoint.some]

theorem reciprocal_continuous : Continuous sphereReciprocal := by
  rw [OnePoint.continuous_iff]
  constructor
  · rw [Filter.coclosedCompact_eq_cocompact,← Metric.cobounded_eq_cocompact]
    apply ((OnePoint.continuous_coe.tendsto (0:ℂ)).comp tendsto_inv₀_cobounded).congr'
    filter_upwards [eventually_ne_cobounded (0:ℂ)] with w hw
    simp [sphereReciprocal,sphereArgument,OnePoint.infty,hw,OnePoint.some]
  · apply continuous_iff_continuousAt.mpr; intro w
    by_cases h : w=0
    · subst w
      change Tendsto (sphereArgument ∞) (𝓝 0) (𝓝 (sphereArgument ∞ 0))
      rw [sphereArgument_zero]; exact sphereArgument_neighborhood ∞
    · apply (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ h)).congr
      filter_upwards [isOpen_ne.mem_nhds h] with z hz
      simp [sphereReciprocal,sphereArgument,OnePoint.infty,hz,OnePoint.some]

def reciprocalChange : SphereChange where
  map :=
    { toFun := sphereReciprocal
      invFun := sphereReciprocal
      left_inv := reciprocal_involutive
      right_inv := reciprocal_involutive
      continuous_toFun := reciprocal_continuous
      continuous_invFun := reciprocal_continuous }
  germ x := by
    cases x with
    | infty =>
      refine ⟨id,1,rfl,analyticAt_id,hasDerivAt_id _,one_ne_zero,?_⟩
      apply Eventually.of_forall; intro w
      have eq := reciprocal_involutive (w : OnePoint ℂ)
      simpa [sphereArgument,sphereReciprocal,OnePoint.infty,OnePoint.some] using eq
    | coe a =>
      by_cases az : a=0
      · subst a; refine ⟨id,1,rfl,analyticAt_id,hasDerivAt_id _,one_ne_zero,?_⟩
        apply Eventually.of_forall; intro w
        simp [sphereArgument,sphereReciprocal,OnePoint.infty,OnePoint.some]
      · let g (w : ℂ) := (w+a)⁻¹-a⁻¹
        have nz : (0:ℂ)+a≠0 := by simpa using az
        have da := (hasDerivAt_id (𝕜:=ℂ) 0).add_const a
        have dg := (da.inv nz).sub_const a⁻¹
        refine ⟨g,_,by simp [g],((analyticAt_id.add analyticAt_const).inv nz).sub analyticAt_const,dg,?_,?_⟩
        · simp [az]
        · have near : ∀ᶠ w : ℂ in 𝓝 0, w+a≠0 := da.continuousAt.tendsto.eventually (isOpen_ne.mem_nhds nz)
          filter_upwards [near] with w hw
          simp [g,sphereReciprocal,sphereArgument,OnePoint.infty,OnePoint.some,az,hw]
end
end AK14.Gluing

