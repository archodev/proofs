import AK14.SphereTarget

namespace AK14.Gluing
open Complex Set Filter Topology Bornology
open scoped OnePoint
noncomputable section

theorem coord_cont (j : Fin 3) : Continuous (fun z : Triangle => z.val j) :=
  (continuous_apply j).comp continuous_subtype_val

private theorem spherePoint_infty_cont (b : Bool) : ContinuousAt (spherePoint b) (vertex 2) := by
  let v := vertex 2
  have hv : baseMass v=0 := (inf_vertex_iff v).mpr rfl
  have cb : Continuous baseMass := (coord_cont 2).add (coord_cont 1)
  have cn : Continuous (fun z => oneMass z+infMass z) := (coord_cont 1).add (coord_cont 0)
  have vnum : oneMass v+infMass v=1 := by change (0:ℝ)+1=1; ring
  let l := 𝓝[≠] v
  have E : ∀ᶠ z in l, baseMass z≠0 := by
    filter_upwards [self_mem_nhdsWithin (s:=({v}ᶜ : Set Triangle)) (a:=v)] with z hz
    exact fun e => hz ((inf_vertex_iff z).mp e)
  have limit : Tendsto baseMass l (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hv ▸ cb.continuousAt.continuousWithinAt, E.mono fun z e => baseMass_pos e⟩
  have num : Tendsto (fun z => oneMass z+infMass z) l (𝓝 (1:ℝ)) :=
    vnum ▸ cn.continuousAt.continuousWithinAt
  have normLim : Tendsto (fun z => ‖affinePoint b z‖) l atTop := by
    apply (num.pos_mul_atTop zero_lt_one (tendsto_inv_nhdsGT_zero.comp limit)).congr'
    filter_upwards [E] with z h
    simpa only [Function.comp_apply,← div_eq_mul_inv] using (affine_norm h b).symm
  have infinity : Tendsto (affinePoint b) l (coclosedCompact ℂ) := by
    rw [coclosedCompact_eq_cocompact,← Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.mp normLim
  apply continuousWithinAt_compl_self.mp
  change Tendsto _ l (𝓝 (spherePoint b v))
  rw [show spherePoint b v=∞ by simp [spherePoint,hv]]
  apply (OnePoint.tendsto_coe_infty.comp infinity).congr'
  filter_upwards [E] with z h
  simp [spherePoint,h]

theorem spherePoint_continuous (b : Bool) : Continuous (spherePoint b) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases h : baseMass z=0
  · obtain rfl := (inf_vertex_iff z).mp h
    exact spherePoint_infty_cont _
  · have cb : Continuous baseMass := (coord_cont 2).add (coord_cont 1)
    apply (OnePoint.continuous_coe.continuousAt.comp (affine_continuousAt b h)).congr_of_eventuallyEq
    filter_upwards [cb.continuousAt.eventually_ne h] with w hw
    simp [spherePoint,hw]

theorem targetPoint_continuous : Continuous targetPoint :=
  continuous_quot_lift _ (continuous_prod_of_discrete_left.mpr fun q : Tri 1 => spherePoint_continuous q.1)

private theorem identify_boundary {z : Triangle} {j : Fin 3} (h : z.val j=0) (b c : Bool) :
    cell flatTriple (b,0) z=cell flatTriple (c,0) z := by
  have flip : cell flatTriple (false,0) z=cell flatTriple (true,0) z :=
    (glue_edge flatTriple (false,0) z j h).trans
      (congrArg (fun q : Tri 1 => cell flatTriple q z) (Prod.ext rfl (Subsingleton.elim _ _)))
  cases b <;> cases c <;> first | rfl | exact flip | exact flip.symm

theorem targetPoint_surjective : Function.Surjective targetPoint := by
  intro y
  induction y using OnePoint.rec with
  | infty =>
    exact ⟨cell flatTriple (true,0) (vertex 2),by simp [spherePoint,(inf_vertex_iff _).mpr rfl]⟩
  | coe w =>
    have h : baseMass (location w)≠0 := by
      rw [location_base]; exact div_ne_zero (by norm_num) (perimeter_pos _).ne'
    exact ⟨cell flatTriple (lowerSide w,0) (location w),by simp [spherePoint,h,affine_location]⟩

private theorem sphere_same_point {z w : Triangle} {b c : Bool} (h : spherePoint b z=spherePoint c w) :
    cell flatTriple (b,0) z=cell flatTriple (c,0) w := by
  by_cases V : baseMass z=0
  · have W : baseMass w=0 := by by_contra non; simpa [spherePoint,V,non] using h
    rw [(inf_vertex_iff _).mp V,(inf_vertex_iff _).mp W]
    exact identify_boundary (j:=1) (by change (0:ℝ)=0; rfl) _ _
  · have W : baseMass w≠0 := by intro zero; simpa [spherePoint,V,zero] using h
    have pt : affinePoint b z=affinePoint c w := by simpa [spherePoint,V,W] using h
    have loc := congrArg location pt
    rw [location_affine b V,location_affine c W] at loc
    subst w
    by_cases bd : ∃ j, z.val j=0
    · obtain ⟨j,hj⟩ := bd; exact identify_boundary hj _ _
    · have p (j : Fin 3) : 0<z.val j := lt_of_le_of_ne (z.property.1 _) (fun eq => bd ⟨j,eq.symm⟩)
      have pos : 0 < imagNum z := by
        unfold imagNum; exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos (mul_pos (p 2) (p 1)) (p 0)))
      have im := congrArg Complex.im pt
      change sideSign b*imagNum z/baseMass z^2=sideSign c*imagNum z/baseMass z^2 at im
      have e := (div_left_inj' (pow_ne_zero 2 V)).mp im
      cases b <;> cases c <;> first | rfl | simp [sideSign] at e; linarith

theorem targetPoint_injective : Function.Injective targetPoint := by
  intro x y
  induction x using Quot.ind with | _ u =>
    induction y using Quot.ind with | _ v =>
      obtain ⟨⟨b,i⟩,z⟩ := u; obtain ⟨⟨c,k⟩,w⟩ := v
      obtain rfl : i=0 := Subsingleton.elim _ _
      obtain rfl : k=0 := Subsingleton.elim _ _
      exact sphere_same_point

/-- A homeomorphism from the explicit doubled triangle to the marked Riemann sphere. -/
def complexTarget : DoubleTriangle ≃ₜ OnePoint ℂ :=
  (Equiv.ofBijective targetPoint ⟨targetPoint_injective,targetPoint_surjective⟩).toHomeomorphOfContinuousClosed
    targetPoint_continuous targetPoint_continuous.isClosedMap

@[simp] theorem complexTarget_zero : complexTarget (cell flatTriple (true,0) (vertex 0))=(0:ℂ) := by
  change (if (1:ℝ)+0=0 then ∞ else ((affinePoint true (vertex 0)):OnePoint ℂ))=_
  rw [if_neg (by norm_num)]
  apply congrArg (fun z : ℂ => (z : OnePoint ℂ))
  apply Complex.ext
  · change (0*(1+0)+0*(0-1))/(1+0)^2=(0:ℝ); norm_num
  · change (-1)*(2*Real.sqrt (1*0*0))/(1+0)^2=(0:ℝ); norm_num

@[simp] theorem complexTarget_one : complexTarget (cell flatTriple (true,0) (vertex 1))=(1:ℂ) := by
  change (if (0:ℝ)+1=0 then ∞ else ((affinePoint true (vertex 1)):OnePoint ℂ))=_
  rw [if_neg (by norm_num)]
  apply congrArg (fun z : ℂ => (z : OnePoint ℂ))
  apply Complex.ext
  · change (1*(0+1)+0*(1-0))/(0+1)^2=(1:ℝ); norm_num
  · change (-1)*(2*Real.sqrt (0*1*0))/(0+1)^2=(0:ℝ); norm_num

@[simp] theorem complexTarget_infty : complexTarget (cell flatTriple (true,0) (vertex 2))=∞ := by
  change spherePoint true (vertex 2)=∞
  simp [spherePoint,(inf_vertex_iff _).mpr rfl]

end
end AK14.Gluing
