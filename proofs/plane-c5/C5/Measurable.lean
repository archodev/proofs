module
public import C5.Boundary
public import C5.Angles

@[expose] public section
namespace C5
open Set MeasureTheory Erdos173 OAI.EuclideanFiveColor Filter
noncomputable section

theorem angular_pure {c : ℂ → Bool} (hm : ∀ a, NullMeasurableSet (cls c a) volume) {x u : ℂ} (hu : ‖u‖ = 1)
    (hx : x ∈ exceptional c)
    (ho : ∀ a : Bool, ∃ b : Bool, ∀ i, Pure c (place x u (outer b i)) a)
    (hi : ∀ i, Pure c (place x u (inner i)) (label c (place x u (inner i)))) :
    CoreWitness c := by
  obtain ⟨i,j,hij,he⟩ := two_equal (fun k => label c (place x u (inner k)))
  let a := label c (place x u (inner j))
  obtain ⟨b,hb⟩ := ho a
  let p := fun k => place x u (pattern b i j k)
  have hp : Pentagon p := two_circles x hu b hij
  refine ⟨a,?_⟩
  apply density_transfer (x := p 0) (q := fun k => p k.succ)
  · have e : p 0 = x := by simp [p,pattern,place]
    rw [e]; exact fun h => hx a ((density_congr (core_ae (hm a)) x).mp h)
  · intro k
    apply (density_congr (core_ae (hm a)).compl _).mpr
    fin_cases k
    · exact hb i
    · change Pure c (place x u (inner i)) (label c (place x u (inner j)))
      rw [← he]; exact hi i
    · exact hi j
    · exact hb j
  · exact fixed_approximates _ hp

/-- The measurable-color theorem uses measurability in the completion of area;
changing either class on a null set is allowed. -/
theorem measurable_core (c : ℂ → Bool) (htrue : NullMeasurableSet (cls c true) volume) : CoreWitness c := by
  by_contra avoid
  have hm (a : Bool) : NullMeasurableSet (cls c a) volume := by
    cases a
    · simpa using htrue.compl
    · exact htrue
  let S := exceptional c
  let s := ‖1+rho‖
  have hs : 0 < s := by
    apply norm_pos_iff.mpr
    intro e
    have h := inner_radius
    rw [e] at h
    norm_num at h
  obtain ⟨x,hx,h₁,h₂⟩ := good_two_radii (measurable_exceptional hm) (null_exceptional hm)
    (nonempty_exceptional hm avoid) zero_lt_one hs
  let f := fun t : Angles => label c (x+direction t)
  have hfm : MeasurableSet {t | f t = true} :=
    (measurable_label_true htrue).preimage (continuous_const.add direction_continuous).measurable
  have hout : ∀ᵐ t ∂angularMeasure, Pure c (x+direction t) (f t) := by
    filter_upwards [not_hits.mp h₁] with t ht
    exact label_spec (by simpa using ht)
  have halt : ∀ᵐ t ∂angularMeasure, f (t+tau) = !(f t) := by
    filter_upwards [hout,shift_ae hout tau] with t ht hv
    by_contra hn
    have e : f (t+tau) = f t := by cases h : f t <;> cases h' : f (t+tau) <;> simp_all
    rw [e,direction_add,dir_tau] at hv
    have he := core_ae (hm (f t))
    apply avoid
    exact ⟨f t,triangle_transfer (direction_norm t)
      (fun h => hx _ ((density_congr he x).mp h))
      ((density_congr he.compl _).mpr ht) ((density_congr he.compl _).mpr hv)⟩
  have hper := twice_period halt
  have family (t : Angles) (g : Angles) (b : Bool) (hb : direction g = if b then rho else 1)
      (labels : ∀ i, f ((t+g)+phase i) = f (t+g))
      (purity : ∀ i, Pure c (x+direction ((t+g)+phase i)) (f ((t+g)+phase i))) :
      ∀ i, Pure c (place x (direction t) (outer b i)) (f (t+g)) := by
    intro i
    have E : x+direction ((t+g)+phase i) = place x (direction t) (outer b i) := by
      simp only [direction_add,dir_phase,hb,place,outer]; ring
    simpa only [labels i,E] using purity i
  have hfp (g : Angles) : ∀ᵐ t ∂angularMeasure, ∀ i : Fin 3,
      Pure c (x+direction ((t+g)+phase i)) (f ((t+g)+phase i)) :=
    eventually_all.mpr fun i => shift_ae (shift_ae hout (phase i)) g
  have innerGood (i : Fin 3) : ∀ᵐ t ∂angularMeasure, place x (direction t) (inner i) ∉ S := by
    have nrm : ‖inner i‖ = s := by
      change ‖rot i*(1+rho)‖ = ‖1+rho‖
      rw [norm_mul,show ‖rot i‖ = 1 by rw [Complex.norm_def,rotation_unit,Real.sqrt_one],one_mul]
    have eq := angularMeasure_mul_mem ((x + ·) ⁻¹' S) (inner i)
    rw [nrm] at eq
    rw [ae_iff]; simp only [not_not]
    exact eq.trans (not_ne_iff.mp h₂)
  apply no_alternating_period f hfm halt
  filter_upwards [hper,shift_ae hper gamma,hfp 0,hfp gamma, eventually_all.mpr innerGood]
    with t ht hg hp hpg hin
  by_contra hn
  apply avoid
  apply angular_pure hm (direction_norm t) hx _ (fun i => label_spec (hin i))
  intro a
  by_cases ea : a = f t
  · refine ⟨false,?_⟩
    simpa [ea] using family t 0 false (by simp [direction]) (by simpa using ht) hp
  · have e : f (t+gamma) = a := by
      cases hf : f t <;> cases hg : f (t+gamma) <;> cases a <;> simp_all
    refine ⟨true,?_⟩
    simpa [e] using family t gamma true dir_gamma hg hpg


theorem measurable_C5 (c : ℂ → Bool) (htrue : NullMeasurableSet (cls c true) volume) : HasMono c :=
  mono_of_core c (measurable_core c htrue)

end
end C5
end
