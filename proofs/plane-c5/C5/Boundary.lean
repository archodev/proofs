module
public import C5.Fold
public import C5.Support
public import Erdos173.Measurable.Boundary

@[expose] public section
namespace C5
open MeasureTheory Set Erdos173 Filter OAI.EuclideanFiveColor
noncomputable section

def cls (c : ℂ → Bool) (a : Bool) := {z | c z = a}

@[simp] theorem compl_cls (c : ℂ → Bool) (a : Bool) : (cls c a)ᶜ = cls c (!a) := by
  ext z; cases a <;> cases h : c z <;> simp [cls,h]

def Pure (c : ℂ → Bool) (z : ℂ) (a : Bool) := DensityZero (cls c a)ᶜ z

def exceptional (c : ℂ → Bool) := {x | ∀ a, ¬ DensityZero (cls c a) x}

def label (c : ℂ → Bool) (x : ℂ) : Bool := by
  classical exact if Pure c x true then true else false

theorem label_spec {c : ℂ → Bool} {x : ℂ} (h : x ∉ exceptional c) : Pure c x (label c x) := by
  classical
  by_cases ht : Pure c x true
  · simpa [label,ht] using ht
  have hf : Pure c x false := by
    by_contra hn
    apply h
    intro b
    cases b
    · simpa [Pure] using ht
    · simpa [Pure] using hn
  simpa [label,ht] using hf

theorem density_congr {A B : Set ℂ} (h : A =ᵐ[volume] B) (x : ℂ) :
    DensityZero A x ↔ DensityZero B x := by
  unfold DensityZero
  have e (r : ℝ) : volume (A ∩ Metric.closedBall x r) = volume (B ∩ Metric.closedBall x r) :=
    measure_congr (h.inter EventuallyEq.rfl)
  simp only [e]

theorem measurable_density {A : Set ℂ} (h : NullMeasurableSet A volume) :
    MeasurableSet {x | DensityZero A x} := by
  obtain ⟨B,hB,he⟩ := h
  convert measurableSet_densityZero hB using 1
  ext x
  exact density_congr he x

theorem ae_density {A : Set ℂ} (h : NullMeasurableSet A volume) : ∀ᵐ x, x ∉ A → DensityZero A x := by
  obtain ⟨B,hB,he⟩ := h
  filter_upwards [ae_densityZero hB,he] with x hx he' ha
  exact (density_congr he x).mpr (hx (by simpa [← he'] using ha))

theorem measurable_exceptional {c : ℂ → Bool} (hm : ∀ a, NullMeasurableSet (cls c a) volume) :
    MeasurableSet (exceptional c) := by
  exact MeasurableSet.iInter (fun a => (measurable_density (hm a)).compl) |>.congr
    (by ext; simp [exceptional])

theorem null_exceptional {c : ℂ → Bool} (hm : ∀ a, NullMeasurableSet (cls c a) volume) :
    volume (exceptional c) = 0 := by
  have h : ∀ᵐ x : ℂ, x ∉ exceptional c := by
    filter_upwards [ae_density (hm true),ae_density (hm false)] with x ht hf hx
    cases he : c x
    · exact hx true (ht (by simp [cls,he]))
    · exact hx false (hf (by simp [cls,he]))
  simpa using ae_iff.mp h

def core (c : ℂ → Bool) (a : Bool) := cls c a ∩ {z | Pure c z a}
def CoreWitness (c : ℂ → Bool) := ∃ a, InClass (core c a)

theorem core_ae {c : ℂ → Bool} {a : Bool} (hm : NullMeasurableSet (cls c a) volume) :
    core c a =ᵐ[volume] cls c a := by
  filter_upwards [ae_density hm.compl] with x hx
  change (x ∈ cls c a ∧ DensityZero (cls c a)ᶜ x) = (x ∈ cls c a)
  exact propext (and_iff_left_of_imp (fun h => hx (fun hc => hc h)))

theorem mono_of_core (c : ℂ → Bool) (h : CoreWitness c) : HasMono c := by
  obtain ⟨a,p,hp,ha⟩ := h
  exact inClass_mono c a ⟨p,hp,fun i => (ha i).1⟩

theorem positive_colors {c : ℂ → Bool} (avoid : ¬CoreWitness c) (a : Bool) :
    volume (cls c a) ≠ 0 := by
  intro hz
  obtain ⟨p,hp⟩ : ∃ p, Pentagon p := ⟨_,base_pentagon false (i := 0) (j := 1) (by decide)⟩
  have good (i : Fin 5) : ∀ᵐ x : ℂ, x+p i ∉ cls c a := by
    rw [ae_iff]
    simp only [not_not]
    change volume ((· + p i) ⁻¹' cls c a) = 0
    rw [measure_preimage_add_right,hz]
  obtain ⟨x,hx⟩ := (Filter.eventually_all.mpr good).exists
  apply avoid
  refine ⟨!a,_,translate_pentagon p hp x,fun i => ⟨?_,?_⟩⟩
  · have h : c (x+p i) ≠ a := hx i
    change c (x+p i) = !a
    cases a <;> cases e : c (x+p i) <;> simp_all
  · unfold Pure
    rw [compl_cls,Bool.not_not]
    intro ε _; exact ⟨1,zero_lt_one,fun r _ _ =>
      by rw [measure_mono_null Set.inter_subset_left hz]; exact bot_le⟩

theorem nonempty_exceptional {c : ℂ → Bool} (hm : ∀ a, NullMeasurableSet (cls c a) volume)
    (avoid : ¬CoreWitness c) : (exceptional c).Nonempty := by
  have purePt (a : Bool) : ∃ x, DensityZero (cls c a)ᶜ x := by
    by_contra! h
    have hn := ae_density (hm a).compl
    have hne : ∀ᵐ x : ℂ, x ∉ cls c a := by
      filter_upwards [hn] with x hx hx'
      exact h x (hx (fun hcomp => hcomp hx'))
    exact positive_colors avoid a (by simpa using ae_iff.mp hne)
  obtain ⟨x,hx⟩ := purePt true
  obtain ⟨y,hy⟩ := purePt false
  obtain ⟨B,hB,he⟩ := hm true
  have e : cls c false =ᵐ[volume] Bᶜ := by simpa using he.compl
  obtain ⟨z,h₁,h₂⟩ := exists_not_densityZero hB
    ((density_congr he.compl x).mp hx) ((density_congr he y).mp (by simpa using hy))
  exact ⟨z,fun a => by cases a; exact fun h => h₂ ((density_congr e z).mp h);
                       exact fun h => h₁ ((density_congr he z).mp h)⟩

theorem measurable_label_true {c : ℂ → Bool} (hm : NullMeasurableSet (cls c true) volume) :
    MeasurableSet {x | label c x = true} := by
  classical
  simpa [label,Pure] using measurable_density hm.compl

end
end C5
end
