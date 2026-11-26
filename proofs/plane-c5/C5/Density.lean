module

public import C5.Coloring
public import Erdos173.Measurable.Density

@[expose] public section

namespace C5
open Erdos173 MeasureTheory Metric Set
noncomputable section

def InClass (K : Set ℂ) : Prop := ∃ p : Fin 5 → ℂ, Pentagon p ∧ ∀ i, p i ∈ K

/-- Five distinct unit vertices can approach this ordered tuple, keeping its root fixed. -/
def Approximates (x : ℂ) (q : Fin 4 → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ p : Fin 5 → ℂ, Pentagon p ∧ p 0 = x ∧
    ∀ i : Fin 4, dist (p i.succ) (q i) ≤ r

theorem translate_pentagon (p : Fin 5 → ℂ) (hp : Pentagon p) (d : ℂ) :
    Pentagon (fun i => d + p i) := by
  simpa [place] using hp.place d (u := 1) (by simp)

/-- A root of positive upper density and four density-one limits suffice, even
when the four limiting positions include repetitions. -/
theorem density_transfer {K : Set ℂ} {x : ℂ} {q : Fin 4 → ℂ}
    (hx : ¬ DensityZero K x) (hq : ∀ i, DensityZero Kᶜ (q i))
    (ha : Approximates x q) : InClass K := by
  unfold DensityZero at hx
  push Not at hx
  obtain ⟨ε,hε,hx⟩ := hx
  choose δ hδ hd using fun i => hq i (ε/32) (by positivity)
  let m := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin 4)).Nonempty) δ
  have hm : 0 < m := by simpa [m, Finset.lt_inf'_iff] using hδ
  obtain ⟨r,hr,hrm,hgood⟩ := hx (m/2) (by positivity)
  obtain ⟨p,hp,hpx,hdist⟩ := ha r hr
  let D := K ∩ closedBall x r
  let bad (i : Fin 4) : Set ℂ := (fun z : ℂ => z + (p i.succ - x)) ⁻¹'
    (Kᶜ ∩ closedBall (q i) (2*r))
  let C := ENNReal.ofReal (ε/32 * (2*r)^2)
  have hbad (i : Fin 4) : volume (bad i) ≤ C := by
    rw [show volume (bad i) = volume (Kᶜ ∩ closedBall (q i) (2*r)) from
      measure_preimage_add_right _ _ _]
    apply hd i _ (by positivity)
    have : m ≤ δ i := Finset.inf'_le _ (Finset.mem_univ i)
    linarith
  by_contra hno
  have cover : D ⊆ ⋃ i, bad i := by
    intro z hz
    by_contra hmiss
    simp only [mem_iUnion, not_exists] at hmiss
    apply hno
    refine ⟨fun j => (z-x) + p j, translate_pentagon _ hp _, ?_⟩
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [hpx] using hz.1
    · by_contra hnot
      apply hmiss i
      have eqv : z + (p i.succ - x) = (z-x) + p i.succ := by ring
      refine ⟨by simpa [eqv] using hnot, ?_⟩
      change dist (z + (p i.succ - x)) (q i) ≤ 2*r
      rw [eqv]
      calc dist ((z-x) + p i.succ) (q i)
              ≤ dist ((z-x) + p i.succ) (p i.succ) + dist (p i.succ) (q i) := dist_triangle _ _ _
        _ ≤ 2*r := by
          have hz' : dist z x ≤ r := hz.2
          simpa [dist_eq_norm, two_mul] using add_le_add hz' (hdist i)
  have hu : volume D ≤ ∑ _i : Fin 4, C :=
    (measure_mono cover).trans ((measure_iUnion_le _).trans
      (by simpa using (ENNReal.tsum_le_tsum hbad)))
  have hsum : (∑ _i : Fin 4, C) < ENNReal.ofReal (ε*r^2) := by
    simp only [Fin.sum_univ_four, C]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    nlinarith [mul_pos hε (sq_pos_of_pos hr)]
  exact (not_lt_of_ge hu) (hsum.trans hgood)

theorem fixed_approximates (p : Fin 5 → ℂ) (hp : Pentagon p) :
    Approximates (p 0) (fun i => p i.succ) :=
  fun _ hr => ⟨p,hp,rfl,fun _ => by simp [hr.le]⟩

theorem inClass_mono (c : ℂ → Bool) (a : Bool) (h : InClass {z | c z = a}) : HasMono c := by
  obtain ⟨p,hp,hl⟩ := h
  exact ⟨p,hp,fun i => (hl i).trans (hl 0).symm⟩

end
end C5

end
