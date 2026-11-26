module
public import C5.Average
public import C5.Stability

@[expose] public section
namespace C5.Model
noncomputable section
open MeasureTheory Filter Topology Set OAI OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor
open OAI.EuclideanFiveColor.ContinuousVectors

/-- A common a.e. convergent subsequence for finitely many L² coordinates. -/
theorem joint_subsequence {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    [Fintype ι] (f : ℕ → ι → Lp ℂ 2 μ) (g : ι → Lp ℂ 2 μ)
    (h : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ x ∂μ, ∀ i, Tendsto (fun n => f (φ n) i x) atTop (𝓝 (g i x)) := by
  classical
  have aux (s : Finset ι) : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i ∈ s, ∀ᵐ x ∂μ, Tendsto (fun n => f (φ n) i x) atTop (𝓝 (g i x)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨id,strictMono_id,by simp⟩
    | insert i s _ ih =>
      obtain ⟨φ,hφ,ih⟩ := ih
      obtain ⟨ψ,hψ,hnew⟩ := (tendstoInMeasure_of_tendsto_Lp ((h i).comp hφ.tendsto_atTop)).exists_seq_tendsto_ae
      refine ⟨φ ∘ ψ,hφ.comp hψ,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact hnew
      · exact (ih j hj).mono fun _ hh => hh.comp hψ.tendsto_atTop
  obtain ⟨φ,hφ,hh⟩ := aux Finset.univ
  exact ⟨φ,hφ,ae_all_iff.mpr fun i => hh i (Finset.mem_univ _)⟩

def binary (a : Bool) : ℂ := if a then 1 else 0
def mixedTuples : Set (Fin 5 → ℂ) := range (fun f : {b : Fin 5 → Bool // ∃ i, b i ≠ b 0} =>
  fun i => binary (f.val i))
theorem mixedTuples_closed : IsClosed mixedTuples := (finite_range _).isClosed

variable [Carrier]

theorem field_mixed (ω : Space templates) (hpure : residual templates ω = 0)
    (p : ↥templates) (d : ℂ) :
    ∀ᵐ η ∂measure templates ω, (fun i => field templates ω (d+(p.val i:ℂ)) η) ∈ mixedTuples := by
  obtain ⟨s,hs,ht⟩ := mem_closure_iff_seq_limit.mp (dense_E d)
  let q := fun n (i : Fin 5) => field templates ω (s n+(p.val i:ℂ))
  have hq (i : Fin 5) : Tendsto (fun n => q n i) atTop (𝓝 (field templates ω (d+(p.val i:ℂ)))) :=
    (field_continuous _ _).continuousAt.tendsto.comp (ht.add_const _)
  obtain ⟨φ,hφ,hlim⟩ := joint_subsequence _ _ hq
  have ep : proj templates ω = raw templates ω := (sub_eq_zero.mp hpure).symm
  have hb (n : ℕ) : ∀ᵐ η ∂measure templates ω, (fun i => q n i η) ∈ mixedTuples := by
    let z : E := ⟨s n,hs n⟩
    have point (i : Fin 5) : q n i =ᵐ[measure templates ω] fun η => binary (η.val (z+p.val i)) := by
      change field templates ω ((z+p.val i:E):ℂ) =ᵐ[_] _
      rw [field_at,ep]
      exact raw_at _ _ _
    filter_upwards [ae_all_iff.mpr point] with η he
    have hbad := η.property p.val p.property z (1 : K)
    simp only [kCoeff_one,one_mul] at hbad
    push Not at hbad
    exact ⟨⟨_,hbad⟩,funext fun i => (he i).symm⟩
  filter_upwards [hlim,ae_all_iff.mpr hb] with η hl hmem
  exact mixedTuples_closed.mem_of_tendsto (tendsto_pi_nhds.mpr hl) (.of_forall fun n => hmem (φ n))

/-- Under vanishing residual, the invariant process gives an ordinary Borel
sample which avoids almost every translate of every carrier pentagon at once. -/
theorem sample_of_pure (ω : Space templates) (hp : residual templates ω = 0) :
    ∃ c : ℂ → Bool, MeasurableSet (cls c true) ∧ ∀ p : ↥templates,
      ∀ᵐ d : ℂ, ¬∀ i, c (d+(p.val i:ℂ)) = c (d+(p.val 0:ℂ)) := by
  obtain ⟨F,hF,hrep⟩ := exists_measurable_field (measure templates ω) (field templates ω) (field_continuous _ _)
  classical
  let c := fun q : ℂ × Space templates => decide (F q = 1)
  have hc : Measurable c := measurable_to_countable' fun a => by
    have he := measurableSet_eq_fun hF (measurable_const (a := (1:ℂ)))
    cases a
    · convert he.compl using 1
      ext q; simp [c]
    · convert he using 1
      ext q; simp [c]
  have hm (p : ↥templates) (i : Fin 5) : Measurable (fun q : ℂ × Space templates =>
      c (q.1+(p.val i:ℂ),q.2)) := hc.comp ((measurable_fst.add_const _).prodMk measurable_snd)
  have good (p : ↥templates) : ∀ᵐ η ∂measure templates ω, ∀ᵐ d : ℂ,
      ¬∀ i, c (d+(p.val i:ℂ),η) = c (d+(p.val 0:ℂ),η) := by
    have measurableEvent : MeasurableSet {q : ℂ × Space templates |
        ¬∀ i, c (q.1+(p.val i:ℂ),q.2) = c (q.1+(p.val 0:ℂ),q.2)} := by
      convert (MeasurableSet.iInter (fun i => measurableSet_eq_fun (hm p i) (hm p 0))).compl using 1
      ext q
      simp
    apply (Measure.ae_ae_comm (p := fun d η => ¬∀ i, c (d+(p.val i:ℂ),η) = c (d+(p.val 0:ℂ),η)) measurableEvent).mp
    apply Eventually.of_forall
    intro d
    filter_upwards [field_mixed ω hp p d,ae_all_iff.mpr (fun i : Fin 5 => hrep (d+(p.val i:ℂ)))] with η ht hr
    obtain ⟨⟨f,⟨i,hi⟩⟩,he⟩ := ht
    have val (j : Fin 5) : c (d+(p.val j:ℂ),η) = f j := by
      have hj := congrFun he j
      change binary (f j) = field templates ω (d+(p.val j:ℂ)) η at hj
      have eq := (hr j).trans hj.symm
      change decide (F (d+(p.val j:ℂ),η) = 1) = f j
      rw [eq]
      cases f j <;> simp [binary]
    intro h
    exact hi (by simpa only [val] using h i)
  obtain ⟨η,hη⟩ := (ae_all_iff.mpr good).exists
  refine ⟨fun z => c (z,η),?_,hη⟩
  exact measurableSet_eq_fun (hc.comp (measurable_id.prodMk (measurable_const (a := η)))) measurable_const

end
end C5.Model
end
