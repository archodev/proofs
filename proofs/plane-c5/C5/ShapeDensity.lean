module
public import C5.Apex
public import C5.Sampling

@[expose] public section
namespace C5
open MeasureTheory Filter Topology OAI.PlaneFiveColor.Spectral
noncomputable section
variable [Carrier]

theorem unit_approx {u : ℂ} (hu : ‖u‖ = 1) :
    ∃ f : ℕ → E, (∀ n, ‖(f n:ℂ)‖ = 1) ∧ Tendsto (fun n => (f n:ℂ)) atTop (𝓝 u) := by
  classical
  obtain ⟨s,hs,ht⟩ := mem_closure_iff_seq_limit.mp (dense_E u)
  let f := fun n => if s n = 0 then 1 else s n/(‖s n‖:ℂ)
  have mem (n) : f n ∈ E := by
    dsimp [f]; split
    · exact E.one_mem
    · exact E.div_mem (hs n) (algebraic_norm ⟨_,hs n⟩)
  have hne : u ≠ 0 := by intro h; simp [h] at hu
  have hev : ∀ᶠ n in atTop, s n ≠ 0 := ht.eventually (isOpen_compl_singleton.mem_nhds hne)
  have hn : Tendsto (fun n => s n/(‖s n‖:ℂ)) atTop (𝓝 u) := by
    simpa only [hu,Complex.ofReal_one,div_one,Pi.div_def,Function.comp_def] using ht.div
      (Complex.continuous_ofReal.continuousAt.tendsto.comp ht.norm)
      (show (‖u‖:ℂ) ≠ 0 by simp [hu])
  refine ⟨fun n => ⟨_,mem n⟩,fun n => ?_,hn.congr' (hev.mono fun n h => by simp [f,h])⟩
  change ‖f n‖ = 1
  by_cases h : s n = 0 <;> simp [f,h,norm_div]

theorem Pentagon.shift {p : Fin 5 → ℂ} (hp : Pentagon p) (j : Fin 5) :
    Pentagon (fun i => p (j+i)) :=
  ⟨fun _ _ e => add_left_cancel (hp.distinct e),fun i => by simpa [add_assoc] using hp.edges (j+i)⟩

theorem normalized_dense {p : Fin 5 → ℂ} (hp : Pentagon p)
    (chord : Complex.normSq (p 3-p 0)<4) (r : ℝ) (hr : 0<r) :
    ∃ q : Fin 5 → E, Pentagon (fun i => (q i:ℂ)) ∧ ∀ i, dist (q i:ℂ) (p i) ≤ r := by
  have h03 : p 0 ≠ p 3 := hp.distinct.ne (by decide)
  have h4a : dist (p 4) (p 0) = 1 := hp.edges 4
  have h4b : dist (p 4) (p 3) = 1 := (dist_comm _ _).trans (hp.edges 3)
  obtain ⟨s,hap⟩ := apex_represents h03 h4a h4b
  obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp (dense_E (p 0))
  have edges (i : Fin 5) : ‖p (i+1)-p i‖ = 1 := by rw [norm_sub_rev,←dist_eq_norm,hp.edges i]
  obtain ⟨e₁,un₁,lim₁⟩ := unit_approx (edges 0)
  obtain ⟨e₂,un₂,lim₂⟩ := unit_approx (edges 1)
  obtain ⟨e₃,un₃,lim₃⟩ := unit_approx (edges 2)
  let a := z
  let b := fun n => a n + (e₁ n:ℂ)
  let c := fun n => b n + (e₂ n:ℂ)
  let d := fun n => c n + (e₃ n:ℂ)
  let w := fun n => (![a n,b n,c n,d n,apex (a n) (d n) s] : Fin 5 → ℂ)
  have hb : Tendsto b atTop (𝓝 (p 1)) := by simpa [b,a] using ht.add lim₁
  have hc : Tendsto c atTop (𝓝 (p 2)) := by simpa [c] using hb.add lim₂
  have hd : Tendsto d atTop (𝓝 (p 3)) := by simpa [d] using hc.add lim₃
  have lim (i : Fin 5) : Tendsto (fun n => w n i) atTop (𝓝 (p i)) := by
    fin_cases i
    · exact ht
    · exact hb
    · exact hc
    · exact hd
    · change Tendsto (fun n => apex (a n) (d n) s) atTop (𝓝 (p 4))
      rw [← hap]; exact (apex_continuous h03 s).tendsto.comp (ht.prodMk_nhds hd)
  have wm (n i) : w n i ∈ E := by
    have B := E.add_mem (hz n) (e₁ n).property
    have C := E.add_mem B (e₂ n).property
    have D := E.add_mem C (e₃ n).property
    fin_cases i <;> first | exact hz n | exact B | exact C | exact D | exact apex_mem (hz n) D s
  have close : ∀ᶠ n in atTop, ∀ i, dist (w n i) (p i) < r :=
    eventually_all.mpr fun i => Metric.tendsto_nhds.mp (lim i) r hr
  have inj : ∀ᶠ n in atTop, Function.Injective (w n) := by
    have h (i j : Fin 5) : ∀ᶠ n in atTop, i ≠ j → w n i ≠ w n j := by
      by_cases he : i=j
      · simp [he]
      · exact (tendsto_const_nhds.eventually_lt ((lim i).dist (lim j)) (dist_pos.mpr (hp.distinct.ne he))).mono fun _ h _ => dist_pos.mp h
    filter_upwards [eventually_all.mpr fun i => eventually_all.mpr (h i)] with n hn
    exact fun i j eq => by_contra fun ne => hn i j ne eq
  have delta : ∀ᶠ n in atTop, Complex.normSq (d n-a n) < 4 :=
    (Complex.continuous_normSq.continuousAt.tendsto.comp (hd.sub ht)).eventually_lt tendsto_const_nhds chord
  obtain ⟨n,hn,hi,hδ⟩ := (close.and (inj.and delta)).exists
  have hnAD : a n ≠ d n := hi.ne (show (0:Fin 5) ≠ 3 by decide)
  have hap' := apex_edges hnAD hδ s
  refine ⟨fun i => ⟨_,wm n i⟩,⟨hi,?_⟩,fun i => (hn i).le⟩
  intro i
  fin_cases i
  · change dist (a n) (a n+(e₁ n:ℂ)) = 1; simpa [dist_eq_norm] using un₁ n
  · change dist (b n) (b n+(e₂ n:ℂ)) = 1; simpa [dist_eq_norm] using un₂ n
  · change dist (c n) (c n+(e₃ n:ℂ)) = 1; simpa [dist_eq_norm] using un₃ n
  · exact (dist_comm _ _).trans hap'.2
  · exact hap'.1

/-- Every simple real unit pentagon can be approximated vertexwise by exact
simple unit pentagons in the carrier, in particular the algebraic numbers. -/
theorem carrier_shapes_dense (p : Fin 5 → ℂ) (hp : Pentagon p) (r : ℝ) (hr : 0<r) :
    ∃ q : ↥Model.templates, ∀ i, dist (q.val i:ℂ) (p i) ≤ r := by
  obtain ⟨v,_,hv⟩ := Finset.exists_max_image Finset.univ (fun i => Complex.normSq (p i)) Finset.univ_nonempty
  let j := v+1
  let t := fun i => p (j+i)
  have ht := hp.shift j
  have ev : t 4 = p v := by change p (v+1+4) = p v; rw [add_assoc,show (1+4:Fin 5)=0 by decide,add_zero]
  have ch := extremal_chord (ht.edges 4) ((dist_comm _ _).trans (ht.edges 3))
    (show Complex.normSq (t 0) ≤ Complex.normSq (t 4) by rw [ev]; exact hv _ (Finset.mem_univ _))
    (show Complex.normSq (t 3) ≤ Complex.normSq (t 4) by rw [ev]; exact hv _ (Finset.mem_univ _))
  obtain ⟨q,hq,near⟩ := normalized_dense ht ch r hr
  refine ⟨⟨fun i => q (-j+i),hq.shift (-j)⟩,fun i => ?_⟩
  simpa [t,←add_assoc] using near (-j+i)

theorem Model.residual_nonzero (ω : Model.Space Model.templates) : Model.residual Model.templates ω ≠ 0 := by
  intro h
  obtain ⟨c,hm,avoid⟩ := Model.sample_of_pure ω h
  obtain ⟨p,a,hp⟩ := measured_test_family c hm.nullMeasurableSet
    (fun q : ↥Model.templates => fun i => (q.val i:ℂ)) carrier_shapes_dense
  apply hp
  have hn : ∀ᵐ d : ℂ, ¬∀ i, c (d+(p.val i:ℂ)) = a :=
    (avoid p).mono fun _ hn he => hn (fun i => (he i).trans (he 0).symm)
  simpa [ae_iff] using hn

end
end C5
end
