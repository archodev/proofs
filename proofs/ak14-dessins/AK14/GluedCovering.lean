import AK14.GluedHausdorff
import AK14.FiniteCovering

/-! An actual topological covering away from the three corners. Two open
triangles together with one open common edge form a covering chart. -/
namespace AK14.Gluing
open Set
open Bundle
noncomputable section

private def strip (e : Fin 3) : Set Triangle := {z | ∀ j, j≠e → z.val j≠0}

private theorem strip_open (e : Fin 3) : IsOpen (strip e) := by
  have eq : strip e=⋂ j : Fin 3, {z : Triangle | j≠e → z.val j≠0} := by ext; simp [strip]
  rw [eq]
  apply isOpen_iInter_of_finite
  intro j
  by_cases h : j=e
  · simp [h]
  · simp only [h,ne_eq,not_false_eq_true,true_implies]
    exact isOpen_ne_fun ((continuous_apply j).comp continuous_subtype_val) continuous_const

private def region (e : Fin 3) : Set DoubleTriangle := barycentric flatTriple ⁻¹' strip e

private theorem region_open (e : Fin 3) : IsOpen (region e) :=
  (strip_open e).preimage (continuous_barycentric _)

private def encode {n : ℕ} (T : Triple n) (e : Fin 3) : Tri n → Fin n
  | (true,i) => i
  | (false,i) => (crossing T e)⁻¹ i

private def decode {n : ℕ} (T : Triple n) (e : Fin 3) (i : Fin n) : Bool → Tri n
  | true => (true,i)
  | false => (false,crossing T e i)

private theorem encode_step {n : ℕ} (T : Triple n) (e : Fin 3) (q : Tri n) :
    encode T e (step T e q)=encode T e q := by obtain ⟨b,i⟩ := q; cases b <;> simp [encode,step]

private theorem step_decode {n : ℕ} (T : Triple n) (e : Fin 3) (i : Fin n) (q : Tri 1) :
    step T e (decode T e i q.1)=decode T e i (step flatTriple e q).1 := by
  obtain ⟨b,k⟩ := q; cases b <;> simp [step,decode]

private def sectionAt {n : ℕ} (T : Triple n) (e : Fin 3) (i : Fin n) : DoubleTriangle → Surface T := by
  classical
  apply Quot.lift (fun u : Cell 1 => if u.2∈strip e then cell T (decode T e i u.1.1) u.2 else cell T (true,i) center)
  rintro ⟨q,z⟩ ⟨r,w⟩ ⟨j,h,b,s⟩
  change z=w at h; change z.val j=0 at b; change step flatTriple j q=r at s
  subst w; subst r; dsimp only
  by_cases m : z∈strip e
  · obtain rfl : j=e := by by_contra ne; exact m j ne b
    rw [if_pos m,if_pos m,← step_decode]
    exact glue_edge _ _ _ _ b
  · rw [if_neg m,if_neg m]

private theorem section_cell {n : ℕ} (T : Triple n) (e : Fin 3) (i : Fin n) (q : Tri 1) {z : Triangle}
    (h : z∈strip e) : sectionAt T e i (cell flatTriple q z)=cell T (decode T e i q.1) z := by
  classical
  simp [sectionAt,cell,h]

private theorem section_cont {n : ℕ} (T : Triple n) (e : Fin 3) (i : Fin n) :
    ContinuousOn (sectionAt T e i) (region e) := by
  apply (isQuotientMap_quot_mk.continuousOn_isOpen_iff (region_open e)).mpr
  have cont : Continuous (fun u : Cell 1 => cell T (decode T e i u.1.1) u.2) :=
    continuous_prod_of_discrete_left.mpr (fun q : Tri 1 => cell_cont T (decode T e i q.1))
  apply cont.continuousOn.congr
  intro u mem
  exact section_cell T e i u.1 mem

private def label {n : ℕ} (T : Triple n) (e : Fin 3) (fallback : Fin n) : Surface T → Fin n := by
  classical
  apply Quot.lift (fun u : Cell n => if u.2∈strip e then encode T e u.1 else fallback)
  rintro ⟨q,z⟩ ⟨r,w⟩ ⟨j,h,b,s⟩
  change z=w at h; change z.val j=0 at b; change step T j q=r at s
  subst w; subst r; dsimp only
  by_cases m : z∈strip e
  · obtain rfl : j=e := by by_contra ne; exact m j ne b
    rw [if_pos m,if_pos m,encode_step]
  · rw [if_neg m,if_neg m]

private theorem label_decode {n : ℕ} (T : Triple n) (e : Fin 3) (d i : Fin n) (b : Bool) {z : Triangle}
    (m : z∈strip e) : label T e d (cell T (decode T e i b) z)=i := by
  classical
  cases b <;> simp [label,decode,encode,cell,m]

/-- A chart is trivial over both face interiors and one open edge. -/
theorem gluing_trivialization {n : ℕ} [NeZero n] (T : Triple n) (e : Fin 3) :
    ∃ tr : Trivialization (Fin n) (coveringProjection T), tr.baseSet=region e := by
  letI := surface_hausdorff T
  apply finite_sections_trivialization _ (projection_continuous T) _ (region_open e) (sectionAt T e) (section_cont T e)
  · intro i y h
    induction y using Quot.ind with | _ u =>
      obtain ⟨⟨b,k⟩,z⟩ := u
      change z∈strip e at h
      change coveringProjection T (sectionAt T e i (cell flatTriple (b,k) z))=_
      rw [section_cell T e i _ h,projection_cell]
      have k0 : k=0 := Subsingleton.elim _ _
      subst k; cases b <;> rfl
  · intro y h
    induction y using Quot.ind with | _ u =>
      obtain ⟨⟨b,i⟩,z⟩ := u
      change z∈strip e at h
      refine ⟨encode T e (b,i),?_,?_⟩
      · change sectionAt T e _ (cell flatTriple (b,0) z)=cell T (b,i) z
        rw [section_cell _ _ _ _ h]
        cases b <;> simp [decode,encode]
      · intro d hi
        change sectionAt T e d (cell flatTriple (b,0) z)=cell T (b,i) z at hi
        rw [section_cell _ _ _ _ h] at hi
        have eq := congrArg (label T e i) hi
        rw [label_decode _ _ _ _ _ h] at eq
        simpa [label,cell,h] using eq

/-- The union of these charts consists of points with at most one zero barycentric coordinate. -/
def awayFromCorners : Set DoubleTriangle := ⋃ e : Fin 3, region e

private theorem vertex_of_zeros (z : Triangle) (j : Fin 3)
    (h : ∀ i, i≠opposite j → z.val i=0) : z=vertex j := by
  have one : z.val (opposite j)=1 := by
    rw [← z.property.2]
    symm
    exact Finset.sum_eq_single _ (fun i _ hi => h i hi) (by simp)
  apply Subtype.ext
  funext i
  change z.val i=((Pi.single (opposite j) 1 : Fin 3 → ℝ) i)
  by_cases e : i=opposite j
  · subst i
    simpa [Pi.single_apply] using one
  · rw [Pi.single_eq_of_ne e,h i e]

private theorem two_zeros_vertex (z : Triangle) {i k : Fin 3} (ne : i≠k)
    (a : z.val i=0) (b : z.val k=0) : ∃ j, z=vertex j := by
  fin_cases i <;> fin_cases k <;> first
    | exact (ne rfl).elim
    | solve | refine ⟨0,vertex_of_zeros _ _ ?_⟩; intro x h; fin_cases x <;> first | assumption | exact (h rfl).elim
    | solve | refine ⟨1,vertex_of_zeros _ _ ?_⟩; intro x h; fin_cases x <;> first | assumption | exact (h rfl).elim
    | solve | refine ⟨2,vertex_of_zeros _ _ ?_⟩; intro x h; fin_cases x <;> first | assumption | exact (h rfl).elim

private theorem regular_coordinates (z : Triangle) :
    (∃ e, z∈strip e) ↔ ∀ j, z≠vertex j := by
  constructor
  · rintro ⟨e,h⟩ j rfl
    have a : first j=e := by by_contra ne; exact h _ ne ((incident _ _).mpr (Or.inl rfl))
    have b : last j=e := by by_contra ne; exact h _ ne ((incident _ _).mpr (Or.inr rfl))
    have different : first j≠last j := by fin_cases j <;> decide
    exact different (a.trans b.symm)
  · intro h
    by_contra absent
    have missing (e : Fin 3) : ∃ j, j≠e ∧ z.val j=0 := by
      by_contra! no
      exact absent ⟨e,no⟩
    obtain ⟨i,_,a⟩ := missing 0
    obtain ⟨k,ne,b⟩ := missing i
    obtain ⟨j,v⟩ := two_zeros_vertex z ne.symm a b
    exact h j v

theorem away_iff_avoids_vertices (y : DoubleTriangle) :
    y∈awayFromCorners ↔ ∀ j, y≠cell flatTriple (true,0) (vertex j) := by
  induction y using Quot.ind with | _ v =>
    obtain ⟨⟨b,i⟩,z⟩ := v
    change (cell flatTriple (b,i) z∈⋃ e : Fin 3, region e) ↔ _
    rw [Set.mem_iUnion]
    change (∃ e, z∈strip e) ↔ _
    rw [regular_coordinates]
    constructor
    · intro h j eq
      exact h j (congrArg (barycentric flatTriple) eq)
    · intro h j eq
      subst z
      apply h j
      have i0 : i=0 := Subsingleton.elim _ _
      subst i
      cases b with
      | true => rfl
      | false => exact glue_edge flatTriple (false,0) (vertex j) (first j) ((incident _ _).mpr (Or.inl rfl)) |>.trans
                    (congrArg (fun q => cell flatTriple q (vertex j)) (Prod.ext rfl (Subsingleton.elim _ _)))

theorem glued_covering_away_from_corners {n : ℕ} [NeZero n] (T : Triple n) :
    IsCoveringMapOn (coveringProjection T) awayFromCorners := by
  intro y mem
  obtain ⟨e,h⟩ := Set.mem_iUnion.mp mem
  obtain ⟨tr,base⟩ := gluing_trivialization T e
  exact (show IsEvenlyCovered (coveringProjection T) y (Fin n) from
    IsEvenlyCovered.of_trivialization (base ▸ h : y∈tr.baseSet)).to_isEvenlyCovered_preimage

end
end AK14.Gluing
