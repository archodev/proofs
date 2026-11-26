import AK14.EdgeSheets
import Mathlib.Topology.Path

/-! Explicit continuous corner loops in the doubled triangle and their lifts in
the glued quotient. The endpoints recover the given generators sheet by sheet. -/
namespace AK14.Gluing
open scoped unitInterval
noncomputable section

def center : Triangle := ⟨fun _ => 1/3,by
  constructor
  · intro i; norm_num
  · norm_num [Fin.sum_univ_three]⟩

private def weights (a b c : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (total : a+b+c=1) : Triangle :=
  ⟨![a,b,c],by
    constructor
    · intro i; fin_cases i <;> assumption
    · simpa [Fin.sum_univ_three] using total⟩

def middle : Fin 3 → Triangle :=
  ![weights 0 (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    weights (1/2) 0 (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    weights (1/2) (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

theorem middle_boundary (e : Fin 3) : (middle e).val e=0 := by fin_cases e <;> rfl

def radius (e : Fin 3) : Path center (middle e) where
  toFun t := ⟨fun i => (1-(t:ℝ))*center.val i+(t:ℝ)*(middle e).val i,by
    constructor
    · intro k
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (center.property.1 k))
        (mul_nonneg t.property.1 ((middle e).property.1 k))
    · rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,center.property.2,(middle e).property.2]
      ring⟩
  continuous_toFun := by apply Continuous.subtype_mk; apply continuous_pi; intro i; fun_prop
  source' := by apply Subtype.ext; funext i; simp
  target' := by apply Subtype.ext; funext i; simp

theorem cell_cont {n : ℕ} (T : Triple n) (q : Tri n) : Continuous (cell T q) :=
  continuous_quot_mk.comp (continuous_const.prodMk continuous_id)

def crossPath {n : ℕ} (T : Triple n) (e : Fin 3) (q : Tri n) :
    Path (cell T q center) (cell T (step T e q) center) :=
  ((radius e).map (cell_cont T q)).trans
    (((radius e).symm.map (cell_cont T (step T e q))).cast (glue_edge T q _ e (middle_boundary e)) rfl)

theorem crossPath_projects {n : ℕ} (T : Triple n) (e : Fin 3) (q : Tri n) (t : I) :
    coveringProjection T (crossPath T e q t)=crossPath flatTriple e (q.1,0) t := by
  simp only [crossPath,Path.trans_apply]
  split
  · rfl
  · change cell flatTriple ((step T e q).1,0) _=cell flatTriple (step flatTriple e (q.1,0)) _
    rw [forget_step T e q]

def cornerPath {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (i : Fin n) :
    Path (cell T (true,i) center) (cell T (true,T j i) center) :=
  ((crossPath T (first j) (true,i)).trans (crossPath T (last j) (step T (first j) (true,i)))).cast
    rfl (congrArg (fun q => cell T q center) (corner_walk T pr j i).symm)

theorem cornerPath_projects {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (i : Fin n) (t : I) :
    coveringProjection T (cornerPath T pr j i t)=cornerPath flatTriple (by simp [flatTriple]) j 0 t := by
  change coveringProjection T (((crossPath T (first j) (true,i)).trans
    (crossPath T (last j) (step T (first j) (true,i)))) t)=
    ((crossPath flatTriple (first j) (true,0)).trans
      (crossPath flatTriple (last j) (step flatTriple (first j) (true,0)))) t
  simp only [Path.trans_apply]
  split
  · exact crossPath_projects _ _ _ _
  · rw [crossPath_projects,forget_step T (first j) (true,i)]

/-- Topological realization for every input triple along the three explicit
corner walks of the doubled triangle, with an actual bijection on the fiber. -/
theorem glued_path_realization {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) :
    ∃ lab : Fin n ≃ {u : Surface T // coveringProjection T u=cell flatTriple (true,0) center},
      ∀ j i, ∃ L : Path (lab i).val (lab (T j i)).val,
        ∀ t, coveringProjection T (L t)=cornerPath flatTriple (by simp [flatTriple]) j 0 t := by
  let lab := interior_sheets T center (fun _ => by norm_num [center]) true
  exact ⟨lab,fun j i => ⟨cornerPath T pr j i,cornerPath_projects T pr j i⟩⟩

end
end AK14.Gluing
