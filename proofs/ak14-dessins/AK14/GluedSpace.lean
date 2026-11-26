import Mathlib.Analysis.Convex.StdSimplex
import AK14.CornerVertices
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions

/-! A topological quotient of actual closed triangles for every permutation
triple, and its continuous projection to the oriented double of one triangle. -/
namespace AK14.Gluing
open Equiv
noncomputable section

abbrev Triangle := ↥(stdSimplex ℝ (Fin 3))
abbrev Cell (n : ℕ) := Tri n × Triangle

def seam {n : ℕ} (T : Triple n) (a b : Cell n) : Prop :=
  ∃ j : Fin 3, a.2=b.2 ∧ a.2.val j=0 ∧ step T j a.1=b.1

abbrev Surface {n : ℕ} (T : Triple n) := Quot (seam T)
abbrev flatTriple : Triple 1 := fun _ => 1
abbrev DoubleTriangle := Surface flatTriple

def cell {n : ℕ} (T : Triple n) (q : Tri n) (z : Triangle) : Surface T := Quot.mk _ (q,z)

theorem glue_edge {n : ℕ} (T : Triple n) (q : Tri n) (z : Triangle) (j : Fin 3) (h : z.val j=0) :
    cell T q z=cell T (step T j q) z := Quot.sound ⟨j,rfl,h,rfl⟩

def barycentric {n : ℕ} (T : Triple n) : Surface T → Triangle :=
  Quot.lift Prod.snd (fun _ _ h => h.choose_spec.1)

theorem continuous_barycentric {n : ℕ} (T : Triple n) : Continuous (barycentric T) :=
  continuous_quot_lift _ continuous_snd

theorem forget_step {n : ℕ} (T : Triple n) (j : Fin 3) (q : Tri n) :
    step flatTriple j (q.1,0)=((step T j q).1,0) := by
  obtain ⟨b,i⟩ := q
  cases b <;> apply Prod.ext <;> first | rfl | exact Subsingleton.elim _ _

def coveringProjection {n : ℕ} (T : Triple n) : Surface T → DoubleTriangle :=
  Quot.lift (fun u => cell flatTriple (u.1.1,0) u.2) (by
    rintro ⟨q,z⟩ ⟨r,w⟩ ⟨j,e,b,s⟩
    change z=w at e; change step T j q=r at s
    subst w; subst r
    change cell flatTriple (q.1,0) z=cell flatTriple ((step T j q).1,0) z
    exact (glue_edge flatTriple (q.1,0) z j b).trans (congrArg (fun a => cell flatTriple a z) (forget_step T j q)))

theorem projection_cell {n : ℕ} (T : Triple n) (q : Tri n) (z : Triangle) :
    coveringProjection T (cell T q z)=cell flatTriple (q.1,0) z := rfl

theorem projection_continuous {n : ℕ} (T : Triple n) : Continuous (coveringProjection T) := by
  apply continuous_quot_lift
  apply continuous_quot_mk.comp
  exact (continuous_fst.fst.prodMk continuous_const).prodMk continuous_snd

private def interiorFace {n : ℕ} (T : Triple n) (z : Triangle) (h : ∀ j, z.val j≠0) :
    Surface T → Option (Tri n) :=
  Quot.lift (fun u => if u.2=z then some u.1 else none) (by
    rintro a b ⟨j,e,boundary,_⟩
    have ne : a.2≠z := fun hz => h j (hz ▸ boundary)
    have ne' : b.2≠z := e ▸ ne
    simp [ne,ne'])

theorem interior_faces_distinct {n : ℕ} (T : Triple n) (z : Triangle) (h : ∀ j, z.val j≠0)
    (a b : Tri n) (e : cell T a z=cell T b z) : a=b := by
  have eq := congrArg (interiorFace T z h) e
  simpa [interiorFace,cell] using eq

def interior_sheets {n : ℕ} (T : Triple n) (z : Triangle) (h : ∀ j, z.val j≠0) (b : Bool) :
    Fin n ≃ {u : Surface T // coveringProjection T u=cell flatTriple (b,0) z} := by
  let F (i : Fin n) : {u : Surface T // coveringProjection T u=cell flatTriple (b,0) z} :=
    ⟨cell T (b,i) z,rfl⟩
  apply Equiv.ofBijective F
  constructor
  · intro i j eq
    exact congrArg Prod.snd (interior_faces_distinct T z h _ _ (congrArg Subtype.val eq))
  · rintro ⟨u,hu⟩
    induction u using Quot.ind with | _ u =>
      obtain ⟨⟨c,i⟩,w⟩ := u
      change cell flatTriple (c,0) w=cell flatTriple (b,0) z at hu
      have e : w=z := congrArg (barycentric flatTriple) hu
      subst w
      have sign : c=b := congrArg Prod.fst (interior_faces_distinct _ z h _ _ hu)
      subst c
      exact ⟨i,rfl⟩

end
end AK14.Gluing
