import AK14.GeometricCorners
import Mathlib.Analysis.Convex.Topology

/-! The glued space is compact and is genuinely path-connected whenever the
ordered triple is transitive. -/
namespace AK14.Gluing
noncomputable section

theorem surface_compact {n : ℕ} (T : Triple n) : CompactSpace (Surface T) := by
  infer_instance

private theorem cell_path {n : ℕ} (T : Triple n) (q : Tri n) (a b : Triangle) :
    Joined (cell T q a) (cell T q b) := by
  have ne : (stdSimplex ℝ (Fin 3)).Nonempty := ⟨a,a.property⟩
  letI : PathConnectedSpace Triangle := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_stdSimplex ℝ (Fin 3)).isPathConnected ne)
  have cont : Continuous (cell T q) := continuous_quot_mk.comp (continuous_const.prodMk continuous_id)
  exact ⟨(PathConnectedSpace.joined a b).somePath.map cont⟩

theorem surface_connected {n : ℕ} {T : Triple n} (nt : 0<n)
    (ht : Transitive T) (pr : T 0*T 1*T 2=1) : PathConnectedSpace (Surface T) := by
  let v := vertex 0
  refine ⟨⟨cell T (true,⟨0,nt⟩) v⟩,?_⟩
  intro x y
  induction x using Quot.ind with | _ x =>
    induction y using Quot.ind with | _ y =>
      obtain ⟨q,u⟩ := x
      obtain ⟨r,w⟩ := y
      have reach := triangles_connected ht pr q r
      have jn : Joined (cell T q v) (cell T r v) := by
        induction reach with
        | rel a b h =>
          obtain ⟨e,rfl⟩ := h
          let k : Fin 3 := ![0,0,1] e
          have h0 : (vertex k).val e=0 := by
            apply (incident _ _).mpr
            fin_cases e <;> decide
          have e0 := glue_edge T a (vertex k) e h0
          exact (cell_path T a v (vertex k)).trans (e0 ▸ cell_path T (step T e a) (vertex k) v)
        | refl => exact Joined.refl _
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih jh => exact ih.trans jh
      exact (cell_path T q u v).trans (jn.trans (cell_path T r v w))

end
end AK14.Gluing
