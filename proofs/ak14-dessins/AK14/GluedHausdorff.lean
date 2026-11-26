import AK14.GluedPaths

/-! Hausdorff separation for the topological realization of any input triple.
On a small patch around z, moving every cell to its value over z is constant
on each local sheet over that patch. -/
namespace AK14.Gluing
noncomputable section

private def patch (z : Triangle) : Set Triangle := {w | ∀ j, z.val j≠0 → w.val j≠0}

private theorem patch_open (z : Triangle) : IsOpen (patch z) := by
  have eq : patch z=⋂ j : Fin 3, {w : Triangle | z.val j≠0 → w.val j≠0} := by
    ext w; simp [patch]
  rw [eq]
  apply isOpen_iInter_of_finite
  intro j
  by_cases e : z.val j=0
  · simp [e]
  · simp only [e,ne_eq,not_false_eq_true,true_implies]
    exact isOpen_ne_fun ((continuous_apply j).comp continuous_subtype_val) continuous_const

private def localLabel {n : ℕ} (T : Triple n) (z : Triangle) : Surface T → Option (Surface T) := by
  classical
  apply Quot.lift (fun u : Cell n => if u.2∈patch z then some (cell T u.1 z) else none)
  rintro ⟨q,w⟩ ⟨r,v⟩ ⟨j,h,b,s⟩
  change w=v at h; change w.val j=0 at b; change step T j q=r at s
  subst v; subst r
  dsimp only
  by_cases e : w∈patch z
  · rw [if_pos e,if_pos e]
    exact congrArg some (glue_edge T q z j (by by_contra nz; exact e j nz b))
  · rw [if_neg e,if_neg e]

private def sector {n : ℕ} (T : Triple n) (z : Triangle) (q : Tri n) : Set (Surface T) :=
  {y | localLabel T z y=some (cell T q z)}

private theorem sector_open {n : ℕ} (T : Triple n) (z : Triangle) (q : Tri n) :
    IsOpen (sector T z q) := by
  classical
  apply isQuotientMap_quot_mk.isOpen_preimage.mp
  have eq : Quot.mk (seam T) ⁻¹' (sector T z q)=
      Prod.snd ⁻¹' (patch z) ∩ Prod.fst ⁻¹' {r | cell T r z=cell T q z} := by
    ext ⟨r,w⟩
    by_cases mem : w∈patch z <;> simp [sector,localLabel,mem]
  rw [eq]
  exact ((patch_open z).preimage continuous_snd).inter ((isOpen_discrete _).preimage continuous_fst)

private theorem in_sector {n : ℕ} (T : Triple n) (z : Triangle) (q : Tri n) : cell T q z∈sector T z q := by
  classical
  have mem : z∈patch z := fun _ h => h
  simp [cell,sector,localLabel,mem]

theorem surface_hausdorff {n : ℕ} (T : Triple n) : T2Space (Surface T) := by
  constructor
  intro x y different
  induction x using Quot.ind with | _ x =>
    induction y using Quot.ind with | _ y =>
      obtain ⟨q,z⟩ := x; obtain ⟨r,w⟩ := y
      by_cases e : z=w
      · subst w
        refine ⟨sector T z q,sector T z r,sector_open _ _ _,sector_open _ _ _,in_sector _ _ _,in_sector _ _ _,?_⟩
        exact Set.disjoint_left.mpr (fun _ hu hv => different (Option.some.inj (hu.symm.trans hv)))
      · obtain ⟨u,v,ou,ov,zu,wv,h⟩ := t2_separation e
        exact ⟨_,_,ou.preimage (continuous_barycentric T),ov.preimage (continuous_barycentric T),zu,wv,h.preimage _⟩

end
end AK14.Gluing
