import AK14.CornerDisks

namespace AK14.Gluing
open Complex Set Topology
noncomputable section

theorem finite_location_zero : location (0:ℂ)=vertex 0 := by
  apply Subtype.ext; funext i; fin_cases i <;> norm_num [location,perimeter,vertex,opposite,Pi.single_apply,Fin.ext_iff]

theorem frame_vertex (j : Fin 3) : frame j (vertex j)=vertex 0 := by
  apply Subtype.ext; funext i; fin_cases j <;> fin_cases i <;> rfl

theorem same_frame_side_seam (j : Fin 3) {z : Triangle} {q r : Bool}
    (diff : q≠r) (eq : cornerValue j q z=cornerValue j r z) : ∃ k, z.val k=0 := by
  by_contra! none
  have p (i : Fin 3) : 0<(frame j z).val i :=
    lt_of_le_of_ne ((frame j z).property.1 _) (Ne.symm (none _))
  have im : 0 < imagNum (frame j z) :=
    mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos (mul_pos (p 2) (p 1)) (p 0)))
  have bp : baseMass (frame j z)≠0 := (add_pos (p 2) (p 1)).ne'
  have e := congrArg Complex.im eq
  change sideSign (frameSide j q)*imagNum (frame j z)/_=sideSign (frameSide j r)*imagNum (frame j z)/_ at e
  have f := (div_left_inj' (pow_ne_zero 2 bp)).mp e
  have g := (mul_left_inj' im.ne').mp f
  have same : frameSide j q=frameSide j r := by
    cases a : frameSide j q <;> cases b : frameSide j r <;> simp [a,b,sideSign] at g ⊢ <;> norm_num at g
  exact diff (by simpa using congrArg (frameSide j) same)

theorem sector_inj_equal_side {n : ℕ} (T : Triple n) (j : Fin 3) (x : Fin n) {q r : Tri n}
    (same : q.1=r.1) (z : Triangle) (hq : (T j).SameCycle x (cornerIndex T j q))
    (hr : (T j).SameCycle x (cornerIndex T j r)) (nz : cornerValue j q.1 z≠0)
    (eq : sectorValue T j x q z=sectorValue T j x r z) : q=r := by
  have dne := degreeAt_ne T j x
  have rn : Polar.halfRoot (degreeAt T j x) (isUpper j q.1) (cornerValue j q.1 z)≠0 := by
    intro h
    cases u : isUpper j q.1
    · rw [u] at h
      have p := Polar.lower_power dne (lower_sign u z)
      rw [h,zero_pow dne] at p; exact nz p.symm
    · rw [u] at h
      have p := Polar.upper_power dne (upper_sign u z)
      rw [h,zero_pow dne] at p; exact nz p.symm
  simp only [sectorValue,←same] at eq
  have ix := orbitPhase_injective (T j) x (Polar.primitive dne) hq hr ((mul_left_inj' rn).mp eq)
  rw [←cornerTri_index T j q,←cornerTri_index T j r,ix,same]

theorem cornerRoot_injOn {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n) :
    InjOn (cornerRoot T pr j x) (closedSheet T j x) := by
  intro a ha b hb eq
  induction a using Quot.ind with | _ u =>
    induction b using Quot.ind with | _ v =>
      obtain ⟨q,z⟩ := u; obtain ⟨r,w⟩ := v
      obtain ⟨bound,oq⟩ := (closedSheet_cell T pr j x q z).mp ha
      obtain ⟨bound',orr⟩ := (closedSheet_cell T pr j x r w).mp hb
      have pos := radial_forces_star bound
      have pos' := radial_forces_star bound'
      have E : sectorValue T j x q z=sectorValue T j x r w :=
        (root_cell T pr j x q pos).symm.trans (eq.trans (root_cell T pr j x r pos'))
      have powers := congrArg (fun v : ℂ => v^(degreeAt T j x)) E
      dsimp only at powers; rw [sector_power _ _ _ _ _ oq,sector_power _ _ _ _ _ orr] at powers
      have loc := congrArg location powers
      simp only [cornerValue,location_affine _ (frame_base_ne pos),location_affine _ (frame_base_ne pos')] at loc
      obtain rfl : z=w := by simpa using congrArg (frame j) loc
      by_cases center : cornerValue j q.1 z=0
      · have located := location_affine (frameSide j q.1) (frame_base_ne pos)
        change location (cornerValue j q.1 z)=_ at located
        rw [center,finite_location_zero,←frame_vertex j] at located
        obtain rfl : vertex j=z := by simpa using congrArg (frame j) located
        change cell T q _=cell T r _
        rw [anchored_index T j q,anchored_index T j r]
        exact (corner_cell_eq_iff T pr j _ _).mpr (oq.symm.trans orr)
      · by_cases same : q.1=r.1
        · rw [sector_inj_equal_side T j x same z oq orr center E]
        · obtain ⟨k,hk⟩ := same_frame_side_seam j same powers
          have glue := glue_edge T q z k hk
          let q' := step T k q
          have ident : cell T q z=cell T q' z := glue
          have oq' := ((closedSheet_cell T pr j x q' z).mp (ident ▸ ha)).2
          have E' : sectorValue T j x q' z=sectorValue T j x r z :=
            (sector_on_seam T pr j k x q hk pos).symm.trans E
          have side : q'.1=r.1 := by
            obtain ⟨b,i⟩ := q; obtain ⟨c,l⟩ := r; cases b <;> cases c <;> first | rfl | exact (same rfl).elim
          have nz : cornerValue j q'.1 z≠0 := by rw [←corner_same hk q.1 q'.1]; exact center
          have full := sector_inj_equal_side T j x side z oq' orr nz E'
          exact ident.trans (congrArg (fun v => cell T v z) full)

theorem cornerRoot_surj {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n) (v : ℂ)
    (bound : ‖v^(degreeAt T j x)‖≤1/2) : ∃ y∈closedSheet T j x, cornerRoot T pr j x y=v := by
  let d := degreeAt T j x
  have dn : d≠0 := degreeAt_ne _ _ _
  letI : NeZero d := ⟨dn⟩
  let t := v^d
  let z := frame j (location t)
  let b := frameSide j (lowerSide t)
  have value : cornerValue j b z=t := by simp [cornerValue,b,z,affine_location]
  have base : baseMass (frame j z)≠0 := by
    simp [z,location_base,(perimeter_pos t).ne']
  have radial := (radius_bound b base).1.mpr (value ▸ bound)
  have pos := radial_forces_star radial
  let R := Polar.halfRoot d (isUpper j b) t
  have rootPower : R^d=t := by
    change (Polar.halfRoot d (isUpper j b) t)^d=t
    cases u : isUpper j b
    · exact Polar.lower_power dn (value ▸ lower_sign u z)
    · exact Polar.upper_power dn (value ▸ upper_sign u z)
  have witness (k : ℕ) (eq : (Polar.phase d)^k*R=v) : ∃ y∈closedSheet T j x, cornerRoot T pr j x y=v := by
    let q := cornerTri T j b ((T j^k) x)
    have row : q.1=b := by cases h : b <;> simp [q,h,cornerTri]
    refine ⟨cell T q z,(closedSheet_cell T pr j x q z).mpr ⟨radial,?_⟩,?_⟩
    · simpa only [q,index_cornerTri,Equiv.Perm.sameCycle_pow_right] using (Equiv.Perm.SameCycle.rfl : (T j).SameCycle x x)
    · rw [root_cell T pr j x q pos,sectorValue,row,value]
      simp only [q,index_cornerTri,orbitPhase_pow _ _ (Polar.primitive dn)]
      exact eq
  by_cases zero : t=0
  · have vz : v=0 := Classical.byContradiction fun h => (pow_ne_zero d h) zero
    have rz : R=0 := Classical.byContradiction fun h => (pow_ne_zero d h) (rootPower.trans zero)
    exact witness 0 (by simp [vz,rz])
  · have rn : R≠0 := fun h => zero (by rw [←rootPower,h,zero_pow dn])
    have pow_one : (v/R)^d=1 := by rw [div_pow,rootPower]; exact div_self zero
    obtain ⟨k,_,hk⟩ := (Polar.primitive dn).eq_pow_of_pow_eq_one pow_one
    exact witness k ((eq_div_iff rn).mp hk)

end
end AK14.Gluing
