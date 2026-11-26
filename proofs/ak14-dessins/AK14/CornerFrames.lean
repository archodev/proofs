import AK14.SphereProjection

namespace AK14.Gluing
open Complex Set Topology
open scoped OnePoint
noncomputable section

def axes (j : Fin 3) : Equiv.Perm (Fin 3) := Equiv.swap 2 (opposite j)
def positiveEdge (j : Fin 3) := axes j 0
def negativeEdge (j : Fin 3) := axes j 1

def frame (j : Fin 3) (z : Triangle) : Triangle :=
  ⟨z.val ∘ axes j,fun _ => z.property.1 _,(Equiv.sum_comp (axes j) z.val).trans z.property.2⟩

@[simp] theorem frame_frame (j : Fin 3) (z : Triangle) : frame j (frame j z)=z := by
  apply Subtype.ext; funext i
  change z.val (Equiv.swap _ _ (Equiv.swap _ _ i))=_
  rw [Equiv.swap_apply_self]

theorem frame_continuous (j : Fin 3) : Continuous (frame j) :=
  Continuous.subtype_mk (continuous_pi (fun i => coord_cont (axes j i))) _

@[simp] theorem frame_zeroMass (j : Fin 3) (z : Triangle) : zeroMass (frame j z)=z.val (opposite j) := by
  change z.val (Equiv.swap _ _ 2)=_; simp

@[simp] theorem frame_oneMass (j : Fin 3) (z : Triangle) : oneMass (frame j z)=z.val (negativeEdge j) := rfl
@[simp] theorem frame_infMass (j : Fin 3) (z : Triangle) : infMass (frame j z)=z.val (positiveEdge j) := rfl

def frameSide (j : Fin 3) (b : Bool) : Bool := if j=0 then b else !b
def isUpper (j : Fin 3) (b : Bool) : Bool := !(frameSide j b)
def cornerValue (j : Fin 3) (b : Bool) (z : Triangle) := affinePoint (frameSide j b) (frame j z)

@[simp] theorem frameSide_twice (j : Fin 3) (b : Bool) : frameSide j (frameSide j b)=b := by
  by_cases h : j=0 <;> simp [frameSide,h]

theorem upper_sign {j : Fin 3} {b : Bool} (h : isUpper j b=true) (z : Triangle) : 0≤(cornerValue j b z).im := by
  have y := chosen_side (frame j z) (frameSide j b)
  cases s : frameSide j b <;> simp [isUpper,s,cornerValue,sideSign] at h y ⊢
  exact y

theorem lower_sign {j : Fin 3} {b : Bool} (h : isUpper j b=false) (z : Triangle) : (cornerValue j b z).im≤0 := by
  have y := chosen_side (frame j z) (frameSide j b)
  cases s : frameSide j b <;> simp [isUpper,s,cornerValue,sideSign] at h y ⊢
  exact y

theorem corner_pos_ray {j : Fin 3} {z : Triangle} (m : z.val (positiveEdge j)=0) (b : Bool) :
    (cornerValue j b z).im=0 ∧ 0≤(cornerValue j b z).re := by
  have c : infMass (frame j z)=0 := m
  have iz : imagNum (frame j z)=0 := boundary_imag_zero _ (j:=0) m
  have bp : 0≤baseMass (frame j z) := add_nonneg ((frame j z).property.1 2) ((frame j z).property.1 1)
  dsimp only [cornerValue,affinePoint]
  rw [iz,realNum,c]
  simp only [mul_zero,zero_div,zero_mul,add_zero,true_and]
  exact div_nonneg (mul_nonneg ((frame j z).property.1 1) bp) (sq_nonneg _)

theorem corner_neg_ray {j : Fin 3} {z : Triangle} (m : z.val (negativeEdge j)=0) (b : Bool) :
    (cornerValue j b z).im=0 ∧ (cornerValue j b z).re≤0 := by
  have c : oneMass (frame j z)=0 := m
  have iz : imagNum (frame j z)=0 := boundary_imag_zero _ (j:=1) m
  dsimp only [cornerValue,affinePoint]
  rw [iz,realNum,c]
  simp only [mul_zero,zero_div,zero_mul,zero_add,zero_sub,mul_neg,true_and]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg ((frame j z).property.1 0)
    ((frame j z).property.1 2))) (sq_nonneg _)

theorem corner_same {j : Fin 3} {z : Triangle} {k : Fin 3} (m : z.val k=0) (b c : Bool) :
    cornerValue j b z=cornerValue j c z := by
  have hz : (frame j z).val ((axes j).symm k)=0 := by change z.val (axes j ((axes j).symm k))=0; simpa using m
  apply Complex.ext
  · rfl
  · simp [cornerValue,affinePoint,boundary_imag_zero _ hz]

def cornerIndex {n : ℕ} (T : Triple n) (j : Fin 3) : Tri n → Fin n
  | (true,i) => i
  | (false,i) => (crossing T (positiveEdge j))⁻¹ i

def cornerTri {n : ℕ} (T : Triple n) (j : Fin 3) (b : Bool) (i : Fin n) : Tri n :=
  if b then (true,i) else (false,crossing T (positiveEdge j) i)

@[simp] theorem index_cornerTri {n : ℕ} (T : Triple n) (j : Fin 3) (b : Bool) (i : Fin n) :
    cornerIndex T j (cornerTri T j b i)=i := by cases b <;> simp [cornerIndex,cornerTri]

@[simp] theorem cornerTri_index {n : ℕ} (T : Triple n) (j : Fin 3) (q : Tri n) :
    cornerTri T j q.1 (cornerIndex T j q)=q := by obtain ⟨b,i⟩ := q; cases b <;> simp [cornerIndex,cornerTri]

theorem index_positive {n : ℕ} (T : Triple n) (j : Fin 3) (q : Tri n) :
    cornerIndex T j (step T (positiveEdge j) q)=cornerIndex T j q := by
  obtain ⟨b,i⟩ := q; cases b <;> simp [step,cornerIndex]

theorem index_negative {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (q : Tri n)
    (h : isUpper j q.1=true) : cornerIndex T j (step T (negativeEdge j) q)=T j (cornerIndex T j q) := by
  have third : T 2=(T 1)⁻¹*(T 0)⁻¹ := by
    have eq := eq_inv_of_mul_eq_one_right pr
    simpa using eq
  obtain ⟨b,i⟩ := q
  fin_cases j <;> cases b <;> first
    | exact Bool.noConfusion h
    | change (T 0) i=(T 0) i; rfl
    | change (T 1) i=(T 1) i; rfl
    | change (T 1)⁻¹ ((T 0)⁻¹ i)=T 2 i; rw [third]; rfl

theorem upper_step {n : ℕ} (T : Triple n) (j k : Fin 3) (q : Tri n) :
    isUpper j (step T k q).1= !(isUpper j q.1) := by
  obtain ⟨b,i⟩ := q; cases b <;> by_cases h : j=0 <;> simp [step,isUpper,frameSide,h]

theorem edge_trichotomy (j k : Fin 3) :
    k=positiveEdge j ∨ k=negativeEdge j ∨ k=opposite j := by
  fin_cases j <;> fin_cases k <;> decide

end
end AK14.Gluing
