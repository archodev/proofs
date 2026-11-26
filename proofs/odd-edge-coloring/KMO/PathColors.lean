import KMO.OpenPath
namespace KMO.OpenPath
variable {n : Nat} {G : Graph n} {s t : Fin n}

def strand (P : OpenPath G s t) (f : Nat → Bool) (b : Bool) : Graph n where
  adj v j := ∃ k,k < P.len ∧ f k = b ∧
    ((P.node k = v ∧ P.node (k+1) = j) ∨ (P.node k = j ∧ P.node (k+1) = v))
  sym := by rintro _ _ ⟨k,hk,bk,e⟩; exact ⟨k,hk,bk,e.symm⟩
  loopless v := by
    rintro ⟨k,hk,_,e⟩
    have eq := (e.elim id id).1.trans (e.elim id id).2.symm
    have h := P.injective (by omega) (by omega) eq; omega

theorem strand_sub (P : OpenPath G s t) (f : Nat → Bool) (b : Bool) : (P.strand f b).Sub P.edges := by
  rintro i j ⟨k,hk,_,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
  · exact ⟨P.step k hk,P.has_at (by omega),P.has_at (by omega)⟩
  · exact ⟨G.sym (P.step k hk),P.has_at (by omega),P.has_at (by omega)⟩

theorem strand_cover (P : OpenPath G s t) (f : Nat → Bool) {i j} (e : P.edges.adj i j) :
    (P.strand f true).adj i j ∨ (P.strand f false).adj i j := by
  obtain ⟨g,⟨a,ha,rfl⟩,⟨b,hb,rfl⟩⟩ := e
  obtain rfl | rfl := (P.induced a b ha hb).mp g
  · cases h : f a
    · right; exact ⟨a,by omega,h,Or.inl ⟨rfl,rfl⟩⟩
    · left; exact ⟨a,by omega,h,Or.inl ⟨rfl,rfl⟩⟩
  · cases h : f b
    · right; exact ⟨b,by omega,h,Or.inr ⟨rfl,rfl⟩⟩
    · left; exact ⟨b,by omega,h,Or.inr ⟨rfl,rfl⟩⟩

theorem strand_disjoint (P : OpenPath G s t) (f : Nat → Bool) : (P.strand f true).Disj (P.strand f false) := by
  rintro i j ⟨a,ha,fa,e⟩ ⟨b,hb,fb,g⟩
  have same : a = b := by
    rcases e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases g with ⟨k,z⟩ | ⟨k,z⟩
    all_goals first
      | exact (P.injective (by omega) (by omega) k).symm
      | have u := P.injective (by omega) (by omega) k
        have v := P.injective (by omega) (by omega) z
        omega
  simp_all

theorem strand_row (P : OpenPath G s t) (f : Nat → Bool) (b : Bool) {k} (hk : k ≤ P.len) (j) :
    (P.strand f b).adj (P.node k) j ↔
    (j = P.node (k-1) ∧ (0 < k ∧ f (k-1) = b)) ∨ (j = P.node (k+1) ∧ (k < P.len ∧ f k = b)) := by
  constructor
  · rintro ⟨a,ha,fa,⟨e,l⟩ | ⟨l,e⟩⟩
    · have eq := P.injective (Nat.le_of_lt ha) hk e
      subst a; exact Or.inr ⟨l.symm,ha,fa⟩
    · have eq := P.injective (by omega) hk e
      have aa : k-1=a := by omega
      exact Or.inl ⟨by rw [aa]; exact l.symm,by omega,by rwa [aa]⟩
  · rintro (⟨rfl,pos,col⟩ | ⟨rfl,lt,col⟩)
    · exact ⟨k-1,by omega,col,Or.inr ⟨rfl,congrArg P.node (by omega)⟩⟩
    · exact ⟨k,lt,col,Or.inl ⟨rfl,rfl⟩⟩

theorem strand_degree (P : OpenPath G s t) (f : Nat → Bool) (b : Bool) {k} (hk : k ≤ P.len) :
    (P.strand f b).degree (P.node k) = bit (0 < k ∧ f (k-1) = b) + bit (k < P.len ∧ f k = b) := by
  have dis j (left : j = P.node (k-1) ∧ (0 < k ∧ f (k-1) = b))
      (right : j = P.node (k+1) ∧ (k < P.len ∧ f k = b)) : False := by
    have u := P.injective (i := k-1) (j := k+1) (by omega) (by omega) (left.1.symm.trans right.1)
    omega
  change card _ = _
  rw [card_congr (P.strand_row f b hk),card_union dis,card_flag,card_flag]

theorem strand_start (P : OpenPath G s t) (f : Nat → Bool) (b : Bool) :
    (P.strand f b).degree s = bit (f 0 = b) := by
  have h := P.strand_degree f b (k := 0) (Nat.zero_le _)
  by_cases eq : f 0 = b <;> simpa [P.first,P.positive,bit,eq] using h

theorem strand_end (P : OpenPath G s t) (f : Nat → Bool) (b : Bool) :
    (P.strand f b).degree t = bit (f (P.len-1) = b) := by
  have h := P.strand_degree f b (Nat.le_refl _)
  by_cases eq : f (P.len-1) = b <;> simpa [P.last,P.positive,bit,eq] using h

end KMO.OpenPath
