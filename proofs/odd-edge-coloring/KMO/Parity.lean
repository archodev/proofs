import KMO.Basic

namespace KMO

variable {n : Nat}

theorem card_mono {S T : Region n} (h : ∀ i, S i → T i) : card S ≤ card T := by
  have e : card (fun i => T i ∧ S i) = card S := card_congr (fun i => ⟨And.right,fun a => ⟨h i a,a⟩⟩)
  have t := card_split T S
  omega

theorem card_erase {S : Region n} {v} (hv : S v) :
    card (fun i => S i ∧ i ≠ v) + 1 = card S := by
  have e : card (fun i => S i ∧ i = v) = 1 :=
    (card_congr (fun i => show (S i ∧ i = v) ↔ i = v from ⟨And.right,fun h => ⟨h ▸ hv,h⟩⟩)).trans (card_single v)
  have t := card_split S (fun i => i = v)
  change card (fun i => S i ∧ i = v) + card (fun i => S i ∧ i ≠ v) = card S at t
  rw [e] at t; omega

namespace Reach
variable {G H : Graph n} {S T : Region n} {x y z : Fin n}

theorem start (p : Reach G S x y) : S x := by induction p <;> assumption
theorem finish (p : Reach G S x y) : S y := by cases p <;> assumption
theorem trans (p : Reach G S x y) (q : Reach G S y z) : Reach G S x z := by
  induction q with | here => exact p | next _ e h ih => exact ih.next e h
theorem reverse (p : Reach G S x y) : Reach G S y x := by
  induction p with
  | here h => exact .here h
  | next p e h ih => exact ((Reach.here h).next (G.sym e) p.finish).trans ih

theorem transport (p : Reach G S x y) (hs : ∀ i, S i → T i)
    (he : ∀ i j, S i → S j → G.adj i j → H.adj i j) : Reach H T x y := by
  induction p with
  | here h => exact .here (hs _ h)
  | next p e h ih => exact ih.next (he _ _ p.finish h e) (hs _ h)
end Reach

def edge {a b : Fin n} (hab : a ≠ b) := Graph.star a (fun v => v = b) hab

theorem degree_edge {a b : Fin n} (hab : a ≠ b) (v) :
    (edge hab).degree v = bit (v = a) + bit (v = b) := by
  unfold edge
  rw [Graph.degree_star,card_single]
  by_cases h : v = a
  · subst v; simp [bit,hab]
  · simp [h,bit]

theorem path_boundary {G : Graph n} {S : Region n} {a b}
    (p : Reach G S a b) : ∃ F : Graph n, F.Sub (G.within S) ∧
      ∀ v, F.degree v % 2 = (bit (v = a) + bit (v = b)) % 2 := by
  induction p with
  | here h =>
    refine ⟨.Empty _,by intro _ _ h; exact False.elim h,?_⟩
    intro v
    have zz : (Graph.Empty n).degree v = 0 := card_empty
    rw [zz]; omega
  | @next c d p e hd ih =>
    obtain ⟨F,sub,par⟩ := ih
    have ne : c ≠ d := fun h => G.loopless d (h ▸ e)
    let E := edge ne
    have es : E.Sub (G.within S) := by
      intro i j h
      change (i = c ∧ j = d) ∨ (j = c ∧ i = d) at h
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨e,p.finish,hd⟩
      · exact ⟨G.sym e,hd,p.finish⟩
    refine ⟨F.xor E,?_,?_⟩
    · intro i j h
      rcases h with h | h
      · exact sub h.1
      · exact es h.1
    · intro v
      rw [Graph.degree_xor]
      have h := par v
      have he := degree_edge ne v
      change (F.degree v + (edge ne).degree v) % 2 = _
      omega

/-- A T-join inside the induced connected graph on S. The empty S is allowed. -/
theorem parity_join (G : Graph n) (S D : Region n)
    (conn : ConnectedOn G S) (sub : ∀ i, D i → S i) (even : card D % 2 = 0) :
    ∃ F : Graph n, F.Sub (G.within S) ∧ ∀ v, F.degree v % 2 = bit (D v) := by
  classical
  by_cases pos : 0 < card D
  · obtain ⟨a,ha⟩ := card_pos.mp pos
    have ca := card_erase ha
    have pp : 0 < card (fun i => D i ∧ i ≠ a) := by omega
    obtain ⟨b,hb,hba⟩ := card_pos.mp pp
    let D' := fun i => (D i ∧ i ≠ a) ∧ i ≠ b
    have cb := card_erase (S := fun i => D i ∧ i ≠ a) (v := b) ⟨hb,hba⟩
    change card D' + 1 = card (fun i => D i ∧ i ≠ a) at cb
    have cd : card D' + 2 = card D := by omega
    obtain ⟨F,fs,fp⟩ := parity_join G S D' conn (fun i h => sub i h.1.1) (by omega)
    obtain ⟨P,ps,pp⟩ := path_boundary (conn a (sub _ ha) b (sub _ hb))
    refine ⟨F.xor P,?_,?_⟩
    · intro i j h; rcases h with h | h
      · exact fs h.1
      · exact ps h.1
    · intro v
      rw [Graph.degree_xor]
      have f := fp v
      have p := pp v
      rw [Nat.add_mod, f,p]
      by_cases va : v = a <;> by_cases vb : v = b <;> by_cases dv : D v <;>
        simp_all [D',bit] <;> omega
  · refine ⟨.Empty _,by intro _ _ h; exact False.elim h,?_⟩
    intro v; have nv : ¬D v := fun h => pos (card_pos.mpr ⟨v,h⟩)
    change card (fun _ : Fin n => False) % 2 = _
    simp [card_empty,bit,nv]
termination_by card D
decreasing_by change card D' < card D; omega

end KMO
