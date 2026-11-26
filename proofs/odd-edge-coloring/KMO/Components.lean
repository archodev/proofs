import KMO.Parity

namespace KMO
variable {n : Nat}

theorem total_mod {n} {f g : Fin n → Nat} (h : ∀ i, f i % 2 = g i % 2) :
    total n f % 2 = total n g % 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have a := h 0
    have b := ih (fun i => h i.succ)
    simp only [total]
    omega

theorem handshaking (G : Graph n) : card G.oddAt % 2 = 0 := by
  have modEq : card G.oddAt % 2 = total n G.degree % 2 := by
    apply total_mod; intro i
    by_cases h : G.degree i % 2 = 1 <;> simp [bit,Graph.oddAt,h] <;> omega
  rw [modEq]
  clear modEq
  induction n with
  | zero => rfl
  | succ n ih =>
    let H : Graph n := ⟨fun i j => G.adj i.succ j.succ,fun e => G.sym e,fun i => G.loopless i.succ⟩
    have tail (i : Fin n) : G.degree i.succ = bit (G.adj 0 i.succ) + H.degree i := by
      change bit (G.adj i.succ 0) + _ = _
      rw [propext (show G.adj i.succ 0 ↔ G.adj 0 i.succ from ⟨G.sym,G.sym⟩)]
      rfl
    have cen : G.degree 0 = total n (fun i => bit (G.adj 0 i.succ)) := by
      change bit (G.adj 0 0) + _ = _; simp [bit,G.loopless]
    have h := ih H
    simp only [total,funext tail, total_add,cen]
    omega

def outside {G : Graph n} {S : Region n} (h : ∀ ⦃i j⦄, G.adj i j → S i) {v} (hv : ¬S v) :
    G.degree v = 0 := by
  have ng : ¬0 < G.degree v := fun pos => by
    obtain ⟨_,e⟩ := Graph.degree_pos.mp pos; exact hv (h e)
  omega

theorem within_same {G : Graph n} {S : Region n}
    (closed : ∀ i j, S i → G.adj i j → S j) {i} (hi : S i) :
    (G.within S).degree i = G.degree i :=
  card_congr (fun j => ⟨And.left,fun e => ⟨e,hi,closed i j hi e⟩⟩)

abbrev Full (n : Nat) : Region n := fun _ => True

def Anchored (G : Graph n) (T : Region n) := ∀ v, G.supp v →
  ∃ t, T t ∧ Reach G (Full n) v t

theorem reach_full_mono {A B : Graph n} (sub : A.Sub B) {x y}
    (p : Reach A (Full n) x y) : Reach B (Full n) x y :=
  p.transport (fun _ => id) (fun _ _ _ _ e => sub e)

theorem anchored_join (G : Graph n) (S D : Region n)
    (conn : ConnectedOn G S) (sub : ∀ i, D i → S i) (even : card D % 2 = 0) :
    ∃ F : Graph n, F.Sub (G.within S) ∧ (∀ v, F.degree v % 2 = bit (D v)) ∧ Anchored F D := by
  obtain ⟨J,js,jp⟩ := parity_join G S D conn sub even
  let M := fun v => ∃ t, D t ∧ Reach J (Full n) v t
  have closed (i j) (hi : M i) (e : J.adj i j) : M j := by
    obtain ⟨t,dt,p⟩ := hi
    exact ⟨t,dt,((Reach.here trivial).next (J.sym e) trivial).trans p⟩
  have inside {i} (d : D i) : M i := ⟨i,d,.here trivial⟩
  refine ⟨J.within M,by intro _ _ e; exact js e.1,?_,?_⟩
  · intro i; by_cases m : M i
    · rw [within_same closed m,jp]
    · have noD : ¬D i := fun h => m (inside h)
      have z := outside (G := J.within M) (S := M) (by intro _ _ e; exact e.2.1) m
      simp [z,bit,noD]
  · intro v hv
    obtain ⟨j,e⟩ := hv
    obtain ⟨t,dt,p⟩ := e.2.1
    refine ⟨t,dt,?_⟩
    have lift {a b} (h : Reach J (Full n) a b) (ha : M a) : Reach (J.within M) (Full n) a b ∧ M b := by
      induction h with
      | here _ => exact ⟨.here trivial,ha⟩
      | next _ e _ ih =>
        have k := closed _ _ ih.2 e
        exact ⟨ih.1.next ⟨e,ih.2,k⟩ trivial,k⟩
    exact (lift p e.2.1).1

/-- The component of v in a graph, including v even when it is isolated. -/
def comp (G : Graph n) (v : Fin n) : Region n := fun z => Reach G (Full n) v z

theorem comp_closed (G : Graph n) (v i j) (h : comp G v i) (e : G.adj i j) : comp G v j :=
  h.next e trivial

theorem comp_handshake (G : Graph n) (v) :
    card (fun i => comp G v i ∧ G.oddAt i) % 2 = 0 := by
  have e : card (fun i => comp G v i ∧ G.oddAt i) = card (G.within (comp G v)).oddAt := by
    apply card_congr; intro i; by_cases hi : comp G v i
    · simp [Graph.oddAt,hi,within_same (comp_closed G v) hi]
    · have z := outside (G := G.within (comp G v)) (S := comp G v) (by intro _ _ e; exact e.2.1) hi
      simp [Graph.oddAt,hi,z]
  rw [e]; exact handshaking _

end KMO
