import KMO.Connectivity
namespace KMO
variable {n : Nat}

structure Piece (n : Nat) where
  a : Fin n
  b : Fin n
  L : Region n

namespace Piece
variable {G : Graph n} {U : Region n}
def valid (p : Piece n) (G : Graph n) (U : Region n) := Shore G (del₂ U p.a p.b) p.L
def minimal (p : Piece n) (G : Graph n) (U : Region n) :=
  p.valid G U ∧ ∀ q : Piece n, q.valid G U → card p.L ≤ card q.L
abbrev domain (p : Piece n) := fun i => p.L i ∨ i = p.a ∨ i = p.b

theorem exists_minimal (two : Two G U) (no : ¬Three G U) : ∃ p : Piece n, p.minimal G U := by
  apply minimize (fun p : Piece n => p.valid G U) (fun p => card p.L)
  classical
  apply Classical.byContradiction; intro bad
  apply no; refine ⟨two,?_⟩
  intro a b; apply Classical.byContradiction; intro disc
  obtain ⟨L,sh⟩ := shore_of_disconnected disc
  exact bad ⟨⟨a,b,L⟩,sh⟩

theorem poles {p : Piece n} (s : p.valid G U) (two : Two G U) :
    U p.a ∧ U p.b ∧ p.a ≠ p.b := by
  have bad := s.disconnected
  constructor
  · apply Classical.byContradiction; intro na; apply bad
    exact conn_congr (S := del U p.b) (fun i => by simp [del₂,del]; grind) (two.2 p.b)
  constructor
  · apply Classical.byContradiction; intro nb; apply bad
    exact conn_congr (S := del U p.a) (fun i => by simp [del₂,del]; grind) (two.2 p.a)
  · intro eq; apply bad
    exact conn_congr (S := del U p.a) (fun i => by simp [del₂,del,eq]) (two.2 p.a)

theorem inner_conn {p : Piece n} (m : p.minimal G U) : ConnectedOn G p.L := by
  classical
  apply Classical.byContradiction; intro disc
  obtain ⟨M,s⟩ := shore_of_disconnected disc
  let q : Piece n := ⟨p.a,p.b,M⟩
  have hq : q.valid G U := by
    refine ⟨s.nonempty,fun i mi => m.1.inside _ (s.inside _ mi),?_,?_⟩
    · obtain ⟨i,ui,no⟩ := m.1.proper
      exact ⟨i,ui,fun mi => no (s.inside _ mi)⟩
    · intro i j mi uj e
      exact s.closed i j mi (m.1.closed i j (s.inside _ mi) uj e) e
  obtain ⟨i,li,no⟩ := s.proper
  exact (Nat.not_le_of_lt (strict_card s.inside li no)) (m.2 q hq)

theorem neighbors_poles {p : Piece n} (s : p.valid G U) (two : Two G U) :
    (∃ i, p.L i ∧ G.adj i p.a) ∧ (∃ i, p.L i ∧ G.adj i p.b) := by
  obtain ⟨ua,ub,ne⟩ := poles s two
  obtain ⟨i,li⟩ := s.nonempty
  have ui := s.inside _ li
  constructor
  · obtain ⟨j,k,_,uk,lj,nk,e⟩ := adjacent_across (two.2 p.b) ⟨ui.1.1,ui.2⟩ ⟨ua,ne⟩ li
      (fun la => (s.inside _ la).1.2 rfl)
    by_cases ka : k = p.a
    · exact ⟨j,lj,ka ▸ e⟩
    · exact False.elim (nk (s.closed _ _ lj ⟨⟨uk.1,ka⟩,uk.2⟩ e))
  · obtain ⟨j,k,_,uk,lj,nk,e⟩ := adjacent_across (two.2 p.a) ui.1 ⟨ub,ne.symm⟩ li
      (fun lb => (s.inside _ lb).2 rfl)
    by_cases kb : k = p.b
    · exact ⟨j,lj,kb ▸ e⟩
    · exact False.elim (nk (s.closed _ _ lj ⟨uk,kb⟩ e))

def torso (p : Piece n) (G : Graph n) (ne : p.a ≠ p.b) := G.union (edge ne)

theorem domain_subset {p : Piece n} (s : p.valid G U) (two : Two G U) :
    ∀ i, p.domain i → U i := by
  obtain ⟨ua,ub,_⟩ := poles s two
  rintro i (li | rfl | rfl)
  · exact (s.inside _ li).1.1
  · exact ua
  · exact ub

theorem neighbor_domain {p : Piece n} (s : p.valid G U)
    {i j} (li : p.L i) (uj : U j) (e : G.adj i j) : p.domain j := by
  by_cases a : j = p.a
  · exact Or.inr (Or.inl a)
  by_cases b : j = p.b
  · exact Or.inr (Or.inr b)
  exact Or.inl (s.closed _ _ li ⟨⟨uj,a⟩,b⟩ e)

theorem torso_three {p : Piece n} (m : p.minimal G U) (two : Two G U)
    {outside : Fin n} (out : ¬U outside) :
    Three (p.torso G (poles m.1 two).2.2) p.domain := by
  classical
  obtain ⟨ua,ub,ne⟩ := poles m.1 two
  let K := p.torso G ne
  have sg : G.Sub K := by intro _ _ e; exact Or.inl e
  have ab : K.adj p.a p.b := Or.inr (Or.inl ⟨rfl,rfl⟩)
  have du := domain_subset m.1 two
  have conn := inner_conn m
  have allpairs (c d : Fin n) : ConnectedOn K (del₂ p.domain c d) := by
    by_cases hit : p.L c ∨ p.L d
    · apply Classical.byContradiction; intro disc
      obtain ⟨M,s⟩ := shore_of_disconnected disc
      have orient : ∃ B, Shore K (del₂ p.domain c d) B ∧ ¬B p.a ∧ ¬B p.b := by
        by_cases ma : M p.a
        · refine ⟨_,shore_complement s,fun k => k.2 ma,fun k => k.2 (s.closed _ _ ma k.1 ab)⟩
        by_cases mb : M p.b
        · exact ⟨_,shore_complement s,fun k => k.2 (s.closed _ _ mb k.1 (K.sym ab)),fun k => k.2 mb⟩
        exact ⟨M,s,ma,mb⟩
      obtain ⟨B,sb,na,nb⟩ := orient
      have bl i (bi : B i) : p.L i := by
        obtain li | eq | eq := (sb.inside _ bi).1.1
        · exact li
        · exact False.elim (na (eq ▸ bi))
        · exact False.elim (nb (eq ▸ bi))
      let q : Piece n := ⟨c,d,B⟩
      have validq : q.valid G U := by
        refine ⟨sb.nonempty,?_,?_,?_⟩
        · intro i bi; have k := sb.inside _ bi
          exact ⟨⟨du _ k.1.1,k.1.2⟩,k.2⟩
        · obtain ⟨i,k,nb⟩ := sb.proper
          exact ⟨i,⟨⟨du _ k.1.1,k.1.2⟩,k.2⟩,nb⟩
        · intro i j bi uj e
          exact sb.closed _ _ bi ⟨⟨neighbor_domain m.1 (bl _ bi) uj.1.1 e,uj.1.2⟩,uj.2⟩ (sg e)
      have lo := m.2 q validq
      change card p.L ≤ card B at lo
      rcases hit with hc | hd
      · exact (Nat.not_le_of_lt (strict_card bl hc (fun bc => (sb.inside _ bc).1.2 rfl))) lo
      · exact (Nat.not_le_of_lt (strict_card bl hd (fun bd => (sb.inside _ bd).2 rfl))) lo
    · have keep i (li : p.L i) : del₂ p.domain c d i :=
        ⟨⟨Or.inl li,fun eq => hit (Or.inl (eq ▸ li))⟩,fun eq => hit (Or.inr (eq ▸ li))⟩
      apply attach_vertices (S := p.L) (conn_move conn (fun _ => Iff.rfl) (fun _ _ _ _ e => sg e)) keep
      intro i di nl
      have ab' := (di.1.1).resolve_left nl
      obtain ⟨pa,pb⟩ := neighbors_poles m.1 two
      rcases ab' with rfl | rfl
      · obtain ⟨j,lj,e⟩ := pa; exact ⟨j,lj,sg (G.sym e)⟩
      · obtain ⟨j,lj,e⟩ := pb; exact ⟨j,lj,sg (G.sym e)⟩
  have nd : ¬p.domain outside := fun d => out (du _ d)
  refine ⟨⟨?_,?_⟩,allpairs⟩
  · exact conn_congr (fun i => by simp [del₂,del]; grind) (allpairs outside outside)
  · intro i; exact conn_congr (fun j => by simp [del₂,del]; grind) (allpairs i outside)

end Piece
end KMO
