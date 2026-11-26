import HensonAll
import Mathlib.ModelTheory.Graph

/-! The first-order consequence of the finite extension theorem. The hypothesis
on the input graph is the defining extension scheme of a Henson graph. -/
namespace HensonAll
open Finset FirstOrder
noncomputable section

variable {U V : Type*} {G : SimpleGraph U} {H : SimpleGraph V} {n r : ℕ}

def Match (G : SimpleGraph U) (H : SimpleGraph V) (u : Fin n → U) (v : Fin n → V) : Prop :=
  (∀ i j, u i = u j ↔ v i = v j) ∧
  (∀ i j, G.Adj (u i) (u j) ↔ H.Adj (v i) (v j))

theorem Match.reverse {u : Fin n → U} {v : Fin n → V} (h : Match G H u v) :
    Match H G v u :=
  ⟨fun i j => (h.1 i j).symm, fun i j => (h.2 i j).symm⟩

private theorem matchSnoc {u : Fin n → U} {v : Fin n → V} (h : Match G H u v)
    {a : U} {b : V} (he : ∀ i, a = u i ↔ b = v i)
    (ha : ∀ i, G.Adj a (u i) ↔ H.Adj b (v i)) :
    Match G H (Fin.snoc u a) (Fin.snoc v b) := by
  constructor
  · intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · simp
      · simpa using he j'
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · simpa only [Fin.snoc_castSucc, Fin.snoc_last, eq_comm (a := u i'), eq_comm (a := v i')]
          using he i'
      · simpa using h.1 i' j'
  · intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · simpa only [Fin.snoc_last] using iff_of_false (G.loopless a) (H.loopless b)
      · simpa using ha j'
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.snoc_last,
            G.adj_comm, H.adj_comm]
        exact ha i'
      · simpa using h.2 i' j'

/-- One move in the bounded back-and-forth argument. -/
theorem extendMatch (hr : 3 ≤ r) (hG : NoClique r G.Adj)
    (hH : CliqueExtension r n H) {u : Fin n → U} {v : Fin n → V} (h : Match G H u v)
    (a : U) : ∃ b, Match G H (Fin.snoc u a) (Fin.snoc v b) := by
  classical
  by_cases old : ∃ i, u i = a
  · obtain ⟨i, rfl⟩ := old
    exact ⟨v i, matchSnoc h (h.1 i) (h.2 i)⟩
  let A : Finset V := (univ.filter (fun i => G.Adj a (u i))).image v
  let B : Finset V := (univ.filter (fun i => ¬ G.Adj a (u i))).image v
  have pos (z : V) : z ∈ A ↔ ∃ i, G.Adj a (u i) ∧ v i = z := by
    simp [A, mem_image, mem_filter]
  have neg (z : V) : z ∈ B ↔ ∃ i, ¬ G.Adj a (u i) ∧ v i = z := by
    simp [B, mem_image, mem_filter]
  have disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨i, hi, ei⟩ := (pos z).mp hz
    obtain ⟨j, hj, ej⟩ := (neg z).mp hz'
    exact hj ((h.1 i j).mpr (ei.trans ej.symm) ▸ hi)
  have size : A.card + B.card ≤ n := by
    rw [← Finset.card_union_of_disjoint disj]
    calc
      (A ∪ B).card ≤ (univ.image v).card := by
        apply Finset.card_le_card
        intro z hz
        rcases Finset.mem_union.mp hz with hp | hn
        · obtain ⟨i,_,hi⟩ := (pos z).mp hp
          exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
        · obtain ⟨i,_,hi⟩ := (neg z).mp hn
          exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
      _ ≤ n := Finset.card_image_le.trans (by simp)
  have aFree : ∀ C : Finset V, C ⊆ A → C.card = r - 1 → PairOn H.Adj C → False := by
    intro C sub card cl
    have hi (x : ↥C) : ∃ i, G.Adj a (u i) ∧ v i = x.val := (pos _).mp (sub x.property)
    choose f hf using hi
    let src (x : ↥C) : U := u (f x)
    have inj : Function.Injective src := by
      intro x y eq
      apply Subtype.ext
      exact (hf x).2.symm.trans (((h.1 (f x) (f y)).mp eq).trans (hf y).2)
    let D : Finset U := univ.image src
    have haD : a ∉ D := by
      intro ha
      obtain ⟨x,_, e⟩ := Finset.mem_image.mp ha
      exact old ⟨f x,e⟩
    have cardD : D.card = r - 1 := by
      dsimp [D]
      rw [Finset.card_image_of_injective _ inj, Finset.card_attach, card]
    have pairD : PairOn G.Adj D := by
      intro x hx y hy ne
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hy
      have neq : p.val ≠ q.val := fun e => ne (congrArg src (Subtype.ext e))
      apply (h.2 (f p) (f q)).mpr
      rw [(hf p).2, (hf q).2]
      exact cl p.val p.property q.val q.property neq
    apply hG (insert a D) (by rw [Finset.card_insert_of_not_mem haD, cardD]; omega)
    intro x hx y hy ne
    by_cases hxa : x = a
    · have hy' := (Finset.mem_insert.mp hy).resolve_left (fun e => ne (hxa.trans e.symm))
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hy'
      rw [hxa]
      exact (hf p).1
    · have hxD := (Finset.mem_insert.mp hx).resolve_left hxa
      by_cases hya : y = a
      · obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hxD
        rw [hya]
        exact G.symm (hf p).1
      · exact pairD x hxD y ((Finset.mem_insert.mp hy).resolve_left hya) ne
  obtain ⟨b, hbA, hbB, yes, no⟩ := hH A B disj size aFree
  have mem (i : Fin n) : v i ∈ A ∨ v i ∈ B := by
    by_cases hh : G.Adj a (u i)
    · exact Or.inl ((pos _).mpr ⟨i,hh,rfl⟩)
    · exact Or.inr ((neg _).mpr ⟨i,hh,rfl⟩)
  refine ⟨b, matchSnoc h ?_ ?_⟩
  · intro i
    refine iff_of_false (fun eq => old ⟨i,eq.symm⟩) ?_
    intro eq
    rcases mem i with hm | hm
    · exact hbA (eq.symm ▸ hm)
    · exact hbB (eq.symm ▸ hm)
  · intro i
    constructor
    · intro hh
      exact yes _ ((pos _).mpr ⟨i,hh,rfl⟩)
    · intro hh
      by_cases ng : G.Adj a (u i)
      · exact ng
      · exact (no _ ((neg _).mpr ⟨i,ng,rfl⟩) hh).elim

private def depth : ∀ {n : ℕ}, (Language.graph.BoundedFormula Empty n) → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp a b => max (depth a) (depth b)
  | _, .all a => depth a + 1

private theorem graphTermIsVar {n : ℕ} (t : Language.graph.Term (Empty ⊕ Fin n)) :
    ∃ i, t = Language.Term.var (.inr i) := by
  cases t with
  | var z =>
    cases z with
    | inl e => exact e.elim
    | inr i => exact ⟨i,rfl⟩
  | func f _ => exact (show Empty from f).elim

private theorem preserve (hr : 3 ≤ r) (hG : NoClique r G.Adj) (hH : NoClique r H.Adj)
    (eg : ∀ j, j ≤ k → CliqueExtension r j G) (eh : ∀ j, j ≤ k → CliqueExtension r j H)
    {n : ℕ} (φ : Language.graph.BoundedFormula Empty n)
    (hk : n + depth φ ≤ k) (u : Fin n → U) (v : Fin n → V) (hm : Match G H u v) :
    @Language.BoundedFormula.Realize _ U G.structure _ _ φ default u ↔
    @Language.BoundedFormula.Realize _ V H.structure _ _ φ default v := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    obtain ⟨i,rfl⟩ := graphTermIsVar t
    obtain ⟨j,rfl⟩ := graphTermIsVar s
    exact hm.1 i j
  | rel R ts =>
    cases R
    obtain ⟨i,hi⟩ := graphTermIsVar (ts 0)
    obtain ⟨j,hj⟩ := graphTermIsVar (ts 1)
    change G.Adj (@Language.Term.realize _ U G.structure _ (Sum.elim (default : Empty → U) u) (ts 0))
        (@Language.Term.realize _ U G.structure _ (Sum.elim (default : Empty → U) u) (ts 1)) ↔
      H.Adj (@Language.Term.realize _ V H.structure _ (Sum.elim (default : Empty → V) v) (ts 0))
        (@Language.Term.realize _ V H.structure _ (Sum.elim (default : Empty → V) v) (ts 1))
    rw [hi,hj]
    exact hm.2 i j
  | imp a b ia ib =>
    simp only [depth] at hk
    exact (ia (by omega) u v hm).imp (ib (by omega) u v hm)
  | @all n a ih =>
    simp only [depth] at hk
    change (∀ x : U, @Language.BoundedFormula.Realize _ U G.structure _ _ a default (Fin.snoc u x)) ↔
      (∀ y : V, @Language.BoundedFormula.Realize _ V H.structure _ _ a default (Fin.snoc v y))
    constructor
    · intro hx y
      obtain ⟨x,hm'⟩ := extendMatch hr hH (eg n (by omega)) hm.reverse y
      exact (ih (by omega) _ _ hm'.reverse).mp (hx x)
    · intro hy x
      obtain ⟨y,hm'⟩ := extendMatch hr hG (eh n (by omega)) hm x
      exact (ih (by omega) _ _ hm').mpr (hy y)

/-- Every first-order sentence of a graph with the Henson extension scheme
has a finite graph model. The theorem is stated in Mathlib's graph language. -/
theorem finiteSentenceModel (r : ℕ) (hr : 3 ≤ r) (G : SimpleGraph U)
    (hG : NoClique r G.Adj) (ext : ∀ k, CliqueExtension r k G)
    (φ : Language.graph.Sentence) (hφ : @Language.Sentence.Realize _ U G.structure φ) :
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (H : SimpleGraph V), NoClique r H.Adj ∧
      @Language.Sentence.Realize _ V H.structure φ := by
  let k := depth φ
  obtain ⟨V,f,H,hH,hE⟩ := finite_clique_extension r k hr
  have hsame : Match G H (default : Fin 0 → U) (default : Fin 0 → V) :=
    ⟨fun i _ => i.elim0, fun i _ => i.elim0⟩
  have eh (j : ℕ) (hj : j ≤ k) : CliqueExtension r j H := by
    intro A B hAB bound rest
    exact hE A B hAB (bound.trans hj) rest
  have hv : Nonempty V := by
    obtain ⟨x, _⟩ := hE ∅ ∅ (by simp) (by simp) (by
      intro C hs hc _
      have hempty : C = ∅ := Finset.subset_empty.mp hs
      simp [hempty] at hc
      omega)
    exact ⟨x⟩
  refine ⟨V,f,hv,H,hH,?_⟩
  exact (preserve hr hG hH (fun j _ => ext j) eh φ (by simp [k]) _ _ hsame).mp hφ

#print axioms finiteSentenceModel

/-- Pseudofiniteness of any Henson graph in the standard Mathlib graph language.
The hypothesis is the usual one-point extension scheme of the countable
homogeneous K_r-free graph. The finite models may depend on the sentence. -/
theorem hensonPseudofinite (r : ℕ) (hr : 3 ≤ r) (G : SimpleGraph U)
    (hG : G.CliqueFree r)
    (ext : ∀ A B : Finset U, Disjoint A B →
      G.CliqueFreeOn (A : Set U) (r - 1) →
      ∃ x, x ∉ A ∧ x ∉ B ∧ (∀ y ∈ A, G.Adj x y) ∧ (∀ b ∈ B, ¬ G.Adj x b))
    (φ : Language.graph.Sentence) (hφ : @Language.Sentence.Realize _ U G.structure φ) :
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (H : SimpleGraph V), H.CliqueFree r ∧
      @Language.Sentence.Realize _ V H.structure φ := by
  have noG : NoClique r G.Adj := fun C hc hcl => hG C ⟨hcl, hc⟩
  have eG (k : ℕ) : CliqueExtension r k G := by
    intro A B disj _ hA
    exact ext A B disj (fun _ hs hc => hA _ (Finset.coe_subset.mp hs) hc.card_eq hc.isClique)
  obtain ⟨V, f, hv, H, hH, hreal⟩ := finiteSentenceModel r hr G noG eG φ hφ
  exact ⟨V, f, hv, H, fun C hc => hH C hc.card_eq hc.isClique, hreal⟩

#print axioms hensonPseudofinite

end
end HensonAll
