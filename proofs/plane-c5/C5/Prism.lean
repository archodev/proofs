module
public import C5.Coloring

@[expose] public section
namespace C5
noncomputable section

def prismPath (r s i j k : Fin 3) : Fin 5 → Fin 3 × Fin 3 :=
  ![(r,i),(r,k),(r,j),(s,j),(s,i)]

def Adj (v w : Fin 3 × Fin 3) : Prop :=
  (v.1 = w.1 ∧ v.2 ≠ w.2) ∨ (v.2 = w.2 ∧ v.1 ≠ w.1)

private theorem walk_spec : ∀ r s i j k : Fin 3, r ≠ s → i ≠ j → i ≠ k → j ≠ k →
    Function.Injective (prismPath r s i j k) ∧
    ∀ t : Fin 5, Adj (prismPath r s i j k t) (prismPath r s i j k (t+1)) := by
  intro r s i j k hrs hij hik hjk
  constructor
  · intro t u he
    fin_cases t <;> fin_cases u <;> simp_all [prismPath,Ne.symm]
  · intro t
    fin_cases t <;> simp [prismPath,Adj,hrs,hij,hik,hjk,Ne.symm]

theorem prism_pentagon {v : Fin 3 × Fin 3 → ℂ} (hi : Function.Injective v)
    (he : ∀ a b, Adj a b → dist (v a) (v b) = 1) {r s i j k : Fin 3}
    (hrs : r ≠ s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Pentagon (v ∘ prismPath r s i j k) := by
  obtain ⟨hp,ha⟩ := walk_spec r s i j k hrs hij hik hjk
  exact ⟨hi.comp hp,fun t => he _ _ (ha t)⟩

def triangle (t : Fin 3 → ℂ) := ∀ i j, i ≠ j → dist (t i) (t j) = 1
def prism (p q : Fin 3 → ℂ) (v : Fin 3 × Fin 3) := p v.2 + q v.1

theorem prism_edges {p q : Fin 3 → ℂ} (hp : triangle p) (hq : triangle q)
    (a b : Fin 3 × Fin 3) (h : Adj a b) : dist (prism p q a) (prism p q b) = 1 := by
  obtain ⟨r,i⟩ := a; obtain ⟨s,j⟩ := b
  rcases h with ⟨rfl,hn⟩|⟨rfl,hn⟩
  · simpa [prism] using hp _ _ hn
  · simpa [prism] using hq _ _ hn

private theorem third : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by decide

private theorem unique_or_pair (f : Fin 3 → Bool) (a : Bool)
    (h : ∀ i j, i ≠ j → f i = a → f j ≠ a) :
    (∀ i, f i = !a) ∨ ∃! i, f i = a := by
  by_cases he : ∃ i, f i = a
  · obtain ⟨i,hi⟩ := he
    exact Or.inr ⟨i,hi,fun j hj => by_contra fun hn => h i j (Ne.symm hn) hi hj⟩
  · left
    intro i
    have hn : f i ≠ a := fun eq => he ⟨i,eq⟩
    cases a <;> cases h : f i <;> simp_all

/-- If one of three disjoint triangular translates is monochromatic, each of
the other two rows contains exactly one point of its color. -/
theorem prism_count (c : ℂ → Bool) (avoid : ¬HasMono c) {p q : Fin 3 → ℂ}
    (hp : triangle p) (hq : triangle q) (hi : Function.Injective (prism p q))
    {r s : Fin 3} (hrs : r ≠ s) (a : Bool) (hr : ∀ i, c (prism p q (r,i)) = a) :
    ∃! i, c (prism p q (s,i)) = a := by
  let f := fun (r i : Fin 3) => c (prism p q (r,i))
  have atMost {v w : Fin 3} (hne : v ≠ w) (b : Bool) (row : ∀ i, f v i = b)
      {i j : Fin 3} (hij : i ≠ j) (hc : f w i = b) : f w j ≠ b := by
    intro hd
    obtain ⟨k,hik,hjk⟩ := third i j hij
    apply avoid
    refine ⟨_,prism_pentagon hi (prism_edges hp hq) hne hij hik hjk,?_⟩
    intro m
    change f (prismPath v w i j k m).1 (prismPath v w i j k m).2 = f v i
    rw [row i]
    fin_cases m <;> first | exact row _ | exact hc | exact hd
  rcases unique_or_pair (f s) a (fun _ _ he => atMost hrs a hr he) with hAll | hOne
  · obtain ⟨t,hrt,hst⟩ := third r s hrs
    obtain ⟨i,j,hij,eq⟩ := two_equal (f t)
    by_cases e : f t i = a
    · exact (atMost hrt a hr hij e (eq.symm.trans e)).elim
    · have e' : f t i = !a := by cases a <;> cases h : f t i <;> simp_all
      exact (atMost hst (!a) hAll hij e' (eq.symm.trans e')).elim
  · exact hOne

end
end C5
end
