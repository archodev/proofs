module

public import C5.Geometry

@[expose] public section

namespace C5

def mixed (f : Fin 3 → Bool) : Prop := ∃ i j, f i ≠ f j

def bit (v : Bool) : ℕ := if v then 1 else 0

private theorem tally :
    ∀ (r : Bool) (f : Fin 3 → Bool), mixed f →
    (∀ i j, i ≠ j → f i = r → f j ≠ r) →
    bit r + bit (f 0) + bit (f 1) + bit (f 2) = 2 := by
  intro r f
  unfold mixed
  have h : ∀ (r a b d : Bool),
      (∃ i j : Fin 3, (![a,b,d] : Fin 3 → Bool) i ≠ ![a,b,d] j) →
      (∀ i j : Fin 3, i ≠ j → (![a,b,d] : Fin 3 → Bool) i = r → ![a,b,d] j ≠ r) →
      bit r + bit a + bit b + bit d = 2 := by decide
  have eqf : f = ![f 0, f 1, f 2] := by funext i; fin_cases i <;> rfl
  simpa only [← eqf] using h r (f 0) (f 1) (f 2)

theorem angular_count (c : ℂ → Bool) (avoid : ¬ HasMono c)
    (x : ℂ) {u : ℂ} (hu : ‖u‖ = 1)
    (outerColors : ∀ a : Bool, ∃ b : Bool, ∀ i, c (place x u (outer b i)) = a)
    (innerMixed : mixed (fun i => c (place x u (inner i)))) :
    bit (c x) + bit (c (place x u (inner 0))) + bit (c (place x u (inner 1))) +
    bit (c (place x u (inner 2))) = 2 := by
  apply tally (c x) _ innerMixed
  intro i j hij ei ej
  obtain ⟨b, hb⟩ := outerColors (c x)
  apply avoid
  refine ⟨_, two_circles x hu b hij, ?_⟩
  intro k
  fin_cases k <;> simpa [pattern, place] using
    (by first | exact rfl | exact hb i | exact ei | exact ej | exact hb j :
      _)

theorem two_equal : ∀ f : Fin 3 → Bool, ∃ i j, i ≠ j ∧ f i = f j := by
  intro f
  by_cases h : f 0 = f 1
  · exact ⟨0,1, by decide,h⟩
  by_cases h' : f 0 = f 2
  · exact ⟨0,2, by decide,h'⟩
  exact ⟨1,2,by decide, by cases ea : f 0 <;> cases eb : f 1 <;> cases ec : f 2 <;> simp_all⟩

/-- Four vertices have one color; the center has no prescribed color. -/
theorem angular_four (c : ℂ → Bool) (x : ℂ) {u : ℂ} (hu : ‖u‖ = 1)
    (outerColors : ∀ a : Bool, ∃ b : Bool, ∀ i, c (place x u (outer b i)) = a) :
    ∃ p : Fin 5 → ℂ, Pentagon p ∧ p 0 = x ∧ ∃ a, ∀ i : Fin 5, i ≠ 0 → c (p i) = a := by
  obtain ⟨i,j,hij,eqij⟩ := two_equal (fun k => c (place x u (inner k)))
  obtain ⟨b,hb⟩ := outerColors (c (place x u (inner j)))
  refine ⟨_,two_circles x hu b hij, by simp [pattern, place], c (place x u (inner j)), ?_⟩
  intro k hk
  fin_cases k
  · exact (hk rfl).elim
  · exact hb _
  · exact eqij
  · rfl
  · exact hb _

end C5

end
