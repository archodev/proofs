import AK14.Uniformization
import AK14.ParameterNormalization

namespace AK14

/-- Every two realizations of one admissible passport, in either of the two
families and in arbitrary degree, are simultaneously conjugate. -/
theorem tetrahedral_dessin_uniqueness : OrientedUniqueness :=
  oriented_uniqueness_of_unmarked_uniformization Gluing.full_glued_uniformization

/-- Expanded public statement with each ordered cycle type, transitivity and
the conjugating sheet bijection shown explicitly. -/
theorem oriented_triples_conjugate (p : Passport) (n : ℕ) (hp : p.Admissible n)
    (T U : Fin 3 → Equiv.Perm (Fin n))
    (pT : T 0*T 1*T 2=1) (tT : Transitive T) (cT : ∀ i, fullType (T i)=p.rows i)
    (pU : U 0*U 1*U 2=1) (tU : Transitive U) (cU : ∀ i, fullType (U i)=p.rows i) :
    ∃ q : Equiv.Perm (Fin n), ∀ i : Fin 3, U i=q*T i*q⁻¹ :=
  tetrahedral_dessin_uniqueness p n hp T U ⟨pT,tT,cT⟩ ⟨pU,tU,cU⟩

/-- There is exactly one oriented isomorphism class for each realized
passport, with no uniformization or rational-model assumption. -/
theorem exactly_one_for_realized_passport {p : Passport} {n : ℕ} (hp : p.Admissible n)
    (existsTriple : ∃ T : Triple n, Realizes p T) :
    ∃ T : Triple n, Realizes p T ∧ ∀ U : Triple n, Realizes p U → SameDessin T U := by
  obtain ⟨T,hT⟩ := existsTriple
  exact ⟨T,hT,fun U hU => tetrahedral_dessin_uniqueness p n hp T U hT hU⟩

/-- Existence is the separate mathematical assertion of Adrianov–Kreines,
Theorem 1.3. Combining it with the checked uniqueness gives exactly one class. -/
theorem tetrahedral_exactly_one (existence : Theorem13Existence) : Conjecture14 :=
  conjecture14_iff_existence_and_uniqueness.mpr ⟨existence,tetrahedral_dessin_uniqueness⟩

end AK14

