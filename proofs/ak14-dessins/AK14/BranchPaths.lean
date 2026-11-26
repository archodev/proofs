import AK14.LoopData
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.PathConnected

/-! Oriented path monodromy for a normalized rational map. Branch cycles are
defined by actual continuous lifts of the same ordered, directed base loops. -/
namespace AK14.SeriesAt
open Filter Topology
open scoped unitInterval
noncomputable section
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]

theorem locally_injective_at_good {p : Passport} {f : RatFunc K} (hf : NormalizedCover p f)
    {x : K} (hx : GoodPoint f x) : ∃ U : Set K, IsOpen U ∧ x∈U ∧ U.InjOn (affineValue f) := by
  have D := (f.num.hasStrictDerivAt x).div (f.denom.hasStrictDerivAt x) hx.1
  have E := D.hasStrictFDerivAt_equiv (good_deriv_ne hf hx)
  let H := E.toOpenPartialHomeomorph (affineValue f)
  exact ⟨H.source,H.open_source,E.mem_toOpenPartialHomeomorph_source,H.injOn⟩

/-- Equality of genuine path lifts follows from local injectivity and connectedness
of the parameter interval. -/
theorem rational_lift_unique {p : Passport} {f : RatFunc K} (hf : NormalizedCover p f)
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {γ : A → K} (avoid : ∀ t, γ t≠0 ∧ γ t≠1)
    (u v : C(A,K)) (eu : ∀ t, (fiberPoly f (γ t)).IsRoot (u t))
    (ev : ∀ t, (fiberPoly f (γ t)).IsRoot (v t)) (a : A) (ea : u a=v a) : u=v := by
  let S := {t : A | u t=v t}
  have cl : IsClosed S := isClosed_eq u.continuous v.continuous
  have op : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have ut := fiber_roots.mp (eu t)
    have good : GoodPoint f (u t) := ⟨ut.1,ut.2 ▸ (avoid t).1,ut.2 ▸ (avoid t).2⟩
    obtain ⟨U,oU,uU,inj⟩ := locally_injective_at_good hf good
    have ru : ∀ᶠ k in 𝓝 t, u k ∈ U := u.continuous.continuousAt (oU.mem_nhds uU)
    have vU : v t∈U := (show u t=v t from ht) ▸ uU
    have rv : ∀ᶠ k in 𝓝 t, v k ∈ U := v.continuous.continuousAt (oU.mem_nhds vU)
    filter_upwards [ru,rv] with k uk vk
    exact inj uk vk ((fiber_roots.mp (eu k)).2.trans (fiber_roots.mp (ev k)).2.symm)
  have all := IsClopen.eq_univ (show IsClopen S from ⟨cl,op⟩) ⟨a,ea⟩
  exact ContinuousMap.ext fun k => (show k ∈ S by rw [all]; trivial)

theorem carries_same_dessin {p : Passport} {n : ℕ} {f : RatFunc K} (hf : NormalizedCover p f)
    {loops : LoopSystem K} {T U : Triple n} (hT : Carries f loops T) (hU : Carries f loops U) :
    SameDessin T U := by
  obtain ⟨t,A⟩ := hT
  obtain ⟨u,B⟩ := hU
  let q := t.trans u.symm
  have reorder (i : Fin n) : u (q i)=t i := u.apply_symm_apply _
  have eq (j : Fin 3) (i : Fin n) : q (T j i)=U j (q i) := by
    obtain ⟨l,ls,le,lift⟩ := A j i
    obtain ⟨r,rs,re,rift⟩ := B j (q i)
    have same := rational_lift_unique hf (loops.avoid j) l r lift rift 0 (by rw [ls,rs,reorder])
    apply u.injective
    rw [reorder]
    apply Subtype.ext
    exact le.symm.trans ((congrArg (fun x : C(I,K) => x 1) same).trans re)
  refine ⟨q,fun j => Equiv.ext fun i => ?_⟩
  have e := eq j (q.symm i)
  change U j i=q (T j (q.symm i))
  simpa only [q.apply_symm_apply] using e.symm

theorem carries_of_same_dessin {n : ℕ} {f : RatFunc K} {loops : LoopSystem K} {T U : Triple n}
    (h : Carries f loops T) (eq : SameDessin T U) : Carries f loops U := by
  obtain ⟨t,A⟩ := h
  obtain ⟨q,b⟩ := eq
  refine ⟨q.symm.trans t,?_⟩
  intro j i
  obtain ⟨l,s,e,L⟩ := A j (q.symm i)
  refine ⟨l,s,?_,L⟩
  simpa [b j] using e

/-- For any two genuine rational realizations of the same normalized passport,
their ordered path permutation triples are simultaneously conjugate. -/
theorem normalized_branch_cycles_unique [IsAlgClosed K] {p : Passport} {n : ℕ}
    (hp : p.Admissible n) {f g : RatFunc K} (hf : NormalizedCover p f) (hg : NormalizedCover p g)
    (loops : LoopSystem K) {T U : Triple n} (hT : Carries f loops T) (hU : Carries g loops U) :
    SameDessin T U := by
  obtain rfl := normalized_rational_unique hp hf hg
  exact carries_same_dessin hf hT hU

end
end AK14.SeriesAt
