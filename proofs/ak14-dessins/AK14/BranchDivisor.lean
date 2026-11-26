import AK14.GluedRiemannSurface
import AK14.CycleDivisor
import Mathlib.Data.Finsupp.Weight

namespace AK14.Gluing
open Equiv Set
open scoped BigOperators Classical
noncomputable section

abbrev CornerSite {n : ℕ} (T : Triple n) := (j : Fin 3) × Corners (T j)

def sitePoint {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (s : CornerSite T) : Surface T :=
  (geometric_corner_fiber T pr s.1 s.2).val

theorem sitePoint_mk {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (j : Fin 3) (x : Fin n) :
    sitePoint T pr ⟨j,cornerClass (T j) x⟩=cell T (true,x) (vertex j) := rfl

theorem vertex_injective : Function.Injective vertex := by
  intro j k eq
  have h : (vertex k).val (opposite j)=(1:ℝ) := by
    rw [←eq]; exact Pi.single_eq_same _ _
  have s : opposite j=opposite k := by
    by_contra ne; rw [show (vertex k).val (opposite j)=0 from Pi.single_eq_of_ne ne _] at h
    norm_num at h
  fin_cases j <;> fin_cases k <;> first | rfl | exact (by decide : ¬(_=_)) s | contradiction

theorem sitePoint_injective {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) :
    Function.Injective (sitePoint T pr) := by
  rintro ⟨j,c⟩ ⟨k,v⟩ eq
  have eq' := congrArg (fun u => barycentric flatTriple (coveringProjection T u)) eq
  have proj (l : Fin 3) (C : Corners (T l)) : coveringProjection T (sitePoint T pr ⟨l,C⟩)=cell flatTriple (true,0) (vertex l) :=
    (geometric_corner_fiber T pr l C).property
  dsimp only at eq'; rw [proj,proj] at eq'
  obtain rfl : j=k := vertex_injective eq'
  have c_eq : c=v := (geometric_corner_fiber T pr j).injective (Subtype.ext eq)
  subst v; rfl

def siteWeight {n : ℕ} (T : Triple n) (s : CornerSite T) : ℤ :=
  differentialWeight s.1 (classDegree (T s.1) s.2)

def branchDivisor {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) : Surface T →₀ ℤ :=
  ∑ i : CornerSite T, Finsupp.single (sitePoint T pr i) (siteWeight T i)

theorem divisor_at_site {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) (s : CornerSite T) :
    branchDivisor T pr (sitePoint T pr s)=siteWeight T s := by
  change (∑ i : CornerSite T, Finsupp.single (sitePoint T pr i) (siteWeight T i)) _=_
  rw [Finset.sum_apply',Finset.sum_eq_single s]
  · exact Finsupp.single_eq_same
  · intro b _ ne; exact Finsupp.single_eq_of_ne ((sitePoint_injective T pr).ne ne.symm)
  · simp

theorem divisor_at_regular {n : ℕ} (T : Triple n) (pr : T 0*T 1*T 2=1) {y : Surface T}
    (hy : coveringProjection T y∈awayFromCorners) : branchDivisor T pr y=0 := by
  change (∑ i : CornerSite T, Finsupp.single (sitePoint T pr i) (siteWeight T i)) y=0
  rw [Finset.sum_apply']; apply Finset.sum_eq_zero
  intro i _
  apply Finsupp.single_eq_of_ne
  intro eq
  exact (away_iff_avoids_vertices _).mp hy i.1 (eq ▸ (geometric_corner_fiber T pr i.1 i.2).property)

theorem branchDivisor_degree {p : Passport} {n : ℕ} (hp : p.Admissible n) {T : Triple n} (hT : Realizes p T) :
    (branchDivisor T hT.product).degree= -2 := by
  unfold branchDivisor
  rw [map_sum]
  simp only [Finsupp.degree_single]
  rw [Fintype.sum_sigma,Fin.sum_univ_three]
  exact total_differential_weight hp hT

end
end AK14.Gluing
