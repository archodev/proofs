import AK14.CycleDivisor
import Mathlib.Data.Fintype.Sum

namespace AK14.Gluing
open Equiv
open scoped Classical
noncomputable section

def labelDegree {n : ℕ} (g : Perm (Fin n)) : CornerLabels g → ℕ :=
  Sum.elim (fun _ => 1) (fun y => y.val.support.card)

theorem corner_label_degree {n : ℕ} (g : Perm (Fin n)) (c : Corners g) :
    labelDegree g (cornerEquiv g c)=classDegree g c := by
  induction c using Quotient.inductionOn with | _ x =>
    change labelDegree g (if h : g x=x then Sum.inl ⟨x,h⟩ else Sum.inr ⟨g.cycleOf x,_⟩)=classDegree g (cornerClass g x)
    split_ifs with h
    · exact (classDegree_fixed g h).symm
    · exact (classDegree_moving g h).symm

theorem weighted_passport {n : ℕ} (g : Perm (Fin n)) :
    Finset.univ.val.map (classDegree g)=fullType g := by
  have same : classDegree g=labelDegree g ∘ cornerEquiv g := funext fun x => (corner_label_degree g x).symm
  rw [same,←Multiset.map_map,Multiset.map_univ_val_equiv]
  change (Finset.univ.val.disjSum Finset.univ.val).map (labelDegree g)=_
  rw [Multiset.disjSum,Multiset.map_add,Multiset.map_map,Multiset.map_map]
  change Finset.univ.val.map (fun _ : Function.fixedPoints g => 1)+
    Finset.univ.val.map (fun y : ↥g.cycleFactorsFinset => y.val.support.card)=_
  have V : (Finset.univ : Finset ↥g.cycleFactorsFinset).val.map Subtype.val=g.cycleFactorsFinset.val := by
    simpa using Finset.univ_val_map_subtype_val (fun y => y∈g.cycleFactorsFinset)
  rw [←show Multiset.map (fun x : Perm (Fin n) => x.support.card) (Finset.univ.val.map (Subtype.val : ↥g.cycleFactorsFinset → _))=
      Finset.univ.val.map (fun y : ↥g.cycleFactorsFinset => y.val.support.card) by rw [Multiset.map_map]; rfl,V]
  rw [Multiset.map_const',show (Finset.univ : Finset (Function.fixedPoints g)).val.card=Fintype.card (Function.fixedPoints g) from rfl,
    fixedPointCount,add_comm]
  rfl

theorem realized_corner_degrees {n : ℕ} {p : Passport} {T : Triple n} (ht : Realizes p T) (j : Fin 3) :
    Finset.univ.val.map (classDegree (T j))=p.rows j := (weighted_passport _).trans (ht.cycles j)

end
end AK14.Gluing
