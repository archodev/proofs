import AK14.WeightedPassport
import AK14.BranchDivisor
import AK14.Descent

namespace AK14.Gluing
open Equiv
open scoped Classical
noncomputable section

private theorem peel {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) (a : ℕ) (m : Multiset ℕ)
    (eq : s.val.map f=a::ₘ m) :
    ∃ x∈s, f x=a ∧ (s.erase x).val.map f=m := by
  have mem : a∈s.val.map f := eq ▸ Multiset.mem_cons_self _ _
  obtain ⟨x,hx,hf⟩ := Multiset.mem_map.mp mem
  refine ⟨x,hx,hf,?_⟩
  apply (Multiset.cons_inj_right a).mp
  rw [←eq,←hf,←Multiset.map_cons]; congr 1
  exact Multiset.cons_erase hx

private theorem rest {α : Type*} {s : Finset α} {f : α → ℕ} {d k : ℕ}
    (eq : s.val.map f=Multiset.replicate k d) {y : α} (hy : y∈s) : f y=d :=
  (Multiset.mem_replicate.mp (eq ▸ Multiset.mem_map_of_mem f hy)).2

structure Marking {n : ℕ} (T : Triple n) (p : Passport) where
  A : CornerSite T
  B : CornerSite T
  C : CornerSite T
  rowA : A.1=0
  rowB : B.1=p.bSlot
  rowC : C.1=2
  degreeA : classDegree (T A.1) A.2=p.a
  degreeB : classDegree (T B.1) B.2=p.b
  degreeC : classDegree (T C.1) C.2=p.c
  ab : A≠B
  bc : B≠C
  ca : C≠A
  others : ∀ s : CornerSite T, s≠A → s≠B → s≠C →
    classDegree (T s.1) s.2=branchOrder s.1

theorem marking_exists {n : ℕ} {T : Triple n} {p : Passport} (ht : Realizes p T) : Nonempty (Marking T p) := by
  have D := realized_corner_degrees ht
  have row0 : Finset.univ.val.map (classDegree (T 0))=p.a::ₘ Multiset.replicate p.r 2 := by
    rw [D]; cases hf : p.family <;> simp [Passport.rows,hf,Multiset.cons_add,←Multiset.singleton_add,add_comm]
  obtain ⟨a,_,da,othera⟩ := peel _ _ _ _ row0
  cases hf : p.family with
  | split =>
    have row1 : Finset.univ.val.map (classDegree (T 1))=p.b::ₘ Multiset.replicate p.s 3 := by
      rw [D]; simp [Passport.rows,hf,←Multiset.singleton_add,Multiset.insert_eq_cons,add_comm,add_left_comm,add_assoc]
    have row2 : Finset.univ.val.map (classDegree (T 2))=p.c::ₘ Multiset.replicate p.t 3 := by
      rw [D]; simp [Passport.rows,hf,←Multiset.singleton_add,Multiset.insert_eq_cons,add_comm,add_left_comm,add_assoc]
    obtain ⟨b,_,db,otherb⟩ := peel _ _ _ _ row1
    obtain ⟨c,_,dc,otherc⟩ := peel _ _ _ _ row2
    refine ⟨⟨⟨0,a⟩,⟨1,b⟩,⟨2,c⟩,rfl,by simp [Passport.bSlot,hf],rfl,da,db,dc,
      fun h => (by decide : (0:Fin 3)≠1) (congrArg Sigma.fst h),
      fun h => (by decide : (1:Fin 3)≠2) (congrArg Sigma.fst h),
      fun h => (by decide : (2:Fin 3)≠0) (congrArg Sigma.fst h),?_⟩⟩
    rintro ⟨j,y⟩ na nb nc
    fin_cases j
    · exact rest othera (Finset.mem_erase.mpr ⟨fun e => na (Sigma.ext rfl (heq_of_eq e)),Finset.mem_univ _⟩)
    · exact rest otherb (Finset.mem_erase.mpr ⟨fun e => nb (Sigma.ext rfl (heq_of_eq e)),Finset.mem_univ _⟩)
    · exact rest otherc (Finset.mem_erase.mpr ⟨fun e => nc (Sigma.ext rfl (heq_of_eq e)),Finset.mem_univ _⟩)
  | together =>
    have row1 : Finset.univ.val.map (classDegree (T 1))=Multiset.replicate p.s 3 := by rw [D]; simp [Passport.rows,hf]
    have row2 : Finset.univ.val.map (classDegree (T 2))=p.b::ₘ p.c::ₘ Multiset.replicate p.t 3 := by
      rw [D]; simp [Passport.rows,hf,←Multiset.singleton_add,Multiset.insert_eq_cons,add_comm,add_left_comm,add_assoc]
    obtain ⟨b,_,db,tail⟩ := peel _ _ _ _ row2
    obtain ⟨c,hc,dc,other⟩ := peel _ _ _ _ tail
    have cb := (Finset.mem_erase.mp hc).1
    refine ⟨⟨⟨0,a⟩,⟨2,b⟩,⟨2,c⟩,rfl,by simp [Passport.bSlot,hf],rfl,da,db,dc,
      fun h => (by decide : (0:Fin 3)≠2) (congrArg Sigma.fst h),
      fun h => cb (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm,
      fun h => (by decide : (2:Fin 3)≠0) (congrArg Sigma.fst h),?_⟩⟩
    rintro ⟨j,y⟩ na nb nc
    fin_cases j
    · exact rest othera (Finset.mem_erase.mpr ⟨fun e => na (Sigma.ext rfl (heq_of_eq e)),Finset.mem_univ _⟩)
    · exact rest row1 (Finset.mem_univ _)
    · exact rest other (Finset.mem_erase.mpr ⟨fun e => nc (Sigma.ext rfl (heq_of_eq e)),
        Finset.mem_erase.mpr ⟨fun e => nb (Sigma.ext rfl (heq_of_eq e)),Finset.mem_univ _⟩⟩)

end
end AK14.Gluing
