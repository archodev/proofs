import AK14.GluedComplexLoops

namespace AK14.Gluing
open Complex Set Topology
open scoped OnePoint unitInterval
open SeriesAt (basePoint circleZero circleOne circleInfinity standardLoops)
noncomputable section

private theorem base_edge_only (k : Fin 3) (zero : (location basePoint).val k=0) : k=0 := by
  have sub : basePoint-1= -(1/2:ℂ) := by unfold basePoint; ring
  fin_cases k
  · rfl
  · change (‖basePoint‖+1-‖basePoint-1‖)/perimeter basePoint=0 at zero
    rw [sub] at zero; norm_num [perimeter,sub,basePoint,norm_div] at zero
  · change (‖basePoint-1‖+1-‖basePoint‖)/perimeter basePoint=0 at zero
    rw [sub] at zero; norm_num [perimeter,sub,basePoint,norm_div] at zero

theorem base_projected {n : ℕ} (T : Triple n) (i : Fin n) : gluedMap T (loopSheet T i)=(basePoint : OnePoint ℂ) :=
  spherePoint_location (b:=true) (by norm_num [basePoint,sideSign])

theorem base_target : complexTarget (cell flatTriple (true,0) (location basePoint))=(basePoint : OnePoint ℂ) :=
  base_projected flatTriple 0

def labeledBase {n : ℕ} (T : Triple n) : Fin n ≃ {x : Surface T // gluedMap T x=(basePoint : OnePoint ℂ)} := by
  have zero : (location basePoint).val 0=0 := by
    change (‖basePoint‖+‖basePoint-1‖-1)/_=0
    rw [show basePoint-1= -(1/2:ℂ) by unfold basePoint; ring]
    norm_num [basePoint,norm_div]
  let e := edge_sheets T (location basePoint) 0 zero base_edge_only
  let F (i : Fin n) : {x : Surface T // gluedMap T x=(basePoint : OnePoint ℂ)} := ⟨loopSheet T i,base_projected T i⟩
  apply Equiv.ofBijective F
  constructor
  · intro i j h
    have val : (F i).val=(F j).val := congrArg Subtype.val h
    exact e.injective (Subtype.ext val)
  · rintro ⟨x,h⟩
    have proj : coveringProjection T x=cell flatTriple (true,0) (location basePoint) :=
      complexTarget.injective (h.trans base_target.symm)
    obtain ⟨i,hi⟩ := e.surjective ⟨x,proj⟩
    have val : (e i).val=x := congrArg Subtype.val hi
    exact ⟨i,Subtype.ext val⟩

theorem labeledBase_val {n : ℕ} (T : Triple n) (i : Fin n) : (labeledBase T i).val=loopSheet T i := rfl

private theorem prod_sheet {n : ℕ} (T : Triple n) (h : T 0*T 1*T 2=1) (i : Fin n) :
    T 0 (T 1 (T 2 i))=i := congrArg (fun g : Equiv.Perm (Fin n) => g i) h

def standardInfinityLift {n : ℕ} (T : Triple n) (h : T 0*T 1*T 2=1) (i : Fin n) :
    Path (loopSheet T i) (loopSheet T (T 2 i)) :=
  (((standardOneLift T (T 2 i)).trans (standardZeroLift T (T 1 (T 2 i)))).symm).cast
    (congrArg (loopSheet T) (prod_sheet T h i)).symm rfl

theorem infinityLift_projects {n : ℕ} (T : Triple n) (h : T 0*T 1*T 2=1) (i : Fin n) (t : I) :
    gluedMap T (standardInfinityLift T h i t)=(circleInfinity t : OnePoint ℂ) := by
  change gluedMap T (((standardOneLift T _).trans (standardZeroLift T _)) (unitInterval.symm t))=
    (((circleOne.trans circleZero) (unitInterval.symm t) : ℂ) : OnePoint ℂ)
  rw [Path.trans_apply,Path.trans_apply]
  split
  · exact oneLift_projects _ _ _
  · exact zeroLift_projects _ _ _

/-- Actual lifts of the named complex loops for every abstract product-one triple. -/
theorem glued_standard_realization {n : ℕ} (T : Triple n) (h : T 0*T 1*T 2=1) :
    ∃ lab : Fin n ≃ {x : Surface T // gluedMap T x=(basePoint : OnePoint ℂ)},
      ∀ (j : Fin 3) (i : Fin n), ∃ L : Path (lab i).val (lab (T j i)).val,
        ∀ t, gluedMap T (L t)=((standardLoops.loop j t : ℂ) : OnePoint ℂ) := by
  refine ⟨labeledBase T,?_⟩
  intro j i
  fin_cases j
  · exact ⟨standardZeroLift T i,zeroLift_projects T i⟩
  · exact ⟨standardOneLift T i,oneLift_projects T i⟩
  · exact ⟨standardInfinityLift T h i,infinityLift_projects T h i⟩

end
end AK14.Gluing
