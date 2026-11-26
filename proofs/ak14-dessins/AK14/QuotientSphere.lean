import AK14.TetraQuotient
import AK14.Pullback
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-! A surjective projective-line quotient and its ramification, in explicit coordinates. -/
namespace AK14.TetraQuotient
open Polynomial
variable {K : Type*} [Field K] [CharZero K]
noncomputable section

def rep : Option K → Pair K
  | none => (1,0)
  | some z => (z,1)

def point (P : Pair K) : Option K := by
  classical
  exact if P.2=0 then none else some (P.1/P.2)

theorem rep_valid (z : Option K) : valid (rep z) := by cases z <;> simp [valid,rep]

theorem points_eq_iff {P R : Pair K} (hp : valid P) (hr : valid R) :
    point P=point R ↔ bracket P R=0 := by
  classical
  obtain ⟨a,b⟩ := P
  obtain ⟨c,d⟩ := R
  change a ≠ 0 ∨ b ≠ 0 at hp
  change c ≠ 0 ∨ d ≠ 0 at hr
  by_cases hb : b=0 <;> by_cases hd : d=0
  · simp [bracket,point,hb,hd]
  · have ha := hp.resolve_right (not_not.mpr hb)
    simp [bracket,point,hb,hd,ha]
  · have hc := hr.resolve_right (not_not.mpr hd)
    simp [bracket,point,hb,hd,hc]
  · simp [bracket,point,hb,hd,div_eq_div_iff hb hd,sub_eq_zero,mul_comm]

@[simp] theorem point_rep (z : Option K) : point (rep z)=z := by
  cases z <;> simp [point,rep]

def sphereMap (s : K) (z : Option K) : Option K := point (qmap s (rep z))

theorem sphereMap_fibers {s i : K} (hs : s^2= -3) (hi : i^2= -1) (x y : Option K) :
    sphereMap s x=sphereMap s y ↔ tetraRelated i (rep x) (rep y) :=
  (points_eq_iff (qmap_valid hs (rep_valid x)) (qmap_valid hs (rep_valid y))).trans (fibers hi hs _ _)

def quart (s : K) : K[X] := X^4+C (2*s)*X^2+1
def edgePoly (K : Type*) [Field K] : K[X] := X*(X^4-1)
def numerator (s : K) : K[X] := C (12*s)*(edgePoly K)^2

@[simp] theorem eval_quart (s x : K) : (quart s).eval x=quartic s (x,1) := by simp [quart,quartic]
@[simp] theorem eval_numerator {s : K} (hs : s^2= -3) (x : K) :
    (numerator s).eval x = (qmap s (x,1)).1 := by
  rw [quartic_difference hs]
  simp [numerator,edgePoly]
  ring

theorem degree_quart (s : K) : (quart s).natDegree=4 := by
  have small := natDegree_C_mul_le (2*s) ((X:K[X])^2)
  rw [natDegree_X_pow] at small
  have d : (X^4+C (2*s)*X^2).natDegree=4 := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow]; omega
  rw [quart,natDegree_add_eq_left_of_natDegree_lt,d]
  rw [natDegree_one,d]; decide

theorem quart_ne_zero (s : K) : quart s ≠ 0 :=
  fun e => by have h := degree_quart s; rw [e,natDegree_zero] at h; contradiction

theorem degree_edge : (edgePoly K).natDegree=5 := by
  have h : ((X:K[X])^4-1).natDegree=4 := by
    simpa using (natDegree_X_pow_sub_C (n := 4) (r := (1:K)))
  have hn : ((X:K[X])^4-1) ≠ 0 := fun e => by simp [e] at h
  rw [edgePoly,natDegree_mul X_ne_zero hn,natDegree_X,h]

theorem degree_numerator {s : K} (hs : s^2= -3) : (numerator s).natDegree=10 := by
  have sn : s ≠ 0 := by intro e; norm_num [e] at hs
  rw [numerator,natDegree_C_mul_of_isUnit (mul_ne_zero (by norm_num) sn).isUnit,
    natDegree_pow,degree_edge]

theorem sphereMap_surjective [IsAlgClosed K] {s : K} (hs : s^2= -3) :
    Function.Surjective (sphereMap s) := by
  intro y
  cases y with
  | none =>
    obtain ⟨x,hx⟩ := IsAlgClosed.exists_root (quart s) (by
      rw [degree_eq_natDegree (quart_ne_zero s),degree_quart]; decide)
    refine ⟨some x,?_⟩
    change (quart s).eval x=0 at hx
    rw [eval_quart] at hx
    simp [sphereMap,rep,point,qmap,hx]
  | some y =>
    by_cases hy : y=0
    · subst y
      exact ⟨none, by simp [sphereMap,point,rep,qmap,quartic]⟩
    let P := numerator s-C y*(quart s)^3
    have d : P.natDegree=12 := by
      have d12 : (C y*(quart s)^3).natDegree=12 := by
        rw [natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hy),natDegree_pow,degree_quart]
      rw [show P=numerator s-C y*(quart s)^3 from rfl,natDegree_sub_eq_right_of_natDegree_lt,d12]
      rw [degree_numerator hs,d12]; decide
    have pn : P ≠ 0 := fun e => by simp [e] at d
    obtain ⟨x,hx⟩ := IsAlgClosed.exists_root P (by rw [degree_eq_natDegree pn,d]; decide)
    refine ⟨some x,?_⟩
    rw [← point_rep (some y)]
    apply (points_eq_iff (qmap_valid hs (rep_valid (some x))) (rep_valid (some y))).mpr
    change P.eval x=0 at hx
    simpa [P,eval_numerator hs,rep,bracket,qmap,mul_comm] using hx

theorem quart_simple {s x : K} (hs : s^2= -3) (hx : (quart s).IsRoot x) :
    (quart s).rootMultiplicity x=1 := by
  have hpos := (rootMultiplicity_pos (quart_ne_zero s)).mpr hx
  by_contra h
  have more : 1 < (quart s).rootMultiplicity x := by omega
  have z := ((one_lt_rootMultiplicity_iff_isRoot (quart_ne_zero s)).mp more).2
  change (quart s).derivative.eval x=0 at z
  have der : (quart s).derivative.eval x = 4*x*(x^2+s) := by
    simp [quart,derivative_add,derivative_mul,derivative_pow] <;> ring
  rw [der] at z
  change (quart s).eval x=0 at hx
  simp [quart,quartic] at hx
  rcases mul_eq_zero.mp z with zero | zero
  · have e : x=0 := (mul_eq_zero.mp zero).resolve_left (by norm_num)
    simp [e] at hx
  · have e : x^2= -s := by linear_combination zero
    rw [show x^4=(x^2)^2 by ring,e] at hx
    have absurd : (4:K)=0 := by linear_combination hx+hs
    exact (by norm_num : (4:K)≠0) absurd

theorem edge_simple {x : K} (hx : (edgePoly K).IsRoot x) :
    (edgePoly K).rootMultiplicity x=1 := by
  have hn : edgePoly K ≠ 0 := fun e => by have d := degree_edge (K := K); simp [e] at d
  have hpos := (rootMultiplicity_pos hn).mpr hx
  by_contra h
  have more : 1 < (edgePoly K).rootMultiplicity x := by omega
  have z := ((one_lt_rootMultiplicity_iff_isRoot hn).mp more).2
  change (edgePoly K).derivative.eval x=0 at z
  have der : (edgePoly K).derivative.eval x=5*x^4-1 := by
    simp [edgePoly,derivative_mul,derivative_pow] <;> ring
  rw [der] at z
  change (edgePoly K).eval x=0 at hx
  have zz : x*(x^4-1)=0 := by simpa [edgePoly] using hx
  rcases mul_eq_zero.mp zz with x0 | x4
  · simp [x0] at z
  · have absurd : (4:K)=0 := by linear_combination z-5*x4
    exact (by norm_num : (4:K)≠0) absurd

end
end AK14.TetraQuotient
