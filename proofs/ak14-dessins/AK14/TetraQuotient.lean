import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! A homogeneous, explicit tetrahedral quotient. The fiber identity holds at all
projective points, including infinity and ramification points. -/
namespace AK14.TetraQuotient

variable {K : Type*} [Field K] [CharZero K]

abbrev Pair (K : Type*) := K × K

def bracket (P Q : Pair K) : K := P.1*Q.2-P.2*Q.1

def valid (P : Pair K) : Prop := P.1 ≠ 0 ∨ P.2 ≠ 0

def quartic (s : K) (P : Pair K) : K := P.1^4 + 2*s*P.1^2*P.2^2 + P.2^4

def qmap (s : K) (P : Pair K) : Pair K :=
  ((quartic s P)^3-(quartic (-s) P)^3, (quartic s P)^3)

def negation (P : Pair K) : Pair K := (-P.1,P.2)
def reciprocal (P : Pair K) : Pair K := (P.2,P.1)
def turn (i : K) (P : Pair K) : Pair K := (P.1+i*P.2,P.1-i*P.2)
def turnTwice (i : K) (P : Pair K) : Pair K := (i*(P.1+P.2),P.1-P.2)

def fourFactor (P R : Pair K) : K :=
  bracket P R * bracket (negation P) R * bracket (reciprocal P) R *
    bracket (negation (reciprocal P)) R

def kleinRelated (P R : Pair K) : Prop :=
  bracket P R = 0 ∨ bracket (negation P) R = 0 ∨ bracket (reciprocal P) R = 0 ∨
    bracket (negation (reciprocal P)) R = 0

def tetraRelated (i : K) (P R : Pair K) : Prop :=
  kleinRelated P R ∨ kleinRelated (turn i P) R ∨ kleinRelated (turnTwice i P) R

theorem fourFactor_eq_zero (P R : Pair K) : fourFactor P R = 0 ↔ kleinRelated P R := by
  simp only [fourFactor,kleinRelated,mul_eq_zero,or_assoc]

theorem quartic_difference {s : K} (hs : s^2 = -3) (P : Pair K) :
    (qmap s P).1 = 12*s*P.1^2*P.2^2*(P.1^4-P.2^4)^2 := by
  dsimp [qmap,quartic]
  linear_combination 16*s*P.1^6*P.2^6*hs

theorem qmap_valid {s : K} (hs : s^2 = -3) {P : Pair K} (hP : valid P) :
    valid (qmap s P) := by
  have sn : s ≠ 0 := by intro h; norm_num [h] at hs
  by_contra hn
  simp only [valid,not_or,not_not,qmap] at hn
  have hp : quartic s P = 0 := eq_zero_of_pow_eq_zero hn.2
  have hm : quartic (-s) P = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 3)
    simpa [hp] using hn.1
  have z : 4*s*P.1^2*P.2^2=0 := by
    dsimp [quartic] at hp hm
    linear_combination hp - hm
  rcases mul_eq_zero.mp z with h | h
  · have u : P.1 = 0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) sn))
    have v : P.2 = 0 := by simpa [quartic,u] using hp
    exact hP.elim (fun h => h u) (fun h => h v)
  · have v := eq_zero_of_pow_eq_zero h
    have u : P.1 = 0 := by simpa [quartic,v] using hp
    exact hP.elim (fun h => h u) (fun h => h v)

theorem qmap_scale (s a : K) (P : Pair K) :
    qmap s (a*P.1,a*P.2) = (a^12*(qmap s P).1,a^12*(qmap s P).2) := by
  apply Prod.ext <;> dsimp [qmap,quartic] <;> ring

set_option maxHeartbeats 3000000 in
theorem fiber_factorization {i s : K} (hi : i^2 = -1) (hs : s^2 = -3) (P R : Pair K) :
    bracket (qmap s P) (qmap s R) =
      -12*s * fourFactor P R * fourFactor (turn i P) R * fourFactor (turnTwice i P) R := by
  obtain ⟨u,v⟩ := P
  obtain ⟨r,t⟩ := R
  have i3 : i^3 = (-1 : K)*i := by
    calc i^3 = (i^2)^1*i^1 := by ring
         _ = _ := by rw [hi]; ring
  have i4 : i^4 = (1 : K) := by
    calc i^4 = (i^2)^2*i^0 := by ring
         _ = _ := by rw [hi]; ring
  have i5 : i^5 = (1 : K)*i := by
    calc i^5 = (i^2)^2*i^1 := by ring
         _ = _ := by rw [hi]; ring
  have i6 : i^6 = (-1 : K) := by
    calc i^6 = (i^2)^3*i^0 := by ring
         _ = _ := by rw [hi]; ring
  have i7 : i^7 = (-1 : K)*i := by
    calc i^7 = (i^2)^3*i^1 := by ring
         _ = _ := by rw [hi]; ring
  have i8 : i^8 = (1 : K) := by
    calc i^8 = (i^2)^4*i^0 := by ring
         _ = _ := by rw [hi]; ring
  have s3 : s^3 = (-3 : K)*s := by
    calc s^3 = (s^2)^1*s^1 := by ring
         _ = _ := by rw [hs]; ring
  have s4 : s^4 = (9 : K) := by
    calc s^4 = (s^2)^2*s^0 := by ring
         _ = _ := by rw [hs]; ring
  have s5 : s^5 = (9 : K)*s := by
    calc s^5 = (s^2)^2*s^1 := by ring
         _ = _ := by rw [hs]; ring
  have s6 : s^6 = (-27 : K) := by
    calc s^6 = (s^2)^3*s^0 := by ring
         _ = _ := by rw [hs]; ring
  have s7 : s^7 = (-27 : K)*s := by
    calc s^7 = (s^2)^3*s^1 := by ring
         _ = _ := by rw [hs]; ring
  have s8 : s^8 = (81 : K) := by
    calc s^8 = (s^2)^4*s^0 := by ring
         _ = _ := by rw [hs]; ring
  dsimp [bracket,qmap,quartic,fourFactor,negation,reciprocal,turn,turnTwice]
  set_option maxRecDepth 8000 in
    ring_nf
  simp only [hi,hs,i3,i4,i5,i6,i7,i8,s3,s4,s5,s6,s7,s8]
  ring

/-- Equality of the projective quotient values is exactly membership in the explicit
list of twelve tetrahedral images. No generic-position restriction is imposed. -/
theorem fibers {i s : K} (hi : i^2 = -1) (hs : s^2 = -3) (P R : Pair K) :
    bracket (qmap s P) (qmap s R) = 0 ↔ tetraRelated i P R := by
  have sn : s ≠ 0 := by intro h; norm_num [h] at hs
  rw [fiber_factorization hi hs]
  simp [tetraRelated,mul_eq_zero,or_assoc,fourFactor_eq_zero,sn]

end AK14.TetraQuotient
