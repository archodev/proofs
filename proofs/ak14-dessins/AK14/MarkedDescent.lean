import AK14.QuotientSphere
import Mathlib.Tactic.ComputeDegree

/-! A Möbius transformation preserving one order-three fiber fixes the tetrahedral
quotient. The Hessian of one tetrahedral quartic gives the other. -/
namespace AK14.TetraQuotient
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

structure Matrix2 (K : Type*) where
  a : K
  b : K
  c : K
  d : K

def Matrix2.det (m : Matrix2 K) := m.a*m.d-m.b*m.c
def Matrix2.act (m : Matrix2 K) (P : Pair K) : Pair K :=
  (m.a*P.1+m.b*P.2,m.c*P.1+m.d*P.2)

def transformed (s : K) (m : Matrix2 K) : K[X] :=
  let u := C m.a*X+C m.b
  let v := C m.c*X+C m.d
  u^4+2*C s*u^2*v^2+v^4

def hessian (p : K[X]) : K[X] := 12*p*p.derivative.derivative-9*p.derivative^2

private theorem binary_identity {R : Type*} [CommRing R] (s u v a c : R) :
    12*(u^4+2*s*u^2*v^2+v^4)*
        (12*u^2*a^2+4*s*(a^2*v^2+4*u*a*v*c+u^2*c^2)+12*v^2*c^2) -
      9*(4*u^3*a+4*s*(u*a*v^2+u^2*v*c)+4*v^3*c)^2 =
    (u*c-v*a)^2*(48*s*(u^4+v^4)+(144-48*s^2)*u^2*v^2) := by ring

theorem hessian_transform {s : K} (hs : s^2= -3) (m : Matrix2 K) :
    hessian (transformed s m)=C (48*s*m.det^2)*transformed (-s) m := by
  let u := C m.a*X+C m.b
  let v := C m.c*X+C m.d
  let a := C m.a
  let c := C m.c
  have du : u.derivative=a := by simp [u,a,derivative_mul]
  have dv : v.derivative=c := by simp [v,c,derivative_mul]
  have da : a.derivative=0 := derivative_C
  have dc : c.derivative=0 := derivative_C
  have d1 : (transformed s m).derivative =
      4*u^3*a+4*C s*(u*a*v^2+u^2*v*c)+4*v^3*c := by
    change derivative (u^4+2*C s*u^2*v^2+v^4)=_
    simp only [derivative_add,derivative_mul,derivative_pow,derivative_C,derivative_ofNat,du,dv]
    norm_num
    simp only [map_ofNat (C : K →+* K[X])]
    ring
  have d2 : (transformed s m).derivative.derivative =
      12*u^2*a^2+4*C s*(a^2*v^2+4*u*a*v*c+u^2*c^2)+12*v^2*c^2 := by
    rw [d1]
    simp only [derivative_add,derivative_mul,derivative_pow,derivative_C,derivative_ofNat,du,dv,da,dc]
    norm_num
    simp only [map_ofNat (C : K →+* K[X])]
    ring
  have det : u*c-v*a= -C m.det := by dsimp [u,v,c,a,Matrix2.det]; simp only [map_sub,map_mul]; ring
  have es : (C s)^2 = (-3:K[X]) := by rw [← map_pow,hs,map_neg,map_ofNat]
  rw [hessian,d2,d1]
  change 12*(u^4+2*C s*u^2*v^2+v^4)*_ - 9*_ = _
  rw [binary_identity,det,es]
  change _ = C (48*s*m.det^2)*(u^4+2*C (-s)*u^2*v^2+v^4)
  simp only [map_mul,map_pow,map_ofNat,map_neg]
  linear_combination (norm := ring) 96*(C m.det)^2*u^2*v^2*es

theorem hessian_quart {s : K} (hs : s^2= -3) : hessian (quart s)=C (48*s)*quart (-s) := by
  let m : Matrix2 K := ⟨1,0,0,1⟩
  have idt (v : K) : transformed v m=quart v := by simp [transformed,quart,m,map_ofNat (C : K →+* K[X])] <;> ring
  have e := hessian_transform hs m
  rw [idt,idt] at e
  simpa [Matrix2.det,m] using e

theorem hessian_scale (s : K) (p : K[X]) : hessian (C s*p) = C (s^2)*hessian p := by
  simp [hessian,derivative_mul]; ring

theorem transformed_degree_le (s : K) (m : Matrix2 K) : (transformed s m).natDegree ≤ 4 := by
  dsimp only [transformed]
  compute_degree!

theorem eval_transformed (s x : K) (m : Matrix2 K) :
    (transformed s m).eval x=quartic s (m.act (x,1)) := by simp [transformed,quartic,Matrix2.act]

theorem scalar_of_preserves_roots [IsAlgClosed K] {s : K} (hs : s^2= -3) (m : Matrix2 K)
    (roots : ∀ x : K, quartic s (x,1)=0 → quartic s (m.act (x,1))=0) :
    ∃ scale : K, transformed s m=C scale*quart s := by
  classical
  by_cases hn : transformed s m=0
  · exact ⟨0,by simp [hn]⟩
  have div : quart s ∣ transformed s m := by
    have sp : (quart s).Splits := IsAlgClosed.splits _
    apply sp.dvd_of_roots_le_roots (quart_ne_zero s)
    apply Multiset.le_iff_count.mpr
    intro x
    rw [count_roots,count_roots]
    by_cases h : (quart s).IsRoot x
    · rw [quart_simple hs h]
      apply (rootMultiplicity_pos hn).mpr
      rw [IsRoot.def,eval_transformed]
      exact roots x (by simpa [IsRoot.def] using h)
    · simp [rootMultiplicity_eq_zero h]
  obtain ⟨p,ep⟩ := div
  have pn : p ≠ 0 := fun h => hn (by rw [ep,h,mul_zero])
  have hd := transformed_degree_le s m
  rw [ep,natDegree_mul (quart_ne_zero s) pn,degree_quart] at hd
  exact ⟨p.coeff 0,by conv_lhs => rw [ep,eq_C_of_natDegree_eq_zero (by omega : p.natDegree=0)]
                      rw [mul_comm]⟩

private theorem conjugate_scalar {s scale : K} (hs : s^2= -3) {m : Matrix2 K}
    (h : transformed s m=C scale*quart s) :
    C (m.det^2)*transformed (-s) m = C (scale^2)*quart (-s) := by
  have sn : s ≠ 0 := by intro z; norm_num [z] at hs
  have nz : C (48*s) ≠ 0 := C_ne_zero.mpr (mul_ne_zero (by norm_num) sn)
  apply mul_left_cancel₀ nz
  have e := congrArg hessian h
  rw [hessian_transform hs,hessian_scale,hessian_quart hs] at e
  rw [map_mul (C : K →+* K[X]) (48*s) (m.det^2)] at e
  linear_combination e

/-- A transformation carrying one four-point branch fiber into itself preserves
the quotient as a rational function. The target order-three swap is eliminated. -/
theorem marked_quartic_fixes_quotient [IsAlgClosed K] {s : K} (hs : s^2= -3)
    (m : Matrix2 K) (nd : m.det ≠ 0)
    (roots : ∀ x : K, quartic s (x,1)=0 → quartic s (m.act (x,1))=0) (x : K) :
    bracket (qmap s (m.act (x,1))) (qmap s (x,1))=0 := by
  obtain ⟨a,ha⟩ := scalar_of_preserves_roots hs m roots
  let b := a^2/m.det^2
  have d2 : m.det^2 ≠ 0 := pow_ne_zero _ nd
  have ba : b*m.det^2=a^2 := div_mul_cancel₀ _ d2
  have hb : transformed (-s) m=C b*quart (-s) := by
    apply mul_left_cancel₀ (C_ne_zero.mpr d2)
    rw [conjugate_scalar hs ha,← mul_assoc,← map_mul,mul_comm (m.det^2) b,ba]
  have hs' : (-s)^2= -3 := by simpa using hs
  have h2 := conjugate_scalar hs' hb
  rw [neg_neg,ha] at h2
  have eq : m.det^2*a=b^2 := by
    apply C_injective (R := K)
    apply mul_right_cancel₀ (quart_ne_zero s)
    rw [map_mul,mul_assoc]
    exact h2
  have cube : b^3=a^3 := by
    calc b^3 = b*b^2 := by ring
         _ = (b*m.det^2)*a := by rw [← eq]; ring
         _ = _ := by rw [ba]; ring
  have u := congrArg (fun P : K[X] => P.eval x) ha
  have v := congrArg (fun P : K[X] => P.eval x) hb
  simp only [eval_transformed,eval_mul,eval_C,eval_quart] at u v
  unfold bracket qmap
  dsimp only
  rw [u,v,mul_pow,mul_pow,cube]
  ring

end
end AK14.TetraQuotient
