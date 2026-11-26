import AK14.LocalKummer
import AK14.Pencil

/-! Local cubic branches centered at either of the two values +2 and -2 of the
quadratic intermediate coordinate. -/
namespace AK14.SeriesAt
open PowerSeries
open scoped PowerSeries
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def inverseContrast {R : Type*} [Field R] (s h : R) : R := 2*s*(1+h)/(1-h)

theorem cubic_center {s b : K} (hs : s^2= -3) (hb : b^2=4) :
    ∃ α : K, α^3=1 ∧ α≠0 ∧ α≠1 ∧ b+2*s≠0 ∧ (b+2*s)*α=b-2*s := by
  have sn : s ≠ 0 := by intro z; norm_num [z] at hs
  have nz : b+2*s ≠ 0 := by
    intro z
    have e : b= -2*s := by linear_combination z
    rw [e] at hb
    have bad : (16:K)=0 := by linear_combination 4*hs-hb
    norm_num at bad
  let α := (b-2*s)/(b+2*s)
  have A : α^3=1 := by
    dsimp only [α]
    rw [div_pow,div_eq_one_iff_eq (pow_ne_zero _ nz)]
    linear_combination -12*s*hb-16*s*hs
  have e : (b+2*s)*α=b-2*s := by dsimp only [α]; field_simp
  refine ⟨α,A,fun z => by simp [z] at A,?_,nz,e⟩
  intro z
  rw [z,mul_one] at e
  apply sn
  linear_combination (norm := ring) e/4

private theorem order_unit {P : K⟦X⟧} (h : constantCoeff (R := K) P≠0) : P.order=0 := by
  apply nonpos_iff_eq_zero.mp
  exact order_le 0 (by simpa only [coeff_zero_eq_constantCoeff] using h)

theorem cubic_local_branch [IsAlgClosed K] (P : K⟦X⟧) (np : P≠0)
    (cp : constantCoeff (R := K) P=0) {s b : K} (hs : s^2= -3) (hb : b^2=4) :
    ∃ H V : K⟦X⟧, H^3=1-P ∧ constantCoeff (R := K) V=0 ∧ V≠0 ∧ V.order.toNat=P.order.toNat ∧
      inverseContrast (constMap K s) (embed K H)=constMap K b+embed K V := by
  obtain ⟨α,cube,na,a1,ns,center⟩ := cubic_center hs hb
  obtain ⟨W,cW,nW⟩ := LocalChart.unit_root (1-P) (by simp [cp]) (by decide : 0<3)
  let c := constantCoeff (R := K) W
  have cw : c^3=1 := by simpa only [map_pow,map_sub,map_one,cp,sub_zero,c] using congrArg (constantCoeff (R := K)) cW
  let H := C (R := K) (α/c)*W
  have hH : H^3=1-P := by
    dsimp only [H]
    rw [mul_pow,← map_pow,div_pow,cw,cube,div_one,map_one,one_mul,cW]
  have hc : constantCoeff (R := K) H=α := by simp [H,c,nW]
  let Δ := H-C (R := K) α
  let S := -(H^2+H*C (R := K) α+(C (R := K) α)^2)
  have eq : P=Δ*S := by
    have ca : (C (R := K) α)^3=1 := by rw [← map_pow,cube,map_one]
    dsimp only [Δ,S]
    linear_combination hH-ca
  have su : constantCoeff (R := K) S≠0 := by
    simp only [S,map_neg,map_add,map_mul,map_pow,constantCoeff_C,hc,neg_ne_zero]
    have e : α^2+α*α+α^2=3*α^2 := by ring
    rw [e]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ na)
  have δn : Δ≠0 := fun zero => np (by rw [eq,zero,zero_mul])
  have ord : P.order=Δ.order := by conv_lhs => rw [eq,order_mul,order_unit su,add_zero]
  let J := (1-H)⁻¹
  have unitH : constantCoeff (R := K) (1-H)≠0 := by simpa [hc,sub_ne_zero] using a1.symm
  have inv : (1-H)*J=1 := PowerSeries.mul_inv_cancel _ unitH
  have cj : constantCoeff (R := K) J≠0 := by
    intro z
    have abs := congrArg (constantCoeff (R := K)) inv
    simp [z] at abs
  let U := C (R := K) (b+2*s)*J
  have u0 : constantCoeff (R := K) U≠0 := by simpa only [U,map_mul,constantCoeff_C] using mul_ne_zero ns cj
  let V := Δ*U
  have vc : constantCoeff (R := K) V=0 := by simp [V,Δ,hc]
  have vn : V≠0 := mul_ne_zero δn (fun z => u0 (by simp [z]))
  have vo : V.order=Δ.order := by rw [show V=Δ*U from rfl,order_mul,order_unit u0,add_zero]
  refine ⟨H,V,hH,vc,vn,congrArg ENat.toNat (vo.trans ord.symm),?_⟩
  let ρ := constMap K
  have je : embed K J=(1-embed K H)⁻¹ := by rw [show J=(1-H)⁻¹ from rfl,embed_unit_inv unitH,map_sub,map_one]
  have nh : 1-embed K H≠0 := by
    rw [← map_one (embed K),← map_sub]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)).mpr
      (fun z => unitH (by simp [z]))
  have cent := congrArg ρ center
  simp only [map_mul,map_add,map_sub,map_ofNat] at cent
  change inverseContrast (ρ s) (embed K H)=ρ b+embed K V
  rw [show V=Δ*(C (R := K) (b+2*s)*J) from rfl,map_mul (embed K) Δ _,map_mul (embed K) (C (R := K) (b+2*s)) J,je]
  change 2*ρ s*(1+embed K H)/(1-embed K H)=ρ b+(embed K (H-C (R := K) α))*(ρ (b+2*s)*(1-embed K H)⁻¹)
  rw [map_sub (embed K),map_add ρ,map_mul ρ,map_ofNat ρ]
  change _=ρ b+(embed K H-ρ α)*((ρ b+2*ρ s)*(1-embed K H)⁻¹)
  field_simp [nh]
  linear_combination cent

end
end AK14.SeriesAt
