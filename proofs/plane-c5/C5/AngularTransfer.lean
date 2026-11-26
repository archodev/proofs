module
public import C5.Rooted
public import C5.Prism

@[expose] public section
namespace C5.Model
noncomputable section
open MeasureTheory Filter Topology Set OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor

def matchWeight (b : Bool) (z : ℂ) : ℝ := if b then z.re else 1-z.re
def angularSet (b : Bool) : Set (Bool × Fin 3 → ℂ) := {f |
  (∑ i, matchWeight b (f (true,i))) + 3*(∑ i, matchWeight b (f (false,i))) ≤ 10}
theorem angularSet_closed (b : Bool) : IsClosed (angularSet b) := by
  apply isClosed_le _ continuous_const
  cases b <;> simp [matchWeight,Fin.sum_univ_three] <;> fun_prop
theorem angularSet_convex (b : Bool) : Convex ℝ (angularSet b) := by
  intro f hf g hg a d ha hd had
  cases b <;> simp [angularSet,matchWeight,Fin.sum_univ_three,Complex.smul_re] at hf hg ⊢ <;>
    nlinarith only [mul_le_mul_of_nonneg_left hf ha,mul_le_mul_of_nonneg_left hg hd,had]

private def hitsBit (b a : Bool) : ℕ := if a=b then 1 else 0
private theorem bitWeight (b a : Bool) : matchWeight b (binary a) = (hitsBit b a:ℝ) := by
  cases a <;> cases b <;> norm_num [matchWeight,binary,hitsBit]

private theorem count_bound (b : Bool) (o z : Fin 3 → Bool)
    (h : ∀ i j, i≠j → o i=b → o j=b → z i=b → z j≠b) :
    (∑ i,hitsBit b (z i))+3*(∑ i,hitsBit b (o i)) ≤ 10 := by
  have cert : ∀ b a d e x y w : Bool,
      (∀ i j : Fin 3, i≠j → ![a,d,e] i=b → ![a,d,e] j=b → ![x,y,w] i=b → ![x,y,w] j≠b) →
      (hitsBit b x+hitsBit b y+hitsBit b w) + 3*(hitsBit b a+hitsBit b d+hitsBit b e) ≤ 10 := by decide
  have ho : (![o 0,o 1,o 2] : Fin 3 → Bool) = o := by funext i; fin_cases i <;> rfl
  have hz : (![z 0,z 1,z 2] : Fin 3 → Bool) = z := by funext i; fin_cases i <;> rfl
  rw [Fin.sum_univ_three,Fin.sum_univ_three]
  exact cert _ _ _ _ _ _ _ (by rwa [ho,hz])

variable [Carrier]

theorem omega_mem : omega ∈ E := by
  apply (Carrier.mem_iff _).mpr
  exact ⟨F.div_mem F.one_mem (by norm_num), F.div_mem (Carrier.sqrt_mem (by norm_num)) (by norm_num)⟩
theorem rho_mem : rho ∈ E := by
  apply (Carrier.mem_iff _).mpr
  exact ⟨F.div_mem (F.neg_mem (by norm_num)) (by norm_num), F.div_mem (Carrier.sqrt_mem (by norm_num)) (by norm_num)⟩
theorem rot_mem (i : Fin 3) : rot i ∈ E := by
  fin_cases i
  · exact E.one_mem
  · exact omega_sq ▸ E.pow_mem omega_mem 2
  · exact rot_sq ▸ E.pow_mem (omega_sq ▸ E.pow_mem omega_mem 2) 2
def omegaE : E := ⟨omega,omega_mem⟩
def rhoE : E := ⟨rho,rho_mem⟩
def rotE (i : Fin 3) : E := ⟨rot i,rot_mem i⟩
def outerE (b : Bool) (i : Fin 3) : E := rotE i * (if b then rhoE else 1)
def innerE (i : Fin 3) : E := rotE i * (1+rhoE)
@[simp] theorem coeOuter (b i) : (outerE b i:ℂ) = outer b i := by cases b <;> rfl
@[simp] theorem coeInner (i) : (innerE i:ℂ) = inner i := rfl

def offsets (s : Bool) (i : Bool × Fin 3) : E := if i.1 then innerE i.2 else outerE s i.2

theorem angular_projection (ω : Space templates) (x u : E) (hu : ‖(u:ℂ)‖=1) (s b : Bool) :
    ∀ᵐ η ∂measure templates ω, field templates ω (x:ℂ) η ≠ binary (!b) →
      (fun j => field templates ω ((x+u*offsets s j:E):ℂ) η) ∈ angularSet b := by
  apply rooted_rule ω (offsets s) _ b (angularSet_closed b) (angularSet_convex b) _ x u hu
  · rintro ⟨a,i⟩ e
    have eq := congrArg (fun z : E => Complex.normSq (z:ℂ)) e
    cases a <;> simp [offsets,outer_radius,inner_radius_sq] at eq
  · intro y v hv η hroot
    let o := fun i => η.val (y+v*outerE s i)
    let z := fun i => η.val (y+v*innerE i)
    have noboth : ∀ i j, i≠j → o i=b → o j=b → z i=b → z j≠b := by
      intro i j hij hoi hoj hzi hzj
      let p : Fin 5 → E := ![0,outerE s i,innerE i, innerE j,outerE s j]
      have hp : p ∈ templates := by
        change Pentagon (fun k => (p k:ℂ))
        have e : (fun k => (p k:ℂ)) = pattern s i j := by funext k; fin_cases k <;> simp [p,pattern]
        rw [e]; exact base_pentagon s hij
      let k : K := ⟨⟨(v:ℂ),mem_sphere_zero_iff_norm.mpr hv⟩,v.property⟩
      apply η.property p hp y k
      intro j'
      have e : kCoeff k = v := rfl
      rw [e]
      change η.val (y+v*p j') = η.val (y+v*0)
      rw [mul_zero,add_zero,hroot]
      fin_cases j' <;> first | simpa [p] using hroot | exact hoi | exact hzi | exact hzj | exact hoj
    change (∑ i, matchWeight b (binary (z i)))+3*(∑ i,matchWeight b (binary (o i))) ≤ 10
    simp only [bitWeight]
    exact_mod_cast count_bound b o z noboth

end
end C5.Model
end
