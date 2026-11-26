import Std

/-!
# The odd maximal-genus diameter of the labelled polygon matching graph

Gross and Šarković, *Polynomial mixing for polygonal side matchings*,
arXiv:2607.02410, Section 2. Lean 4.19.0, using the standard distribution.

Main results: `labelled_graph_diameter_bound` and `no_joint_diameter_omega`
in the namespace `OddDiameter`. The executable finite certificates concern
only local configurations and the six-side base case.
-/


/-! ## Core -/

/-! Labelled orientable polygon matchings. The cycle counter contracts the
successive labels in the supplied enumeration. Contracting a fixed point
counts one completed cycle; otherwise it splices the label out of its cycle. -/
set_option grind.warning false
set_option linter.constructorNameAsVariable false
namespace OddDiameter

def Inj (p : α → α) := ∀ ⦃x y⦄, p x = p y → x = y

def exchange [DecidableEq α] (a b x : α) :=
  if x = a then b else if x = b then a else x

@[simp] theorem ex_twice [DecidableEq α] (a b x : α) :
    exchange a b (exchange a b x) = x := by
  unfold exchange
  split <;> split <;> simp_all <;> split <;> simp_all

theorem ex_inj [DecidableEq α] (a b : α) : Inj (exchange a b) := by
  intro x y h
  simpa using congrArg (exchange a b) h

structure Matching (α : Type) where
  mate : α → α
  inv : ∀ x, mate (mate x) = x
  free : ∀ x, mate x ≠ x

theorem Matching.inj (m : Matching α) : Inj m.mate := by
  intro x y h
  simpa only [m.inv] using congrArg m.mate h

def Matching.switch [DecidableEq α] (m : Matching α) (a b : α) : Matching α where
  mate x := exchange a b (m.mate (exchange a b x))
  inv x := by simp [m.inv]
  free x h := by
    apply m.free (exchange a b x)
    simpa using congrArg (exchange a b) h

def cut [DecidableEq α] (p : α → α) (a x : α) :=
  if x = a then a else if p x = a then p a else p x

def cycles [DecidableEq α] (p : α → α) : List α → Nat
  | [] => 0
  | a :: l => (if p a = a then 1 else 0) + cycles (cut p a) l

theorem cut_inj [DecidableEq α] {p : α → α} (hp : Inj p) (a : α) :
    Inj (cut p a) := by
  intro x y h
  unfold cut at h
  have h₁ := @hp x a
  have h₂ := @hp y a
  have h₃ := @hp x y
  grind

theorem cut_comm [DecidableEq α] {p : α → α} (hp : Inj p) (a b : α) :
    cut (cut p a) b = cut (cut p b) a := by
  funext x
  unfold cut
  have h₁ := @hp x a
  have h₂ := @hp x b
  grind

theorem cycles_perm [DecidableEq α] {l r : List α} (h : l.Perm r)
    {p : α → α} (hp : Inj p) : cycles p l = cycles p r := by
  induction h generalizing p with
  | nil => rfl
  | cons x _ ih => simp only [cycles, ih (cut_inj hp x)]
  | swap a b l =>
    simp only [cycles, cut_comm hp b a]
    unfold cut
    grind
  | trans _ _ ih₁ ih₂ => exact (ih₁ hp).trans (ih₂ hp)

def vertices [DecidableEq α] (s : α → α) (m : Matching α) (l : List α) :=
  cycles (fun x => s (m.mate x)) l

def successor {k : Nat} (x : Fin k) : Fin k :=
  ⟨(x.val + 1) % k, Nat.mod_lt _ (Nat.zero_lt_of_lt x.isLt)⟩

def sides (n : Nat) := List.finRange (2*n)

def AtGenus (n g : Nat) (m : Matching (Fin (2*n))) : Prop :=
  vertices successor m (sides n) + 2*g = n+1

def Legal [DecidableEq α] (s : α → α) (l : List α) (m q : Matching α) : Prop :=
  ∃ a b, a ≠ b ∧ m.mate a ≠ b ∧ q = m.switch a b ∧
    vertices s m l = vertices s q l

abbrev Edge (n : Nat) := Legal (@successor (2*n)) (sides n)

inductive Walk {α : Type} [DecidableEq α] (s : α → α) (l : List α) :
    Matching α → Matching α → Nat → Prop
  | nil (m) : Walk s l m m 0
  | cons : Legal s l m q → Walk s l q r k → Walk s l m r (k+1)

theorem odd_genus_iff {g : Nat} {m : Matching (Fin (2*(2*g+1)))} :
    AtGenus (2*g+1) g m ↔ vertices successor m (sides (2*g+1)) = 2 := by
  unfold AtGenus; omega


/-- Restrict cycle elimination along an injective renaming which intertwines
the two vertex maps. Neither the enumeration nor the vertex map is quotiented. -/
theorem cycles_map [DecidableEq α] [DecidableEq β] {e : α → β} (he : ∀ {x y}, e x = e y → x = y)
    (l : List α) {p : α → α} {q : β → β}
    (hq : ∀ x, q (e x) = e (p x)) : cycles q (l.map e) = cycles p l := by
  induction l generalizing p q with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, cycles, hq a]
    have hh : e (p a) = e a ↔ p a = a := ⟨he, congrArg e⟩
    simp only [hh]
    congr 1
    apply ih
    intro x
    have h₁ : e x = e a ↔ x = a := ⟨he, congrArg e⟩
    have h₂ : e (p x) = e a ↔ p x = a := ⟨he, congrArg e⟩
    simp only [cut, hq, h₁, h₂]
    grind

inductive Four | u | v | x | y deriving DecidableEq, Repr
open Four

def partner : Four → Four
  | u => x | v => y | x => u | y => v

def insertM (m : Matching α) : Matching (Four ⊕ α) where
  mate := Sum.map partner m.mate
  inv := by intro i; cases i with
            | inl b => cases b <;> rfl
            | inr b => simp [m.inv]
  free := by intro i; cases i with
             | inl b => cases b <;> simp [partner]
             | inr b => simpa using m.free b

def insertS [DecidableEq α] (s : α → α) (z : α) : Four ⊕ α → Four ⊕ α
  | .inl u => .inl v
  | .inl v => .inl x
  | .inl x => .inl y
  | .inl y => .inr z
  | .inr i => if s i = z then .inl u else .inr (s i)

def insertL (l : List α) : List (Four ⊕ α) :=
  [.inl u, .inl v, .inl x, .inl y] ++ l.map Sum.inr

theorem vertices_insert [DecidableEq α] (s : α → α) (z : α) (m : Matching α)
    (l : List α) : vertices (insertS s z) (insertM m) (insertL l) = vertices s m l := by
  unfold vertices insertL
  simp only [List.cons_append, List.nil_append, cycles]
  simp [insertM, partner, insertS, cut]
  apply cycles_map (e := Sum.inr) Sum.inr.inj
  intro i
  by_cases h : s (m.mate i) = z <;> simp [cut,insertS,insertM,h,partner]

@[ext] theorem Matching.ext {m q : Matching α} (h : ∀ x, m.mate x = q.mate x) : m = q := by
  cases m; cases q; congr; exact funext h

@[simp] theorem exchange_inr [DecidableEq α] [DecidableEq β] (a b i : α) :
    exchange (Sum.inr (α := β) a) (.inr b) (.inr i) = .inr (exchange a b i) := by
  by_cases h : i = a <;> by_cases h' : i = b <;> simp_all [exchange]

theorem insert_switch [DecidableEq α] (m : Matching α) (a b : α) :
    (insertM m).switch (.inr a) (.inr b) = insertM (m.switch a b) := by
  apply Matching.ext
  intro i
  cases i with
  | inl c => simp [Matching.switch, insertM, exchange, Sum.map]
  | inr c => simp [Matching.switch, insertM]

theorem legal_insert [DecidableEq α] {s : α → α} {l : List α} {m q : Matching α}
    (h : Legal s l m q) (z : α) :
    Legal (insertS s z) (insertL l) (insertM m) (insertM q) := by
  obtain ⟨a,b,hab,hpair,rfl,hg⟩ := h
  exact ⟨.inr a,.inr b, by simpa using hab, by simpa [insertM] using hpair,
    (insert_switch m a b).symm, by simpa only [vertices_insert] using hg⟩

theorem walk_insert [DecidableEq α] {s : α → α} {l : List α} {m q : Matching α} {k : Nat}
    (h : Walk s l m q k) (z : α) :
    Walk (insertS s z) (insertL l) (insertM m) (insertM q) k := by
  induction h with
  | nil => exact .nil _
  | cons e _ ih => exact .cons (legal_insert e z) ih

def cuts [DecidableEq α] (p : α → α) : List α → (α → α)
  | [] => p
  | a :: l => cuts (cut p a) l

theorem cycles_append [DecidableEq α] (p : α → α) (l r : List α) :
    cycles p (l++r) = cycles p l + cycles (cuts p l) r := by
  induction l generalizing p with
  | nil => simp [cycles, cuts]
  | cons a l ih => simp [cycles, cuts, ih, Nat.add_assoc]

theorem cuts_inj [DecidableEq α] {p : α → α} (hp : Inj p) (l : List α) : Inj (cuts p l) := by
  induction l generalizing p with
  | nil => exact hp
  | cons a l ih => exact ih (cut_inj hp a)

theorem cuts_keep_fixed [DecidableEq α] {p : α → α} {x : α} (hx : p x = x)
    (l : List α) : cuts p l x = x := by
  induction l generalizing p with
  | nil => exact hx
  | cons a l ih =>
    apply ih
    by_cases h : x = a <;> simp [cut,hx,h]

theorem cuts_fixed [DecidableEq α] {x : α} {l : List α} (hx : x ∈ l)
    (p : α → α) : cuts p l x = x := by
  induction l generalizing p with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · change cuts (cut p _) _ _ = _
      apply cuts_keep_fixed
      simp [cut]
    · exact ih h _

theorem cuts_arrow [DecidableEq α] {p : α → α} {x y : α} (h : p x = y) {l : List α}
    (hx : x ∉ l) (hy : y ∉ l) : cuts p l x = y := by
  induction l generalizing p with
  | nil => exact h
  | cons a l ih =>
    simp at hx hy
    apply ih _ hx.2 hy.2
    simp [cut,h,hx.1,hy.1]

theorem cut_right [DecidableEq α] (p d : α → α) (hd : Inj d) {a : α} (ha : d a = a) :
    cut (p ∘ d) a = cut p a ∘ d := by
  funext i
  have h : d i = a ↔ i = a := ⟨fun h => hd (h.trans ha.symm), fun h => h ▸ ha⟩
  simp [cut,Function.comp_def,h,ha]

theorem factor_right [DecidableEq α] (p d : α → α) (hd : Inj d) (l : List α)
    (h : ∀ x ∈ l, d x = x) :
    cycles (p ∘ d) l = cycles p l ∧ cuts (p ∘ d) l = cuts p l ∘ d := by
  induction l generalizing p with
  | nil => exact ⟨rfl,rfl⟩
  | cons a l ih =>
    have ha := h a (.head _)
    have hl := ih (cut p a) (fun x hx => h x (.tail _ hx))
    simp [cycles,cuts,cut_right p d hd ha,ha,hl]

theorem nodup_perm_of_mem [DecidableEq α] {l r : List α} (hl : l.Nodup) (hr : r.Nodup)
    (h : ∀ x, x ∈ l ↔ x ∈ r) : l.Perm r := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => exact .nil
    | cons a t => simpa using (h a).mpr (.head _)
  | cons a l ih =>
    have ha := (h a).mp (.head _)
    have perm := List.perm_cons_erase ha
    have hr' := perm.nodup hr
    simp only [List.nodup_cons] at hl hr'
    apply List.Perm.trans _ perm.symm
    apply List.Perm.cons
    apply ih hl.2 hr'.2
    intro i
    have hm := (h i).trans (perm.mem_iff)
    simp only [List.mem_cons] at hm
    by_cases eq : i = a
    · subst i; simp [hl.1,hr'.1]
    · simpa [eq] using hm

theorem inj_map_nodup [DecidableEq α] [DecidableEq β] {e : α → β}
    (he : ∀ {a b}, e a = e b → a = b) {l : List α} (h : l.Nodup) : (l.map e).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.nodup_cons] at h
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih h.2⟩
    intro hm
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp hm
    exact h.1 (he eq ▸ hi)

structure Enum (l : List α) : Prop where
  nodup : l.Nodup
  all : ∀ x, x ∈ l

theorem fin_enum (k : Nat) : Enum (List.finRange k) := by
  induction k with
  | zero => exact ⟨by simp, fun x => Fin.elim0 x⟩
  | succ k ih =>
    rw [List.finRange_succ]
    constructor
    · simp only [List.nodup_cons]
      exact ⟨by simp [Fin.succ_ne_zero], inj_map_nodup Fin.succ_inj.mp ih.nodup⟩
    · intro x
      refine Fin.cases (by simp) (fun i => ?_) x
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,ih.all i,rfl⟩)

theorem split_enum [DecidableEq α] [DecidableEq β] {l : List α} (hl : Enum l)
    {e : β → α} (he : ∀ {a b}, e a = e b → a = b)
    {t : List β} (ht : Enum t) :
    ∃ o : List α, l.Perm (o ++ t.map e) ∧ (∀ i, e i ∉ o) ∧
      (∀ x, x ∈ o ∨ ∃ i, x = e i) := by
  let t' := t.map e
  let o := l.filter (fun x => x ∉ t')
  have ho : ∀ x, x ∈ o ↔ x ∉ t' := by intro x; simp [o,hl.all]
  refine ⟨o, nodup_perm_of_mem hl.nodup ?_ ?_, ?_, ?_⟩
  · apply List.pairwise_append.mpr
    exact ⟨hl.nodup.filter _, inj_map_nodup he ht.nodup, by
      intro x hx y hy eq; exact (ho x).mp hx (eq ▸ hy)⟩
  · intro x; simp [ho,hl.all,t']; grind
  · intro i hi
    exact (ho _).mp hi (List.mem_map.mpr ⟨i,ht.all i,rfl⟩)
  · intro x
    by_cases h : x ∈ t'
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨i,rfl⟩
    · exact Or.inl ((ho _).mpr h)

/-- After eliminating the unmarked labels there is one return permutation on
the marked ports. Every rewiring of the ports uses the same discarded cycles. -/
theorem localize [DecidableEq α] [DecidableEq β] {l : List α} (hl : Enum l)
    {p : α → α} (hp : Inj p) {e : β → α} (he : ∀ {a b}, e a = e b → a = b)
    {t : List β} (ht : Enum t) :
    ∃ (f : β → β) (k : Nat), Inj f ∧
      (∀ i j, p (e i) = e j → f i = j) ∧
      cycles p l = k + cycles f t ∧
      (∀ (d : α → α) (r : β → β), Inj d →
        (∀ x, (∀ i, x ≠ e i) → d x = x) →
        (∀ i, d (e i) = e (r i)) →
        cycles (p ∘ d) l = k + cycles (f ∘ r) t) := by
  obtain ⟨o,perm,disj,cover⟩ := split_enum hl he ht
  let q := cuts p o
  have hq : Inj q := cuts_inj hp o
  have maps (i : β) : ∃ j, q (e i) = e j := by
    rcases cover (q (e i)) with h | h
    · have fixed := cuts_fixed h p
      have eq : q (e i) = e i := hq fixed
      exact False.elim (disj i (eq ▸ h))
    · exact h
  let f := fun i => Classical.choose (maps i)
  have hf : ∀ i, q (e i) = e (f i) := fun i => Classical.choose_spec (maps i)
  refine ⟨f,cycles p o,?_,?_,?_,?_⟩
  · intro a b H
    exact he (hq ((hf a).trans ((congrArg e H).trans (hf b).symm)))
  · intro i j hij
    exact he ((hf i).symm.trans (cuts_arrow hij (disj i) (disj j)))
  · rw [cycles_perm perm hp,cycles_append,cycles_map he t hf]
  · intro d r hd hout hport
    have hd' := factor_right p d hd o (fun x hx => hout x (fun i eq => disj i (eq ▸ hx)))
    rw [cycles_perm (p := p ∘ d) perm (fun _ _ h => hd (hp h)), cycles_append,hd'.1,hd'.2]
    congr 1
    apply cycles_map he
    intro i
    change q (d (e i)) = e (f (r i))
    rw [hport,hf]

theorem inj_comp {p q : α → α} (hp : Inj p) (hq : Inj q) : Inj (p ∘ q) :=
  fun _ _ h => hq (hp h)

/-- The two vertex cycles are classified on any two selected ports. -/
inductive Two | left | right deriving DecidableEq
def twoList := [Two.left, .right]
theorem twoEnum : Enum twoList := ⟨by decide, by intro x; cases x <;> decide⟩

theorem ex_natural [DecidableEq α] [DecidableEq β] {e : α → β}
    (he : ∀ {a b}, e a = e b → a = b) (a b i : α) :
    e (exchange a b i) = exchange (e a) (e b) (e i) := by
  have h₁ : e i = e a ↔ i = a := ⟨he,congrArg e⟩
  have h₂ : e i = e b ↔ i = b := ⟨he,congrArg e⟩
  by_cases h : i = a <;> by_cases h' : i = b <;> simp_all [exchange]

theorem switch_vertex [DecidableEq α] (s : α → α) (m : Matching α) (a b : α) :
    (fun x => s ((m.switch a b).mate x)) =
      (s ∘ m.mate) ∘ (exchange (m.mate a) (m.mate b) ∘ exchange a b) := by
  funext i
  simp only [Function.comp_apply, Matching.switch, ex_natural (e := m.mate) (fun h => m.inj h), m.inv]

structure Wiring (e : β → α) (base q : Matching α) (v : Matching β) : Prop where
  onPort : ∀ i, q.mate (e i) = e (v.mate i)
  offPort : ∀ x, (∀ i, x ≠ e i) → q.mate x = base.mate x

theorem Wiring.switch [DecidableEq α] [DecidableEq β] {e : β → α} {base q : Matching α}
    {v : Matching β} (w : Wiring e base q v)
    (he : ∀ {a b}, e a = e b → a = b) (a b : β) :
    Wiring e base (q.switch (e a) (e b)) (v.switch a b) := by
  constructor
  · intro i
    simp only [Matching.switch, ← ex_natural he, w.onPort]
  · intro i hi
    have hn (j : β) : q.mate i ≠ e j := by
      intro eq
      have h' := congrArg q.mate eq
      rw [q.inv,w.onPort] at h'
      exact hi _ h'
    simp only [Matching.switch,exchange,if_neg (hi a),if_neg (hi b),if_neg (hn a),if_neg (hn b)]
    exact w.offPort i hi

theorem matching_kernel [DecidableEq α] [DecidableEq β] {l : List α} (hl : Enum l)
    {s : α → α} (hs : Inj s) {e : β → α} (he : ∀ {a b}, e a = e b → a = b)
    {t : List β} (ht : Enum t) (base : Matching α) (v : Matching β)
    (hw : ∀ i, base.mate (e i) = e (v.mate i)) :
    ∃ (f : β → β) (k : Nat), Inj f ∧
      (∀ i j, s (base.mate (e i)) = e j → f i = j) ∧
      vertices s base l = k + cycles f t ∧
      (∀ (q : Matching α) (v' : Matching β), Wiring e base q v' →
        vertices s q l = k + cycles (f ∘ (v.mate ∘ v'.mate)) t) := by
  obtain ⟨f,k,hf,arrows,count,change⟩ := localize hl (inj_comp hs base.inj) he ht
  refine ⟨f,k,hf,arrows,count,?_⟩
  intro q v' w
  have H := change (base.mate ∘ q.mate) (v.mate ∘ v'.mate) (inj_comp base.inj q.inj)
    (fun i hi => by simp [w.offPort i hi,base.inv])
    (fun i => by simp [w.onPort,hw])
  simpa [vertices,Function.comp_def,base.inv] using H

inductive Six | u | v | x | y | a | b deriving DecidableEq
namespace Six
def labels := [u,v,x,y,a,b]
theorem enumeration : Enum labels := ⟨by decide,by intro i; cases i <;> decide⟩
def before : Six → Six
  | u => v | v => u | x => a | a => x | y => b | b => y
def initial : Matching Six := ⟨before, by intro i; cases i <;> rfl, by intro i; cases i <;> decide⟩
def middle := initial.switch v x
def finalM := middle.switch a y

/-- Three arrows of the compressed vertex permutation are forced by the four
consecutive sides. The other three images run over the remaining three ports. -/
def table (i j k : Six) : Six → Six
  | u => x | v => v | a => y | x => i | y => j | b => k
def test (i j k : Six) : Bool := Id.run do
  let f := table i j k
  let c := cycles f labels
  if decide (labels.map f).Nodup && c ≤ 2 then
    return cycles (f ∘ (before ∘ middle.mate)) labels == c &&
      cycles (f ∘ (before ∘ finalM.mate)) labels == c
  return true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem all_tables : labels.all (fun i => labels.all (fun j => labels.all (test i j))) = true := by decide

theorem kernel_transfer {f : Six → Six} (hf : Inj f) (hu : f u = x) (hv : f v = v)
    (ha : f a = y) (hc : cycles f labels ≤ 2) :
    cycles (f ∘ (before ∘ middle.mate)) labels = cycles f labels ∧
    cycles (f ∘ (before ∘ finalM.mate)) labels = cycles f labels := by
  have htab : table (f x) (f y) (f b) = f := by
    funext i; cases i <;> simp [table,hu,hv,ha]
  have ht := List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp all_tables _ (enumeration.all (f x))) _ (enumeration.all (f y))) _
    (enumeration.all (f b))
  have hn := inj_map_nodup (e := f) (fun h => hf h) enumeration.nodup
  simpa [test,htab,hn,hc,Id.run] using ht
end Six

theorem extract_from_leaf [DecidableEq α] (s : α → α) (hs : Inj s)
    (l : List α) (hl : Enum l) (m : Matching α) (e : Six → α)
    (he : ∀ {a b}, e a = e b → a = b)
    (hw : ∀ i, m.mate (e i) = e (Six.before i))
    (suv : s (e .u) = e .v) (svx : s (e .v) = e .x) (sxy : s (e .x) = e .y)
    (hgen : vertices s m l = 2) :
    ∃ q, Walk s l m q 2 ∧ q.mate (e .u) = e .x ∧ q.mate (e .v) = e .y := by
  let m₁ := m.switch (e .v) (e .x)
  let m₂ := m₁.switch (e .a) (e .y)
  have w₀ : Wiring e m m Six.initial := ⟨hw,fun _ _ => rfl⟩
  have w₁ : Wiring e m m₁ Six.middle := w₀.switch he _ _
  have w₂ : Wiring e m m₂ Six.finalM := w₁.switch he _ _
  obtain ⟨f,k,hf,arrows,count,change⟩ := matching_kernel hl hs he Six.enumeration m Six.initial hw
  have hu := arrows Six.u Six.x (by rw [hw]; exact svx)
  have hv := arrows Six.v Six.v (by rw [hw]; exact suv)
  have ha := arrows Six.a Six.y (by rw [hw]; exact sxy)
  obtain ⟨hm,he'⟩ := Six.kernel_transfer hf hu hv ha (by omega)
  have c₁ := change _ _ w₁
  have c₂ := change _ _ w₂
  change vertices s m₁ l = k + cycles (f ∘ (Six.before ∘ Six.middle.mate)) Six.labels at c₁
  change vertices s m₂ l = k + cycles (f ∘ (Six.before ∘ Six.finalM.mate)) Six.labels at c₂
  rw [hm] at c₁
  rw [he'] at c₂
  have ne (a b : Six) (h : a ≠ b) : e a ≠ e b := fun H => h (he H)
  have edge₁ : Legal s l m m₁ :=
    ⟨_,_,ne .v .x (by decide),by rw [hw]; exact ne .u .x (by decide),rfl,count.trans c₁.symm⟩
  have edge₂ : Legal s l m₁ m₂ :=
    ⟨_,_,ne .a .y (by decide),by rw [w₁.onPort]; exact ne .v .y (by decide),rfl,c₁.trans c₂.symm⟩
  exact ⟨m₂,.cons edge₁ (.cons edge₂ (.nil _)),w₂.onPort .u,w₂.onPort .v⟩

/-- Connectivity in the undirected graph of the permutation arrows. -/
inductive Conn (p : α → α) : α → α → Prop
  | refl (x) : Conn p x x
  | step (x) : Conn p x (p x)
  | symm {x y : α} : Conn p x y → Conn p y x
  | trans {x y z : α} : Conn p x y → Conn p y z → Conn p x z

theorem Conn.transport {p : α → α} {q : β → β} (f : α → β)
    (edges : ∀ x, Conn q (f x) (f (p x))) {x y : α} (h : Conn p x y) :
    Conn q (f x) (f y) := by
  induction h with
  | refl => exact .refl _
  | step => exact edges _
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

theorem Conn.invariant {p : α → α} {P : α → Prop} (step : ∀ i, P i ↔ P (p i))
    {x y : α} (h : Conn p x y) : P x ↔ P y := by
  induction h with
  | refl => rfl
  | step => apply step
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

theorem Conn.isolated {p : α → α} (hp : Inj p) {x y : α} (h : Conn p x y)
    (hx : p x = x) : x = y := by
  have hi (i : α) : i = x ↔ p i = x :=
    ⟨fun e => e ▸ hx,fun eq => hp (eq.trans hx.symm)⟩
  exact ((h.invariant hi).mp rfl).symm

theorem conn_cut_fwd [DecidableEq α] {p : α → α} {a x y : α} (hx : x ≠ a) (hy : y ≠ a)
    (h : Conn p x y) : Conn (cut p a) x y := by
  let skip := fun x => if x = a then p a else x
  have lift (i : α) : Conn (cut p a) (skip i) (skip (p i)) := by
    by_cases hi : i = a
    · subst i
      by_cases ha : p a = a <;> simp [skip,ha,Conn.refl]
    · simpa [cut,skip,hi] using Conn.step (p := cut p a) i
  simpa [skip,hx,hy] using h.transport skip lift

theorem conn_cut_back [DecidableEq α] {p : α → α} {a x y : α}
    (h : Conn (cut p a) x y) : Conn p x y := by
  apply h.transport id
  intro i
  by_cases hi : i = a
  · simp [cut,hi,Conn.refl]
  · by_cases he : p i = a
    · simpa [cut,hi,he] using (Conn.step (p := p) i).trans (Conn.step (p i))
    · simpa [cut,hi,he] using Conn.step (p := p) i

theorem conn_cuts [DecidableEq α] {p : α → α} {l : List α} {x y : α}
    (hx : x ∉ l) (hy : y ∉ l) : Conn p x y ↔ Conn (cuts p l) x y := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih =>
    simp at hx hy
    exact (Iff.intro (conn_cut_fwd hx.1 hy.1) conn_cut_back).trans (ih hx.2 hy.2)

theorem connected_count [DecidableEq α] {p : α → α} (hp : Inj p) {l : List α} (hl : l.Nodup)
    (h : ∀ i ∈ l, ∀ j ∈ l, Conn p i j) : cycles p l ≤ 1 := by
  induction l generalizing p with
  | nil => simp [cycles]
  | cons a l ih =>
    simp only [List.nodup_cons] at hl
    by_cases ha : p a = a
    · have empty : l = [] := by
        cases l with
        | nil => rfl
        | cons b t =>
          have eq := (h a (by simp) b (by simp)).isolated hp ha
          exact False.elim (hl.1 (by simp [eq]))
      simp [empty,cycles,ha]
    · simp only [cycles,if_neg ha,Nat.zero_add]
      apply ih (cut_inj hp a) hl.2
      intro i hi j hj
      have ne (v : α) (hv : v ∈ l) : v ≠ a := fun e => hl.1 (e ▸ hv)
      exact conn_cut_fwd (ne i hi) (ne j hj) (h i (.tail _ hi) j (.tail _ hj))

def twoSite (a b : α) : Two → α
  | .left => a | .right => b

theorem twoSite_inj {a b : α} (ne : a ≠ b) {i j : Two} :
    twoSite a b i = twoSite a b j → i = j := by
  cases i <;> cases j <;> simp_all [twoSite,Ne.symm ne]

/-- Exact cut-and-join formula, including whether the two ports lie on
the same vertex cycle. -/
theorem right_swap [DecidableEq α] {p : α → α} (hp : Inj p) {l : List α} (hl : Enum l)
    {a b : α} (ne : a ≠ b) :
    (Conn p a b → cycles (p ∘ exchange a b) l = cycles p l + 1) ∧
    (¬ Conn p a b → cycles (p ∘ exchange a b) l + 1 = cycles p l) := by
  let e := twoSite a b
  have he : ∀ {i j}, e i = e j → i = j := twoSite_inj ne
  obtain ⟨o,perm,disj,cover⟩ := split_enum hl he twoEnum
  let q := cuts p o
  have hq : Inj q := cuts_inj hp o
  have ha : a ∉ o := disj .left
  have hb : b ∉ o := disj .right
  have img (i : Two) : q (e i) = a ∨ q (e i) = b := by
    rcases cover (q (e i)) with h | ⟨j,h⟩
    · have eq : q (e i) = e i := hq (cuts_fixed h p)
      exact False.elim (disj i (eq ▸ h))
    · cases j <;> simp_all [e,twoSite]
  have out (x : α) (h : x ∈ o) : exchange a b x = x := by
    have h₁ : x ≠ a := fun eq => ha (eq ▸ h)
    have h₂ : x ≠ b := fun eq => hb (eq ▸ h)
    simp [exchange,h₁,h₂]
  obtain ⟨hcount,hcuts⟩ := factor_right p _ (ex_inj a b) o out
  have per : l.Perm (o ++ [a,b]) := perm
  have c₀ : cycles p l = cycles p o + cycles q [a,b] :=
    (cycles_perm per hp).trans (cycles_append ..)
  have c₁ : cycles (p ∘ exchange a b) l = cycles p o + cycles (q ∘ exchange a b) [a,b] := by
    rw [cycles_perm per (inj_comp hp (ex_inj a b)),cycles_append,hcount,hcuts]
  have I := conn_cuts (p := p) ha hb
  change Conn p a b ↔ Conn q a b at I
  obtain h | h := img .left <;> obtain h' | h' := img .right <;>
    change q a = _ at h <;> change q b = _ at h'
  · exact False.elim (ne (hq (h.trans h'.symm)))
  · have notC := fun (c : Conn p a b) => ne ((I.mp c).isolated hq h)
    rw [c₀,c₁]
    simp [cycles,cut,exchange,Function.comp_def,h,h',ne,Ne.symm ne,show ¬Conn p a b from notC,Nat.add_assoc]
  · have hc : Conn p a b := I.mpr (h ▸ Conn.step a)
    rw [c₀,c₁]
    simp [cycles,cut,exchange,Function.comp_def,h,h',ne,Ne.symm ne,hc]
  · exact False.elim (ne (hq (h.trans h'.symm)))

theorem exchange_perm [DecidableEq α] {l : List α} (hl : Enum l) (a b : α) :
    l.Perm (l.map (exchange a b)) := by
  apply nodup_perm_of_mem hl.nodup (inj_map_nodup (fun h => ex_inj a b h) hl.nodup)
  intro i
  exact ⟨fun _ => List.mem_map.mpr ⟨_,hl.all (exchange a b i),ex_twice ..⟩,fun _ => hl.all i⟩

theorem left_right_count [DecidableEq α] {p : α → α} (hp : Inj p) {l : List α} (hl : Enum l)
    (a b : α) : cycles (exchange a b ∘ p) l = cycles (p ∘ exchange a b) l := by
  rw [cycles_perm (exchange_perm hl a b) (inj_comp (ex_inj a b) hp)]
  apply cycles_map (fun h => ex_inj a b h)
  intro i; rfl

theorem count_pos [DecidableEq α] {p : α → α} (hp : Inj p) {l : List α} (hl : Enum l)
    (a : α) : 0 < cycles p l := by
  let e := fun (_ : Unit) => a
  have he : ∀ {i j}, e i = e j → i = j := fun _ => Subsingleton.elim .. 
  have hu : Enum [()] := ⟨by decide,by intro i; cases i; simp⟩
  obtain ⟨f,k,_,_,H,_⟩ := localize hl hp he hu
  have h : f () = () := Subsingleton.elim .. 
  simp [H,cycles,h]

theorem switch_lr [DecidableEq α] (s : α → α) (hs : Inj s) (m : Matching α) (a b : α) :
    (s ∘ (m.switch a b).mate) = exchange (s a) (s b) ∘ ((s ∘ m.mate) ∘ exchange a b) := by
  funext i
  exact ex_natural (e := s) (fun h => hs h) _ _ _

theorem switch_separate [DecidableEq α] (s : α → α) (hs : Inj s) {l : List α} (hl : Enum l)
    (m : Matching α) (a b : α) (hab : ¬Conn (s ∘ m.mate) a b) (pair : m.mate a ≠ b)
    (hc : vertices s m l = 2) : Legal s l m (m.switch a b) := by
  let p := s ∘ m.mate
  have hp := inj_comp hs m.inj
  have ne : a ≠ b := fun eq => hab (eq ▸ Conn.refl a)
  have ne' : s a ≠ s b := fun eq => ne (hs eq)
  let r := p ∘ exchange a b
  have hr : Inj r := inj_comp hp (ex_inj a b)
  have h₁ := (right_swap hp hl ne).2 hab
  change cycles p l = 2 at hc
  change cycles r l + 1 = cycles p l at h₁
  have pos := count_pos (inj_comp hr (ex_inj (s a) (s b))) hl a
  have h₂ := right_swap hr hl ne'
  have h₃ : Conn r (s a) (s b) := by
    apply Classical.byContradiction
    intro H
    have := h₂.2 H
    omega
  have h₄ := h₂.1 h₃
  refine ⟨a,b,ne,pair,rfl,?_⟩
  change cycles p l = cycles (s ∘ (m.switch a b).mate) l
  rw [switch_lr s hs, left_right_count hr hl]
  omega

theorem leaf_at [DecidableEq α] (s : α → α) (hs : Inj s) {l : List α} (hl : Enum l)
    (m : Matching α) (i : α) (diff : ¬Conn (s ∘ m.mate) i (s (s i))) :
    ∃ q, Legal s l m q ∧ q.mate i = s i := by
  let p := s ∘ m.mate
  let a := m.mate i
  let b := s i
  have hp : Inj p := inj_comp hs m.inj
  have hpa : p a = b := by simp [p,a,b,m.inv]
  have ne : a ≠ b := by
    intro eq
    apply diff
    have h : p i = s (s i) := congrArg s eq
    exact h ▸ Conn.step i
  have ab : Conn p a b := hpa ▸ Conn.step a
  have pair : m.mate a ≠ b := by
    intro eq
    have eq' : i = s i := (m.inv i).symm.trans eq
    apply diff
    simpa [← eq'] using Conn.refl (p := p) i
  let r := p ∘ exchange a b
  have hr : Inj r := inj_comp hp (ex_inj a b)
  have hrp (x y : α) (c : Conn r x y) : Conn p x y := by
    apply c.transport id
    intro j
    have aux : Conn p j (exchange a b j) := by
      by_cases h : j = a
      · simpa [exchange,h] using ab
      · by_cases h' : j = b
        · simpa [exchange,h',Ne.symm ne] using ab.symm
        · simp [exchange,h,h',Conn.refl]
    exact aux.trans (.step _)
  have different : ¬Conn r (s a) (s b) := fun c => diff ((Conn.step i).trans (hrp _ _ c))
  have h₁ := (right_swap hp hl ne).1 ab
  have h₂ := (right_swap hr hl (fun eq => ne (hs eq))).2 different
  refine ⟨m.switch a b, ⟨a,b,ne,pair,rfl,?_⟩,?_⟩
  · change cycles p l = cycles (s ∘ (m.switch a b).mate) l
    rw [switch_lr s hs, left_right_count hr hl]
    change cycles r l = cycles p l + 1 at h₁
    omega
  · have ia : i ≠ a := Ne.symm (m.free i)
    have ib : i ≠ b := by simpa [a,m.inv] using pair
    change exchange a b (m.mate (exchange a b i)) = b
    simp only [exchange,if_neg ia,if_neg ib]
    simp [a]

theorem cosets {s : α → α} (circ : ∀ i j, Conn s i j) (i j : α) :
    Conn (s ∘ s) i j ∨ Conn (s ∘ s) (s i) j := by
  let R := Conn (s ∘ s)
  let P := fun j => R i j ∨ R (s i) j
  have shift {a b : α} (h : R a b) : R (s a) (s b) :=
    Conn.transport (p := s ∘ s) (q := s ∘ s) s (fun a => .step (s a)) h
  have move (a : α) : P a → P (s a) := by
    intro h
    rcases h with h | h
    · exact .inr (shift h)
    · exact .inl ((Conn.step i).trans (shift h))
  have back (a : α) (h : P (s a)) : P a := by
    rcases move _ h with h | h
    · exact .inl (h.trans (Conn.step a).symm)
    · exact .inr (h.trans (Conn.step a).symm)
  exact ((circ i j).invariant (fun a => ⟨move a,back a⟩)).mp (.inl (.refl _))

theorem alternating_classes [DecidableEq α] {s p : α → α} (circ : ∀ i j, Conn s i j)
    {l : List α} (hl : Enum l) (hp : Inj p) (hc : cycles p l = 2)
    (double : ∀ i, Conn p i (s (s i))) :
    (∀ i, ¬Conn p i (s i)) ∧ (∀ i j, Conn p i j ↔ Conn (s ∘ s) i j) := by
  have lift {i j} (h : Conn (s ∘ s) i j) : Conn p i j := h.transport id double
  have sep (i : α) (bad : Conn p i (s i)) : False := by
    have all (j : α) : Conn p i j := (cosets circ i j).elim lift (fun h => bad.trans (lift h))
    have := connected_count hp hl.nodup (fun a _ b _ => (all a).symm.trans (all b))
    omega
  refine ⟨sep, fun i j => ⟨?_,lift⟩⟩
  intro h
  exact (cosets circ i j).elim id (fun H => False.elim (sep i (h.trans (lift H).symm)))

theorem make_leaf [DecidableEq α] (s : α → α) (hs : Inj s) (circ : ∀ i j, Conn s i j)
    {l : List α} (hl : Enum l) (m : Matching α) (a : α) (hc : vertices s m l = 2) :
    ∃ q k, k ≤ 2 ∧ Walk s l m q k ∧ ∃ i, q.mate i = s i := by
  classical
  by_cases h : ∃ i, m.mate i = s i
  · exact ⟨m,0,by decide,.nil _,h⟩
  let p := s ∘ m.mate
  have hp := inj_comp hs m.inj
  by_cases first : ∃ i, ¬ Conn p i (s (s i))
  · obtain ⟨i,diff⟩ := first
    obtain ⟨q,edge,pair⟩ := leaf_at s hs hl m i diff
    exact ⟨q,1,by decide,.cons edge (.nil _),i,pair⟩
  have d : ∀ i, Conn p i (s (s i)) := by simpa using first
  obtain ⟨sep,old⟩ := alternating_classes circ hl hp hc d
  let b := s a
  have unpaired : m.mate a ≠ b := fun eq => h ⟨a,eq⟩
  let q := m.switch a b
  have edge : Legal s l m q := switch_separate s hs hl m a b (sep a) unpaired hc
  have cq : vertices s q l = 2 := edge.choose_spec.choose_spec.2.2.2.symm.trans hc
  have witness : ∃ i, ¬Conn (s ∘ q.mate) i (s (s i)) := by
    apply Classical.byContradiction
    intro neg
    have d' : ∀ i, Conn (s ∘ q.mate) i (s (s i)) := by simpa using neg
    obtain ⟨sep',new⟩ := alternating_classes circ hl (inj_comp hs q.inj) cq d'
    have mba : m.mate b ≠ a := by
      intro eq; exact unpaired ((m.inv b).symm.trans (congrArg m.mate eq) |>.symm)
    have qa : q.mate a = m.mate b := by simp [q,Matching.switch,exchange,mba,m.free b]
    have ca : Conn (s ∘ q.mate) a (p b) := by
      simpa [Function.comp_def,p,qa] using Conn.step (p := s ∘ q.mate) a
    exact sep' a (ca.trans ((new b (p b)).mpr ((old b (p b)).mp (.step b))).symm)
  obtain ⟨i,diff⟩ := witness
  obtain ⟨r,last,pair⟩ := leaf_at s hs hl q i diff
  exact ⟨r,2,by decide,.cons edge (.cons last (.nil _)),i,pair⟩

theorem Walk.append [DecidableEq α] {s : α → α} {l : List α} {m q r : Matching α} {k j : Nat}
    (h : Walk s l m q k) (w : Walk s l q r j) : Walk s l m r (k+j) := by
  induction h with
  | nil => simpa using w
  | cons e _ ih => simpa [Nat.succ_add] using Walk.cons e (ih w)

theorem Walk.count_eq [DecidableEq α] {s : α → α} {l : List α} {m q : Matching α} {k : Nat}
    (h : Walk s l m q k) : vertices s m l = vertices s q l := by
  induction h with
  | nil => rfl
  | cons e _ ih => exact e.choose_spec.choose_spec.2.2.2.trans ih

theorem successor_val (i : Fin k) : (successor i).val =
    if i.val+1 < k then i.val+1 else 0 := by
  unfold successor
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · have h : i.val+1 = k := by omega
    simp [h]

theorem successor_inj (k : Nat) : Inj (@successor k) := by
  intro a b h
  have H := congrArg Fin.val h
  simp only [successor_val] at H
  apply Fin.ext
  split at H <;> split at H <;> omega

theorem successor_circular (a b : Fin k) : Conn successor a b := by
  let zero : Fin k := ⟨0,Nat.zero_lt_of_lt a.isLt⟩
  have reach (i : Nat) (h : i < k) : Conn successor zero ⟨i,h⟩ := by
    induction i with
    | zero => exact .refl _
    | succ i ih =>
      have hi : i < k := by omega
      have eq : successor (⟨i,hi⟩ : Fin k) = ⟨i+1,h⟩ := by
        apply Fin.ext; simp [successor_val,h]
      exact (ih hi).trans (eq ▸ Conn.step _)
  exact (reach a.val a.isLt).symm.trans (reach b.val b.isLt)

def fourSites (s : α → α) (i : α) : Four → α
  | u => i | v => s i | x => s (s i) | y => s (s (s i))

theorem four_distinct (hk : 4 ≤ k) (i : Fin k) {a b : Four}
    (h : fourSites successor i a = fourSites successor i b) : a = b := by
  have H := congrArg Fin.val h
  cases a <;> cases b <;> first | rfl | (simp only [fourSites,successor_val] at H; exfalso)
  all_goals
    (repeat' split at H) <;> omega

theorem no_second_leaf [DecidableEq α] {p : α → α} (hp : Inj p) {l : List α} (hl : Enum l)
    {e : Four → α} (he : ∀ {i j}, e i = e j → i = j)
    (hv : p (e v) = e v) (hy : p (e y) = e y) (hc : cycles p l = 2) : False := by
  have enum : Enum [u,v,x,y] := ⟨by decide,by intro i; cases i <;> decide⟩
  obtain ⟨f,k,hf,arrows,c,_⟩ := localize hl hp he enum
  have V := arrows _ _ hv
  have Y := arrows _ _ hy
  have sep₁ := @hf u v
  have sep₂ := @hf u y
  have sep₃ := @hf x v
  have sep₄ := @hf x y
  have sep₅ := @hf u x
  cases U : f u <;> cases X : f x <;>
    simp_all [cycles,cut] <;> omega

def sixSites (s : α → α) (m : Matching α) (i : α) : Six → α
  | .u => i | .v => s i | .x => s (s i) | .y => s (s (s i))
  | .a => m.mate (s (s i)) | .b => m.mate (s (s (s i)))

theorem six_distinct [DecidableEq α] (s : α → α) (hs : Inj s) (l : List α) (hl : Enum l)
    (m : Matching α) (i : α) (hi : m.mate i = s i) (hc : vertices s m l = 2)
    (hd : ∀ {a b}, fourSites s i a = fourSites s i b → a = b) :
    ∀ {a b}, sixSites s m i a = sixSites s m i b → a = b := by
  have ne (a b : Four) (n : a ≠ b) : fourSites s i a ≠ fourSites s i b := fun h => n (hd h)
  have N₁ := ne u v (by decide); have N₂ := ne u x (by decide)
  have N₃ := ne u y (by decide); have N₄ := ne v x (by decide)
  have N₅ := ne v y (by decide); have N₆ := ne x y (by decide)
  simp only [fourSites] at N₁ N₂ N₃ N₄ N₅ N₆
  have H : m.mate (s (s i)) ≠ s (s (s i)) := by
    intro bad
    have h₁ := (congrArg m.mate hi).symm.trans (m.inv i)
    have h₂ := (congrArg m.mate bad).symm.trans (m.inv _)
    exact no_second_leaf (p := s ∘ m.mate) (inj_comp hs m.inj) hl hd
      (congrArg s h₁) (congrArg s h₂) hc
  have h₁ := m.inv i
  have h₂ := m.inv (s (s i))
  have h₃ := m.inv (s (s (s i)))
  have h₄ := m.free (s (s i))
  have h₅ := m.free (s (s (s i)))
  intro a b h
  cases a <;> cases b <;> simp only [sixSites] at h <;> grind

theorem extraction [DecidableEq α] (s : α → α) (hs : Inj s) (circ : ∀ i j, Conn s i j)
    (l : List α) (hl : Enum l) (m : Matching α) (a : α) (hc : vertices s m l = 2)
    (hd : ∀ i {j k}, fourSites s i j = fourSites s i k → j = k) :
    ∃ q k i, k ≤ 4 ∧ Walk s l m q k ∧ q.mate i = s (s i) ∧
      q.mate (s i) = s (s (s i)) := by
  obtain ⟨m₁,k,bound,w,i,hi⟩ := make_leaf s hs circ hl m a hc
  have hc₁ := w.count_eq.symm.trans hc
  let e := sixSites s m₁ i
  have he := @six_distinct _ _ s hs l hl m₁ i hi hc₁ (hd i)
  have hw (j : Six) : m₁.mate (e j) = e (Six.before j) := by
    cases j <;> simp [e,sixSites,Six.before,m₁.inv,hi,
      show m₁.mate (s i) = i from (congrArg m₁.mate hi).symm.trans (m₁.inv i)]
  obtain ⟨q,path,H₁,H₂⟩ := extract_from_leaf s hs l hl m₁ e (fun h => he h) hw rfl rfl rfl hc₁
  exact ⟨q,k+2,i,by omega,w.append path,H₁,H₂⟩

theorem labelled_extraction {g : Nat} (hg : 0 < g) (m : Matching (Fin (2*(2*g+1))))
    (hm : AtGenus (2*g+1) g m) :
    ∃ q k i, k ≤ 4 ∧ Walk successor (sides (2*g+1)) m q k ∧
      q.mate i = successor (successor i) ∧
      q.mate (successor i) = successor (successor (successor i)) := by
  exact extraction successor (successor_inj _) successor_circular _ (fin_enum _) m
    ⟨0,by omega⟩ (odd_genus_iff.mp hm) (four_distinct (by omega))
end OddDiameter


/-! ## Polygon -/
namespace OddDiameter

structure Bijection (α β : Type) where
  to : α → β
  back : β → α
  left : ∀ i, back (to i) = i
  right : ∀ j, to (back j) = j

theorem Bijection.inj (b : Bijection α β) {x y} (H : b.to x = b.to y) : x = y := by
  simpa only [b.left] using congrArg b.back H

def Bijection.inverse (b : Bijection α β) : Bijection β α := ⟨b.back,b.to,b.right,b.left⟩

def Bijection.matching (b : Bijection α β) (m : Matching α) : Matching β where
  mate i := b.to (m.mate (b.back i))
  inv i := by simp only [b.left,m.inv,b.right]
  free i H := m.free _ (by simpa only [b.left] using congrArg b.back H)

@[simp] theorem Bijection.mate_to (b : Bijection α β) (m : Matching α) (i : α) :
    (b.matching m).mate (b.to i) = b.to (m.mate i) := by simp [Bijection.matching,b.left]

theorem Bijection.switch [DecidableEq α] [DecidableEq β] (b : Bijection α β)
    (m : Matching α) (a c : α) : b.matching (m.switch a c) = (b.matching m).switch (b.to a) (b.to c) := by
  apply Matching.ext
  intro i
  conv => lhs; rw [← b.right i]
  conv => rhs; rw [← b.right i]
  simp only [b.mate_to,Matching.switch, ← ex_natural b.inj,b.mate_to]

theorem Bijection.count [DecidableEq α] [DecidableEq β] (b : Bijection α β)
    {s : α → α} {t : β → β} (ht : Inj t) (eq : ∀ i, t (b.to i) = b.to (s i))
    {l : List α} {r : List β} (order : r.Perm (l.map b.to)) (m : Matching α) :
    vertices t (b.matching m) r = vertices s m l := by
  unfold vertices
  rw [cycles_perm order (p := fun x => t ((b.matching m).mate x)) (fun _ _ h => (b.matching m).inj (ht h))]
  apply cycles_map b.inj
  intro i; simp [eq]

theorem Bijection.walk [DecidableEq α] [DecidableEq β] (b : Bijection α β)
    {s : α → α} {t : β → β} (ht : Inj t) (eq : ∀ i, t (b.to i) = b.to (s i))
    {l : List α} {r : List β} (order : r.Perm (l.map b.to)) {m q : Matching α} {k}
    (w : Walk s l m q k) : Walk t r (b.matching m) (b.matching q) k := by
  induction w with
  | nil => exact .nil _
  | cons h _ ih =>
    obtain ⟨a,c,ne,diff,rfl,vc⟩ := h
    exact .cons ⟨b.to a,b.to c,fun H => ne (b.inj H),by simpa only [b.mate_to] using
      (fun H => diff (b.inj H) : b.to _ ≠ b.to c),b.switch ..,by simpa only [b.count ht eq order] using vc⟩ ih

theorem enum_perm {α} [DecidableEq α] {l r : List α} (hl : Enum l) (hr : Enum r) : l.Perm r :=
  nodup_perm_of_mem hl.nodup hr.nodup (fun i => ⟨fun _ => hr.all i, fun _ => hl.all i⟩)

theorem Bijection.enum [DecidableEq α] [DecidableEq β] (b : Bijection α β) {l : List α} (hl : Enum l) :
    Enum (l.map b.to) :=
  ⟨inj_map_nodup b.inj hl.nodup, fun i => List.mem_map.mpr ⟨_,hl.all _,b.right i⟩⟩

def sumM (m : Matching α) (q : Matching β) : Matching (α ⊕ β) where
  mate := Sum.map m.mate q.mate
  inv := by intro i; cases i <;> simp [m.inv,q.inv]
  free := by intro i; cases i <;> simp [m.free,q.free]

def sumL (l : List α) (r : List β) : List (α ⊕ β) := l.map Sum.inl ++ r.map Sum.inr

theorem sum_enum [DecidableEq α] [DecidableEq β] {l : List α} {r : List β}
    (hl : Enum l) (hr : Enum r) : Enum (sumL l r) := by
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨inj_map_nodup Sum.inl.inj hl.nodup,inj_map_nodup Sum.inr.inj hr.nodup,?_⟩
    intro a ha b hb
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hb
    simp
  · intro i; cases i <;> simp [sumL,hl.all,hr.all]

theorem sum_inj {s : α → α} {t : β → β} (hs : Inj s) (ht : Inj t) : Inj (Sum.map s t) := by
  intro i j h; cases i <;> cases j <;> simp_all
  · exact hs h
  · exact ht h

theorem cuts_on_other [DecidableEq α] [DecidableEq β] (s : α → α) (t : β → β) (l : List α) (i : β) :
    cuts (Sum.map s t) (l.map Sum.inl) (.inr i) = .inr (t i) := by
  apply cuts_arrow (by rfl) <;> simp

theorem cycles_sum [DecidableEq α] [DecidableEq β] (s : α → α) (t : β → β) (l : List α) (r : List β) :
    cycles (Sum.map s t) (sumL l r) = cycles s l + cycles t r := by
  rw [sumL,cycles_append,cycles_map (e := Sum.inl) Sum.inl.inj l (p := s) (fun _ => rfl)]
  congr 1
  exact cycles_map Sum.inr.inj r (cuts_on_other s t l)

def joinS [DecidableEq α] [DecidableEq β] (s : α → α) (t : β → β) (a : α) (b : β) :=
  exchange (.inl a) (.inr b) ∘ Sum.map s t

theorem vertices_join [DecidableEq α] [DecidableEq β]
    {l : List α} {r : List β} (hl : Enum l) (hr : Enum r) {s : α → α} {t : β → β}
    (hs : Inj s) (ht : Inj t) (a : α) (b : β) (m : Matching α) (q : Matching β) :
    vertices (joinS s t a b) (sumM m q) (sumL l r) + 1 = vertices s m l + vertices t q r := by
  let p := Sum.map (s ∘ m.mate) (t ∘ q.mate)
  have hp : Inj p := sum_inj (inj_comp hs m.inj) (inj_comp ht q.inj)
  have sep : ¬Conn p (.inl a) (.inr b) := by
    intro H
    let P : α ⊕ β → Prop := fun i => i.isLeft
    have stable (i) : P i ↔ P (p i) := by cases i <;> rfl
    exact Bool.noConfusion ((H.invariant stable).mp rfl)
  have h := (right_swap hp (sum_enum hl hr) (a := .inl a) (b := .inr b) (by simp)).2 sep
  rw [← left_right_count hp (sum_enum hl hr)] at h
  have eq : (fun i => joinS s t a b ((sumM m q).mate i)) =
      exchange (.inl a) (.inr b) ∘ p := by funext i; cases i <;> rfl
  unfold vertices
  rw [eq,h]
  exact cycles_sum .. 

@[simp] theorem exchange_inl [DecidableEq α] [DecidableEq β] (a b i : α) :
    exchange (Sum.inl (β := β) a) (.inl b) (.inl i) = .inl (exchange a b i) := by
  by_cases h : i = a <;> by_cases h' : i = b <;> simp_all [exchange]

theorem sum_switch_left [DecidableEq α] [DecidableEq β] (m : Matching α) (q : Matching β) (a b : α) :
    (sumM m q).switch (.inl a) (.inl b) = sumM (m.switch a b) q := by
  apply Matching.ext
  intro i; cases i with
  | inl i => simp [Matching.switch,sumM]
  | inr i => simp [Matching.switch,sumM,exchange]

theorem walk_join_left [DecidableEq α] [DecidableEq β]
    {l : List α} {r : List β} (hl : Enum l) (hr : Enum r) {s : α → α} {t : β → β}
    (hs : Inj s) (ht : Inj t) (a : α) (b : β) {m q : Matching α} (n : Matching β) {k}
    (w : Walk s l m q k) : Walk (joinS s t a b) (sumL l r) (sumM m n) (sumM q n) k := by
  induction w with
  | nil => exact .nil _
  | cons h _ ih =>
    obtain ⟨i,j,ne,diff,rfl,eq⟩ := h
    apply Walk.cons _ ih
    refine ⟨.inl i,.inl j,by simpa using ne,by simpa [sumM] using diff,(sum_switch_left ..).symm,?_⟩
    apply Nat.add_right_cancel (m := 1)
    rw [vertices_join hl hr hs ht,vertices_join hl hr hs ht,eq]

end OddDiameter


/-! ## Words -/
set_option grind.warning false
namespace OddDiameter

def Reads (s : α → α) : List α → α → α → Prop
  | [], a,b => a = b
  | i::l, a,b => i = a ∧ Reads s l (s i) b

def Circular (s : α → α) (l : List α) := ∃ a, Reads s l a a

theorem reads_append (s : α → α) (l r : List α) (a b : α) :
    Reads s (l++r) a b ↔ ∃ c, Reads s l a c ∧ Reads s r c b := by
  induction l generalizing a with
  | nil => simp [Reads]
  | cons i l ih => simp [Reads,ih]; grind

theorem circular_rotate {s : α → α} {l r : List α} :
    Circular s (l++r) → Circular s (r++l) := by
  rintro ⟨a,H⟩
  obtain ⟨b,h,h'⟩ := (reads_append ..).mp H
  exact ⟨b,(reads_append ..).mpr ⟨a,h',h⟩⟩

theorem reads_first {s : α → α} {l : List α} {a b : α}
    (h : Reads s l a b) (i : Nat) (hi : i+1 < l.length) :
    s l[i] = l[i+1] := by
  induction l generalizing i a with
  | nil => simp at hi
  | cons j l ih =>
    obtain ⟨_,h⟩ := h
    cases i with
    | zero =>
      cases l with
      | nil => simp at hi
      | cons k l => exact h.1.symm
    | succ i => exact ih h i (by simpa using hi)

theorem reads_last {s : α → α} {l : List α} {a b : α}
    (h : Reads s l a b) (i : Nat) (hi : i+1 = l.length) :
    s l[i] = b := by
  induction l generalizing i a with
  | nil => simp at hi
  | cons j l ih =>
    obtain ⟨_,h⟩ := h
    cases i with
    | zero =>
      cases l with
      | nil => exact h
      | cons k t => simp only [List.length_cons] at hi; omega
    | succ i => exact ih h i (by simpa using hi)

theorem reads_head {s : α → α} {l : List α} {a b : α}
    (h : Reads s l a b) (hl : 0 < l.length) : l[0] = a := by
  cases l with
  | nil => simp at hl
  | cons j l => exact h.1

theorem circular_step {s : α → α} {l : List α} (H : Circular s l) (i : Fin l.length) :
    s (l.get i) = l.get (successor i) := by
  obtain ⟨a,h⟩ := H
  by_cases hi : i.val + 1 < l.length
  · simpa only [List.get_eq_getElem,successor_val,if_pos hi] using reads_first h i.val hi
  · have eq : i.val+1 = l.length := by omega
    have Hz := reads_head h (by omega)
    simp only [List.get_eq_getElem,successor_val,if_neg hi]
    exact (reads_last h _ eq).trans Hz.symm

theorem reads_of_steps {s : α → α} (l : List α) (a b : α)
    (start : ∀ (h : 0 < l.length), l[0] = a)
    (empty : l = [] → a = b)
    (step : ∀ i (h : i+1 < l.length), s l[i] = l[i+1])
    (last : ∀ i (h : i+1 = l.length), s l[i] = b) : Reads s l a b := by
  induction l generalizing a with
  | nil => exact empty rfl
  | cons i l ih =>
    refine ⟨start (by simp), ih _ ?_ ?_ ?_ ?_⟩
    · intro h; exact (step 0 (by simpa using h)).symm
    · intro H; subst l; exact last 0 rfl
    · intro j h; exact step (j+1) (by simpa using h)
    · intro j h; exact last (j+1) (by simpa using h)

theorem fin_circular {n : Nat} (hn : 0 < n) : Circular successor (List.finRange n) := by
  let z : Fin n := ⟨0,hn⟩
  refine ⟨z,reads_of_steps _ _ _ ?_ ?_ ?_ ?_⟩
  · intro h; simp [z]
  · intro _; rfl
  · intro i hi; simp only [List.length_finRange] at hi
    apply Fin.ext; simp [successor_val,hi]
  · intro i hi; simp only [List.length_finRange] at hi
    apply Fin.ext; simp [successor_val,hi,z]

theorem get_index_inj {l : List α} (hn : l.Nodup) {i j : Fin l.length}
    (h : l.get i = l.get j) : i = j := by
  apply Fin.ext
  apply List.getElem?_inj i.isLt hn
  simpa [List.getElem?_eq_getElem, i.isLt, j.isLt] using h

theorem get_index_onto {l : List α} {x : α} (hx : x ∈ l) :
    ∃ i : Fin l.length, l.get i = x := by
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp hx
  exact ⟨⟨i,hi⟩,e⟩

noncomputable def bijective {α β : Type} (f : α → β) (inj : ∀ {x y}, f x = f y → x = y)
    (onto : ∀ y, ∃ x, f x = y) : Bijection α β where
  to := f
  back y := Classical.choose (onto y)
  left x := inj (Classical.choose_spec (onto (f x)))
  right y := Classical.choose_spec (onto y)

noncomputable def indexChart {l : List α} (hl : Enum l) : Bijection (Fin l.length) α :=
  bijective l.get (get_index_inj hl.nodup) (fun i => get_index_onto (hl.all i))

theorem get_order (l : List α) : (List.finRange l.length).map l.get = l := by
  apply List.ext_getElem <;> simp

theorem circular_inj {s : α → α} {l : List α} (hl : Enum l) (circ : Circular s l) : Inj s := by
  intro i j eq
  obtain ⟨a,rfl⟩ := get_index_onto (hl.all i)
  obtain ⟨b,rfl⟩ := get_index_onto (hl.all j)
  rw [circular_step circ,circular_step circ] at eq
  exact congrArg l.get (successor_inj _ (get_index_inj hl.nodup eq))

theorem circular_conn {s : α → α} {l : List α} (hl : Enum l) (circ : Circular s l)
    (i j : α) : Conn s i j := by
  obtain ⟨a,rfl⟩ := get_index_onto (hl.all i)
  obtain ⟨b,rfl⟩ := get_index_onto (hl.all j)
  exact (successor_circular a b).transport l.get (fun i => circular_step circ i ▸ Conn.step _)

theorem reads_map {s : α → α} {t : β → β} {a b : α} {l : List α}
    (f : α → β) (eq : ∀ x, t (f x) = f (s x)) (h : Reads s l a b) :
    Reads t (l.map f) (f a) (f b) := by
  induction l generalizing a with
  | nil => exact congrArg f h
  | cons i l ih => exact ⟨congrArg f h.1,eq i ▸ ih h.2⟩

end OddDiameter


/-! ## Patch -/
set_option grind.warning false
namespace OddDiameter

def splitTo (w r : List α) : Fin w.length ⊕ Fin r.length → α := Sum.elim w.get r.get

noncomputable def splitChart (w r : List α) (h : Enum (w++r)) :
    Bijection (Fin w.length ⊕ Fin r.length) α := by
  have nw := (List.pairwise_append.mp h.nodup).1
  have nr := (List.pairwise_append.mp h.nodup).2.1
  have disj := (List.pairwise_append.mp h.nodup).2.2
  apply bijective (splitTo w r)
  · intro i j eq; cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg _ (get_index_inj nw eq)
      | inr j => exact False.elim (disj _ (List.get_mem ..) _ (List.get_mem ..) eq)
    | inr i =>
      cases j with
      | inr j => exact congrArg _ (get_index_inj nr eq)
      | inl j => exact False.elim (disj _ (List.get_mem ..) _ (List.get_mem ..) eq.symm)
  · intro i; rcases List.mem_append.mp (h.all i) with h | h
    · obtain ⟨j,rfl⟩ := get_index_onto h; exact ⟨.inl j,rfl⟩
    · obtain ⟨j,rfl⟩ := get_index_onto h; exact ⟨.inr j,rfl⟩

@[simp] theorem splitChart_to (w r : List α) (h : Enum (w++r)) (i) :
    (splitChart w r h).to i = splitTo w r i := rfl

def zeroOf {k : Nat} (hk : 0 < k) : Fin k := ⟨0,hk⟩

theorem chart_step {s : α → α} {w r : List α} (hw : 0 < w.length) (hr : 0 < r.length)
    (h : Circular s (w++r)) (i : Fin w.length ⊕ Fin r.length) :
    s (splitTo w r i) =
      splitTo w r (joinS successor successor (zeroOf hw) (zeroOf hr) i) := by
  obtain ⟨a,H⟩ := h
  obtain ⟨b,hw',hr'⟩ := (reads_append ..).mp H
  have work {w r : List α} {a b : α} (hw' : Reads s w a b) (hr' : Reads s r b a)
      (hw : 0 < w.length) (hr : 0 < r.length) (i : Fin w.length) :
      s (w.get i) = if successor i = zeroOf hw then r.get (zeroOf hr) else w.get (successor i) := by
    by_cases hi : i.val+1 < w.length
    · have ne : successor i ≠ zeroOf hw := by
        intro H; have := congrArg Fin.val H; simp [successor_val,hi,zeroOf] at this
      simpa [ne,successor_val,hi] using reads_first hw' i.val hi
    · have eq : successor i = zeroOf hw := by apply Fin.ext; simp [successor_val,hi,zeroOf]
      rw [if_pos eq]
      exact (reads_last hw' i.val (by omega)).trans (reads_head hr' hr).symm
  cases i with
  | inl i =>
    have H := work hw' hr' hw hr i
    by_cases h : successor i = zeroOf hw <;> simpa [joinS,splitTo,exchange,h] using H
  | inr i =>
    have H := work hr' hw' hr hw i
    by_cases h : successor i = zeroOf hr <;> simpa [joinS,splitTo,exchange,h] using H

def On (m : Matching α) (w : List α) (p : Matching (Fin w.length)) :=
  ∀ i, m.mate (w.get i) = w.get (p.mate i)

noncomputable def restriction (m : Matching α) (w : List α) (nw : w.Nodup)
    (closed : ∀ a ∈ w, m.mate a ∈ w) : Matching (Fin w.length) := by
  have H (i : Fin w.length) := get_index_onto (closed _ (List.get_mem w i))
  let p := fun i => Classical.choose (H i)
  have step (i) : w.get (p i) = m.mate (w.get i) := Classical.choose_spec (H i)
  exact ⟨p,fun i => get_index_inj nw (by rw [step, step,m.inv]),fun i eq =>
    m.free _ ((step i).symm.trans (congrArg w.get eq))⟩

theorem on_restriction (m : Matching α) (w : List α) (nw : w.Nodup) (cl) :
    On m w (restriction m w nw cl) := fun i => (Classical.choose_spec (get_index_onto (cl _ (List.get_mem w i)))).symm

theorem complement_closed {w r : List α} (hen : Enum (w++r)) {m : Matching α}
    {p : Matching (Fin w.length)} (on : On m w p) : ∀ a ∈ r, m.mate a ∈ r := by
  intro a ha
  rcases List.mem_append.mp (hen.all (m.mate a)) with bad | ok
  · obtain ⟨i,eq⟩ := get_index_onto bad
    have H := congrArg m.mate eq
    rw [on,m.inv] at H
    exact False.elim ((List.pairwise_append.mp hen.nodup).2.2 _ (List.get_mem ..) _ ha H)
  · exact ok

theorem combined_eq {w r : List α} (hen : Enum (w++r)) {m : Matching α}
    {p : Matching (Fin w.length)} {q : Matching (Fin r.length)} (h : On m w p) (h' : On m r q) :
    (splitChart w r hen).matching (sumM p q) = m := by
  let b := splitChart w r hen
  apply Matching.ext
  intro i
  rw [← b.right i]
  change (b.matching _).mate (b.to _) = m.mate (b.to _)
  rw [b.mate_to]
  cases b.back i with
  | inl j => exact (h j).symm
  | inr j => exact (h' j).symm

theorem Enum.permute {l r : List α} (hl : Enum l) (h : l.Perm r) : Enum r :=
  ⟨h.nodup hl.nodup,fun i => h.mem_iff.mp (hl.all i)⟩

theorem patch_count [DecidableEq α] {s : α → α} {w r : List α}
    (hen : Enum (w++r)) (circ : Circular s (w++r))
    (hw : 0 < w.length) (hr : 0 < r.length)
    {m : Matching α} {p : Matching (Fin w.length)} {q : Matching (Fin r.length)}
    (h : On m w p) (h' : On m r q) :
    vertices s m (w++r) + 1 =
      vertices successor p (List.finRange w.length) + vertices successor q (List.finRange r.length) := by
  let b := splitChart w r hen
  have he := sum_enum (fin_enum w.length) (fin_enum r.length)
  have main := b.count (circular_inj hen circ) (chart_step hw hr circ) (enum_perm hen (b.enum he)) (sumM p q)
  rw [combined_eq hen h h'] at main
  rw [main,vertices_join (fin_enum _) (fin_enum _) (successor_inj _) (successor_inj _)]

theorem patch_move [DecidableEq α] {s : α → α} {w r : List α}
    (hen : Enum (w++r)) (circ : Circular s (w++r)) (hw : 0 < w.length)
    {m : Matching α} {p q : Matching (Fin w.length)} (on : On m w p) {k : Nat}
    (path : Walk successor (List.finRange w.length) p q k) :
    ∃ m', Walk s (w++r) m m' k ∧ On m' w q ∧ ∀ i ∈ r, m'.mate i = m.mate i := by
  by_cases hr : 0 < r.length
  · let z := restriction m r (List.pairwise_append.mp hen.nodup).2.1 (complement_closed hen on)
    have hz : On m r z := on_restriction m r _ _
    let b := splitChart w r hen
    have path' := walk_join_left (fin_enum _) (fin_enum _) (successor_inj _) (successor_inj _)
      (zeroOf hw) (zeroOf hr) z path
    have he := sum_enum (fin_enum w.length) (fin_enum r.length)
    have walk := b.walk (circular_inj hen circ) (chart_step hw hr circ) (enum_perm hen (b.enum he)) path'
    rw [combined_eq hen on hz] at walk
    refine ⟨_,walk,?_,?_⟩
    · intro i; exact b.mate_to (sumM q z) (.inl i)
    · intro j hj; obtain ⟨i,rfl⟩ := get_index_onto hj
      exact (b.mate_to (sumM q z) (.inr i)).trans (hz i).symm
  · have eq : r = [] := List.length_eq_zero_iff.mp (by omega)
    subst r
    simp only [List.append_nil] at *
    let b := indexChart hen
    have path' := b.walk (circular_inj hen circ) (circular_step circ) (enum_perm hen (b.enum (fin_enum _))) path
    have start : b.matching p = m := by
      apply Matching.ext; intro i
      rw [← b.right i, b.mate_to]
      exact (on _).symm
    rw [start] at path'
    exact ⟨_,path', fun i => b.mate_to q i,by simp⟩

/-- The indices of a word obtained by substituting labels in a numerical template. -/
def mapIndex (e : Fin n → α) : Bijection (Fin n) (Fin ((List.finRange n).map e).length) where
  to i := ⟨i.val,by simp⟩
  back i := ⟨i.val,by simpa using i.isLt⟩
  left _ := rfl
  right _ := rfl

theorem mapIndex_succ (e : Fin n → α) (i : Fin n) :
    successor ((mapIndex e).to i) = (mapIndex e).to (successor i) := by
  apply Fin.ext; simp [successor_val,mapIndex]

theorem mapIndex_get (e : Fin n → α) (i : Fin n) :
    ((List.finRange n).map e).get ((mapIndex e).to i) = e i := by simp [mapIndex]

theorem patch_named [DecidableEq α] (e : Fin n → α) {r : List α} {s : α → α}
    (hn : 0 < n) (hen : Enum ((List.finRange n).map e ++ r))
    (circ : Circular s ((List.finRange n).map e ++ r)) (m : Matching α)
    {p q : Matching (Fin n)} (on : ∀ i, m.mate (e i) = e (p.mate i)) {k}
    (path : Walk successor (List.finRange n) p q k) :
    ∃ m', Walk s ((List.finRange n).map e ++ r) m m' k ∧
      (∀ i, m'.mate (e i) = e (q.mate i)) ∧ ∀ i ∈ r, m'.mate i = m.mate i := by
  let b := mapIndex e
  have w := b.walk (successor_inj _) (mapIndex_succ e) (enum_perm (fin_enum _) (b.enum (fin_enum _))) path
  have h : On m ((List.finRange n).map e) (b.matching p) := by
    intro i; rw [← b.right i,b.mate_to,mapIndex_get,mapIndex_get]; apply on
  obtain ⟨m',w',eq,off⟩ := patch_move hen circ (by simpa using hn) h w
  refine ⟨m',w',?_,off⟩
  intro i
  simpa only [b.mate_to,b,mapIndex_get] using eq (b.to i)
end OddDiameter


/-! ## Tiles -/
set_option grind.warning false
namespace OddDiameter

inductive Tile (α : Type)
  | leaf (a b : α)
  | handle (a b c d : α)
deriving DecidableEq, Repr
namespace Tile
def labels : Tile α → List α
  | .leaf a b => [a,b]
  | .handle a b c d => [a,b,c,d]
def map (e : α → β) : Tile α → Tile β
  | .leaf a b => .leaf (e a) (e b)
  | .handle a b c d => .handle (e a) (e b) (e c) (e d)
def weight : Tile α → Nat
  | .leaf .. => 0
  | .handle .. => 1
def Fits (m : Matching α) : Tile α → Prop
  | .leaf a b => m.mate a = b
  | .handle a b c d => m.mate a = c ∧ m.mate b = d
@[simp] theorem labels_map (e : α → β) (t : Tile α) : (t.map e).labels = t.labels.map e := by
  cases t <;> rfl
@[simp] theorem weight_map (e : α → β) (t : Tile α) : (t.map e).weight = t.weight := by
  cases t <;> rfl
theorem fits_congr {m q : Matching α} {t : Tile α} (eq : ∀ i ∈ t.labels, m.mate i = q.mate i)
    (h : t.Fits m) : t.Fits q := by
  cases t with
  | leaf a b => exact (eq a (by simp [labels])).symm.trans h
  | handle a b c d => exact ⟨(eq a (by simp [labels])).symm.trans h.1,
      (eq b (by simp [labels])).symm.trans h.2⟩
end Tile

def word (ts : List (Tile α)) := ts.flatMap Tile.labels
def handles (ts : List (Tile α)) := (ts.map Tile.weight).sum
def FitsAll (m : Matching α) (ts : List (Tile α)) := ∀ t ∈ ts, t.Fits m

@[simp] theorem word_append (a b : List (Tile α)) : word (a++b) = word a ++ word b := by
  simp [word]
@[simp] theorem handles_append (a b : List (Tile α)) : handles (a++b) = handles a + handles b := by
  induction a with
  | nil => simp [handles]
  | cons t a ih => simpa [handles,Nat.add_assoc] using congrArg (t.weight + ·) ih
@[simp] theorem word_map (e : α → β) (ts : List (Tile α)) :
    word (ts.map (Tile.map e)) = (word ts).map e := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simpa [word] using congrArg (fun l => t.labels.map e ++ l) ih
@[simp] theorem handles_map (e : α → β) (ts : List (Tile α)) :
    handles (ts.map (Tile.map e)) = handles ts := by simp [handles,List.map_map,Function.comp_def]
theorem length_word (ts : List (Tile α)) : (word ts).length = 2 * ts.length + 2 * handles ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t <;> simp [word,Tile.labels,handles,Tile.weight] at * <;> omega

theorem fits_append {m : Matching α} {a b : List (Tile α)} :
    FitsAll m (a++b) ↔ FitsAll m a ∧ FitsAll m b := by simp [FitsAll]; grind

theorem fits_map_of_on {m : Matching α} {q : Matching β} (e : β → α)
    (eq : ∀ i, m.mate (e i) = e (q.mate i)) {ts : List (Tile β)} (h : FitsAll q ts) :
    FitsAll m (ts.map (Tile.map e)) := by
  intro t ht
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
  have H := h j hj
  cases j <;> simp_all [Tile.map,Tile.Fits,eq]

theorem on_unique_from_tiles {α β : Type} {m : Matching α} {p : Matching β} {ts : List (Tile β)}
    (e : β → α) (all : ∀ i, i ∈ word ts) (hp : FitsAll p ts)
    (hm : FitsAll m (ts.map (Tile.map e))) : ∀ i, m.mate (e i) = e (p.mate i) := by
  intro i
  obtain ⟨t,ht,hi⟩ := List.mem_flatMap.mp (all i)
  have h := hp t ht
  have h' := hm (t.map e) (List.mem_map.mpr ⟨t,ht,rfl⟩)
  cases t with
  | leaf a b =>
    simp [Tile.labels] at hi
    have H : p.mate a = b := h
    have H' : m.mate (e a) = e b := h'
    rcases hi with rfl | rfl
    · rw [H,H']
    · rw [← H',m.inv,← H,p.inv]
  | handle a b c d =>
    simp [Tile.labels] at hi
    obtain ⟨H,J⟩ := h
    obtain ⟨H',J'⟩ := h'
    change m.mate (e a) = e c at H'
    change m.mate (e b) = e d at J'
    rcases hi with rfl | rfl | rfl | rfl
    · rw [H]; exact H'
    · rw [J]; exact J'
    · rw [← H',m.inv,← H,p.inv]
    · rw [← J',m.inv,← J,p.inv]

/-- Concrete matching from a list of disjoint tiles on a bounded patch. -/
def lookTile [DecidableEq α] (i : α) : Tile α → Option α
  | .leaf a b => if i=a then some b else if i=b then some a else none
  | .handle a b c d => if i=a then some c else if i=c then some a else
      if i=b then some d else if i=d then some b else none

def tileMate [DecidableEq α] (ts : List (Tile α)) (i : α) :=
  (ts.findSome? (lookTile i)).getD i

def concrete {n : Nat} (ts : List (Tile (Fin n)))
    (inv : ∀ i, tileMate ts (tileMate ts i) = i)
    (free : ∀ i, tileMate ts i ≠ i) : Matching (Fin n) := ⟨tileMate ts,inv,free⟩

def moves [DecidableEq α] (m : Matching α) : List (α × α) → Matching α
  | [] => m
  | (a,b)::rest => moves (m.switch a b) rest
def passes [DecidableEq α] (s : α → α) (l : List α) (m : Matching α) : List (α × α) → Bool
  | [] => true
  | (a,b)::rest => a != b && m.mate a != b &&
      vertices s m l == vertices s (m.switch a b) l && passes s l (m.switch a b) rest

theorem passes_walk [DecidableEq α] {s : α → α} {l : List α} (m : Matching α)
    (sw : List (α × α)) (H : passes s l m sw = true) :
    Walk s l m (moves m sw) sw.length := by
  induction sw generalizing m with
  | nil => exact .nil _
  | cons ab rest ih =>
    obtain ⟨a,b⟩ := ab
    simp only [passes,Bool.and_eq_true,bne_iff_ne,beq_iff_eq] at H
    exact .cons ⟨a,b,H.1.1.1,H.1.1.2,rfl,H.1.2⟩ (ih _ H.2)

instance fitsDec [DecidableEq α] (m : Matching α) (t : Tile α) : Decidable (t.Fits m) := by
  cases t <;> unfold Tile.Fits <;> infer_instance
instance fitsAllDec [DecidableEq α] (m : Matching α) (ts : List (Tile α)) : Decidable (FitsAll m ts) :=
  inferInstanceAs (Decidable (∀ t ∈ ts, t.Fits m))

end OddDiameter


/-! ## Repair -/
set_option grind.warning false
namespace OddDiameter

structure Blueprint (n : Nat) (ts : List (Tile (Fin n))) (i : Fin n) where
  pre : List (Fin n)
  v : Fin n
  x : Fin n
  y : Fin n
  post : List (Fin n)
  rem : List (Tile (Fin n))
  word_eq : word ts = pre ++ [i,v,x,y] ++ post
  full : word ts = List.finRange n
  rem_eq : word rem = pre ++ post
  len_eq : rem.length + 1 = ts.length
  genus_eq : handles rem + 1 = handles ts
  initial : Matching (Fin n)
  finalM : Matching (Fin n)
  length : Nat
  bound : length ≤ 12
  path : Walk successor (List.finRange n) initial finalM length
  start : FitsAll initial ts
  finish : FitsAll finalM (.handle i v x y :: rem)

/-- A repaired target. In its linear word the four specified sides are consecutive.
The remaining tiles occur in polygon order after these four positions are deleted. -/
structure Repair (s : α → α) [DecidableEq α] (ts : List (Tile α)) (m : Matching α)
    (i : α) where
  pre : List α
  v : α
  x : α
  y : α
  post : List α
  rem : List (Tile α)
  target : Matching α
  length : Nat
  bound : length ≤ 12
  word_eq : word ts = pre ++ [i,v,x,y] ++ post
  rem_eq : word rem = pre ++ post
  len_eq : rem.length + 1 = ts.length
  genus_eq : handles rem + 1 = handles ts
  path : Walk s (word ts) m target length
  handle : (Tile.handle i v x y).Fits target
  finish : FitsAll target rem

noncomputable def realize [DecidableEq α] {n : Nat} {ts : List (Tile (Fin n))} {i : Fin n}
    (p : Blueprint n ts i) (e : Fin n → α) (tail : List (Tile α))
    (s : α → α) (m : Matching α)
    (hen : Enum (word (ts.map (Tile.map e) ++ tail)))
    (circ : Circular s (word (ts.map (Tile.map e) ++ tail)))
    (fits : FitsAll m (ts.map (Tile.map e) ++ tail)) :
    Nonempty (Repair s (ts.map (Tile.map e) ++ tail) m (e i)) := by
  have wordFull : word (ts.map (Tile.map e) ++ tail) = (List.finRange n).map e ++ word tail := by
    simp [p.full]
  obtain ⟨fi,ft⟩ := fits_append.mp fits
  have all (j : Fin n) : j ∈ word ts := p.full ▸ (fin_enum n).all j
  obtain ⟨m',w,eq,off⟩ := patch_named e (Nat.zero_lt_of_lt i.isLt) (wordFull ▸ hen)
    (wordFull ▸ circ) m (on_unique_from_tiles e all p.start fi) p.path
  have fin := fits_map_of_on e eq p.finish
  refine ⟨⟨p.pre.map e, e p.v, e p.x, e p.y, p.post.map e ++ word tail,
    p.rem.map (Tile.map e) ++ tail, m', p.length, p.bound, ?_, ?_, ?_, ?_,
    wordFull ▸ w, ?_, ?_⟩⟩
  · simp [p.word_eq,List.append_assoc]
  · simp [p.rem_eq,List.append_assoc]
  · simp; have := p.len_eq; omega
  · simp; have := p.genus_eq; omega
  · exact fin _ (.head _)
  · apply fits_append.mpr
    refine ⟨fun t ht => fin t (.tail _ ht),?_⟩
    intro t ht
    exact Tile.fits_congr (fun i hi => (off i (List.mem_flatMap.mpr ⟨t,ht,hi⟩)).symm) (ft t ht)

def certifiedPlan {n : Nat} (ts : List (Tile (Fin n))) (i : Fin n)
    (pre : List (Fin n)) (v x y : Fin n) (post : List (Fin n)) (rem : List (Tile (Fin n)))
    (sw : List (Fin n × Fin n))
    (inv : ∀ j, tileMate ts (tileMate ts j) = j := by decide)
    (free : ∀ j, tileMate ts j ≠ j := by decide)
    (w : word ts = pre ++ [i,v,x,y] ++ post := by decide)
    (full : word ts = List.finRange n := by decide)
    (rest : word rem = pre ++ post := by decide)
    (len : rem.length + 1 = ts.length := by decide)
    (gen : handles rem + 1 = handles ts := by decide)
    (bound : sw.length ≤ 12 := by decide)
    (legal : passes successor (List.finRange n) (concrete ts inv free) sw = true := by decide)
    (start : FitsAll (concrete ts inv free) ts := by decide)
    (finalFits : FitsAll (moves (concrete ts inv free) sw) (.handle i v x y :: rem) := by decide) :
    Blueprint n ts i :=
  ⟨pre,v,x,y,post,rem,w,full,rest,len,gen,_,_,_,bound,passes_walk _ _ legal,start,finalFits⟩

private def tilesHHH : List (Tile (Fin 12)) := [.handle 0 1 2 3, .handle 4 5 6 7, .handle 8 9 10 11]
private def planHHH0 : Blueprint 12 tilesHHH 0 :=
  certifiedPlan _ _ [] 1 2 3 [4,5,6,7,8,9,10,11] [.handle 4 5 6 7, .handle 8 9 10 11] []
private def planHHH1 : Blueprint 12 tilesHHH 1 :=
  certifiedPlan _ _ [0] 2 3 4 [5,6,7,8,9,10,11] [.handle 0 5 6 7, .handle 8 9 10 11] [(4, 0)]
private def planHHH2 : Blueprint 12 tilesHHH 2 :=
  certifiedPlan _ _ [0,1] 3 4 5 [6,7,8,9,10,11] [.handle 0 1 6 7, .handle 8 9 10 11] [(4, 0),(5, 1)]
private def planHHH3 : Blueprint 12 tilesHHH 3 :=
  certifiedPlan _ _ [0,1,2] 4 5 6 [7,8,9,10,11] [.handle 0 1 2 7, .handle 8 9 10 11] [(5, 1)]

private theorem repairHHH [DecidableEq α] (s : α → α) (m : Matching α)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : α) (tail : List (Tile α)) (i : α)
    (hi : i ∈ [z0,z1,z2,z3])
    (en : Enum (word ([.handle z0 z1 z2 z3, .handle z4 z5 z6 z7, .handle z8 z9 z10 z11] ++ tail)))
    (circ : Circular s (word ([.handle z0 z1 z2 z3, .handle z4 z5 z6 z7, .handle z8 z9 z10 z11] ++ tail)))
    (fits : FitsAll m ([.handle z0 z1 z2 z3, .handle z4 z5 z6 z7, .handle z8 z9 z10 z11] ++ tail)) :
    Nonempty (Repair s ([.handle z0 z1 z2 z3, .handle z4 z5 z6 z7, .handle z8 z9 z10 z11] ++ tail) m i) := by
  let e : Fin 12 → α := fun j => ([z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11] : List α).get j
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact realize planHHH0 e tail s m en circ fits
  · exact realize planHHH1 e tail s m en circ fits
  · exact realize planHHH2 e tail s m en circ fits
  · exact realize planHHH3 e tail s m en circ fits

private def tilesLHH : List (Tile (Fin 10)) := [.leaf 0 1, .handle 2 3 4 5, .handle 6 7 8 9]
private def planLHH0 : Blueprint 10 tilesLHH 0 :=
  certifiedPlan _ _ [] 1 2 3 [4,5,6,7,8,9] [.leaf 4 5, .handle 6 7 8 9] [(2, 1),(4, 3)]
private def planLHH1 : Blueprint 10 tilesLHH 1 :=
  certifiedPlan _ _ [0] 2 3 4 [5,6,7,8,9] [.leaf 0 5, .handle 6 7 8 9] [(3, 0)]

private theorem repairLHH [DecidableEq α] (s : α → α) (m : Matching α)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : α) (tail : List (Tile α)) (i : α)
    (hi : i ∈ [z0,z1])
    (en : Enum (word ([.leaf z0 z1, .handle z2 z3 z4 z5, .handle z6 z7 z8 z9] ++ tail)))
    (circ : Circular s (word ([.leaf z0 z1, .handle z2 z3 z4 z5, .handle z6 z7 z8 z9] ++ tail)))
    (fits : FitsAll m ([.leaf z0 z1, .handle z2 z3 z4 z5, .handle z6 z7 z8 z9] ++ tail)) :
    Nonempty (Repair s ([.leaf z0 z1, .handle z2 z3 z4 z5, .handle z6 z7 z8 z9] ++ tail) m i) := by
  let e : Fin 10 → α := fun j => ([z0,z1,z2,z3,z4,z5,z6,z7,z8,z9] : List α).get j
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl
  · exact realize planLHH0 e tail s m en circ fits
  · exact realize planLHH1 e tail s m en circ fits

private def tilesHLH : List (Tile (Fin 10)) := [.handle 0 1 2 3, .leaf 4 5, .handle 6 7 8 9]
private def planHLH0 : Blueprint 10 tilesHLH 0 :=
  certifiedPlan _ _ [] 1 2 3 [4,5,6,7,8,9] [.leaf 4 5, .handle 6 7 8 9] []
private def planHLH1 : Blueprint 10 tilesHLH 1 :=
  certifiedPlan _ _ [0] 2 3 4 [5,6,7,8,9] [.leaf 0 5, .handle 6 7 8 9] [(4, 0)]
private def planHLH2 : Blueprint 10 tilesHLH 2 :=
  certifiedPlan _ _ [0,1] 3 4 5 [6,7,8,9] [.leaf 0 1, .handle 6 7 8 9] [(4, 0),(3, 0)]
private def planHLH3 : Blueprint 10 tilesHLH 3 :=
  certifiedPlan _ _ [0,1,2] 4 5 6 [7,8,9] [.leaf 0 1, .handle 2 7 8 9] [(4, 0),(3, 0),(6, 2)]

private theorem repairHLH [DecidableEq α] (s : α → α) (m : Matching α)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : α) (tail : List (Tile α)) (i : α)
    (hi : i ∈ [z0,z1,z2,z3])
    (en : Enum (word ([.handle z0 z1 z2 z3, .leaf z4 z5, .handle z6 z7 z8 z9] ++ tail)))
    (circ : Circular s (word ([.handle z0 z1 z2 z3, .leaf z4 z5, .handle z6 z7 z8 z9] ++ tail)))
    (fits : FitsAll m ([.handle z0 z1 z2 z3, .leaf z4 z5, .handle z6 z7 z8 z9] ++ tail)) :
    Nonempty (Repair s ([.handle z0 z1 z2 z3, .leaf z4 z5, .handle z6 z7 z8 z9] ++ tail) m i) := by
  let e : Fin 10 → α := fun j => ([z0,z1,z2,z3,z4,z5,z6,z7,z8,z9] : List α).get j
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact realize planHLH0 e tail s m en circ fits
  · exact realize planHLH1 e tail s m en circ fits
  · exact realize planHLH2 e tail s m en circ fits
  · exact realize planHLH3 e tail s m en circ fits

private def tilesHHL : List (Tile (Fin 10)) := [.handle 0 1 2 3, .handle 4 5 6 7, .leaf 8 9]
private def planHHL0 : Blueprint 10 tilesHHL 0 :=
  certifiedPlan _ _ [] 1 2 3 [4,5,6,7,8,9] [.handle 4 5 6 7, .leaf 8 9] []
private def planHHL1 : Blueprint 10 tilesHHL 1 :=
  certifiedPlan _ _ [0] 2 3 4 [5,6,7,8,9] [.handle 0 5 6 7, .leaf 8 9] [(4, 0)]
private def planHHL2 : Blueprint 10 tilesHHL 2 :=
  certifiedPlan _ _ [0,1] 3 4 5 [6,7,8,9] [.handle 0 1 6 7, .leaf 8 9] [(4, 0),(5, 1)]
private def planHHL3 : Blueprint 10 tilesHHL 3 :=
  certifiedPlan _ _ [0,1,2] 4 5 6 [7,8,9] [.handle 0 1 2 7, .leaf 8 9] [(5, 1)]

private theorem repairHHL [DecidableEq α] (s : α → α) (m : Matching α)
    (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : α) (tail : List (Tile α)) (i : α)
    (hi : i ∈ [z0,z1,z2,z3])
    (en : Enum (word ([.handle z0 z1 z2 z3, .handle z4 z5 z6 z7, .leaf z8 z9] ++ tail)))
    (circ : Circular s (word ([.handle z0 z1 z2 z3, .handle z4 z5 z6 z7, .leaf z8 z9] ++ tail)))
    (fits : FitsAll m ([.handle z0 z1 z2 z3, .handle z4 z5 z6 z7, .leaf z8 z9] ++ tail)) :
    Nonempty (Repair s ([.handle z0 z1 z2 z3, .handle z4 z5 z6 z7, .leaf z8 z9] ++ tail) m i) := by
  let e : Fin 10 → α := fun j => ([z0,z1,z2,z3,z4,z5,z6,z7,z8,z9] : List α).get j
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact realize planHHL0 e tail s m en circ fits
  · exact realize planHHL1 e tail s m en circ fits
  · exact realize planHHL2 e tail s m en circ fits
  · exact realize planHHL3 e tail s m en circ fits

theorem handles_le (ts : List (Tile α)) : handles ts ≤ ts.length := by
  induction ts with
  | nil => exact Nat.le_refl 0
  | cons t ts ih => cases t <;> simp [handles,Tile.weight] at * <;> omega

theorem repair_three [DecidableEq α] (s : α → α) (m : Matching α) (t₁ t₂ t₃ : Tile α)
    (tail : List (Tile α)) (i : α) (hi : i ∈ t₁.labels)
    (oneLeaf : (t₁::t₂::t₃::tail).length = handles (t₁::t₂::t₃::tail) + 1)
    (en : Enum (word (t₁::t₂::t₃::tail))) (circ : Circular s (word (t₁::t₂::t₃::tail)))
    (fits : FitsAll m (t₁::t₂::t₃::tail)) : Nonempty (Repair s (t₁::t₂::t₃::tail) m i) := by
  have H := handles_le tail
  cases t₁ <;> cases t₂ <;> cases t₃ <;>
    first | exact repairHHH s m _ _ _ _ _ _ _ _ _ _ _ _ tail i hi en circ fits
          | exact repairLHH s m _ _ _ _ _ _ _ _ _ _ tail i hi en circ fits
          | exact repairHLH s m _ _ _ _ _ _ _ _ _ _ tail i hi en circ fits
          | exact repairHHL s m _ _ _ _ _ _ _ _ _ _ tail i hi en circ fits
          | (simp only [List.length_cons,handles,List.map_cons,Tile.weight,List.sum_cons] at oneLeaf H; omega)

end OddDiameter


/-! ## BaseCases -/
set_option grind.warning false
namespace OddDiameter

theorem Legal.symm [DecidableEq α] {s : α → α} {l : List α} {m q : Matching α} (h : Legal s l m q) :
    Legal s l q m := by
  obtain ⟨a,b,ne,diff,rfl,h⟩ := h
  refine ⟨a,b,ne,?_,?_,h.symm⟩
  · have notA : m.mate b ≠ a := fun H => diff ((m.inv b).symm.trans (congrArg m.mate H) |>.symm)
    simp [Matching.switch,exchange,notA,m.free b]
  · apply Matching.ext; intro i; simp [Matching.switch]

theorem Walk.reverse [DecidableEq α] {s : α → α} {l : List α} {m q : Matching α} {k}
    (w : Walk s l m q k) : Walk s l q m k := by
  induction w with
  | nil => exact .nil _
  | cons h _ ih => exact ih.append (.cons h.symm (.nil _))

theorem finiteSix (i : Fin 6) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by
  have H := (fin_enum 6).all i
  change i ∈ [0,1,2,3,4,5] at H
  simpa using H

private def originTiles : List (Tile (Fin 6)) := [.handle 0 1 2 3,.leaf 4 5]
def origin6 := concrete originTiles (by decide) (by decide)

theorem base_six (m : Matching (Fin 6)) (hc : vertices successor m (List.finRange 6) = 2) :
    ∃ k, k ≤ 5 ∧ Walk successor (List.finRange 6) m origin6 k := by
  rcases finiteSix (m.mate 0) with h0|h0|h0|h0|h0|h0
  · exact False.elim (m.free 0 h0)
  · have h1 : m.mate 1 = 0 := (congrArg m.mate h0).symm.trans (m.inv _)
    rcases finiteSix (m.mate 2) with h2|h2|h2|h2|h2|h2
    · have bad := m.inj (h2.trans h1.symm)
      exact False.elim ((by decide : (2 : Fin 6) ≠ 1) bad)
    · have bad := m.inj (h2.trans h0.symm)
      exact False.elim ((by decide : (2 : Fin 6) ≠ 0) bad)
    · exact False.elim (m.free 2 h2)
    · have h3 : m.mate 3 = 2 := (congrArg m.mate h2).symm.trans (m.inv _)
      rcases finiteSix (m.mate 4) with h4|h4|h4|h4|h4|h4
      · have bad := m.inj (h4.trans h1.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 1) bad)
      · have bad := m.inj (h4.trans h0.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 0) bad)
      · have bad := m.inj (h4.trans h3.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 3) bad)
      · have bad := m.inj (h4.trans h2.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 2) bad)
      · exact False.elim (m.free 4 h4)
      · have h5 : m.mate 5 = 4 := (congrArg m.mate h4).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 1, .leaf 2 3, .leaf 4 5]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        exact False.elim ((by decide : vertices successor t (List.finRange 6) ≠ 2) hc)
    · have h4 : m.mate 4 = 2 := (congrArg m.mate h2).symm.trans (m.inv _)
      rcases finiteSix (m.mate 3) with h3|h3|h3|h3|h3|h3
      · have bad := m.inj (h3.trans h1.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 1) bad)
      · have bad := m.inj (h3.trans h0.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 0) bad)
      · have bad := m.inj (h3.trans h4.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 4) bad)
      · exact False.elim (m.free 3 h3)
      · have bad := m.inj (h3.trans h2.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 2) bad)
      · have h5 : m.mate 5 = 3 := (congrArg m.mate h3).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 1, .leaf 2 4, .leaf 3 5]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        let sw : List (Fin 6 × Fin 6) := [(3, 0),(4, 0)]
        have w := passes_walk t sw (by decide : passes successor (List.finRange 6) t sw = true)
        have eq : moves t sw = origin6 := Matching.ext (by decide)
        exact ⟨_,by decide,eq ▸ w⟩
    · have h5 : m.mate 5 = 2 := (congrArg m.mate h2).symm.trans (m.inv _)
      rcases finiteSix (m.mate 3) with h3|h3|h3|h3|h3|h3
      · have bad := m.inj (h3.trans h1.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 1) bad)
      · have bad := m.inj (h3.trans h0.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 0) bad)
      · have bad := m.inj (h3.trans h5.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 5) bad)
      · exact False.elim (m.free 3 h3)
      · have h4 : m.mate 4 = 3 := (congrArg m.mate h3).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 1, .leaf 2 5, .leaf 3 4]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        exact False.elim ((by decide : vertices successor t (List.finRange 6) ≠ 2) hc)
      · have bad := m.inj (h3.trans h2.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 2) bad)
  · have h2 : m.mate 2 = 0 := (congrArg m.mate h0).symm.trans (m.inv _)
    rcases finiteSix (m.mate 1) with h1|h1|h1|h1|h1|h1
    · have bad := m.inj (h1.trans h2.symm)
      exact False.elim ((by decide : (1 : Fin 6) ≠ 2) bad)
    · exact False.elim (m.free 1 h1)
    · have bad := m.inj (h1.trans h0.symm)
      exact False.elim ((by decide : (1 : Fin 6) ≠ 0) bad)
    · have h3 : m.mate 3 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 4) with h4|h4|h4|h4|h4|h4
      · have bad := m.inj (h4.trans h2.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 2) bad)
      · have bad := m.inj (h4.trans h3.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 3) bad)
      · have bad := m.inj (h4.trans h0.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 0) bad)
      · have bad := m.inj (h4.trans h1.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 1) bad)
      · exact False.elim (m.free 4 h4)
      · have h5 : m.mate 5 = 4 := (congrArg m.mate h4).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 2, .leaf 1 3, .leaf 4 5]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        let sw : List (Fin 6 × Fin 6) := []
        have w := passes_walk t sw (by decide : passes successor (List.finRange 6) t sw = true)
        have eq : moves t sw = origin6 := Matching.ext (by decide)
        exact ⟨_,by decide,eq ▸ w⟩
    · have h4 : m.mate 4 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 3) with h3|h3|h3|h3|h3|h3
      · have bad := m.inj (h3.trans h2.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 2) bad)
      · have bad := m.inj (h3.trans h4.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 4) bad)
      · have bad := m.inj (h3.trans h0.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 0) bad)
      · exact False.elim (m.free 3 h3)
      · have bad := m.inj (h3.trans h1.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 1) bad)
      · have h5 : m.mate 5 = 3 := (congrArg m.mate h3).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 2, .leaf 1 4, .leaf 3 5]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        let sw : List (Fin 6 × Fin 6) := [(4, 3)]
        have w := passes_walk t sw (by decide : passes successor (List.finRange 6) t sw = true)
        have eq : moves t sw = origin6 := Matching.ext (by decide)
        exact ⟨_,by decide,eq ▸ w⟩
    · have h5 : m.mate 5 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 3) with h3|h3|h3|h3|h3|h3
      · have bad := m.inj (h3.trans h2.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 2) bad)
      · have bad := m.inj (h3.trans h5.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 5) bad)
      · have bad := m.inj (h3.trans h0.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 0) bad)
      · exact False.elim (m.free 3 h3)
      · have h4 : m.mate 4 = 3 := (congrArg m.mate h3).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 2, .leaf 1 5, .leaf 3 4]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        let sw : List (Fin 6 × Fin 6) := [(4, 1)]
        have w := passes_walk t sw (by decide : passes successor (List.finRange 6) t sw = true)
        have eq : moves t sw = origin6 := Matching.ext (by decide)
        exact ⟨_,by decide,eq ▸ w⟩
      · have bad := m.inj (h3.trans h1.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 1) bad)
  · have h3 : m.mate 3 = 0 := (congrArg m.mate h0).symm.trans (m.inv _)
    rcases finiteSix (m.mate 1) with h1|h1|h1|h1|h1|h1
    · have bad := m.inj (h1.trans h3.symm)
      exact False.elim ((by decide : (1 : Fin 6) ≠ 3) bad)
    · exact False.elim (m.free 1 h1)
    · have h2 : m.mate 2 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 4) with h4|h4|h4|h4|h4|h4
      · have bad := m.inj (h4.trans h3.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 3) bad)
      · have bad := m.inj (h4.trans h2.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 2) bad)
      · have bad := m.inj (h4.trans h1.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 1) bad)
      · have bad := m.inj (h4.trans h0.symm)
        exact False.elim ((by decide : (4 : Fin 6) ≠ 0) bad)
      · exact False.elim (m.free 4 h4)
      · have h5 : m.mate 5 = 4 := (congrArg m.mate h4).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 3, .leaf 1 2, .leaf 4 5]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        exact False.elim ((by decide : vertices successor t (List.finRange 6) ≠ 2) hc)
    · have bad := m.inj (h1.trans h0.symm)
      exact False.elim ((by decide : (1 : Fin 6) ≠ 0) bad)
    · have h4 : m.mate 4 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 2) with h2|h2|h2|h2|h2|h2
      · have bad := m.inj (h2.trans h3.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 3) bad)
      · have bad := m.inj (h2.trans h4.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 4) bad)
      · exact False.elim (m.free 2 h2)
      · have bad := m.inj (h2.trans h0.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 0) bad)
      · have bad := m.inj (h2.trans h1.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 1) bad)
      · have h5 : m.mate 5 = 2 := (congrArg m.mate h2).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 3, .leaf 1 4, .leaf 2 5]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        let sw : List (Fin 6 × Fin 6) := [(1, 0),(4, 2)]
        have w := passes_walk t sw (by decide : passes successor (List.finRange 6) t sw = true)
        have eq : moves t sw = origin6 := Matching.ext (by decide)
        exact ⟨_,by decide,eq ▸ w⟩
    · have h5 : m.mate 5 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 2) with h2|h2|h2|h2|h2|h2
      · have bad := m.inj (h2.trans h3.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 3) bad)
      · have bad := m.inj (h2.trans h5.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 5) bad)
      · exact False.elim (m.free 2 h2)
      · have bad := m.inj (h2.trans h0.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 0) bad)
      · have h4 : m.mate 4 = 2 := (congrArg m.mate h2).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 3, .leaf 1 5, .leaf 2 4]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        let sw : List (Fin 6 × Fin 6) := [(1, 0),(4, 0)]
        have w := passes_walk t sw (by decide : passes successor (List.finRange 6) t sw = true)
        have eq : moves t sw = origin6 := Matching.ext (by decide)
        exact ⟨_,by decide,eq ▸ w⟩
      · have bad := m.inj (h2.trans h1.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 1) bad)
  · have h4 : m.mate 4 = 0 := (congrArg m.mate h0).symm.trans (m.inv _)
    rcases finiteSix (m.mate 1) with h1|h1|h1|h1|h1|h1
    · have bad := m.inj (h1.trans h4.symm)
      exact False.elim ((by decide : (1 : Fin 6) ≠ 4) bad)
    · exact False.elim (m.free 1 h1)
    · have h2 : m.mate 2 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 3) with h3|h3|h3|h3|h3|h3
      · have bad := m.inj (h3.trans h4.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 4) bad)
      · have bad := m.inj (h3.trans h2.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 2) bad)
      · have bad := m.inj (h3.trans h1.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 1) bad)
      · exact False.elim (m.free 3 h3)
      · have bad := m.inj (h3.trans h0.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 0) bad)
      · have h5 : m.mate 5 = 3 := (congrArg m.mate h3).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 4, .leaf 1 2, .leaf 3 5]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        let sw : List (Fin 6 × Fin 6) := [(3, 2),(4, 2)]
        have w := passes_walk t sw (by decide : passes successor (List.finRange 6) t sw = true)
        have eq : moves t sw = origin6 := Matching.ext (by decide)
        exact ⟨_,by decide,eq ▸ w⟩
    · have h3 : m.mate 3 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 2) with h2|h2|h2|h2|h2|h2
      · have bad := m.inj (h2.trans h4.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 4) bad)
      · have bad := m.inj (h2.trans h3.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 3) bad)
      · exact False.elim (m.free 2 h2)
      · have bad := m.inj (h2.trans h1.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 1) bad)
      · have bad := m.inj (h2.trans h0.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 0) bad)
      · have h5 : m.mate 5 = 2 := (congrArg m.mate h2).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 4, .leaf 1 3, .leaf 2 5]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        let sw : List (Fin 6 × Fin 6) := [(4, 2)]
        have w := passes_walk t sw (by decide : passes successor (List.finRange 6) t sw = true)
        have eq : moves t sw = origin6 := Matching.ext (by decide)
        exact ⟨_,by decide,eq ▸ w⟩
    · have bad := m.inj (h1.trans h0.symm)
      exact False.elim ((by decide : (1 : Fin 6) ≠ 0) bad)
    · have h5 : m.mate 5 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 2) with h2|h2|h2|h2|h2|h2
      · have bad := m.inj (h2.trans h4.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 4) bad)
      · have bad := m.inj (h2.trans h5.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 5) bad)
      · exact False.elim (m.free 2 h2)
      · have h3 : m.mate 3 = 2 := (congrArg m.mate h2).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 4, .leaf 1 5, .leaf 2 3]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        let sw : List (Fin 6 × Fin 6) := [(3, 0),(4, 1)]
        have w := passes_walk t sw (by decide : passes successor (List.finRange 6) t sw = true)
        have eq : moves t sw = origin6 := Matching.ext (by decide)
        exact ⟨_,by decide,eq ▸ w⟩
      · have bad := m.inj (h2.trans h0.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 0) bad)
      · have bad := m.inj (h2.trans h1.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 1) bad)
  · have h5 : m.mate 5 = 0 := (congrArg m.mate h0).symm.trans (m.inv _)
    rcases finiteSix (m.mate 1) with h1|h1|h1|h1|h1|h1
    · have bad := m.inj (h1.trans h5.symm)
      exact False.elim ((by decide : (1 : Fin 6) ≠ 5) bad)
    · exact False.elim (m.free 1 h1)
    · have h2 : m.mate 2 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 3) with h3|h3|h3|h3|h3|h3
      · have bad := m.inj (h3.trans h5.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 5) bad)
      · have bad := m.inj (h3.trans h2.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 2) bad)
      · have bad := m.inj (h3.trans h1.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 1) bad)
      · exact False.elim (m.free 3 h3)
      · have h4 : m.mate 4 = 3 := (congrArg m.mate h3).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 5, .leaf 1 2, .leaf 3 4]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        exact False.elim ((by decide : vertices successor t (List.finRange 6) ≠ 2) hc)
      · have bad := m.inj (h3.trans h0.symm)
        exact False.elim ((by decide : (3 : Fin 6) ≠ 0) bad)
    · have h3 : m.mate 3 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 2) with h2|h2|h2|h2|h2|h2
      · have bad := m.inj (h2.trans h5.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 5) bad)
      · have bad := m.inj (h2.trans h3.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 3) bad)
      · exact False.elim (m.free 2 h2)
      · have bad := m.inj (h2.trans h1.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 1) bad)
      · have h4 : m.mate 4 = 2 := (congrArg m.mate h2).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 5, .leaf 1 3, .leaf 2 4]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        let sw : List (Fin 6 × Fin 6) := [(4, 0)]
        have w := passes_walk t sw (by decide : passes successor (List.finRange 6) t sw = true)
        have eq : moves t sw = origin6 := Matching.ext (by decide)
        exact ⟨_,by decide,eq ▸ w⟩
      · have bad := m.inj (h2.trans h0.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 0) bad)
    · have h4 : m.mate 4 = 1 := (congrArg m.mate h1).symm.trans (m.inv _)
      rcases finiteSix (m.mate 2) with h2|h2|h2|h2|h2|h2
      · have bad := m.inj (h2.trans h5.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 5) bad)
      · have bad := m.inj (h2.trans h4.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 4) bad)
      · exact False.elim (m.free 2 h2)
      · have h3 : m.mate 3 = 2 := (congrArg m.mate h2).symm.trans (m.inv _)
        let t : Matching (Fin 6) := concrete ([.leaf 0 5, .leaf 1 4, .leaf 2 3]) (by decide) (by decide)
        have eq : m = t := by
          apply Matching.ext; intro i
          rcases finiteSix i with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
        subst m
        exact False.elim ((by decide : vertices successor t (List.finRange 6) ≠ 2) hc)
      · have bad := m.inj (h2.trans h1.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 1) bad)
      · have bad := m.inj (h2.trans h0.symm)
        exact False.elim ((by decide : (2 : Fin 6) ≠ 0) bad)
    · have bad := m.inj (h1.trans h0.symm)
      exact False.elim ((by decide : (1 : Fin 6) ≠ 0) bad)
end OddDiameter


/-! ## Normalize -/
set_option grind.warning false
namespace OddDiameter

theorem Walk.reorder [DecidableEq α] {s : α → α} (hs : Inj s) {l r : List α} (h : l.Perm r)
    {m q : Matching α} {k} (w : Walk s l m q k) : Walk s r m q k := by
  induction w with
  | nil => exact .nil _
  | cons edge _ ih =>
    obtain ⟨a,b,ne,diff,rfl,eq⟩ := edge
    apply Walk.cons _ ih
    refine ⟨_,_,ne,diff,rfl,?_⟩
    exact (cycles_perm h (inj_comp hs (Matching.inj _))).symm.trans (eq.trans (cycles_perm h (inj_comp hs (Matching.inj _))))

theorem Bijection.roundtrip (b : Bijection α β) (m : Matching β) :
    b.matching (b.inverse.matching m) = m := by
  apply Matching.ext; intro i; simp [Bijection.matching,Bijection.inverse,b.right]

noncomputable def sizeChart {l : List α} (he : Enum l) (hn : l.length = n) : Bijection (Fin n) α :=
  hn ▸ indexChart he

theorem size_step {l : List α} (he : Enum l) {s : α → α} (H : Circular s l)
    (hn : l.length = n) (i : Fin n) :
    s ((sizeChart he hn).to i) = (sizeChart he hn).to (successor i) := by
  subst n; exact circular_step H i

theorem base_labelled [DecidableEq α] (s : α → α) (l : List α) (he : Enum l) (H : Circular s l)
    (hn : l.length = 6) (m q : Matching α) (hm : vertices s m l = 2) (hq : vertices s q l = 2) :
    ∃ k, k ≤ 10 ∧ Walk s l m q k := by
  let b := sizeChart he hn
  have order := enum_perm he (b.enum (fin_enum 6))
  have cc (d : Matching α) := b.count (circular_inj he H) (size_step he H hn) order (b.inverse.matching d)
  simp only [Bijection.roundtrip] at cc
  obtain ⟨i,bi,wi⟩ := base_six _ ((cc m).symm.trans hm)
  obtain ⟨j,bj,wj⟩ := base_six _ ((cc q).symm.trans hq)
  have path := b.walk (circular_inj he H) (size_step he H hn) order (wi.append wj.reverse)
  exact ⟨i+j,by omega,by simpa only [Bijection.roundtrip] using path⟩

private def fourBlock : Matching (Fin 4) := concrete [.handle 0 1 2 3] (by decide) (by decide)
private theorem fourCount : vertices successor fourBlock (List.finRange 4) = 1 := by decide

theorem on_four {m : Matching α} {a b c d : α} (h : (Tile.handle a b c d).Fits m) :
    On m [a,b,c,d] fourBlock := by
  intro i
  change Fin 4 at i
  have hi := (fin_enum 4).all i
  change i ∈ [0,1,2,3] at hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl
  · exact h.1
  · exact h.2
  · exact (congrArg m.mate h.1).symm.trans (m.inv a)
  · exact (congrArg m.mate h.2).symm.trans (m.inv b)

noncomputable def posIn {α} (r : List α) (hr : 0 < r.length) (i : α) : Fin r.length := by
  classical
  exact if h : i ∈ r then Classical.choose (get_index_onto h) else zeroOf hr

theorem pos_spec {r : List α} (hr : 0 < r.length) {i : α} (hi : i ∈ r) :
    r.get (posIn r hr i) = i := by
  simp only [posIn,dif_pos hi]
  exact Classical.choose_spec (get_index_onto hi)

theorem pos_get {r : List α} (hr : 0 < r.length) (hn : r.Nodup) (i : Fin r.length) :
    posIn r hr (r.get i) = i := get_index_inj hn (pos_spec hr (List.get_mem r i))

theorem pos_word {r : List α} (hr : 0 < r.length) (hn : r.Nodup) :
    r.map (posIn r hr) = List.finRange r.length := by
  apply List.ext_getElem
  · simp
  · intro i h h'
    have hi : i < r.length := by simpa using h
    simpa using pos_get hr hn (⟨i,hi⟩ : Fin r.length)

theorem restrict_tiles {r : List α} (hr : 0 < r.length) (hn : r.Nodup)
    {m : Matching α} {p : Matching (Fin r.length)} (on : On m r p)
    {ts : List (Tile α)} (sub : ∀ i ∈ word ts, i ∈ r) (fit : FitsAll m ts) :
    FitsAll p (ts.map (Tile.map (posIn r hr))) := by
  intro t ht
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
  have okay (i : α) (hi : i ∈ b.labels) := sub i (List.mem_flatMap.mpr ⟨b,hb,hi⟩)
  have localEq (i j : α) (hi : i ∈ b.labels) (hj : j ∈ b.labels) (M : m.mate i = j) :
      p.mate (posIn r hr i) = posIn r hr j := by
    apply get_index_inj hn
    rw [← on,pos_spec hr (okay i hi),pos_spec hr (okay j hj), M]
  have F := fit b hb
  cases b with
  | leaf a b => exact localEq a b (by simp [Tile.labels]) (by simp [Tile.labels]) F
  | handle a b c d =>
    exact ⟨localEq a c (by simp [Tile.labels]) (by simp [Tile.labels]) F.1,
      localEq b d (by simp [Tile.labels]) (by simp [Tile.labels]) F.2⟩

/-- The induction statement quantifies over all label types and all representations
of the same cyclic order. There is one leaf and g handles in the target. -/
def Normal (g : Nat) := ∀ {α : Type} [DecidableEq α] (s : α → α) (ts : List (Tile α)),
    handles ts = g → ts.length = g+1 → Enum (word ts) → Circular s (word ts) →
    ∀ m q : Matching α, vertices s m (word ts) = 2 → vertices s q (word ts) = 2 →
    FitsAll q ts → ∃ k, k ≤ 16*g ∧ Walk s (word ts) m q k

theorem vertex_reorder [DecidableEq α] {s : α → α} (hs : Inj s) (m : Matching α)
    {l r : List α} (perm : l.Perm r) : vertices s m l = vertices s m r :=
  cycles_perm perm (inj_comp hs m.inj)

theorem use_repair [DecidableEq α] {s : α → α} {ts : List (Tile α)} {m q : Matching α} {i g}
    (ind : Normal g) (hg : handles ts = g+1) (hl : ts.length = g+2)
    (hen : Enum (word ts)) (circ : Circular s (word ts))
    (hm : vertices s m (word ts) = 2) (hq : vertices s q (word ts) = 2)
    (H₁ : m.mate i = s (s i)) (H₂ : m.mate (s i) = s (s (s i)))
    (fix : Repair s ts q i) :
    ∃ k, k ≤ 16*g+12 ∧ Walk s (word ts) m q k := by
  let w := [i,fix.v,fix.x,fix.y]
  let r := fix.post ++ fix.pre
  have split : word ts = fix.pre ++ (w ++ fix.post) := by simpa [List.append_assoc,w] using fix.word_eq
  have perm : (word ts).Perm (w++r) := by
    rw [split]
    exact List.perm_append_comm.trans (by simp [r,List.append_assoc])
  have hwc : Circular s (w++r) := by
    have C := circular_rotate (split ▸ circ : Circular s (fix.pre ++ (w++fix.post)))
    simpa [r,List.append_assoc] using C
  have en := hen.permute perm
  have hs := circular_inj hen circ
  have hw : w.length > 0 := by simp [w]
  have hr : 0 < r.length := by
    have L := length_word ts
    rw [split] at L
    simp only [List.length_append, w, List.length_cons,List.length_nil] at L
    simp only [r,List.length_append]; omega
  have circleCopy := hwc
  obtain ⟨_,H⟩ := circleCopy
  obtain ⟨_,R,_⟩ := (reads_append ..).mp H
  have sv : s i = fix.v := reads_first R 0 (by simp [w])
  have sx : s fix.v = fix.x := reads_first R 1 (by simp [w])
  have sy : s fix.x = fix.y := reads_first R 2 (by simp [w])
  have fitM : (Tile.handle i fix.v fix.x fix.y).Fits m := by
    exact ⟨by simpa [sv,sx] using H₁,by simpa [sv,sx,sy] using H₂⟩
  have onM := on_four fitM
  have onQ := on_four fix.handle
  have nr := (List.pairwise_append.mp en.nodup).2.1
  let M := restriction m r nr (complement_closed en onM)
  let Q := restriction fix.target r nr (complement_closed en onQ)
  have Hm : On m r M := on_restriction m r _ _
  have Hq : On fix.target r Q := on_restriction fix.target r _ _
  have cM := patch_count en hwc hw hr onM Hm
  have cQ := patch_count en hwc hw hr onQ Hq
  have cm := (vertex_reorder hs m perm).symm.trans hm
  have cq := (vertex_reorder hs fix.target perm).symm.trans (fix.path.count_eq.symm.trans hq)
  change vertices s m (w++r) + 1 = vertices successor fourBlock (List.finRange 4) + _ at cM
  change vertices s fix.target (w++r) + 1 = vertices successor fourBlock (List.finRange 4) + _ at cQ
  rw [cm,fourCount] at cM
  rw [cq,fourCount] at cQ
  let ts' := fix.rem.map (Tile.map (posIn r hr))
  have hem : (List.finRange r.length).Perm (word ts') := by
    change (List.finRange r.length).Perm (word (fix.rem.map _))
    rw [← pos_word hr nr, word_map,fix.rem_eq]
    exact List.perm_append_comm.map _
  have enc := (fin_enum _).permute hem
  have cc : Circular successor (word ts') := by
    change Circular successor (word (fix.rem.map _))
    rw [word_map,fix.rem_eq,List.map_append]
    apply circular_rotate
    rw [← List.map_append,pos_word hr nr]
    exact fin_circular hr
  have fit := restrict_tiles hr nr Hq (ts := fix.rem) (by
    intro j hj; rw [fix.rem_eq] at hj; simpa [r,List.mem_append,or_comm] using hj) fix.finish
  have eM := vertex_reorder (successor_inj _) M hem
  have eQ := vertex_reorder (successor_inj _) Q hem
  obtain ⟨k,bnd,path⟩ := ind successor ts' (by simp [ts']; have := fix.genus_eq; omega)
    (by simp [ts']; have := fix.len_eq; omega) enc cc M Q (by omega) (by omega) fit
  have per' := perm.trans List.perm_append_comm
  obtain ⟨final,path',on,off⟩ := patch_move (hen.permute per') (circular_rotate hwc) hr Hm
    (path.reorder (successor_inj _) hem.symm)
  have finalEq : final = fix.target := by
    apply Matching.ext; intro j
    rcases List.mem_append.mp (en.all j) with hwj | hrj
    · obtain ⟨a,rfl⟩ := get_index_onto hwj
      exact (off _ (List.get_mem w a)).trans ((onM a).trans (onQ a).symm)
    · obtain ⟨a,rfl⟩ := get_index_onto hrj
      exact (on a).trans (Hq a).symm
  rw [finalEq] at path'
  exact ⟨k+fix.length,by have := fix.bound; omega,(path'.reorder hs per'.symm).append fix.path.reverse⟩

theorem repair_at_start [DecidableEq α] {s : α → α} {m : Matching α} {t : Tile α}
    {ts : List (Tile α)} {i : α} (hi : i ∈ t.labels) (len : 2 ≤ ts.length)
    (one : (t::ts).length = handles (t::ts) + 1)
    (en : Enum (word (t::ts))) (circ : Circular s (word (t::ts))) (fits : FitsAll m (t::ts)) :
    Nonempty (Repair s (t::ts) m i) := by
  cases ts with
  | nil => simp at len
  | cons b ts =>
    cases ts with
    | nil => simp at len
    | cons c rest => exact repair_three s m t b c rest i hi one en circ fits

theorem normal_step {g : Nat} (hgpos : 0 < g) (ind : Normal g) : Normal (g+1) := by
  intro α _ s ts hg hl en circ m q hm hq fits
  let l := word ts
  have len : 4 ≤ l.length := by have h := length_word ts; dsimp [l]; omega
  have hs := circular_inj en circ
  have hd (i : α) {a b : Four} (eq : fourSites s i a = fourSites s i b) : a = b := by
    obtain ⟨j,rfl⟩ := get_index_onto (en.all i)
    have H (z : Four) : fourSites s (l.get j) z = l.get (fourSites successor j z) := by
      cases z <;> simp only [fourSites,l,circular_step circ]
    rw [H,H] at eq
    exact four_distinct len j (get_index_inj en.nodup eq)
  obtain ⟨m',k,i,bnd,path,H₁,H₂⟩ := extraction s hs (circular_conn en circ) l en m
    (l.get ⟨0,by omega⟩) hm hd
  obtain ⟨t,ht,hi⟩ := List.mem_flatMap.mp (en.all i)
  obtain ⟨pre,post,split⟩ := List.append_of_mem ht
  let rest := post ++ pre
  have rot : (word ts).Perm (word (t::rest)) := by
    rw [split,word_append]
    exact List.perm_append_comm.trans (by simp [word,rest,List.append_assoc])
  have c' : Circular s (word (t::rest)) := by
    have rr : Circular s (word pre ++ word (t::post)) := by simpa [split,word_append] using circ
    simpa [word,rest,List.append_assoc] using circular_rotate rr
  have hf' : FitsAll q (t::rest) := by
    intro u hu; apply fits u; rw [split]
    simp [rest,List.mem_append] at hu ⊢; grind
  have hg' : handles (t::rest) = g+1 := by
    rw [split,handles_append] at hg
    change t.weight + handles (post++pre) = g+1
    rw [handles_append]
    change handles pre + (t.weight + handles post) = g+1 at hg
    omega
  have hl' : (t::rest).length = g+2 := by
    rw [split] at hl
    simp only [List.length_append,List.length_cons,rest] at hl ⊢
    omega
  obtain ⟨fix⟩ := repair_at_start hi (by simp at hl'; omega) (by omega) (en.permute rot) c' hf'
  obtain ⟨j,bd,w⟩ := use_repair ind hg' hl' (en.permute rot) c'
    ((vertex_reorder hs m' rot).symm.trans (path.count_eq.symm.trans hm))
    ((vertex_reorder hs q rot).symm.trans hq) H₁ H₂ fix
  exact ⟨k+j,by omega,path.append (w.reorder hs rot.symm)⟩

theorem normal_positive : ∀ g, Normal (g+1) := by
  intro g
  induction g with
  | zero =>
    intro α _ s ts hg hl en circ m q hm hq _
    have len := length_word ts
    obtain ⟨k,bd,w⟩ := base_labelled s _ en circ (by omega) m q hm hq
    exact ⟨k,by omega,w⟩
  | succ g ih => exact normal_step (by omega) ih

end OddDiameter


/-! ## Semantics -/
set_option grind.warning false
namespace OddDiameter

/-- The computed number of cycles is the cardinality of a set of orbit
representatives: exactly one representative per connected component of the
vertex permutation, the graph whose arrows are the polygon's identifications. -/
theorem orbit_representatives [DecidableEq α] {f : α → α} (hf : Inj f) {l : List α}
    (nodup : l.Nodup) (closed : ∀ i ∈ l, f i ∈ l) :
    ∃ reps : List α, reps.length = cycles f l ∧ (∀ i ∈ reps, i ∈ l) ∧
      reps.Pairwise (fun i j => ¬Conn f i j) ∧ ∀ i ∈ l, ∃ j ∈ reps, Conn f i j := by
  induction l generalizing f with
  | nil => exact ⟨[],rfl,by simp,by simp,by simp⟩
  | cons a l ih =>
    obtain ⟨notMem,nd⟩ := List.nodup_cons.mp nodup
    have ne (i : α) (hi : i ∈ l) : i ≠ a := fun eq => notMem (eq ▸ hi)
    have rest (i : α) (hi : i ∈ l) : cut f a i ∈ l := by
      have inc := closed i (.tail _ hi)
      by_cases h : f i = a
      · have notFixed : f a ≠ a := fun e => ne i hi (hf (h.trans e.symm))
        simpa [cut,ne i hi,h] using (List.mem_cons.mp (closed a (.head _))).resolve_left notFixed
      · simpa [cut,ne i hi,h] using (List.mem_cons.mp inc).resolve_left h
    obtain ⟨reps,len,sub,apart,cover⟩ := ih (cut_inj hf a) nd rest
    have unchanged : reps.Pairwise (fun i j => ¬Conn f i j) := by
      apply apart.imp_of_mem
      intro i j hi hj h c
      exact h (conn_cut_fwd (ne i (sub i hi)) (ne j (sub j hj)) c)
    have hit (i : α) (hi : i ∈ l) : ∃ j ∈ reps, Conn f i j := by
      obtain ⟨j,hj,c⟩ := cover i hi
      exact ⟨j,hj,conn_cut_back c⟩
    by_cases h : f a = a
    · refine ⟨a::reps,by simp [cycles,h,len,Nat.add_comm],?_,?_,?_⟩
      · intro i hi; rcases List.mem_cons.mp hi with rfl|hb
        · simp
        · exact .tail _ (sub i hb)
      · apply List.pairwise_cons.mpr
        exact ⟨fun b hb c => ne b (sub b hb) (c.isolated hf h).symm,unchanged⟩
      · intro i hi; rcases List.mem_cons.mp hi with rfl|hi
        · exact ⟨_,.head _,.refl _⟩
        · obtain ⟨j,hj,c⟩ := hit i hi; exact ⟨j,.tail _ hj,c⟩
    · refine ⟨reps,by simp [cycles,h,len],fun i hi => .tail _ (sub i hi),unchanged,?_⟩
      intro i hi; rcases List.mem_cons.mp hi with rfl|hi
      · obtain ⟨j,hj,c⟩ := hit _ ((List.mem_cons.mp (closed i (.head _))).resolve_left h)
        exact ⟨j,hj,(Conn.step _).trans c⟩
      · exact hit i hi

/-- Exactly the two alternative perfect matchings on four endpoints of two old
chords, with all chords outside these endpoints kept. -/
def PaperSwap (m q : Matching α) : Prop :=
  ∃ a b c d, m.mate a = b ∧ m.mate c = d ∧ a ≠ c ∧ b ≠ c ∧
    ((q.mate a = c ∧ q.mate b = d) ∨ (q.mate a = d ∧ q.mate b = c)) ∧
    ∀ z, z ≠ a → z ≠ b → z ≠ c → z ≠ d → q.mate z = m.mate z

theorem switch_off [DecidableEq α] (m : Matching α) (a b z : α) (za : z ≠ a) (zb : z ≠ b)
    (zc : z ≠ m.mate a) (zd : z ≠ m.mate b) : (m.switch a b).mate z = m.mate z := by
  have h (i : α) (hy : z ≠ m.mate i) : m.mate z ≠ i := fun eq =>
    hy ((m.inv z).symm.trans (congrArg m.mate eq))
  simp [Matching.switch,exchange,za,zb,h _ zc,h _ zd]

theorem switch_paper [DecidableEq α] (m : Matching α) {a c : α} (ne : a ≠ c) (diff : m.mate a ≠ c) :
    PaperSwap m (m.switch a c) := by
  have h' : m.mate c ≠ a := fun eq => diff ((m.inv c).symm.trans (congrArg m.mate eq) |>.symm)
  refine ⟨a,m.mate a,c,m.mate c,rfl,rfl,ne,diff,.inr ⟨?_,?_⟩,?_⟩
  · simp [Matching.switch,exchange,h',m.free c]
  · simp [Matching.switch,exchange,m.free a,diff,m.inv]
  · intro z za zb zc zd; exact switch_off m a c z za zc zb zd

theorem paper_switch [DecidableEq α] {m q : Matching α} (h : PaperSwap m q) :
    ∃ a b, a ≠ b ∧ m.mate a ≠ b ∧ q = m.switch a b := by
  obtain ⟨a,b,c,d,hab,hcd,ne,diff,alt,off⟩ := h
  have ba : m.mate b = a := (congrArg m.mate hab).symm.trans (m.inv a)
  have dc : m.mate d = c := (congrArg m.mate hcd).symm.trans (m.inv c)
  have H₁ := m.free a; have H₂ := m.free c
  have H₃ := (fun (e : m.mate a = m.mate c) => m.inj e)
  have H₄ := (fun (e : m.mate a = m.mate d) => m.inj e)
  have H₅ := (fun (e : m.mate b = m.mate c) => m.inj e)
  rcases alt with ⟨ac,bd⟩|⟨ad,bc⟩
  · refine ⟨a,d,by grind,by grind,?_⟩
    have ca := (congrArg q.mate ac).symm.trans (q.inv a)
    have db := (congrArg q.mate bd).symm.trans (q.inv b)
    apply Matching.ext; intro z
    by_cases A : z = a <;> by_cases B : z = b <;> by_cases C : z = c <;> by_cases D : z = d
    all_goals first | (rw [off z A B C D]; apply Eq.symm; apply switch_off <;> grind) | (simp only [Matching.switch,exchange]; grind)
  · refine ⟨a,c,ne,by grind,?_⟩
    have da := (congrArg q.mate ad).symm.trans (q.inv a)
    have cb := (congrArg q.mate bc).symm.trans (q.inv b)
    apply Matching.ext; intro z
    by_cases A : z = a <;> by_cases B : z = b <;> by_cases C : z = c <;> by_cases D : z = d
    all_goals first | (rw [off z A B C D]; apply Eq.symm; apply switch_off <;> grind) | (simp only [Matching.switch,exchange]; grind)

theorem legal_iff_paper [DecidableEq α] {s : α → α} {m q : Matching α} {l : List α} :
    Legal s l m q ↔ PaperSwap m q ∧ vertices s m l = vertices s q l := by
  constructor
  · rintro ⟨a,b,ne,diff,rfl,eq⟩; exact ⟨switch_paper m ne diff,eq⟩
  · rintro ⟨h,eq⟩; obtain ⟨a,b,ne,diff,rfl⟩ := paper_switch h
    exact ⟨a,b,ne,diff,rfl,eq⟩

abbrev State (n g : Nat) := { m : Matching (Fin (2*n)) // AtGenus n g m }

/-- Walk in the paper's graph on fixed-genus states, with genuine swaps as edges. -/
inductive StateWalk {n g : Nat} : State n g → State n g → Nat → Prop
  | nil (x) : StateWalk x x 0
  | cons {x y z : State n g} : PaperSwap x.val y.val → StateWalk y z k → StateWalk x z (k+1)

theorem walk_at_genus {n g : Nat} {m q : Matching (Fin (2*n))} {k}
    (w : Walk successor (sides n) m q k) (hm : AtGenus n g m) (hq : AtGenus n g q) :
    StateWalk ⟨m,hm⟩ ⟨q,hq⟩ k := by
  induction w with
  | nil => exact .nil _
  | cons h _ ih =>
    obtain ⟨edge,eq⟩ := legal_iff_paper.mp h
    unfold AtGenus at hm
    have mid := eq ▸ hm
    exact .cons edge (ih mid hq)

theorem StateWalk.forget {n g : Nat} {m q : State n g} {k} (w : StateWalk m q k) :
    Walk successor (sides n) m.val q.val k := by
  induction w with
  | nil => exact .nil _
  | @cons k x y z h _ ih =>
    apply Walk.cons (legal_iff_paper.mpr ⟨h,?_⟩) ih
    have X := x.property; have Y := y.property
    unfold AtGenus at X Y; omega

end OddDiameter


/-! ## OddDiameter -/
set_option grind.warning false

/-! A refutation of Gross–Šarković Conjecture 2.10.
The main theorem quantifies over every two labelled involutions of genus g.
The proof uses cyclic order only to construct paths. Rotations are not edges. -/
namespace OddDiameter

private def twoM : Matching (Fin 2) := concrete [.leaf 0 1] (by decide) (by decide)
private def handM : Matching (Fin 4) := concrete [.handle 0 1 2 3] (by decide) (by decide)

theorem canonical (g : Nat) {α : Type} [DecidableEq α] (s : α → α) (l : List α)
    (en : Enum l) (circ : Circular s l) (len : l.length = 4*g+2) :
    ∃ (ts : List (Tile α)) (q : Matching α), word ts = l ∧ handles ts = g ∧
      ts.length = g+1 ∧ FitsAll q ts ∧ vertices s q l = 2 := by
  induction g generalizing α with
  | zero =>
    let b := sizeChart en len
    let ts := [Tile.leaf (b.to 0) (b.to 1)]
    have order : word ts = l := by
      have h : (List.finRange 2).map b.to = l := by
        have eq (j : Nat) (e : l.length = j) : (List.finRange j).map (sizeChart en e).to = l := by
          subst j; exact get_order l
        exact eq 2 len
      exact h
    refine ⟨ts,b.matching twoM,order,rfl,rfl,?_,?_⟩
    · intro t ht; have eq : t = Tile.leaf (b.to 0) (b.to 1) := by simpa [ts] using ht
      subst t; exact b.mate_to twoM 0
    · have E := b.count (circular_inj en circ) (size_step en circ len) (enum_perm en (b.enum (fin_enum 2))) twoM
      exact E.trans (by decide)
  | succ g ih =>
    obtain ⟨a,b,c,d,r,rfl⟩ : ∃ a b c d r, l = a::b::c::d::r := by
      cases l with
      | nil => simp at len <;> omega
      | cons a l => cases l with
        | nil => simp at len <;> omega
        | cons b l => cases l with
          | nil => simp at len <;> omega
          | cons c l => cases l with
            | nil => simp at len <;> omega
            | cons d r => exact ⟨a,b,c,d,r,rfl⟩
    let w := [a,b,c,d]
    have lr : r.length = 4*g+2 := by simp at len; omega
    have hr : 0 < r.length := by omega
    obtain ⟨ts,q,ord,hg,hl,fit,hq⟩ := ih successor (List.finRange r.length) (fin_enum _) (fin_circular hr) (by simpa using lr)
    let ix := splitChart w r en
    let M := ix.matching (sumM handM q)
    have hw : On M w handM := fun i => ix.mate_to _ (.inl i)
    have hz : On M r q := fun i => ix.mate_to _ (.inr i)
    let out := Tile.handle a b c d :: ts.map (Tile.map r.get)
    refine ⟨out,M,?_,?_,?_,?_,?_⟩
    · change [a,b,c,d] ++ word (ts.map (Tile.map r.get)) = _
      rw [word_map,ord,get_order]; rfl
    · change 1 + handles (ts.map (Tile.map r.get)) = _
      rw [handles_map,hg]; omega
    · simp [out,hl]
    · intro t ht; rcases List.mem_cons.mp ht with rfl | h
      · exact ⟨hw (0 : Fin 4),hw (1 : Fin 4)⟩
      · exact fits_map_of_on r.get hz fit t h
    · have H := patch_count (w := w) (r := r) en circ (by decide : 0 < (4 : Nat)) hr hw hz
      change vertices s M (a::b::c::d::r) + 1 =
        vertices successor handM (List.finRange 4) + vertices successor q (List.finRange r.length) at H
      have hh : vertices successor handM (List.finRange 4) = 1 := by decide
      omega

/-- Uniform path bound in the exact labelled graph on n=2g+1 chords. -/
theorem odd_diameter (g : Nat) (hg : 1 ≤ g) (m q : Matching (Fin (2*(2*g+1))))
    (hm : AtGenus (2*g+1) g m) (hq : AtGenus (2*g+1) g q) :
    ∃ k, k ≤ 32*g ∧ Walk successor (sides (2*g+1)) m q k := by
  obtain ⟨ts,t,order,handles,tiles,fit,gen⟩ := canonical g successor (sides (2*g+1))
    (fin_enum _) (fin_circular (by omega)) (by simp [sides]; omega)
  have norm : Normal g := by cases g with
    | zero => omega
    | succ g => exact normal_positive g
  have toTarget (x : Matching (Fin (2*(2*g+1)))) (hx : AtGenus (2*g+1) g x) :
      ∃ k, k ≤ 16*g ∧ Walk successor (sides (2*g+1)) x t k := by
    have W := norm successor ts handles tiles (order ▸ fin_enum _) (order ▸ fin_circular (by omega))
      x t (order ▸ odd_genus_iff.mp hx) (order ▸ gen) fit
    simpa only [order] using W
  obtain ⟨k,hk,w⟩ := toTarget m hm
  obtain ⟨j,hj,v⟩ := toTarget q hq
  exact ⟨k+j,by omega,w.append v.reverse⟩

/-- Diameter lower bound multiplied by a natural denominator K, expressed using
a pair in the same component with every legal walk between them long enough. -/
def FarPair (n g K : Nat) : Prop :=
  ∃ m q : Matching (Fin (2*n)), AtGenus n g m ∧ AtGenus n g q ∧
    (∃ k, Walk successor (sides n) m q k) ∧
    ∀ k, Walk successor (sides n) m q k → n + g*g ≤ K*k

/-- Even restricted to n>2g and with both parameters above an arbitrary
threshold, the conjectured joint lower bound fails. -/
theorem no_joint_omega :
    ¬ ∃ K N : Nat, 0 < K ∧ ∀ n g : Nat, N ≤ n → N ≤ g → 2*g < n → FarPair n g K := by
  rintro ⟨K,N,_,lower⟩
  let g := 32*K + N + 1
  obtain ⟨m,q,hm,hq,_,far⟩ := lower (2*g+1) g (by dsimp [g]; omega) (by dsimp [g]; omega) (by omega)
  obtain ⟨k,bound,walk⟩ := odd_diameter g (by dsimp [g]; omega) m q hm hq
  have lo := far k walk
  have upper := Nat.mul_le_mul_left K bound
  have eq : K * (32*g) = (32*K)*g := by rw [← Nat.mul_assoc,Nat.mul_comm K 32]
  have small : 32*K < g := by dsimp [g]; omega
  have pos : 0 < g := by omega
  have strict := Nat.mul_lt_mul_of_pos_right small pos
  omega

/-- For a connected graph the diameter is its least uniform path-length bound. -/
def Within (n g k : Nat) : Prop := ∀ m q : State n g, ∃ j, j ≤ k ∧ StateWalk m q j

def IsDiameter (n g d : Nat) : Prop := Within n g d ∧ ∀ k, Within n g k → d ≤ k

theorem odd_within (g : Nat) (hg : 0 < g) : Within (2*g+1) g (32*g) := by
  intro m q
  obtain ⟨k,b,w⟩ := odd_diameter g hg m.val q.val m.property q.property
  exact ⟨k,b,walk_at_genus w m.property q.property⟩

private theorem least_nat {P : Nat → Prop} (x : Nat) (hx : P x) :
    ∃ d, P d ∧ ∀ k, P k → d ≤ k := by
  classical
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases H : ∃ j, j < x ∧ P j
    · obtain ⟨j,lt,hj⟩ := H; exact ih j lt hj
    · exact ⟨x,hx,fun k hk => Nat.le_of_not_gt (fun lt => H ⟨k,lt,hk⟩)⟩

theorem labelled_graph_diameter_bound (g : Nat) (hg : 0 < g) :
    ∃ d, IsDiameter (2*g+1) g d ∧ d ≤ 32*g := by
  have hw := odd_within g hg
  obtain ⟨d,hd,least⟩ := least_nat _ hw
  exact ⟨d,⟨hd,least⟩,least _ hw⟩

/-- Failure of a uniform positive joint lower constant, even in the strict
connected range with both parameters tending to infinity. A positive constant
in a lower bound can always be weakened to 1/K for a positive integer K. -/
theorem no_joint_diameter_omega :
    ¬ ∃ K N : Nat, 0 < K ∧ ∀ n g d : Nat,
      N ≤ n → N ≤ g → 2*g < n → IsDiameter n g d → n+g*g ≤ K*d := by
  rintro ⟨K,N,_,lower⟩
  let g := 32*K+N+1
  have pos : 0 < g := by dsimp [g]; omega
  obtain ⟨d,hd,bd⟩ := labelled_graph_diameter_bound g pos
  have lo := lower _ _ d (by dsimp [g]; omega) (by dsimp [g]; omega) (by omega) hd
  have hi := Nat.mul_le_mul_left K bd
  have eq : K*(32*g) = (32*K)*g := by rw [← Nat.mul_assoc,Nat.mul_comm K 32]
  have strict := Nat.mul_lt_mul_of_pos_right (show 32*K < g by dsimp [g]; omega) pos
  omega

#print axioms orbit_representatives
#print axioms legal_iff_paper
#print axioms labelled_extraction
#print axioms walk_insert
#print axioms repair_three
#print axioms normal_positive
#print axioms odd_diameter
#print axioms no_joint_omega
#print axioms labelled_graph_diameter_bound
#print axioms no_joint_diameter_omega

end OddDiameter
