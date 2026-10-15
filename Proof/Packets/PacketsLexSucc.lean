import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsGlue.LexSucc

/-- One digit level: its field and its bound (read from the digits outside this level). -/
structure Level (ι : Type) where
  field : ι
  bound : (ι → ℕ) → ℕ

variable {ι : Type} [DecidableEq ι]

/-- The fields of a spec. -/
def fields (spec : List (Level ι)) : List ι := spec.map Level.field

/-- The dependent lexicographic enumeration, outermost level first. -/
def enum : List (Level ι) → (ι → ℕ) → List (ι → ℕ)
  | [], d => [d]
  | l :: ls, d => (List.range (l.bound d)).flatMap (fun v => enum ls (Function.update d l.field v))

/-- Reset every level's field to `0`. -/
def zero : List (Level ι) → (ι → ℕ) → (ι → ℕ)
  | [], d => d
  | l :: ls, d => zero ls (Function.update d l.field 0)

/-- The carry cascade: advance the innermost level that can advance, reset the levels inside it;
`none` when every level overflows. -/
def next : List (Level ι) → (ι → ℕ) → Option (ι → ℕ)
  | [], _ => none
  | l :: ls, d =>
    match next ls d with
    | some e => some e
    | none =>
      if d l.field + 1 < l.bound d then some (zero ls (Function.update d l.field (d l.field + 1)))
      else none

/-- Well-formed: distinct fields, and each bound ignores its own field and every inner field. -/
def WF : List (Level ι) → Prop
  | [] => True
  | l :: ls => l.field ∉ fields ls ∧
      (∀ d e : ι → ℕ, (∀ x, x ∉ fields (l :: ls) → d x = e x) → l.bound d = l.bound e) ∧ WF ls

/-- Every bound is positive (every inner list is nonempty). -/
def Pos (spec : List (Level ι)) : Prop := ∀ l ∈ spec, ∀ d, 0 < l.bound d

/-- The successor with an explicit past-the-end code. -/
def succD (spec : List (Level ι)) (done : ι → ℕ) (d : ι → ℕ) : ι → ℕ := (next spec d).getD done

theorem zero_congr : ∀ (spec : List (Level ι)) (d e : ι → ℕ),
    (∀ x, x ∉ fields spec → d x = e x) → zero spec d = zero spec e
  | [], d, e, h => by
    funext x
    exact h x (by simp [fields])
  | l :: ls, d, e, h => by
    apply zero_congr ls
    intro x hx
    by_cases hxi : x = l.field
    · subst hxi
      simp
    · rw [Function.update_of_ne hxi, Function.update_of_ne hxi]
      exact h x (by simp [fields] at hx ⊢; exact ⟨hxi, hx⟩)

theorem enum_frame : ∀ (spec : List (Level ι)) (d x : ι → ℕ), x ∈ enum spec d →
    ∀ f, f ∉ fields spec → x f = d f
  | [], d, x, hx, f, _ => by
    simp only [enum, List.mem_singleton] at hx
    rw [hx]
  | l :: ls, d, x, hx, f, hf => by
    simp only [enum, List.mem_flatMap] at hx
    obtain ⟨v, _, hv⟩ := hx
    have hf' : f ∉ fields ls := by simp [fields] at hf ⊢; exact hf.2
    have hfi : f ≠ l.field := by simp [fields] at hf; exact hf.1
    rw [enum_frame ls _ x hv f hf', Function.update_of_ne hfi]

theorem next_cons_of_some (l : Level ι) (ls : List (Level ι)) (x y : ι → ℕ)
    (h : next ls x = some y) : next (l :: ls) x = some y := by
  simp [next, h]

theorem next_cons_of_none (l : Level ι) (ls : List (Level ι)) (x : ι → ℕ)
    (h : next ls x = none) : next (l :: ls) x =
      if x l.field + 1 < l.bound x then some (zero ls (Function.update x l.field (x l.field + 1)))
      else none := by
  simp [next, h]

/-- The three facts about one level's enumeration (chain, last, head). -/
def Walks (spec : List (Level ι)) (d : ι → ℕ) : Prop :=
  List.IsChain (fun x y => next spec x = some y) (enum spec d) ∧
    (∀ x ∈ (enum spec d).getLast?, next spec x = none) ∧
    (enum spec d).head? = some (zero spec d)

theorem getLast?_flatMap_range {α : Type} (f : ℕ → List α) (n : ℕ) (hf : ∀ v, f v ≠ []) :
    ((List.range (n+1)).flatMap f).getLast? = (f n).getLast? := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.getLast?_append]
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp (mt List.getLast?_eq_none_iff.mp (hf n))
  rw [hz]
  rfl

theorem enum_next : ∀ (spec : List (Level ι)), WF spec → Pos spec → ∀ d, Walks spec d
  | [], _, _, d => by
    refine ⟨List.isChain_singleton _, ?_, rfl⟩
    intro x _
    rfl
  | l :: ls, hwf, hpos, d => by
    obtain ⟨hi, hbound, hwf'⟩ := hwf
    have hpos' : Pos ls := fun l' hl' => hpos l' (List.mem_cons_of_mem _ hl')
    have hb : 0 < l.bound d := hpos l (by simp) d
    set i := l.field with hi_def
    set b := l.bound d with hb_def
    let block : ℕ → List (ι → ℕ) := fun v => enum ls (Function.update d i v)
    have IH : ∀ v, Walks ls (Function.update d i v) := fun v => enum_next ls hwf' hpos' _
    have hne : ∀ v, block v ≠ [] := by
      intro v hv
      have := (IH v).2.2
      simp only [block] at hv
      rw [hv] at this
      simp at this
    -- facts about members of block v
    have hmem_i : ∀ v x, x ∈ block v → x i = v := by
      intro v x hx
      have := enum_frame ls _ x hx i hi
      rw [this, Function.update_self]
    have hmem_out : ∀ v x, x ∈ block v → ∀ f, f ∉ fields (l :: ls) → x f = d f := by
      intro v x hx f hf
      have hf' : f ∉ fields ls := by simp [fields] at hf ⊢; exact hf.2
      have hfi : f ≠ i := by simp [fields] at hf; exact hf.1
      rw [enum_frame ls _ x hx f hf', Function.update_of_ne hfi]
    have hmem_bound : ∀ v x, x ∈ block v → l.bound x = b := by
      intro v x hx
      exact hbound x d (hmem_out v x hx)
    -- the junction between block v and block (v+1)
    have hjunction : ∀ v, v + 1 < b → ∀ x ∈ (block v).getLast?, ∀ y ∈ (block (v+1)).head?,
        next (l :: ls) x = some y := by
      intro v hv x hx y hy
      have hxn : next ls x = none := (IH v).2.1 x hx
      have hxm : x ∈ block v := List.mem_of_getLast? hx
      rw [next_cons_of_none l ls x hxn, ← hi_def, hmem_i v x hxm, hmem_bound v x hxm, if_pos hv]
      have hy' : y = zero ls (Function.update d i (v+1)) := by
        have h2 := (IH (v+1)).2.2
        simp only [block] at hy
        rw [h2] at hy
        exact (Option.some.inj hy).symm
      rw [hy']
      congr 1
      apply zero_congr
      intro f hf
      by_cases hfi : f = i
      · subst hfi
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hfi, Function.update_of_ne hfi]
        have := enum_frame ls _ x hxm f hf
        rw [this, Function.update_of_ne hfi]
    -- induction over the range
    have hrange : ∀ n, n + 1 ≤ b →
        List.IsChain (fun x y => next (l :: ls) x = some y) ((List.range (n+1)).flatMap block) ∧
        ((List.range (n+1)).flatMap block).getLast? = (block n).getLast? := by
      intro n
      induction n with
      | zero =>
        intro _
        refine ⟨?_, ?_⟩
        · simp only [zero_add, List.range_one, List.flatMap_singleton]
          exact (IH 0).1.imp (fun x y h => next_cons_of_some l ls x y h)
        · simp
      | succ n ihn =>
        intro hn
        obtain ⟨hc, hl⟩ := ihn (by omega)
        refine ⟨?_, getLast?_flatMap_range block (n+1) hne⟩
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
        refine List.IsChain.append hc ((IH (n+1)).1.imp (fun x y h => next_cons_of_some l ls x y h)) ?_
        intro x hx y hy
        rw [hl] at hx
        exact hjunction n (by omega) x hx y hy
    obtain ⟨m, hm⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
    have henum : enum (l :: ls) d = (List.range (m+1)).flatMap block := by
      simp only [enum, block, ← hi_def, ← hb_def, hm]
    obtain ⟨hc, hl⟩ := hrange m (by omega)
    refine ⟨henum ▸ hc, ?_, ?_⟩
    · intro x hx
      rw [henum, hl] at hx
      have hxn : next ls x = none := (IH m).2.1 x hx
      have hxm : x ∈ block m := List.mem_of_getLast? hx
      rw [next_cons_of_none l ls x hxn, ← hi_def, hmem_i m x hxm, hmem_bound m x hxm, if_neg (by omega)]
    · rw [henum, List.range_succ_eq_map, List.flatMap_cons, List.head?_append, (IH 0).2.2]
      rfl

/-- **The indexed successor law.** Along the enumeration, `succD` maps entry `j` to entry `j+1`,
and the last entry to the past-the-end code. -/
theorem succD_spec (spec : List (Level ι)) (hwf : WF spec) (hpos : Pos spec) (d done : ι → ℕ)
    (j : ℕ) (hj : j < (enum spec d).length) :
    succD spec done (enum spec d)[j] = ((enum spec d)[j+1]?).getD done := by
  obtain ⟨hc, hl, _⟩ := enum_next spec hwf hpos d
  by_cases hj' : j + 1 < (enum spec d).length
  · rw [succD, hc.getElem j hj', List.getElem?_eq_getElem hj']
  · have hlast : j = (enum spec d).length - 1 := by omega
    have hx : (enum spec d)[j] ∈ (enum spec d).getLast? := by
      rw [List.getLast?_eq_getElem?]
      subst hlast
      simp
    rw [succD, hl _ hx, List.getElem?_eq_none (by omega)]

end NearCubicWires.PacketsGlue.LexSucc

