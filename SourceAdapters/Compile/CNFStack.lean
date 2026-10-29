import SourceAdapters.Compile.CNFInterpA

/-!
# Generic cell stacks

The interpreter's index stack (`CNFInterpA.StkRel`, `pushP`, `popP`) with the store and the height register as
parameters: `StkG m sp a st`, `pushG_spec`, `popG_spec` (the same proofs). Used by the balanced encoder (proof of `lem:multitape-refuter`, Step 3: the native balanced outer coding of the clause list), which keeps a task stack and a value stack.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false

variable {C : Ctx}

/-- The stack `st` (top first) is stored bottom first in store `m`, height in register `sp`. -/
structure StkG (m : Fin MM) (sp : Fin VV) (a : DS VV MM) (st : List ℕ) : Prop where
  sp : a.env sp = st.length
  take : (a.ram m).take st.length = st.reverse
  len : st.length ≤ (a.ram m).length

/-- Push `env x` (seek `m` to the height, write, increment). -/
def pushG (m : Fin MM) (sp x : Fin VV) : St VV MM := .seq (seekP m sp) (.seq (.op (.wrM m x)) (.op (.inc sp)))

theorem pushG_spec (m : Fin MM) (sp x : Fin VV) (hspn : sp ∉ [iS, iJ]) (hx : x ∉ [iS, iJ, sp]) (a : DS VV MM)
    (st : List ℕ) (h : StkG m sp a st)
    (hW : st.length + 2 < 2 ^ C.Wd) :
    Hs C (pushG m sp x) a (a.rc m + 5 * st.length + 10) (fun b => StkG m sp b (a.env x :: st) ∧
      (b.ram m).length ≤ max (a.ram m).length (st.length + 1) ∧ b.rc m = st.length + 1 ∧
      (∀ m2, m2 ≠ m → b.ram m2 = a.ram m2 ∧ b.rc m2 = a.rc m2) ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b [iS, iJ, sp]) := by
  have hx' : x ≠ iS ∧ x ≠ iJ ∧ x ≠ sp := by simpa using hx
  refine Hs.seqc (t1 := a.rc m + 5 * st.length + 6) (t2 := 3) (Hs.mono (seekP_spec (C := C) m sp
    hspn a (by rw [h.sp]; exact h.len) (by rw [h.sp]; omega)) (by rw [h.sp]) (fun b hb => hb))
    (fun b hb => ?_) (by omega)
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  rw [h.sp] at b1
  refine Hs.seqc (t1 := 1) (t2 := 1) (hs_wrM C m x b (by rw [b1, b2]; exact h.len)) (fun d hd => ?_) (by omega)
  subst hd
  have hsp : (b.put m (b.env x)).env sp = st.length := by
    simp only [DS.put]; rw [b6 sp (by simpa using hspn), h.sp]
  refine Hs.op (OpEx.inc sp _ (by rw [hsp]; omega)) ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [DS.set_env_self, hsp]; simp
  · simp only [DS.set_ram, DS.put, Function.update_self, List.length_cons]
    rw [b1, b2, take_putAt _ _ _ h.len, h.take, b6 x (by simp [hx'.1, hx'.2.1])]; simp
  · simp only [DS.set_ram, DS.put, Function.update_self, List.length_cons]
    rw [b1, b2, putAt_length _ _ _ h.len]; omega
  · simp only [DS.set_ram, DS.put, Function.update_self]
    rw [b1, b2, putAt_length _ _ _ h.len]
  · simp [DS.put, b1]
  · intro m2 hm
    simp only [DS.set_ram, DS.set_rc, DS.put, Function.update_of_ne hm]
    exact ⟨by rw [b2], b3 m2 hm⟩
  · simp [DS.put, b4]
  · simp [DS.put, b5]
  · intro y hy
    have hy' : y ≠ iS ∧ y ≠ iJ ∧ y ≠ sp := by simpa using hy
    simp only [DS.set, DS.put]
    rw [Function.update_of_ne hy'.2.2]
    exact b6 y (by simp [hy'.1, hy'.2.1])

/-- Pop into `x` (`0` on the empty stack). -/
def popG (m : Fin MM) (sp x : Fin VV) : St VV MM :=
  .ite (.eq sp vZ) (.op (.zero x)) (.seq (.op (.sub sp v1)) (.seq (seekP m sp) (.op (.rdM m x))))

theorem popG_spec (m : Fin MM) (sp x : Fin VV) (hspn : sp ∉ [iS, iJ, vZ, v1]) (hx : x ∉ [iS, iJ, sp]) (a : DS VV MM)
    (st : List ℕ) (h : StkG m sp a st)
    (hz : a.env vZ = 0) (h1 : a.env v1 = 1) (hW : st.length + 2 < 2 ^ C.Wd) :
    Hs C (popG m sp x) a (a.rc m + 5 * st.length + 10) (fun b => b.env x = (popS st).1 ∧ StkG m sp b (popS st).2 ∧
      b.ram = a.ram ∧ b.rc m ≤ max (a.rc m) st.length ∧ (∀ m2, m2 ≠ m → b.rc m2 = a.rc m2) ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b [iS, iJ, sp, x]) := by
  have hx' : x ≠ iS ∧ x ≠ iJ ∧ x ≠ sp := by simpa using hx
  have hsp4 : sp ≠ iS ∧ sp ≠ iJ ∧ sp ≠ vZ ∧ sp ≠ v1 := by simpa using hspn
  refine Hs.ite hsp4.2.2.1 (fun hc => ?_) (fun hc => ?_)
  · have he : st = [] := by
      have : a.env sp = 0 := by simpa [Cnd.eval, hz] using hc
      rw [h.sp] at this; exact List.eq_nil_of_length_eq_zero this
    subst he
    refine Hs.mono (hs_zero C x a) (by omega) ?_
    rintro b rfl
    refine ⟨by simp [popS], ⟨?_, by simp [popS], by simp [popS]⟩, rfl, by simp, fun _ _ => rfl, rfl, rfl, by fr_tac⟩
    rw [DS.set_env_ne _ _ (Ne.symm hx'.2.2), h.sp]; rfl
  · obtain ⟨top, rest, rfl⟩ : ∃ top rest, st = top :: rest := by
      cases st with
      | nil => simp [Cnd.eval, h.sp, hz] at hc
      | cons t r => exact ⟨t, r, rfl⟩
    have hsp := h.sp
    simp only [List.length_cons] at hsp
    have htake := h.take
    simp only [List.length_cons, List.reverse_cons] at htake
    have hlen := h.len
    simp only [List.length_cons] at hlen hW
    refine Hs.seqc (t1 := 1) (t2 := a.rc m + 5 * rest.length + 8) (hs_sub C sp v1 a hsp4.2.2.2
      (by rw [hsp, h1]; omega)) (fun b hb => ?_) (by simp only [List.length_cons]; omega)
    subst hb
    have bsp : (a.set sp (a.env sp - a.env v1)).env sp = rest.length := by
      rw [DS.set_env_self, hsp, h1]; simp
    refine Hs.seqc (t1 := a.rc m + 5 * rest.length + 6) (t2 := 1) (Hs.mono (seekP_spec (C := C) m sp
      (by simp [hsp4.1, hsp4.2.1]) _ (by rw [bsp]; simp; omega) (by rw [bsp]; omega)) (by rw [bsp]; simp) (fun b hb => hb))
      (fun d hd => ?_) (by omega)
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
    rw [bsp] at d1
    simp only [DS.set_ram] at d2
    have hget : (a.ram m)[rest.length]?.getD 0 = top := by
      have e := congrArg (fun l : List ℕ => l[rest.length]?) htake
      simp at e
      simp [e]
    refine Hs.op (OpEx.rdM m x d (by rw [d1, d2]; omega)) ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [DS.adv, popS, d1, d2, hget]
    · simp only [DS.adv, popS]
      rw [DS.set_env_ne _ _ (Ne.symm hx'.2.2), d6 sp (by simp [hsp4.1, hsp4.2.1]), bsp]
    · simp only [DS.adv, DS.set_ram, popS, d2]
      have := congrArg (fun l => l.take rest.length) htake
      simp only [List.take_take] at this
      rw [Nat.min_eq_left (by omega)] at this
      rw [this, List.take_left' (by simp)]
    · simp only [DS.adv, DS.set_ram, popS, d2]; omega
    · simp [DS.adv, DS.set, d2]
    · simp [DS.adv, d1]
    · intro m2 hm
      simp only [DS.adv, DS.set_rc, Function.update_of_ne hm]
      rw [d3 m2 hm]; rfl
    · simp [DS.adv, d4]
    · simp [DS.adv, d5]
    · intro y hy
      have hy' : y ≠ iS ∧ y ≠ iJ ∧ y ≠ sp ∧ y ≠ x := by simpa using hy
      simp only [DS.adv, DS.set]
      rw [Function.update_of_ne hy'.2.2.2, d6 y (by simp [hy'.1, hy'.2.1])]
      simp [Function.update_of_ne hy'.2.2.1]

end NearCubicGates.Adapters.Compile
