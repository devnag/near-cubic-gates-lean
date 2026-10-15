import Bindings.TuringBridge.Exec

/-! # Input loading and output extraction for the simulating bit machine

Stage 4 of the bridge.

* Loading (`scan_loop`, `scan_end`, `transfer_loop`): the framed input word `w` on tape 0
  (`RepairOrdinary.frame`) is scanned left to right, each bit's code being pushed on the scratch
  stack (`codeWidth + 4` steps per bit); then the scratch stack is popped onto stack `k₀`
  (`2·codeWidth + 3` steps per bit). The double reversal puts `w[0]` on top, which is Mathlib's
  `initList` convention (the list head is the stack top).
* Output (`out_loop`): stack `k₁` is popped top first and each symbol's bit is written on the
  fresh output tape, moving right (`codeWidth + 2` steps per bit), which is `haltList`'s order.
  The output tape then EQUALS the written list (no trailing cells), as `WordFunction` requires.
-/

namespace NearCubicWires.Bindings.Sim
open LocalBitMultitape RepairOrdinary Turing
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Reading a framed word -/

theorem frame_even : ∀ (w : List Bool) (i : ℕ),
    readTapeBit (frame w) (2 * i) = decide (i < w.length)
  | [], 0 => by simp [frame, readTapeBit]
  | [], i + 1 => by
      have : 2 * (i + 1) = (2 * i + 1) + 1 := by ring
      simp [frame, readTapeBit, this]
  | b :: bs, 0 => by simp [frame, readTapeBit]
  | b :: bs, i + 1 => by
      have ih := frame_even bs i
      have : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
      simp only [readTapeBit] at ih ⊢
      rw [this, frame, List.getD_cons_succ, List.getD_cons_succ, ih]
      simp

theorem frame_odd : ∀ (w : List Bool) (i : ℕ), i < w.length →
    readTapeBit (frame w) (2 * i + 1) = w.getD i false
  | [], _, h => absurd h (by simp)
  | b :: bs, 0, _ => by simp [frame, readTapeBit]
  | b :: bs, i + 1, h => by
      have ih := frame_odd bs i (by simp at h; omega)
      have : 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 := by ring
      simp only [readTapeBit] at ih ⊢
      rw [this, frame, List.getD_cons_succ, List.getD_cons_succ, ih, List.getD_cons_succ]

section IO
variable (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool)

/-! ## Loading: scan -/

/-- Scratch-stack codes after scanning `i` input bits (top first). -/
def loadCodes (w : List Bool) (i : ℕ) : List (Src tm) := ((w.take i).reverse).map Sum.inl

theorem loadCodes_length (w : List Bool) (i : ℕ) (hi : i ≤ w.length) :
    (loadCodes tm w i).length = i := by
  simp [loadCodes, hi]

theorem loadCodes_succ (w : List Bool) (i : ℕ) (hi : i < w.length) :
    loadCodes tm w (i + 1) = Sum.inl (w.getD i false) :: loadCodes tm w i := by
  unfold loadCodes
  rw [List.take_succ_eq_append_getElem hi, List.reverse_append, List.getD_eq_getElem _ _ hi]
  rfl

/-- The untouched part of the bank during loading: stack tapes and output tape fresh. -/
def Fresh (C0 : Cf tm) : Prop :=
  (∀ k, C0.heads (stkTape tm k) = 0 ∧ C0.tapes (stkTape tm k) = []) ∧
    C0.tapes (outTape tm) = [] ∧ C0.heads (outTape tm) = 0

theorem Fresh.congr {C0 C1 : Cf tm} (h : Fresh tm C0)
    (hoth : ∀ j, j ≠ inTape tm → j ≠ tmpTape tm → C1.heads j = C0.heads j ∧ C1.tapes j = C0.tapes j) :
    Fresh tm C1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have ho := hoth (outTape tm) (inTape_ne_out tm).symm (tmpTape_ne_out tm).symm
  refine ⟨fun k => ?_, by rw [ho.2]; exact h2, by rw [ho.1]; exact h3⟩
  have hk := hoth (stkTape tm k) (stkTape_ne_in tm k) (stkTape_ne_tmp tm k)
  rw [hk.1, hk.2]
  exact h1 k

/-- The loading invariant after scanning `i` bits. -/
def LoadInv (w : List Bool) (i : ℕ) (C0 : Cf tm) : Prop :=
  C0.tapes (inTape tm) = frame w ∧ C0.heads (inTape tm) = 2 * i ∧
    C0.heads (tmpTape tm) = i * (codeWidth tm + 1) ∧
    Agrees (C0.tapes (tmpTape tm)) (lay (enc tm) (loadCodes tm w i)) ∧ Fresh tm C0

theorem scan_step (w : List Bool) (i : ℕ) (hi : i < w.length) (C0 : Cf tm)
    (hC : C0.control = code tm (.at .ldScan)) (hinv : LoadInv tm w i C0) :
    ∃ C', Runs (machine tm ein eout) (codeWidth tm + 4) C0 C' ∧ LoadInv tm w (i + 1) C' ∧
      C'.control = code tm (.at .ldScan) := by
  obtain ⟨hin, hinh, htmph, htmpa, hfr⟩ := hinv
  have r1 := (loc tm ein eout (.at .ldScan) rfl).runs C0 hC
  have hb1 : C0.scanned (inTape tm) = true := by
    simp only [Configuration.scanned, hin, hinh, frame_even, decide_eq_true_eq]
    exact hi
  simp only [tapeOf, rule, hb1, if_true] at r1
  set C1 := act C0 (code tm (.at .ldBit)) (inTape tm) none .right with hC1
  have r2 := (loc tm ein eout (.at .ldBit) rfl).runs C1 rfl
  have hb2 : C1.scanned (inTape tm) = w.getD i false := by
    simp only [Configuration.scanned, hC1, act_heads_self, HeadMove.apply_right, act_tapes_none,
      hin, hinh]
    exact frame_odd w i hi
  simp only [tapeOf, rule, hb2] at r2
  set C2 := act C1 (code tm (.push (tmpTape tm) (.inl (w.getD i false)) ⟨0, by omega⟩ .ldScan))
    (inTape tm) none .right with hC2
  have h2h : C2.heads (tmpTape tm) = (loadCodes tm w i).length * (codeWidth tm + 1) := by
    rw [loadCodes_length tm w i hi.le, hC2, act_heads_ne _ _ _ _ _ _ (tmpTape_ne_in tm), hC1,
      act_heads_ne _ _ _ _ _ _ (tmpTape_ne_in tm), htmph]
  have h2a : Agrees (C2.tapes (tmpTape tm)) (lay (enc tm) (loadCodes tm w i)) := by
    simpa [hC2, hC1] using htmpa
  obtain ⟨C3, r3, hc3, hh3, ha3, hoth3⟩ :=
    push_op tm ein eout (tmpTape tm) (.inl (w.getD i false)) .ldScan (loadCodes tm w i) C2 rfl
      h2h h2a
  refine ⟨C3, (Runs.trans (Runs.trans r1 r2) r3).of_eq (by omega), ⟨?_, ?_, ?_, ?_, ?_⟩, hc3⟩
  · rw [(hoth3 _ (tmpTape_ne_in tm).symm).2]
    simpa [hC2, hC1] using hin
  · rw [(hoth3 _ (tmpTape_ne_in tm).symm).1]
    simp [hC2, hC1, HeadMove.apply_right, hinh]
    ring
  · rw [hh3, loadCodes_length tm w i hi.le]
  · rw [loadCodes_succ tm w i hi]; exact ha3
  · refine hfr.congr tm (fun j hj1 hj2 => ?_)
    rw [(hoth3 j hj2).1, (hoth3 j hj2).2]
    simp [hC2, hC1, act_heads_ne _ _ _ _ _ _ hj1, act_tapes_ne _ _ _ _ _ _ hj1]

theorem scan_loop (w : List Bool) : ∀ (d i : ℕ) (C0 : Cf tm), i + d = w.length →
    C0.control = code tm (.at .ldScan) → LoadInv tm w i C0 →
    ∃ C', Runs (machine tm ein eout) (d * (codeWidth tm + 4)) C0 C' ∧
      LoadInv tm w w.length C' ∧ C'.control = code tm (.at .ldScan)
  | 0, i, C0, hid, hC, hinv => ⟨C0, by simpa using Runs.refl _ C0, by simpa [← hid] using hinv, hC⟩
  | d + 1, i, C0, hid, hC, hinv => by
      obtain ⟨C1, r1, hinv1, hc1⟩ := scan_step tm ein eout w i (by omega) C0 hC hinv
      obtain ⟨C2, r2, hinv2, hc2⟩ := scan_loop w d (i + 1) C1 (by omega) hc1 hinv1
      exact ⟨C2, (Runs.trans r1 r2).of_eq (by ring), hinv2, hc2⟩

/-- End of the scan: the frame's closing `false` is read. -/
theorem scan_end (w : List Bool) (C0 : Cf tm) (hC : C0.control = code tm (.at .ldScan))
    (hinv : LoadInv tm w w.length C0) :
    Runs (machine tm ein eout) 1 C0 ⟨code tm (.at (.popAt (tmpTape tm) .tr)), C0.heads, C0.tapes⟩ := by
  have r1 := (loc tm ein eout (.at .ldScan) rfl).runs C0 hC
  have hb : C0.scanned (inTape tm) = false := by
    simp only [Configuration.scanned, hinv.1, hinv.2.1, frame_even, lt_irrefl, decide_false]
  simpa [tapeOf, rule, hb, act_none_stay] using r1

/-! ## Loading: transfer -/

theorem transfer_loop : ∀ (r v : List (Src tm)) (C0 : Cf tm),
    C0.control = code tm (.at (.popAt (tmpTape tm) .tr)) →
    C0.heads (tmpTape tm) = r.length * (codeWidth tm + 1) →
    Agrees (C0.tapes (tmpTape tm)) (lay (enc tm) r) →
    C0.heads (stkTape tm tm.k₀) = v.length * (codeWidth tm + 1) →
    Agrees (C0.tapes (stkTape tm tm.k₀)) (lay (enc tm) v) →
    ∃ C', Runs (machine tm ein eout) (r.length * (2 * codeWidth tm + 3) + 1) C0 C' ∧
      C'.control = code tm (.at (.exec (mainPt tm) tm.initialState)) ∧
      C'.heads (stkTape tm tm.k₀) = (r.reverse ++ v).length * (codeWidth tm + 1) ∧
      Agrees (C'.tapes (stkTape tm tm.k₀)) (lay (enc tm) (r.reverse ++ v)) ∧
      (∀ j, j ≠ tmpTape tm → j ≠ stkTape tm tm.k₀ →
        C'.heads j = C0.heads j ∧ C'.tapes j = C0.tapes j)
  | [], v, C0, hC, hth, hta, hkh, hka => by
      have r1 := pop_op_nil tm ein eout (tmpTape tm) .tr C0 hC (by simpa using hth) hta
      exact ⟨_, r1.of_eq (by simp), rfl, by simpa using hkh, by simpa using hka,
        fun _ _ _ => ⟨rfl, rfl⟩⟩
  | c :: r, v, C0, hC, hth, hta, hkh, hka => by
      obtain ⟨C1, r1, hc1, hh1, ht1, hoth1⟩ :=
        pop_op_cons tm ein eout (tmpTape tm) .tr c r C0 hC (by simpa using hth) hta
      simp only [resume] at hc1
      have hne : stkTape tm tm.k₀ ≠ tmpTape tm := stkTape_ne_tmp tm tm.k₀
      obtain ⟨C2, r2, hc2, hh2, ha2, hoth2⟩ :=
        push_op tm ein eout (stkTape tm tm.k₀) c (.popAt (tmpTape tm) .tr) v C1 hc1
          (by rw [hoth1 _ hne, hkh]) (by rw [ht1]; exact hka)
      obtain ⟨C3, r3, hc3, hh3, ha3, hoth3⟩ := transfer_loop r (c :: v) C2 hc2
        (by rw [(hoth2 _ hne.symm).1, hh1])
        (by rw [(hoth2 _ hne.symm).2, ht1]; exact hta.tail (enc tm))
        (by rw [hh2]; simp)
        ha2
      refine ⟨C3, (Runs.trans (Runs.trans r1 r2) r3).of_eq (by simp; ring), hc3, ?_, ?_, ?_⟩
      · rw [hh3]; simp
      · simpa using ha3
      · intro j hj1 hj2
        rw [(hoth3 j hj1 hj2).1, (hoth3 j hj1 hj2).2, (hoth2 j hj2).1, (hoth2 j hj2).2,
          hoth1 j hj1, ht1]
        exact ⟨rfl, rfl⟩

/-! ## Output -/

theorem out_loop : ∀ (cs : List (Src tm)) (L : List Bool) (C0 : Cf tm),
    C0.control = code tm (.at (.popAt (stkTape tm tm.k₁) .out)) →
    C0.heads (stkTape tm tm.k₁) = cs.length * (codeWidth tm + 1) →
    Agrees (C0.tapes (stkTape tm tm.k₁)) (lay (enc tm) cs) →
    C0.tapes (outTape tm) = L → C0.heads (outTape tm) = L.length →
    ∃ C', Runs (machine tm ein eout) (cs.length * (codeWidth tm + 2) + 1) C0 C' ∧
      C'.control = code tm (.at .done) ∧
      C'.tapes (outTape tm) = L ++ cs.map (outBit tm ein eout)
  | [], L, C0, hC, hh, ha, hot, _ => by
      have r1 := pop_op_nil tm ein eout (stkTape tm tm.k₁) .out C0 hC (by simpa using hh) ha
      exact ⟨_, r1.of_eq (by simp), rfl, by simpa using hot⟩
  | c :: cs, L, C0, hC, hh, ha, hot, hoh => by
      obtain ⟨C1, r1, hc1, hh1, ht1, hoth1⟩ :=
        pop_op_cons tm ein eout (stkTape tm tm.k₁) .out c cs C0 hC (by simpa using hh) ha
      simp only [resume] at hc1
      have r2 := (loc tm ein eout (.emit c) rfl).runs C1 hc1
      simp only [tapeOf, rule] at r2
      set C2 := act C1 (code tm (.at (.popAt (stkTape tm tm.k₁) .out))) (outTape tm)
        (some (outBit tm ein eout c)) .right with hC2
      have hne : outTape tm ≠ stkTape tm tm.k₁ := (stkTape_ne_out tm tm.k₁).symm
      have h1o : C1.heads (outTape tm) = L.length := by rw [hoth1 _ hne, hoh]
      have h1t : C1.tapes (outTape tm) = L := by rw [ht1, hot]
      obtain ⟨C3, r3, hc3, ht3⟩ := out_loop cs (L ++ [outBit tm ein eout c]) C2 rfl
        (by rw [hC2, act_heads_ne _ _ _ _ _ _ hne.symm, hh1])
        (by rw [hC2, act_tapes_ne _ _ _ _ _ _ hne.symm, ht1]; exact ha.tail (enc tm))
        (by rw [hC2, act_tapes_some, h1o, h1t, writeTapeBit_length_eq_append])
        (by rw [hC2, act_heads_self, HeadMove.apply_right, h1o]; simp)
      refine ⟨C3, (Runs.trans (Runs.trans r1 r2) r3).of_eq (by simp; ring), hc3, ?_⟩
      rw [ht3]; simp

/-- Decoding the output stack: codes of `L.map eout.symm` print `L`. -/
theorem outBit_map : ∀ (cs : List (Src tm)) (L : List Bool),
    cs.map (val tm ein tm.k₁) = (L.map eout.symm).map some → cs.map (outBit tm ein eout) = L
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, b :: L, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [List.map_cons, outBit_map cs L h.2]
      simp [outBit, h.1]

end IO

end NearCubicWires.Bindings.Sim
