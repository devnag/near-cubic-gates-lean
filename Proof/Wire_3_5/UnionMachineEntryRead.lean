import Proof.Wire_3_5.UnionMachineLoopWhile

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Entry
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine.Round

/-! ## The call table -/

/-- One call of the schedule: the test (`0` = `V`, `1` = `Q`, `2` = `μ`), the coefficient's sign and magnitude, the
request's word. -/
structure CallEntry where
  kind : Fin 3
  neg : Bool
  mag : ℕ
  word : List Bool

/-- The kind's two flag bits. -/
def kindHi (k : Fin 3) : Bool := k.val == 2
def kindLo (k : Fin 3) : Bool := k.val == 1

/-- **One entry's word.** -/
def entryWord (e : CallEntry) : List Bool :=
  [true, kindHi e.kind, kindLo e.kind, e.neg] ++ List.replicate e.mag true ++ false :: frame e.word

/-- **The call table's word.** -/
def tableWord (L : List CallEntry) : List Bool := L.flatMap entryWord ++ [false]

/-! ## The entry bank -/

/-- The entry bank's state: stream `0` the table, stream `1` the estimator's input tape; 15 registers. -/
abbrev ES := WState 1 15

local notation "s0" => (0 : Fin 2)
local notation "s1" => (1 : Fin 2)
local notation "rCC" => (0 : Fin 15)
local notation "rSG" => (1 : Fin 15)
local notation "rK1" => (2 : Fin 15)
local notation "rK0" => (3 : Fin 15)
local notation "rCT" => (4 : Fin 15)
local notation "rT" => (5 : Fin 15)

variable (cap : ℕ)

/-- Read the scanned table bit into a clear flag and advance. -/
def bitReg (r : Fin 15) : WM 1 15 := .seq (.ifs s0 (.inc r) .skip) (.fwd s0)

theorem bitReg_spec (r : Fin 15) (σ : ES) (hr : σ.val r = 0) (hc : 1 ≤ cap) :
    WExec cap (bitReg r) σ ((σ.setv r (readTapeBit (σ.st s0) (σ.sh s0)).toNat).seth s0 (σ.sh s0 + 1)) 6 := by
  have hf := WExec.fwd (cap := cap) s0 (σ.setv r (readTapeBit (σ.st s0) (σ.sh s0)).toNat)
  cases hb : readTapeBit (σ.st s0) (σ.sh s0)
  · have e : σ.setv r (false.toNat) = σ := by rw [Bool.toNat_false, ← hr]; exact wsetv_same σ r
    have hk : WExec cap (.ifs s0 (.inc r) .skip) σ (σ.setv r (false.toNat)) 1 := by
      rw [e]; exact WExec.mono (WExec.ifsF (by simpa [wbit] using hb) (WExec.skip σ)) (by omega)
    rw [hb] at hf
    exact WExec.mono (hk.seq (by simpa using hf)) (by omega)
  · have hk : WExec cap (.ifs s0 (.inc r) .skip) σ (σ.setv r (true.toNat)) 4 := by
      have := WExec.inc (cap := cap) r σ (by omega)
      rw [hr] at this
      exact WExec.ifsT (by simpa [wbit] using hb) this
    rw [hb] at hf
    exact WExec.mono (hk.seq (by simpa using hf)) (by omega)

/-- One round of the framed copy: the marker, then the bit. -/
def cpBody : WM 1 15 :=
  .seq (emitC s1 rCT true) <| .seq (.fwd s0) <| .seq (.ifs s0 (emitC s1 rCT true) (emitC s1 rCT false)) (.fwd s0)

/-- **The framed copy**: `frameP w` at the table's head is appended to stream `1`. -/
theorem cpLoop_spec : ∀ (w : List Bool) (σ : ES) (pre rest : List Bool),
    σ.st s0 = pre ++ frameP w ++ false :: rest → σ.sh s0 = pre.length → σ.sh s1 = (σ.st s1).length →
    σ.val rCT + 2 * w.length ≤ cap →
    WExec cap (.whs s0 cpBody) σ
      (((σ.seth s0 (σ.sh s0 + 2 * w.length)).sets s1 (σ.st s1 ++ frameP w)).seth s1 (σ.sh s1 + 2 * w.length) |>.setv
        rCT (σ.val rCT + 2 * w.length)) (w.length * 25 + 1)
  | [], σ, pre, rest, h0, hs0, hs1, _ => by
    have hb : wbit σ s0 = false := by
      simp only [wbit, h0, hs0, frameP_nil, List.append_nil]
      rw [show pre.length = pre.length + 0 by rfl, readTapeBit_app]; rfl
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; fin_cases x <;> simp [Function.update_apply]
    · funext x; fin_cases x <;> simp [Function.update_apply]
    · funext x; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> simp_all
  | b :: w, σ, pre, rest, h0, hs0, hs1, hc => by
    have hb : wbit σ s0 = true := by
      simp only [wbit, h0, hs0, frameP_cons]
      rw [show pre.length = pre.length + 0 by rfl, List.append_assoc, readTapeBit_app]; rfl
    have e1 := emitC_spec cap s1 rCT true σ hs1 (by simp at hc; omega)
    set σ1 := ((σ.sets s1 (σ.st s1 ++ [true])).seth s1 (σ.sh s1 + 1)).setv rCT (σ.val rCT + 1) with hσ1
    have e2 := WExec.fwd (cap := cap) s0 σ1
    set σ2 := σ1.seth s0 (σ1.sh s0 + 1) with hσ2
    have hb2 : wbit σ2 s0 = b := by
      simp only [wbit, σ2, σ1, WState.seth_st, WState.setv_st, WState.sets_st, WState.seth_sh, WState.setv_sh,
        WState.sets_sh, Function.update_apply]
      simp only [if_true, show ¬ ((0 : Fin 2) = 1) by decide, if_false, h0, hs0, frameP_cons]
      rw [show pre.length + 1 = pre.length + 1 by rfl, List.append_assoc, readTapeBit_app]; rfl
    have hs12 : σ2.sh s1 = (σ2.st s1).length := by simp [σ2, σ1, Function.update_apply, hs1]
    have e3 : WExec cap (.ifs s0 (emitC s1 rCT true) (emitC s1 rCT false)) σ2
        (((σ2.sets s1 (σ2.st s1 ++ [b])).seth s1 (σ2.sh s1 + 1)).setv rCT (σ2.val rCT + 1)) 8 := by
      cases b
      · exact WExec.ifsF hb2 (emitC_spec cap s1 rCT false σ2 hs12 (by simp [σ2, σ1] at hc ⊢; omega))
      · exact WExec.ifsT hb2 (emitC_spec cap s1 rCT true σ2 hs12 (by simp [σ2, σ1] at hc ⊢; omega))
    set σ3 := ((σ2.sets s1 (σ2.st s1 ++ [b])).seth s1 (σ2.sh s1 + 1)).setv rCT (σ2.val rCT + 1) with hσ3
    have e4 := WExec.fwd (cap := cap) s0 σ3
    set σ4 := σ3.seth s0 (σ3.sh s0 + 1) with hσ4
    have ih := cpLoop_spec w σ4 (pre ++ [true, b]) rest
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, h0])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hs0])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hs1])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply] at hc ⊢; omega)
    refine WExec.cast cap (WExec.whsT hb (e1.seq (e2.seq (e3.seq e4))) ih) ?_ (by simp; omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; fin_cases x <;> simp [σ4, σ3, σ2, σ1, Function.update_apply] <;> omega
    · funext x; fin_cases x <;> simp [σ4, σ3, σ2, σ1, Function.update_apply]
    · funext x; simp only [σ4, σ3, σ2, σ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> simp_all <;> omega

/-! ## Reading one entry -/

/-- **Read one entry**: skip the marker, the kind and sign flags, the magnitude into `CC`, the framed request onto
stream `1`, both end markers, stream `1` back to `0`. -/
def readE : WM 1 15 :=
  .seq (.fwd s0) <| .seq (bitReg rK1) <| .seq (bitReg rK0) <| .seq (bitReg rSG) <|
  .seq (WM.readU s0 rT rCC) <| .seq (.whs s0 cpBody) <| .seq (.wr s1 false) <| .seq (.fwd s0) (WM.rewind s1 rCT)

theorem entryWord_split (e : CallEntry) (pre rest : List Bool) :
    pre ++ entryWord e ++ rest =
      (pre ++ [true, kindHi e.kind, kindLo e.kind, e.neg] ++ List.replicate e.mag true ++ [false]) ++
        frameP e.word ++ false :: rest := by
  simp [entryWord, frame_eq_frameP]

theorem entryWord_length (e : CallEntry) : (entryWord e).length = 2 * e.word.length + e.mag + 6 := by
  simp [entryWord, frame_eq_frameP]; omega

theorem entry_ones (e : CallEntry) (rest : List Bool) (k : ℕ) (hk : k < e.mag) :
    readTapeBit (entryWord e ++ rest) (4 + k) = true := by
  simp only [entryWord, List.append_assoc, readTapeBit_append, List.length_cons, List.length_nil,
    List.length_replicate]
  split_ifs <;> first | omega | (rw [readTapeBit_rep _ _ _ (by omega)])

theorem entry_zero (e : CallEntry) (rest : List Bool) :
    readTapeBit (entryWord e ++ rest) (4 + e.mag) = false := by
  simp only [entryWord, List.append_assoc, readTapeBit_append, List.length_cons, List.length_nil,
    List.length_replicate]
  split_ifs <;> first | omega | (rw [show 4 + e.mag - 4 - e.mag = 0 by omega]; rfl)

/-- The registers `readE` writes. -/
def readRegs : List (Fin 15) := [rCC, rSG, rK1, rK0, rCT, rT]

theorem readE_spec (e : CallEntry) (pre rest : List Bool) (σ : ES) (h0 : σ.st s0 = pre ++ entryWord e ++ rest)
    (hs0 : σ.sh s0 = pre.length) (h1 : σ.st s1 = []) (hs1 : σ.sh s1 = 0)
    (hz : ∀ r ∈ readRegs, σ.val r = 0) (hcap : 2 * e.word.length + e.mag + 2 ≤ cap) :
    ∃ τ : ES, WExec cap readE σ τ (40 * (e.mag + e.word.length + 2)) ∧ τ.st s0 = σ.st s0 ∧
      τ.sh s0 = pre.length + (entryWord e).length ∧ τ.st s1 = frame e.word ∧ τ.sh s1 = 0 ∧
      τ.val rCC = e.mag ∧ τ.val rSG = e.neg.toNat ∧ τ.val rK1 = (kindHi e.kind).toNat ∧
      τ.val rK0 = (kindLo e.kind).toNat ∧ τ.val rCT = 0 ∧ (∀ r, r ∉ readRegs → τ.val r = σ.val r) ∧
      τ.cell = σ.cell := by
  have hz' : ∀ r ∈ readRegs, σ.val r = 0 := hz
  simp only [readRegs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hz'
  obtain ⟨zCC, zSG, zK1, zK0, zCT, zT⟩ := hz'
  have hread : ∀ k, readTapeBit (σ.st s0) (pre.length + k) =
      readTapeBit (entryWord e ++ rest) k := fun k => by rw [h0, List.append_assoc, readTapeBit_app]
  have hc1 : 1 ≤ cap := by omega
  -- the marker
  have e1 := WExec.fwd (cap := cap) s0 σ
  set σ1 := σ.seth s0 (σ.sh s0 + 1) with hσ1
  -- the flags
  have e2 := bitReg_spec cap rK1 σ1 (by simp [σ1, zK1]) hc1
  have b2 : readTapeBit (σ1.st s0) (σ1.sh s0) = kindHi e.kind := by
    simp only [σ1, WState.seth_st, WState.seth_sh, Function.update_self, hs0]; rw [hread]; simp [entryWord, readTapeBit]
  rw [b2] at e2
  set σ2 := (σ1.setv rK1 (kindHi e.kind).toNat).seth s0 (σ1.sh s0 + 1) with hσ2
  have e3 := bitReg_spec cap rK0 σ2 (by simp [σ2, σ1, Function.update_apply, zK0]) hc1
  have b3 : readTapeBit (σ2.st s0) (σ2.sh s0) = kindLo e.kind := by
    simp only [σ2, σ1, WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh, Function.update_self, hs0]
    rw [show pre.length + 1 + 1 = pre.length + 2 by omega, hread]; simp [entryWord, readTapeBit]
  rw [b3] at e3
  set σ3 := (σ2.setv rK0 (kindLo e.kind).toNat).seth s0 (σ2.sh s0 + 1) with hσ3
  have e4 := bitReg_spec cap rSG σ3 (by simp [σ3, σ2, σ1, Function.update_apply, zSG]) hc1
  have b4 : readTapeBit (σ3.st s0) (σ3.sh s0) = e.neg := by
    simp only [σ3, σ2, σ1, WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh, Function.update_self, hs0]
    rw [show pre.length + 1 + 1 + 1 = pre.length + 3 by omega, hread]; simp [entryWord, readTapeBit]
  rw [b4] at e4
  set σ4 := (σ3.setv rSG e.neg.toNat).seth s0 (σ3.sh s0 + 1) with hσ4
  have hs4 : σ4.sh s0 = pre.length + 4 := by simp [σ4, σ3, σ2, σ1, hs0]
  have ht4 : σ4.st s0 = σ.st s0 := by simp [σ4, σ3, σ2, σ1]
  -- the magnitude
  have e5 := wreadU_spec cap s0 rT rCC (by decide) e.mag σ4
    (fun k hk => by
      rw [ht4, hs4, show pre.length + 4 + k = pre.length + (4 + k) by omega, hread]
      exact entry_ones e rest k hk)
    (by
      rw [ht4, hs4, show pre.length + 4 + e.mag = pre.length + (4 + e.mag) by omega, hread]
      exact entry_zero e rest)
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, zT]; omega)
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, zCC]; omega)
  set σ5 := ((σ4.seth s0 (σ4.sh s0 + e.mag + 1)).setv rT (σ4.val rT + e.mag + 1)).setv rCC (σ4.val rCC + e.mag)
    with hσ5
  -- the framed request
  have e6 := cpLoop_spec cap e.word σ5 (pre ++ [true, kindHi e.kind, kindLo e.kind, e.neg] ++
      List.replicate e.mag true ++ [false]) rest
    (by simp only [σ5, WState.setv_st, WState.seth_st, ht4, h0]; exact entryWord_split e pre rest)
    (by simp [σ5, hs4]; omega)
    (by simp [σ5, σ4, σ3, σ2, σ1, h1, hs1])
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, zCT]; omega)
  set σ6 := (((σ5.seth s0 (σ5.sh s0 + 2 * e.word.length)).sets s1 (σ5.st s1 ++ frameP e.word)).seth s1
    (σ5.sh s1 + 2 * e.word.length)).setv rCT (σ5.val rCT + 2 * e.word.length) with hσ6
  have hs16 : σ6.sh s1 = 2 * e.word.length := by simp [σ6, σ5, σ4, σ3, σ2, σ1, hs1]
  have ht16 : σ6.st s1 = frameP e.word := by simp [σ6, σ5, σ4, σ3, σ2, σ1, h1]
  -- the end markers
  have e7 := WExec.wr (cap := cap) s1 false σ6
  rw [ht16, hs16, show 2 * e.word.length = (frameP e.word).length by simp, writeTapeBit_end',
    ← frame_eq_frameP] at e7
  set σ7 := σ6.sets s1 (frame e.word) with hσ7
  have e8 := WExec.fwd (cap := cap) s0 σ7
  set σ8 := σ7.seth s0 (σ7.sh s0 + 1) with hσ8
  -- stream 1 back
  have e9 := wrewind_spec cap s1 rCT (2 * e.word.length) σ8
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, zCT])
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, zCT]; omega)
  refine ⟨_, WExec.mono (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))) ?_, ?_⟩
  · simp; nlinarith
  · simp only [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, readRegs, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Function.update_apply]
    · simp [Function.update_apply, hs0, entryWord_length]; omega
    · simp [Function.update_apply]
    · simp [Function.update_apply, hs1]
    · simp [Function.update_apply, zCC]
    · simp [Function.update_apply]
    · simp [Function.update_apply]
    · simp [Function.update_apply]
    · simp [Function.update_apply]
    · intro r hr
      simp only [not_or] at hr
      simp [Function.update_apply, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]
    · rfl

end NearCubicWires.WireExponent3_5.UnionMachine.Entry
