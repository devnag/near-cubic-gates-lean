import Proof.Gates.OuterM.ARunA
import Proof.Gates.CheckedPCPP.Harness
import Proof.Gates.CheckedPCPP.Dock

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Succinct NearCubicGates.Close.WordPrograms

section Layout
variable (pT pA : Program)

/-- The number of streams minus one. -/
def nsL : ℕ := 3 + pT.tapeCount + pA.tapeCount

theorem five_le_nsL : 5 ≤ nsL pT pA := by have := pT.twoTapes; have := pA.twoTapes; unfold nsL; omega

/-- The time program's tapes: its input tape on stream `4`, the others from stream `6` on. -/
def tmapT (j : Fin pT.tapeCount) : Fin (nsL pT pA + 1) :=
  ⟨if j.val = 0 then 4 else 5 + j.val, by have := j.isLt; have := pA.twoTapes; unfold nsL; split_ifs <;> omega⟩

/-- The constructor's tapes: its input tape on stream `5`, the others after the time program's. -/
def tmapA (j : Fin pA.tapeCount) : Fin (nsL pT pA + 1) :=
  ⟨if j.val = 0 then 5 else 4 + pT.tapeCount + j.val, by
    have := j.isLt; have := pT.twoTapes; have := pA.twoTapes; unfold nsL; split_ifs <;> omega⟩

theorem tmapT_inj : Function.Injective (tmapT pT pA) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [tmapT] at this
  apply Fin.ext
  split_ifs at this <;> omega

theorem tmapA_inj : Function.Injective (tmapA pT pA) := by
  intro a b h
  have := pT.twoTapes
  have := congrArg Fin.val h
  simp only [tmapA] at this
  apply Fin.ext
  split_ifs at this <;> omega

theorem tmapT_val (j : Fin pT.tapeCount) : (tmapT pT pA j).val = if j.val = 0 then 4 else 5 + j.val := rfl
theorem tmapA_val (j : Fin pA.tapeCount) : (tmapA pT pA j).val = if j.val = 0 then 5 else 4 + pT.tapeCount + j.val :=
  rfl

/-- The time program's output stream. -/
def sTB : Fin (nsL pT pA + 1) := tmapT pT pA pT.outputTape

theorem sTB_val : (sTB pT pA).val = 5 + pT.outputTape.val := by
  unfold sTB; rw [tmapT_val, if_neg pT.outputFresh]

/-- The constructor's output stream. -/
def sW : Fin (nsL pT pA + 1) := tmapA pT pA pA.outputTape

theorem sW_val : (sW pT pA).val = 4 + pT.tapeCount + pA.outputTape.val := by
  unfold sW; rw [tmapA_val, if_neg pA.outputFresh]

end Layout

theorem frameP_ones : ∀ ν : ℕ, frameP (List.replicate ν true) = List.replicate (2 * ν) true
  | 0 => rfl
  | ν + 1 => by
    rw [List.replicate_succ, frameP_cons, frameP_ones ν, show 2 * (ν + 1) = 2 * ν + 1 + 1 by ring]
    simp [List.replicate_succ]

/-- `frame 1^ν` is `2ν` marked ones and the end marker. -/
theorem frame_ones (ν : ℕ) : RepairOrdinary.frame (List.replicate ν true) = List.replicate (2 * ν) true ++ [false] := by
  rw [frame_eq_frameP, frameP_ones]

/-- The time program's input stream. -/
def sTI (pT pA : Program) : Fin (nsL pT pA + 1) := ⟨4, by have := five_le_nsL pT pA; omega⟩
/-- The constructor's input stream. -/
def sCI (pT pA : Program) : Fin (nsL pT pA + 1) := ⟨5, by have := five_le_nsL pT pA; omega⟩

section PhaseB
variable (pT pA : Program)

/-- Phase B: `frame 1^ν` on stream `4` (register `3` holds `ν`, `20` counts), rewound, then the time program. -/
def phaseB : WMX (nsL pT pA) nrA :=
  .seq (.wm (emitP2 (sTI pT pA) 3 20)) (.seq (.wm (emitC (sTI pT pA) 20 false)) (.seq (.wm (WM.rewind (sTI pT pA) 20))
    (.mach pT.machine (tmapT pT pA))))

/-- The cost of phase B (`fuel` the time program's). -/
def costB (ν fuel : ℕ) : ℕ := (19 * ν + 1) + 1 + (7 + 1 + ((5 * (2 * ν + 1) + 1) + 1 + fuel))

/-- **Phase B** (lem:succinct-verifier (i)): the time program run on `frame 1^ν`; its final tapes on its streams. -/
theorem phaseB_spec (ν fuel : ℕ) (outT : Fin pT.tapeCount → List Bool)
    (hT : ClockJoin.ReadyRun pT.machine fuel (pT.inputTapes (List.replicate ν true)) outT)
    (cap : ℕ) (σ : WState (nsL pT pA) nrA) (hTI : σ.st (sTI pT pA) = []) (hTIh : σ.sh (sTI pT pA) = 0)
    (hfresh : ∀ j : Fin pT.tapeCount, j.val ≠ 0 → σ.st (tmapT pT pA j) = [] ∧ σ.sh (tmapT pT pA j) = 0)
    (h3 : σ.val 3 = ν) (h20 : σ.val 20 = 0) (hcap : 2 * ν + 2 ≤ cap) :
    ∃ τ, WXExec cap (phaseB pT pA) σ τ (costB ν fuel) ∧ (∀ j, τ.st (tmapT pT pA j) = outT j) ∧
      (∀ j, τ.sh (tmapT pT pA j) = 0) ∧
      (∀ r : Fin nrA, r ≠ 3 → r ≠ 20 → τ.val r = σ.val r) ∧ τ.val 3 = 0 ∧ τ.val 20 = 0 ∧
      (∀ i : Fin (nsL pT pA + 1), (∀ j, tmapT pT pA j ≠ i) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) := by
  have e1 := emitP2_spec cap (sTI pT pA) (3 : Fin nrA) 20 (by decide) ν σ h3 (by rw [hTI, hTIh]; rfl) (by rw [h20]; omega)
    (by omega)
  set σ1 := (((σ.sets (sTI pT pA) (σ.st (sTI pT pA) ++ List.replicate (2 * ν) true)).seth (sTI pT pA) ((σ.st (sTI pT pA)).length + 2 * ν)).setv 20
    (σ.val 20 + 2 * ν)).setv 3 0 with hσ1
  have e2 := emitC_spec cap (sTI pT pA) (20 : Fin nrA) false σ1 (by simp [σ1, hTI]) (by simp [σ1, h20]; omega)
  set σ2 := ((σ1.sets (sTI pT pA) (σ1.st (sTI pT pA) ++ [false])).seth (sTI pT pA) (σ1.sh (sTI pT pA) + 1)).setv 20 (σ1.val 20 + 1) with hσ2
  have e3 := wrewind_spec cap (sTI pT pA) (20 : Fin nrA) (2 * ν + 1) σ2 (by simp [σ2, σ1, h20]) (by simp [σ2, σ1, h20]; omega)
  set σ3 := (σ2.setv 20 0).seth (sTI pT pA) (σ2.sh (sTI pT pA) - (2 * ν + 1)) with hσ3
  have h3TI : σ3.st (sTI pT pA) = RepairOrdinary.frame (List.replicate ν true) := by
    simp [σ3, σ2, σ1, hTI, frame_ones]
  have hin : ∀ j, σ3.st (tmapT pT pA j) = pT.inputTapes (List.replicate ν true) j := by
    intro j
    rw [CheckedPCPP.program_inputTapes]
    by_cases hj : j.val = 0
    · rw [if_pos hj]
      have : tmapT pT pA j = (sTI pT pA) := Fin.ext (by rw [tmapT_val, if_pos hj]; rfl)
      rw [this, h3TI]
    · rw [if_neg hj]
      have hne : tmapT pT pA j ≠ (sTI pT pA) := fun h => by
        have := congrArg Fin.val h; rw [tmapT_val, if_neg hj] at this; change 5 + j.val = 4 at this; omega
      simp [σ3, σ2, σ1, Function.update_apply, hne, (hfresh j hj).1]
  have hsh : ∀ j, σ3.sh (tmapT pT pA j) = 0 := by
    intro j
    by_cases hj : j.val = 0
    · have : tmapT pT pA j = (sTI pT pA) := Fin.ext (by rw [tmapT_val, if_pos hj]; rfl)
      rw [this]; simp [σ3, σ2, σ1, hTI, hTIh]
    · have hne : tmapT pT pA j ≠ (sTI pT pA) := fun h => by
        have := congrArg Fin.val h; rw [tmapT_val, if_neg hj] at this; change 5 + j.val = 4 at this; omega
      simp [σ3, σ2, σ1, Function.update_apply, hne, (hfresh j hj).2]
  obtain ⟨τ, e4, hd⟩ := CheckedPCPP.Dock.ready_mach cap hT (tmapT_inj pT pA) σ3 hsh hin
  refine ⟨τ, ?_, hd.st, hd.sh, ?_, ?_, ?_, ?_⟩
  · refine WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2) (WXExec.seq (WXExec.wm e3) e4))) ?_
    unfold costB; omega
  · intro r hr3 hr20
    rw [hd.val]; simp [σ3, σ2, σ1, Function.update_apply, hr3, hr20]
  · rw [hd.val]; simp [σ3, σ2, σ1]
  · rw [hd.val]; simp [σ3]
  · intro i hi
    rw [(hd.other i hi).1, (hd.other i hi).2]
    have hne : i ≠ (sTI pT pA) := fun h => hi ⟨0, by have := pT.twoTapes; omega⟩ (by
      rw [h]; exact Fin.ext (by rw [tmapT_val]; rfl))
    simp [σ3, σ2, σ1, Function.update_apply, hne]

end PhaseB

end NearCubicGates.Close.OuterM
