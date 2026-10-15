import Proof.Gates.OuterM.ARunC

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Succinct NearCubicGates.Close.WordPrograms

theorem frameP_append (a b : List Bool) : frameP (a ++ b) = frameP a ++ frameP b := by
  simp [frameP, List.flatMap_append]

theorem frameP_frameP (w : List Bool) : frameP (frameP w) = quad w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frameP_cons, quad, ih] at *

/-- The constructor's input on one tape. -/
theorem frame_frame (w t : List Bool) :
    RepairOrdinary.frame (RepairOrdinary.frame w ++ RepairOrdinary.frame t) =
      quad w ++ [true, false] ++ quad t ++ [true, false] ++ [false] := by
  rw [frame_eq_frameP, frame_eq_frameP, frame_eq_frameP, frameP_append, frameP_append, frameP_append,
    frameP_frameP, frameP_frameP]
  simp

/-- The copy stream on the A-run's layout. -/
def sSL (pT pA : Program) : Fin (nsL pT pA + 1) := ⟨3, by have := five_le_nsL pT pA; omega⟩

/-- The cost of phase D. -/
def costD (L n fuel : ℕ) : ℕ :=
  (40 * L + 1) + 1 + (7 + 1 + (7 + 1 + ((40 * n + 1) + 1 + (7 + 1 + (7 + 1 + (7 + 1 +
    ((5 * (4 * L + 2 + 4 * n + 3) + 1) + 1 + fuel)))))))

section PhaseD
variable (pT pA : Program)

/-- Phase D. -/
def phaseD : WMX (nsL pT pA) nrA :=
  .seq (.wm (emitFF (sSL pT pA) (sCI pT pA) 10 26))
  (.seq (.wm (emitC (sCI pT pA) 26 true))
  (.seq (.wm (emitC (sCI pT pA) 26 false))
  (.seq (.wm (emitFF (sTB pT pA) (sCI pT pA) 21 26))
  (.seq (.wm (emitC (sCI pT pA) 26 true))
  (.seq (.wm (emitC (sCI pT pA) 26 false))
  (.seq (.wm (emitC (sCI pT pA) 26 false))
  (.seq (.wm (WM.rewind (sCI pT pA) 26))
  (.mach pA.machine (tmapA pT pA)))))))))

theorem sCI_ne_sSL : sCI pT pA ≠ sSL pT pA := fun h => by have := congrArg Fin.val h; simp [sCI, sSL] at this
theorem sTB_ne_sCI : sTB pT pA ≠ sCI pT pA := fun h => by
  have := congrArg Fin.val h; rw [sTB_val] at this; simp [sCI] at this; have := pT.outputFresh; omega
theorem sTB_ne_sSL : sTB pT pA ≠ sSL pT pA := fun h => by
  have := congrArg Fin.val h; rw [sTB_val] at this; simp [sSL] at this; omega

theorem quad_length (w : List Bool) : (quad w).length = 4 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have : quad (b :: w) = [true, true, true, b] ++ quad w := rfl
    rw [this, List.length_append, ih]; simp; ring

/-- **Phase D**: the constructor run on `frame w ++ frame t` (`w` the first `L` cells of the copy, `t` the time word);
its final tapes on its streams; streams `0 1 2` untouched. -/
theorem phaseD_spec (L : ℕ) (d t : List Bool) (fuel : ℕ) (outA : Fin pA.tapeCount → List Bool)
    (hA : ClockJoin.ReadyRun pA.machine fuel
      (pA.inputTapes (RepairOrdinary.frame (cellsOf d L) ++ RepairOrdinary.frame t)) outA)
    (cap : ℕ) (σ : WState (nsL pT pA) nrA)
    (hS : σ.st (sSL pT pA) = cellsOf d (L + 1)) (hSh : σ.sh (sSL pT pA) = 0) (h10 : σ.val 10 = L)
    (hT : σ.st (sTB pT pA) = t) (hTh : σ.sh (sTB pT pA) = 0) (h21 : σ.val 21 = t.length) (h26 : σ.val 26 = 0)
    (hCI : σ.st (sCI pT pA) = []) (hCIh : σ.sh (sCI pT pA) = 0)
    (hfresh : ∀ j : Fin pA.tapeCount, j.val ≠ 0 → σ.st (tmapA pT pA j) = [] ∧ σ.sh (tmapA pT pA j) = 0)
    (hcap : 4 * L + 4 * t.length + 8 ≤ cap) :
    ∃ τ, WXExec cap (phaseD pT pA) σ τ (costD L t.length fuel) ∧ (∀ j, τ.st (tmapA pT pA j) = outA j) ∧
      (∀ i : Fin (nsL pT pA + 1), i.val < 3 → τ.st i = σ.st i) := by
  have hCS := sCI_ne_sSL pT pA
  have hTC := sTB_ne_sCI pT pA
  have hTS := sTB_ne_sSL pT pA
  have hSC := Ne.symm hCS
  have hCT := Ne.symm hTC
  have hST := Ne.symm hTS
  have e1 := emitFF_spec cap (sSL pT pA) (sCI pT pA) (10 : Fin nrA) 26 hSC (by decide) L σ h10
    (by rw [hCI, hCIh]; rfl) (by rw [h26]; omega) (by omega)
  set σ1 := ((((σ.sets (sCI pT pA) (σ.st (sCI pT pA) ++ quad (List.ofFn fun i : Fin L =>
    readTapeBit (σ.st (sSL pT pA)) (σ.sh (sSL pT pA) + i.val)))).seth (sCI pT pA) ((σ.st (sCI pT pA)).length + 4 * L)).seth
    (sSL pT pA) (σ.sh (sSL pT pA) + L)).setv 26 (σ.val 26 + 4 * L)).setv 10 0 with hσ1
  have hw : (List.ofFn fun i : Fin L => readTapeBit (σ.st (sSL pT pA)) (σ.sh (sSL pT pA) + i.val)) = cellsOf d L := by
    rw [hS, hSh]
    unfold cellsOf
    congr 1
    funext i
    rw [Nat.zero_add]
    have := read_cellsOf d (L + 1) i.val
    unfold cellsOf at this
    rw [this, if_pos (by omega)]
  have h1st : σ1.st (sCI pT pA) = quad (cellsOf d L) := by simp [σ1, hCI, hw]
  have h1sh : σ1.sh (sCI pT pA) = 4 * L := by simp [σ1, Function.update_apply, hCS, hCI]
  have h1v : σ1.val 26 = 4 * L := by simp [σ1, h26]
  have e2 := emitC_spec cap (sCI pT pA) (26 : Fin nrA) true σ1 (by rw [h1sh, h1st, quad_length]; simp [cellsOf])
    (by rw [h1v]; omega)
  set σ2 := ((σ1.sets (sCI pT pA) (σ1.st (sCI pT pA) ++ [true])).seth (sCI pT pA) (σ1.sh (sCI pT pA) + 1)).setv 26
    (σ1.val 26 + 1) with hσ2
  have e3 := emitC_spec cap (sCI pT pA) (26 : Fin nrA) false σ2
    (by simp [σ2, h1sh, h1st, quad_length, cellsOf]) (by simp [σ2, h1v]; omega)
  set σ3 := ((σ2.sets (sCI pT pA) (σ2.st (sCI pT pA) ++ [false])).seth (sCI pT pA) (σ2.sh (sCI pT pA) + 1)).setv 26
    (σ2.val 26 + 1) with hσ3
  have h3st : σ3.st (sCI pT pA) = quad (cellsOf d L) ++ [true, false] := by simp [σ3, σ2, h1st]
  have h3sh : σ3.sh (sCI pT pA) = 4 * L + 2 := by simp [σ3, σ2, h1sh]
  have h3v : σ3.val 26 = 4 * L + 2 := by simp [σ3, σ2, h1v]
  have h3T : σ3.st (sTB pT pA) = t := by simp [σ3, σ2, σ1, Function.update_apply, hTC, hT]
  have h3Th : σ3.sh (sTB pT pA) = 0 := by simp [σ3, σ2, σ1, Function.update_apply, hTC, hTS, hTh]
  have h3_21 : σ3.val 21 = t.length := by simp [σ3, σ2, σ1, h21]
  have e4 := emitFF_spec cap (sTB pT pA) (sCI pT pA) (21 : Fin nrA) 26 hTC (by decide) t.length σ3 h3_21
    (by rw [h3sh, h3st]; simp [quad_length, cellsOf]) (by rw [h3v]; omega) (by omega)
  have ht : (List.ofFn fun i : Fin t.length => readTapeBit (σ3.st (sTB pT pA)) (σ3.sh (sTB pT pA) + i.val)) = t := by
    rw [h3T, h3Th]
    have := cellsOf_self t
    unfold cellsOf at this
    simpa using this
  set σ4 := ((((σ3.sets (sCI pT pA) (σ3.st (sCI pT pA) ++ quad (List.ofFn fun i : Fin t.length =>
    readTapeBit (σ3.st (sTB pT pA)) (σ3.sh (sTB pT pA) + i.val)))).seth (sCI pT pA)
    ((σ3.st (sCI pT pA)).length + 4 * t.length)).seth (sTB pT pA) (σ3.sh (sTB pT pA) + t.length)).setv 26
    (σ3.val 26 + 4 * t.length)).setv 21 0 with hσ4
  have h4st : σ4.st (sCI pT pA) = quad (cellsOf d L) ++ [true, false] ++ quad t := by
    have : σ4.st (sCI pT pA) = σ3.st (sCI pT pA) ++ quad (List.ofFn fun i : Fin t.length =>
        readTapeBit (σ3.st (sTB pT pA)) (σ3.sh (sTB pT pA) + i.val)) := by simp [σ4]
    rw [this, ht, h3st]
  have h4sh : σ4.sh (sCI pT pA) = 4 * L + 2 + 4 * t.length := by
    simp [σ4, Function.update_apply, hCT, h3st, quad_length, cellsOf]
  have h4v : σ4.val 26 = 4 * L + 2 + 4 * t.length := by simp [σ4, h3v]
  have h4len : (σ4.st (sCI pT pA)).length = 4 * L + 2 + 4 * t.length := by
    rw [h4st]; simp [quad_length, cellsOf]; ring
  have e5 := emitC_spec cap (sCI pT pA) (26 : Fin nrA) true σ4 (by rw [h4sh, h4len]) (by rw [h4v]; omega)
  set σ5 := ((σ4.sets (sCI pT pA) (σ4.st (sCI pT pA) ++ [true])).seth (sCI pT pA) (σ4.sh (sCI pT pA) + 1)).setv 26
    (σ4.val 26 + 1) with hσ5
  have e6 := emitC_spec cap (sCI pT pA) (26 : Fin nrA) false σ5 (by simp [σ5, h4sh, h4len]) (by simp [σ5, h4v]; omega)
  set σ6 := ((σ5.sets (sCI pT pA) (σ5.st (sCI pT pA) ++ [false])).seth (sCI pT pA) (σ5.sh (sCI pT pA) + 1)).setv 26
    (σ5.val 26 + 1) with hσ6
  have e7 := emitC_spec cap (sCI pT pA) (26 : Fin nrA) false σ6 (by simp [σ6, σ5, h4sh, h4len])
    (by simp [σ6, σ5, h4v]; omega)
  set σ7 := ((σ6.sets (sCI pT pA) (σ6.st (sCI pT pA) ++ [false])).seth (sCI pT pA) (σ6.sh (sCI pT pA) + 1)).setv 26
    (σ6.val 26 + 1) with hσ7
  have h7v : σ7.val 26 = 4 * L + 2 + 4 * t.length + 3 := by simp [σ7, σ6, σ5, h4v]
  have h7sh : σ7.sh (sCI pT pA) = 4 * L + 2 + 4 * t.length + 3 := by simp [σ7, σ6, σ5, h4sh]
  have e8 := wrewind_spec cap (sCI pT pA) (26 : Fin nrA) (4 * L + 2 + 4 * t.length + 3) σ7 h7v (by rw [h7v]; omega)
  set σ8 := (σ7.setv 26 0).seth (sCI pT pA) (σ7.sh (sCI pT pA) - (4 * L + 2 + 4 * t.length + 3)) with hσ8
  have h8st : σ8.st (sCI pT pA) =
      RepairOrdinary.frame (RepairOrdinary.frame (cellsOf d L) ++ RepairOrdinary.frame t) := by
    rw [frame_frame]; simp [σ8, σ7, σ6, σ5, h4st]
  have hin : ∀ j, σ8.st (tmapA pT pA j) =
      pA.inputTapes (RepairOrdinary.frame (cellsOf d L) ++ RepairOrdinary.frame t) j := by
    intro j
    rw [CheckedPCPP.program_inputTapes]
    by_cases hj : j.val = 0
    · rw [if_pos hj]
      have : tmapA pT pA j = sCI pT pA := Fin.ext (by rw [tmapA_val, if_pos hj]; rfl)
      rw [this, h8st]
    · rw [if_neg hj]
      have hne : tmapA pT pA j ≠ sCI pT pA := fun h => by
        have := congrArg Fin.val h; rw [tmapA_val, if_neg hj] at this; change _ = 5 at this; have := pT.twoTapes; omega
      have hne2 : tmapA pT pA j ≠ sSL pT pA := fun h => by
        have := congrArg Fin.val h; rw [tmapA_val, if_neg hj] at this; change _ = 3 at this; have := pT.twoTapes; omega
      have hne3 : tmapA pT pA j ≠ sTB pT pA := fun h => by
        have := congrArg Fin.val h; rw [tmapA_val, if_neg hj, sTB_val] at this
        have := pT.outputTape.isLt; omega
      simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hne, hne2, hne3, (hfresh j hj).1]
  have hsh : ∀ j, σ8.sh (tmapA pT pA j) = 0 := by
    intro j
    by_cases hj : j.val = 0
    · have : tmapA pT pA j = sCI pT pA := Fin.ext (by rw [tmapA_val, if_pos hj]; rfl)
      rw [this]; simp [σ8, h7sh]
    · have hne : tmapA pT pA j ≠ sCI pT pA := fun h => by
        have := congrArg Fin.val h; rw [tmapA_val, if_neg hj] at this; change _ = 5 at this; have := pT.twoTapes; omega
      have hne2 : tmapA pT pA j ≠ sSL pT pA := fun h => by
        have := congrArg Fin.val h; rw [tmapA_val, if_neg hj] at this; change _ = 3 at this; have := pT.twoTapes; omega
      have hne3 : tmapA pT pA j ≠ sTB pT pA := fun h => by
        have := congrArg Fin.val h; rw [tmapA_val, if_neg hj, sTB_val] at this
        have := pT.outputTape.isLt; omega
      simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hne, hne2, hne3, (hfresh j hj).2]
  obtain ⟨τ, e9, hd⟩ := CheckedPCPP.Dock.ready_mach cap hA (tmapA_inj pT pA) σ8 hsh hin
  refine ⟨τ, ?_, hd.st, ?_⟩
  · refine WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2) (WXExec.seq (WXExec.wm e3)
      (WXExec.seq (WXExec.wm e4) (WXExec.seq (WXExec.wm e5) (WXExec.seq (WXExec.wm e6) (WXExec.seq (WXExec.wm e7)
      (WXExec.seq (WXExec.wm e8) e9)))))))) ?_
    unfold costD; omega
  · intro i hi
    have hnot : ∀ j, tmapA pT pA j ≠ i := fun j h => by
      have := congrArg Fin.val h; rw [tmapA_val] at this; split_ifs at this <;> omega
    rw [(hd.other i hnot).1]
    have hne : i ≠ sCI pT pA := fun h => by rw [h] at hi; simp [sCI] at hi
    have hne3 : i ≠ sTB pT pA := fun h => by rw [h, sTB_val] at hi; omega
    have hne2 : i ≠ sSL pT pA := fun h => by rw [h] at hi; simp [sSL] at hi
    simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hne, hne3, hne2]

end PhaseD

end NearCubicGates.Close.OuterM
