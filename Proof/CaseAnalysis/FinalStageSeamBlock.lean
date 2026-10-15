import Proof.CaseAnalysis.FinalStageSeam
import Proof.CaseAnalysis.FinalTailCompose
import Proof.Amplification.RecoveryTseitinReadOnly

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeamBlock

open Finset
open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose
  (BlockRuns entryOf entry_eq wflag wport winput wwit wflag_val)
open NearCubicWires.RepairSource.RecoveryTseitinReadOnly (NoWrite)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The docked body never writes tapes `0` and `1` -/

theorem step_noWrite {t s : ℕ} {p : Machine t s} {n : ℕ} {H H' : Fin t → ℕ}
    {A A' : Fin t → List Bool} (h : Step p n H A H' A') (i : Fin t) (hp : NoWrite p i) :
    A' i = A i := by
  obtain ⟨r, hr, _, ht, _⟩ := h
  rw [← ht]
  exact RepairSource.RecoveryTseitinReadOnly.run_tape p i hp n _ r hr

theorem noWrite_dockBody (i : Fin 218) (hi : i.val < 2) : NoWrite dockBody i := by
  unfold dockBody
  refine RepairSource.RecoveryTseitinReadOnly.composition _ _ i ?_ ?_
  · refine RepairSource.RecoveryTseitinReadOnly.unselected entrySlot _ i ?_
    intro j h
    have hv := congrArg Fin.val h
    rw [entrySlot_val] at hv
    omega
  · refine RepairSource.RecoveryTseitinReadOnly.unselected foldSlot _ i ?_
    intro j h
    have hv := congrArg Fin.val h
    rw [foldSlot_val] at hv
    split at hv <;> omega

theorem noWrite_emitLoader (i : Fin 218) (hi : i.val < 2) : NoWrite emitLoader i := by
  unfold emitLoader
  refine RepairSource.RecoveryTseitinReadOnly.composition _ _ i
    (RepairSource.RecoveryTseitinReadOnly.composition _ _ i ?_ ?_) ?_
  · refine RepairSource.RecoveryTseitinReadOnly.unselected slotsP _ i ?_
    intro k h
    have hv := congrArg Fin.val h
    rcases slotsP_vals k with h' | h' | h' | h' | h' <;> omega
  · refine RepairSource.RecoveryTseitinReadOnly.unselected slotsN _ i ?_
    intro k h
    have hv := congrArg Fin.val h
    rcases slotsN_vals k with h' | h' | h' | h' | h' <;> omega
  · refine RepairSource.RecoveryTseitinReadOnly.unselected slotsD _ i ?_
    intro k h
    have hv := congrArg Fin.val h
    rcases slotsD_vals k with h' | h' | h' | h' | h' <;> omega

theorem noWrite_answer (i : Fin 218) (hi : i.val < 2) :
    NoWrite (RecoveryFocus.machine answerSlot CompetitorCountRecordAppend.machine) i := by
  refine RepairSource.RecoveryTseitinReadOnly.unselected answerSlot _ i ?_
  intro j h
  have hv := congrArg Fin.val h
  rw [answerSlot_val] at hv
  omega

/-- **The docked body never writes tapes `0` and `1`.** -/
theorem noWrite_dockedBody (i : Fin 218) (hi : i.val < 2) :
    NoWrite (dockedBody emitLoader) i := by
  unfold dockedBody
  exact RepairSource.RecoveryTseitinReadOnly.composition _ _ i (noWrite_dockBody i hi)
    (RepairSource.RecoveryTseitinReadOnly.composition _ _ i (noWrite_emitLoader i hi)
      (noWrite_answer i hi))

/-! ## §2 The dock without its loader, framing tapes `0` and `1` -/

/-- **`docked_run` plus `exit 0 = bank 0 ∧ exit 1 = bank 1`.** -/
theorem docked_run_frame (entryWidth : ℕ) (entries : List Entry)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry)
    (bank : Fin 218 → List Bool) (hready : DockReady entryWidth entries bank)
    (hentry : EmitEntry (joinScalarWidth entryWidth entries.length) bank) (n : ℕ) :
    ∃ (heads : Fin 218 → ℕ) (exit : Fin 218 → List Bool),
      Step (dockedBody emitLoader)
        (dockedFuel (fun _ => emitFuel (joinScalarWidth entryWidth entries.length))
          entryWidth entries.length n)
        (fun _ => 0) bank heads exit ∧
      exit port = CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (foldWidth (CompetitorRationalDecision.width entryWidth) entries)
        (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)) 1 1 ∧
      exit 0 = bank 0 ∧ exit 1 = bank 1 := by
  obtain ⟨heads, exit, hrun, hencoded⟩ :=
    docked_run entryWidth entries hentries bank hready hentry n
  exact ⟨heads, exit, hrun, hencoded,
    step_noWrite hrun 0 (noWrite_dockedBody 0 (by decide)),
    step_noWrite hrun 1 (noWrite_dockedBody 1 (by decide))⟩

/-! ## §3 T3's parked bank, against the seam's layout -/

/-- **T3's `entryOf` on `218 + e` tapes is the 218-tape `entryOf` with every
extra tape blank.**  `entry_eq` on both sides of `stageInput_addCases`. -/
theorem entryOf_addCases (e : ℕ) (input witness : List Bool) :
    entryOf (wflag e) input witness =
      Fin.addCases (entryOf flag input witness) (fun _ : Fin e => []) := by
  have hw0 : (wflag e).val ≠ 0 := by rw [wflag_val]; omega
  have hw1 : (wflag e).val ≠ 1 := by rw [wflag_val]; omega
  rw [← entry_eq (TapeEmbedding.machine e dockBody) (by omega) (Fin.castAdd e result) (wflag e)
      hw0 hw1 input witness,
    ← entry_eq dockBody dockTapes_two result flag (by decide) (by decide) input witness]
  exact stageInput_addCases (TapeEmbedding.machine e dockBody) dockBody (by omega) input witness

/-! ## §4 The seam, as a block -/

theorem blockRuns_of_stage {e st : ℕ} (stage : Machine (218+e) st) (stageFuel emitFuel : ℕ → ℕ)
    (onset entryWidth : ℕ) (len : ℕ) (x : BitInput len) (bits : List Bool) (entries : List Entry)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry)
    (bank : Fin 218 → List Bool) (scratch : Fin e → List Bool)
    (hready : DockReady entryWidth entries bank)
    (hentry : EmitEntry (joinScalarWidth entryWidth entries.length) bank)
    (h0 : bank 0 = frame (List.ofFn x)) (h1 : bank 1 = frame bits)
    (hemit : emitFuel =
      fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel
        (joinScalarWidth entryWidth entries.length))
    (hstage : Step stage (stageFuel len) (fun _ => 0)
      (exitTapes (Fin.castAdd e flag)
        ((UAcceptanceCarrier.verifier
          (worker onset (Fin.castAdd e inputTape) (Fin.castAdd e flag) (Fin.castAdd e result)
            (stagedBody stage emitLoader))
          (by omega) (Fin.castAdd e result)).inputTapes (List.ofFn x) bits) 0 true)
      (fun _ => 0) (Fin.addCases bank scratch)) :
    BlockRuns e (stagedBody stage emitLoader)
      (stagedFuel stageFuel emitFuel entryWidth entries.length len) (List.ofFn x) bits
      (CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (foldWidth (CompetitorRationalDecision.width entryWidth) entries)
        (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)) 1 1) := by
  subst hemit
  obtain ⟨heads, exit, hrun, hencoded, hx0, hx1⟩ :=
    docked_run_frame entryWidth entries hentries bank hready hentry len
  have hembed :
      Step (TapeEmbedding.machine e (dockedBody emitLoader))
        (dockedFuel (fun _ => emitFuel (joinScalarWidth entryWidth entries.length))
          entryWidth entries.length len)
        (fun _ => 0) (Fin.addCases bank scratch)
        (Fin.addCases heads (fun _ : Fin e => 0)) (Fin.addCases exit scratch) :=
    (hrun.embed (fun _ : Fin e => 0) scratch).congr_in (addCases_zero e) rfl
  have hw0 : (Fin.castAdd e flag).val ≠ 0 := by
    have h : (Fin.castAdd e flag).val = 216 := rfl
    omega
  have hw1 : (Fin.castAdd e flag).val ≠ 1 := by
    have h : (Fin.castAdd e flag).val = 216 := rfl
    omega
  have hstep := (hstage.seq hembed).congr_in rfl
    (entry_eq
      (worker onset (Fin.castAdd e inputTape) (Fin.castAdd e flag) (Fin.castAdd e result)
        (stagedBody stage emitLoader))
      (by omega) (Fin.castAdd e result) (Fin.castAdd e flag) hw0 hw1 (List.ofFn x) bits)
  unfold BlockRuns
  refine ⟨_, _, hstep, ?_, ?_, ?_⟩
  · unfold wport
    simp only [Fin.addCases_left]
    exact hencoded
  · unfold winput
    simp only [Fin.addCases_left]
    exact hx0.trans h0
  · unfold wwit
    simp only [Fin.addCases_left]
    exact hx1.trans h1

end NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeamBlock
