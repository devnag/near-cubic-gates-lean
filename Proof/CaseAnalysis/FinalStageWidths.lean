import Proof.CaseAnalysis.FinalComposeWidths

namespace NearCubicWires.RepairSource.CloseoutFinal.C10StageWidths

open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.CloseoutFinalC10WorkerDock
open RepairOrdinary.CloseoutFinalC10WorkerFold
open RepairOrdinary.CloseoutFinalC10WorkerChain
open RepairOrdinary.CloseoutFinalC10WorkerEmitBody
open RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open RepairOrdinary.CloseoutFinalC10StageSeam
open RepairOrdinary.CloseoutFinalC10StageSeamBlock
open RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream
open C10TailCompose C10BodyWidths
open C10LengthGate

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem blockRuns_widths_of_stage {e st : ℕ} (he : 58 ≤ e) (stage : LocalBitMultitape.Machine (218+e) st) (stageFuel emitFuel : ℕ → ℕ)
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
      (fun _ => 0) (Fin.addCases bank scratch))
    (hwidth : ∀ j, Fin.addCases bank scratch (retained e he j) =
      widthWord (foldWidth (CompetitorRationalDecision.width entryWidth) entries) j) :
    BlockRunsWidths e he (stagedBody stage emitLoader)
      (stagedFuel stageFuel emitFuel entryWidth entries.length len) (List.ofFn x) bits
      (CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (foldWidth (CompetitorRationalDecision.width entryWidth) entries)
        (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)) 1 1)
      (foldWidth (CompetitorRationalDecision.width entryWidth) entries) := by
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
  unfold BlockRunsWidths
  refine ⟨_, _, hstep, ?_, ?_, ?_, ?_⟩
  · unfold wport
    simp only [Fin.addCases_left]
    exact hencoded
  · unfold winput
    simp only [Fin.addCases_left]
    exact hx0.trans h0
  · unfold wwit
    simp only [Fin.addCases_left]
    exact hx1.trans h1

  · intro j
    have hj : 56+j.val < e := by have := j.isLt; omega
    have hi : retained e he j = (⟨56+j.val, hj⟩ : Fin e).natAdd 218 := by
      apply Fin.ext
      show 274+j.val = 218+(56+j.val)
      omega
    have h := hwidth j
    rw [hi, Fin.addCases_right] at h ⊢
    exact h

end NearCubicWires.RepairSource.CloseoutFinal.C10StageWidths
