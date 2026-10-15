import Proof.MachineModel.ClosureRawRowState

/-! Full-state reuse of the existing warm scanner/printer.  These identities
test the actual exit, not just its answer port.  The next row's header and
metadata still require their physical producer. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.ScannedRowState
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open CloseoutRowsEstimator C10RowFrameJoin CloseoutRowsEstimatorCoefficients
open CompetitorSelectedCount MatrixScoreBatch P1Independent RecoveryRootRound
attribute [local irreducible] Warm.input RecoveryRootRound.install

theorem output_empty_input (p : Program) (row : EquationRow.Input) (C D Q : Nat)
    (q : CompetitorValidity.Estimate) (den : Nat)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) :
    ScannedRow.output p row C D Q q den select [] =
      ScannedRow.input p row C D Q q den select
        (Warm.input p row C Q q den select) [] := by
  have native : Warm.input p row C Q q den select (NativeReadOnly.slot p) =
      Header.stream row := by
    unfold Warm.input Warm.supplied NativeReadOnly.slot
    rw [Fin.addCases_left]
    change Prepare.output row 52 = _
    exact Prepare.header_input row 52
  funext i
  refine Fin.addCases (m:=Reuse.tapes p+7) (n:=3) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m:=Reuse.tapes p) (n:=7) (fun j => ?_) (fun j => ?_) j
    · simp only [ScannedRow.output,ScannedRow.input,ScannedRow.bank,Fin.addCases_left,
        WarmTransaction.output]
      by_cases hn : j=Reuse.native p
      · subst j
        rw [Function.update_self,exitTapes_native,native]
        simp only [WarmTransaction.caps,Fin.val_castAdd,native_val,↓reduceIte]
      · have hv : j.val ≠ 52 := by
          intro he
          apply hn
          exact Fin.ext (he.trans (native_val p).symm)
        simp only [WarmTransaction.caps,Fin.val_castAdd,hv,if_false,ZeroPadding.pad_zero,
          Function.update_of_ne hn]
    · have hv : Reuse.tapes p+j.val ≠ 52 := by
        have ht := tapes_ge p
        unfold Reuse.tapes
        omega
      simp only [ScannedRow.output,ScannedRow.input,ScannedRow.bank,Fin.addCases_left,
        Fin.addCases_right,WarmTransaction.output,WarmTransaction.caps,
        Fin.val_natAdd,hv,if_false,ZeroPadding.pad_zero]
  · simp only [ScannedRow.output,ScannedRow.input,ScannedRow.bank,Fin.addCases_right]

theorem clear_output (p : Program) (row : EquationRow.Input) (C D Q : Nat)
    (q : CompetitorValidity.Estimate) (den : Nat)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (word : List Bool) :
    Function.update (ScannedRow.output p row C D Q q den select word)
        (ScannedRawRow.port p) [] = ScannedRow.output p row C D Q q den select [] := by
  funext i
  by_cases he : i=ScannedRawRow.port p
  · subst i
    rw [Function.update_self,ScannedRawRow.output_port]
  · rw [Function.update_of_ne he]
    revert he
    refine Fin.addCases (m:=Reuse.tapes p+7) (n:=3) (fun j => ?_) (fun j _ => ?_) i
    · refine Fin.addCases (m:=Reuse.tapes p) (n:=7) (fun j he => ?_) (fun j _ => ?_) j
      · have hj : j ≠ Reuse.output p := by
          intro hj
          subst j
          exact he rfl
        simp only [ScannedRow.output,Fin.addCases_left,WarmTransaction.output,exitTapes,
          hj,if_false]
      · simp only [ScannedRow.output,Fin.addCases_left,Fin.addCases_right,WarmTransaction.output]
    · simp only [ScannedRow.output,Fin.addCases_right]

theorem reset_to_input (p : Program) (row : EquationRow.Input) (C D Q : Nat)
    (q : CompetitorValidity.Estimate) (den : Nat)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (word : List Bool) :
    Function.update (ScannedRow.output p row C D Q q den select word)
        (ScannedRawRow.port p) [] =
      ScannedRow.input p row C D Q q den select
        (Warm.input p row C Q q den select) [] :=
  (clear_output p row C D Q q den select word).trans
    (output_empty_input p row C D Q q den select)

end NearCubicWires.P1Closure.ScannedRowState
