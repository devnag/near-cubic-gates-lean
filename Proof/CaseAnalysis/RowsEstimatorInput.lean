import Proof.CaseAnalysis.RowsRawRecord
import Proof.CaseAnalysis.RowsProjectionReset

/-! Consumer-first interface for the shared physical row estimator. Only
the selection mask reaches its input; all natural table values are computed
by the existing Williams/count-table machine itself. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorCountMask CompetitorSelectedCount CompetitorMonomialStream
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cells_mask {u : ℕ} (odd : Bool) (f g : Fin u→Fin u→ℕ)
    (select : Fin u→Fin u→Bool) :
    mask (CompetitorSelectedCells.cells odd f select)=mask (CompetitorSelectedCells.cells odd g select) := by
  cases odd <;> simp [CompetitorSelectedCells.cells,CompetitorSelectedCells.rect,mask,
    List.map_flatten,List.map_ofFn,Function.comp_def]

theorem input_mask (p : Program) (row : EquationRow.Input) (Q : ℕ) (q : ℚ)
    (denominator : ℕ) (xs ys : List (Bool × ℕ)) (hm : mask xs=mask ys) :
    CloseoutRowsRawRecord.input p row Q q denominator xs=
      CloseoutRowsRawRecord.input p row Q q denominator ys := by
  unfold CloseoutRowsRawRecord.input CloseoutRowsRawRecord.extra CompetitorCountTableRecord.input
    CompetitorSelectedTable.extend CompetitorSelectedTable.extra
  rw [hm]

def input (p : Program) (row : EquationRow.Input) (Q : ℕ) (q : ℚ) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :=
  CloseoutRowsRawRecord.input p row Q q denominator
    (CompetitorSelectedCells.cells row.odd (fun _ _=>0) select)

theorem actual_input (p : Program) (row : EquationRow.Input) (Q : ℕ) (q : ℚ) (denominator : ℕ)
    (f : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :
    CloseoutRowsRawRecord.input p row Q q denominator (CompetitorSelectedCells.cells row.odd f select)=
      input p row Q q denominator select :=
  input_mask p row Q q denominator _ _ (cells_mask row.odd f (fun _ _=>0) select)

theorem prepared_run (a : WilliamsAlgorithm) (row : EquationRow.Input) (Q : ℕ)
    (f : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (q : ℚ) (denominator : ℕ) (hQ : Q≤(EquationRow.request row).p)
    (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : ℤ)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat)) :
    ∃ actual,run (CloseoutRowsRawRecord.machine (producer a) (CompetitorCountTableRecord.machine a))
      (CloseoutRowsRawRecord.budget a row Q) (input (producer a) row Q q denominator select)=some actual ∧
      actual.steps≤CloseoutRowsRawRecord.envelope a row ∧
      actual.final.tapes (CloseoutRowsRawRecord.receive (producer a) (CompetitorCountTableRecord.slots (producer a) 117))=
        recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator ∧
      actual.final.heads (CloseoutRowsRawRecord.receive (producer a) (CompetitorCountTableRecord.slots (producer a) 117))=
        (recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator).length ∧
      actual.final.tapes (CloseoutRowsRawRecord.receive (producer a) (CompetitorCountTableRecord.slots (producer a) 0))=
        physicalInput (EquationRow.request row) := by
  obtain ⟨actual,hr,hrest⟩ := CloseoutRowsRawRecord.raw_record_run a row Q f select q denominator hQ hf hc
  rw [actual_input] at hr
  exact ⟨actual,hr,hrest⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
