import Proof.CaseAnalysis.RowsEstimatorConsumer
import Proof.CaseAnalysis.RowsEstimatorCoefficientsRequest

/-! Shared SYM/THR consumer: the original row producer and Williams count
table emit the same six-field record with equivalent unreduced coefficient
operands. Only selection-mask bytes, never count values, enter the bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Record
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorCountMask CompetitorSelectedCount
open CompetitorCrossScheduler (producer)
open CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem table_zero (p : Program) (row : EquationRow.Input) (Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ) (xs : List (Bool × ℕ))
    (i : Fin (CompetitorCountTableRecord.tapes p)) (hi:i.val=0) :
    Table.input p (EquationRow.request row) Q row.odd q denominator xs i=
      physicalInput (EquationRow.request row):=by
  let z : Fin (CompetitorCrossScheduler.tapes p):=⟨0,by unfold CompetitorCrossScheduler.tapes;omega⟩
  have he:i=(((z.castAdd 511).castAdd 124).castAdd 92).castAdd 27:=Fin.ext hi
  rw [he]
  simp [Table.input,CompetitorSelectedTable.extend,CompetitorSelectedTable.tapes,
    CompetitorCountTable.input,CompetitorCountTable.extend,CompetitorCountTable.tapes,
    CompetitorCountBanks.input,CompetitorCountBanks.extend,CompetitorCountBanks.tapes,
    CompetitorCrossScheduler.input,CompetitorCrossScheduler.tapes,Fin.addCases,z]

theorem table_mask (p : Program) (row : EquationRow.Input) (Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ) (xs ys : List (Bool × ℕ))
    (hm:mask xs=mask ys) :
    Table.input p (EquationRow.request row) Q row.odd q denominator xs=
      Table.input p (EquationRow.request row) Q row.odd q denominator ys:=by
  unfold Table.input CompetitorSelectedTable.extend CompetitorSelectedTable.extra
  rw [hm]

def input (p : Program) (row : EquationRow.Input) (Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool):=
  Consumer.input p row (Table.input p (EquationRow.request row) Q row.odd q denominator
    (CompetitorSelectedCells.cells row.odd (fun _ _=>0) select))

theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (Q : ℕ)
    (f : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (q : CompetitorValidity.Estimate) (denominator : ℕ) (hQ:Q≤(EquationRow.request row).p)
    (hf:∀ i j,f i j<2^Q)
    (hc:∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : ℤ)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat)) :
    ∃ actual,LocalBitMultitape.run
      (CloseoutRowsRawRecord.machine (producer a) (CompetitorCountTableRecord.machine a))
      (CloseoutRowsRawRecord.budget a row Q) (input (producer a) row Q q denominator select)=some actual ∧
      actual.steps≤CloseoutRowsRawRecord.envelope a row ∧
      actual.final.tapes (CloseoutRowsRawRecord.receive (producer a) (CompetitorCountTableRecord.slots (producer a) 117))=
        Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator ∧
      actual.final.heads (CloseoutRowsRawRecord.receive (producer a) (CompetitorCountTableRecord.slots (producer a) 117))=
        (Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator).length ∧
      actual.final.tapes (CloseoutRowsRawRecord.receive (producer a) (CompetitorCountTableRecord.slots (producer a) 0))=
        physicalInput (EquationRow.request row):=by
  have hwidth:Q≤CompetitorSameBucketColdDense.width (EquationRow.request row):=by
    rw [CompetitorSameBucketColdDense.width_eq]
    exact hQ.trans (by omega)
  obtain ⟨child,ch,cs,ct,co,c0⟩:=Table.record_run a (EquationRow.request row) Q row.odd
    f select q denominator hwidth (CompetitorRowCountMeaning.odd_even_size row) hf hc
  obtain ⟨actual,ha,hs,hh,ht⟩:=Consumer.prefix_run (producer a) (CompetitorCountTableRecord.machine a)
    row _ (table_zero (producer a) row Q q denominator _) _ child ch
  have hm:=table_mask (producer a) row Q q denominator _ _ (cells_mask row.odd f (fun _ _=>0) select)
  rw [hm] at ha
  have cb:=cs.trans (CompetitorCountTableRecord.budget_bound a (EquationRow.request row) Q hQ)
  refine ⟨actual,ha,?_,(ht _).trans ct,(hh _).trans co,(ht _).trans c0⟩
  unfold CloseoutRowsRawRecord.envelope
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Record
