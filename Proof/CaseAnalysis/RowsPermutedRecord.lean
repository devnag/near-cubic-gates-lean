import Proof.Hierarchy.CompetitorCountTableRecordRow
import Proof.Hierarchy.CompetitorRowCountPermutation
import Proof.Hierarchy.CompetitorOffsetScalar

/-! The actual occurrence order reaches the physical six-field record writer.
The record is valid at its actual common width, and the whole table phase
retains the established linear-table times short-width-polynomial envelope. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRows
open LocalBitMultitape RepairRepresentation MatrixScoreBatch
open CompetitorSelectedCount CompetitorCountMask CompetitorCrossScheduler
open CompetitorMonomialStream CompetitorMonomialProducts CompetitorRationalDecision
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem record_run_perm {l r : ℕ} (a : WilliamsAlgorithm) (w Q : ℕ)
    (rows : List (List (List (Equation l r)))) (row : EquationRow.Input)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (q : ℚ) (denominator : ℕ)
    (hc : row.cuts.Perm (RowPowerBinLift.batch w Q rows))
    (hw : ∀ ms∈rows, ∀ e∈ms.flatten, equationMagnitudeBound e<2^w)
    (hrows : rows.length<2^Q) (hQ : Q≤row.p)
    (hp : positive q<2^(scalarWidth (EquationRow.request row) Q))
    (hn : negative q<2^(scalarWidth (EquationRow.request row) Q))
    (hq : q.den<2^(scalarWidth (EquationRow.request row) Q))
    (hd : denominator<2^(scalarWidth (EquationRow.request row) Q))
    (hpos : 0<denominator) :
    (CompetitorOffsetScalar.entry row.odd (CompetitorCountTable.rowValues rows row)
      select q denominator).Valid (scalarWidth (EquationRow.request row) Q) ∧
    ∃ actual, run (CompetitorCountTableRecord.machine a)
      (CompetitorCountTableRecord.budget a (EquationRow.request row) Q)
      (CompetitorCountTableRecord.input (producer a) (EquationRow.request row) Q row.odd q denominator
        (CompetitorSelectedCells.cells row.odd (CompetitorCountTable.rowValues rows row) select))=some actual ∧
      actual.steps≤CompetitorCountTableRecord.envelope a (EquationRow.request row) ∧
      actual.final.tapes (CompetitorCountTableRecord.slots (producer a) 117)=recordWord
        (scalarWidth (EquationRow.request row) Q) q
        (selected (CompetitorSelectedCells.cells row.odd (CompetitorCountTable.rowValues rows row) select)).sum denominator ∧
      actual.final.heads (CompetitorCountTableRecord.slots (producer a) 117)=(recordWord
        (scalarWidth (EquationRow.request row) Q) q
        (selected (CompetitorSelectedCells.cells row.odd (CompetitorCountTable.rowValues rows row) select)).sum denominator).length ∧
      actual.final.tapes (CompetitorCountTableRecord.slots (producer a) 0)=
        MatrixScoreBatch.physicalInput (EquationRow.request row) := by
  have hfit : ∀ i j, CompetitorCountTable.rowValues rows row i j<2^Q :=
    fun i j => CompetitorRowCountMeaning.count_fit Q rows hrows i.val j.val
  refine ⟨CompetitorOffsetScalar.entry_valid (EquationRow.request row) Q row.odd
    (CompetitorCountTable.rowValues rows row) select q denominator hfit hp hn hq hd hpos,?_⟩
  have hwidth : Q≤CompetitorSameBucketColdDense.width (EquationRow.request row) := by
    rw [CompetitorSameBucketColdDense.width_eq]
    change Q≤row.d+2*(row.p+1)+3
    omega
  obtain ⟨actual,ha,hs,ht,hh,h0⟩ := CompetitorCountTableRecord.record_run a (EquationRow.request row)
    Q row.odd (CompetitorCountTable.rowValues rows row) select q denominator hwidth
    (CompetitorRowCountMeaning.odd_even_size row) hfit
    (fun i => CompetitorRowCountMeaning.request_modEq_perm w Q rows row hc hw i.divNat i.modNat)
  have hQ' : Q≤(EquationRow.request row).p := by change Q≤row.p+1; omega
  exact ⟨actual,ha,hs.trans (CompetitorCountTableRecord.budget_bound a (EquationRow.request row) Q hQ'),ht,hh,h0⟩

end NearCubicWires.RepairOrdinary.CloseoutRows
