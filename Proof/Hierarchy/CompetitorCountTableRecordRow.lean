import Proof.Hierarchy.CompetitorCountTableRecord
import Proof.Hierarchy.CompetitorCountTableBounds

/-! Actual power-bin-lift rows discharge the count/congruence hypotheses
of the physical table-to-record caller. Its complete cost keeps the same
quadratic U factor and source-fixed short-width exponent. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountTableRecord
open LocalBitMultitape RecoveryRootRound RepairRepresentation MatrixScoreBatch
open CompetitorSelectedCount CompetitorCountMask
open CompetitorCrossScheduler (producer)
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def coefficient (a : WilliamsAlgorithm) := CompetitorCountTable.coefficient a+1034000
noncomputable def envelope (a : WilliamsAlgorithm) (r : Request) :=
  coefficient a*(r.U+1)^2*(r.d+r.p+1)^CompetitorCrossScheduler.exponent a

theorem budget_bound (a : WilliamsAlgorithm) (r : Request) (Q : ℕ) (hQ : Q≤r.p) :
    budget a r Q≤envelope a r := by
  have hwidth : Q≤CompetitorSameBucketColdDense.width r := by
    rw [CompetitorSameBucketColdDense.width_eq]
    omega
  have ht := CompetitorCountTable.budget_bound a r Q hwidth
  have hr := CompetitorCountRecordRequest.budget_bound r Q hQ
  have hp : (r.d+r.p+1)^2≤(r.d+r.p+1)^CompetitorCrossScheduler.exponent a :=
    Nat.pow_le_pow_right (by omega) (by unfold CompetitorCrossScheduler.exponent;omega)
  have hr' := hr.trans (Nat.mul_le_mul_left (1034000*(r.U+1)^2) hp)
  unfold budget envelope coefficient CompetitorCountTable.envelope at *
  nlinarith

theorem row_run {l r : ℕ} (a : WilliamsAlgorithm) (w Q : ℕ)
    (rows : List (List (List (Equation l r)))) (row : EquationRow.Input)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (q : ℚ) (denominator : ℕ)
    (hc : row.cuts=RowPowerBinLift.batch w Q rows)
    (hw : ∀ ms ∈ rows,∀ e ∈ ms.flatten,equationMagnitudeBound e<2^w)
    (hrows : rows.length<2^Q) (hQ : Q≤row.p) :
    ∃ actual,run (machine a) (budget a (EquationRow.request row) Q)
      (input (producer a) (EquationRow.request row) Q row.odd q denominator
        (CompetitorSelectedCells.cells row.odd (CompetitorCountTable.rowValues rows row) select))=some actual ∧
      actual.steps≤envelope a (EquationRow.request row) ∧
      actual.final.tapes (slots (producer a) 117)=CompetitorMonomialStream.recordWord
        (scalarWidth (EquationRow.request row) Q) q
        (selected (CompetitorSelectedCells.cells row.odd (CompetitorCountTable.rowValues rows row) select)).sum denominator ∧
      actual.final.heads (slots (producer a) 117)=(CompetitorMonomialStream.recordWord
        (scalarWidth (EquationRow.request row) Q) q
        (selected (CompetitorSelectedCells.cells row.odd (CompetitorCountTable.rowValues rows row) select)).sum denominator).length ∧
      actual.final.tapes (slots (producer a) 0)=MatrixScoreBatch.physicalInput (EquationRow.request row) := by
  have hwidth : Q≤CompetitorSameBucketColdDense.width (EquationRow.request row) := by
    rw [CompetitorSameBucketColdDense.width_eq]
    change Q≤row.d+2*(row.p+1)+3
    omega
  obtain ⟨actual,ha,hs,ht,hh,h0⟩ := record_run a (EquationRow.request row) Q row.odd
    (CompetitorCountTable.rowValues rows row) select q denominator hwidth
    (CompetitorRowCountMeaning.odd_even_size row)
    (fun i j => CompetitorRowCountMeaning.count_fit Q rows hrows i.val j.val)
    (fun i => CompetitorRowCountMeaning.request_modEq w Q rows row hc hw i.divNat i.modNat)
  have hQ' : Q≤(EquationRow.request row).p := by change Q≤row.p+1;omega
  exact ⟨actual,ha,hs.trans (budget_bound a (EquationRow.request row) Q hQ'),ht,hh,h0⟩

end NearCubicWires.RepairOrdinary.CompetitorCountTableRecord
