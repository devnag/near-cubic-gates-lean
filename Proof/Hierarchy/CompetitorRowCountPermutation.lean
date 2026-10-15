import Proof.Hierarchy.CompetitorCountTableBounds

/-! Physical positional-subset enumeration may permute external cut order.
The exact signed sum is invariant under that permutation; ordered equations
inside each power-radix stack are unchanged. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRowCountMeaning
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope MatrixScoreBatch EquationRow RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem request_modEq_perm {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r))))
    (input : EquationRow.Input) (hc : input.cuts.Perm (RowPowerBinLift.batch w Q rows))
    (hw : ∀ ms ∈ rows,∀ e ∈ ms.flatten,equationMagnitudeBound e<2^w)
    (row column : Fin (request input).U) : Int.ModEq ((2 : ℤ)^Q)
      (weightedDominance (leftScore (request input)) (rightScore (request input))
        (weight (request input)) row column) (count rows row.val column.val) := by
  rw [request_value]
  have hs := (hc.map (fun c => exactValue c row.val column.val)).sum_eq
  rw [hs,batch_value w Q rows hw]
  exact lifted_modEq Q rows row.val column.val

end NearCubicWires.RepairOrdinary.CompetitorRowCountMeaning

namespace NearCubicWires.RepairOrdinary.CompetitorCountTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
open CompetitorCrossScheduler (producer)
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem row_run_perm {l r : ℕ} (a : WilliamsAlgorithm) (w Q : ℕ)
    (rows : List (List (List (Equation l r)))) (row : EquationRow.Input)
    (hc : row.cuts.Perm (RowPowerBinLift.batch w Q rows))
    (hw : ∀ ms ∈ rows,∀ e ∈ ms.flatten,equationMagnitudeBound e<2^w)
    (hrows : rows.length<2^Q) (hQ : Q≤row.p) :
    ∃ actual,run (machine a) (budget a (EquationRow.request row) Q)
      (input (producer a) (EquationRow.request row) Q row.odd)=some actual ∧
      actual.steps≤budget a (EquationRow.request row) Q ∧
      actual.final.heads=heads (producer a) (MatrixScoreBatch.output (EquationRow.request row)).length ∧
      actual.final.tapes (slot (producer a) 141)=CompetitorFinalTable.word Q row.odd (rowValues rows row) ∧
      actual.final.tapes (slot (producer a) 36)=List.replicate Q true ∧
      actual.final.tapes (slot (producer a) 37)=UnaryTemplate.tape (EquationRow.request row).U ∧
      actual.final.tapes (slot (producer a) 38)=[row.odd] ∧
      actual.final.tapes (old (producer a) (CompetitorCountBanks.field (producer a) 0))=
        MatrixScoreBatch.physicalInput (EquationRow.request row) := by
  have hwidth : Q≤CompetitorSameBucketColdDense.width (EquationRow.request row) := by
    rw [CompetitorSameBucketColdDense.width_eq]
    change Q≤row.d+2*(row.p+1)+3
    omega
  exact cold_run a (EquationRow.request row) Q row.odd (rowValues rows row) hwidth
    (CompetitorRowCountMeaning.odd_even_size row)
    (fun i => CompetitorRowCountMeaning.count_fit Q rows hrows i.divNat.val i.modNat.val)
    (fun i => CompetitorRowCountMeaning.request_modEq_perm w Q rows row hc hw i.divNat i.modNat)

end NearCubicWires.RepairOrdinary.CompetitorCountTable
