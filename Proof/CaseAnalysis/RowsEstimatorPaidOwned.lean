import Proof.CaseAnalysis.RowsEstimatorPaidOwnedRun
import Proof.CaseAnalysis.CloseoutRowsEstimatorPaidOwnedColdJoin

/-! Complete original scan, scalar evaluation, and retirement retain the reusable bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem owned_run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (f : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) (out : List Bool)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : ℤ)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat)) :
    Owned a (producer a) (machine a) (budget a row C Q) (bound a row C Q)
      (entry a row C Q q denominator select out) row C (Driver.value a row.d row.p row.cuts.length C)
      (out++Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
        (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator)
      (WarmFields.words row Q q denominator select) := by
  have hw:=warm_owned_run a row C Q q denominator f select out hC hQ hf hc
  have hr:=retire_owned_join a (producer a) row C (Driver.value a row.d row.p row.cuts.length C) _ _ _ _
    (warmMachine a) (warmEntry a row C Q q denominator select out) hw
  exact cold_owned_join a (producer a) row C (Driver.value a row.d row.p row.cuts.length C) _ _ out _
    (WarmFields.words row Q q denominator select) (retiredMachine a)
    (Composition.leftConfig 5 (warmEntry a row C Q q denominator select out))
    (nested_start (driver a) (warm a) (retire a (producer a)) _ _) hC hr

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
