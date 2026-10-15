import Proof.CaseAnalysis.RowsEstimatorReuse
import Proof.CaseAnalysis.RowsEstimatorInputSupport
import Proof.CaseAnalysis.RowsEstimatorReuseRetained

/-! Actual shared estimator consumer after scanner/driver preparation.
The chosen D discharges runtime and every literal input-support bound;
its ordinary driver and metadata producers must fill the stated entry. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmActual
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open RepairSource.RecoveryTseitinReadOnly
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (a : WilliamsAlgorithm):=WarmReuse.machine (producer a) (Warm.machine a)
noncomputable def entry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) (out : List Bool):=
  WarmReuse.entry (producer a) (Warm.machine a) (Driver.value a row.d row.p row.cuts.length C)
    (Warm.input (producer a) row C Q q denominator select) out
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ):=
  Reuse.budget (Warm.budget a row Q) (scalarWidth (EquationRow.request row) Q)
    (Driver.value a row.d row.p row.cuts.length C)

theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (f : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) (out : List Bool)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : ℤ)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat)) : ∃ r,
    runFrom (machine a) (budget a row C Q) (entry a row C Q q denominator select out)=some r ∧
      r.steps ≤ 4*Driver.value a row.d row.p row.cuts.length C+
        40*scalarWidth (EquationRow.request row) Q+64 ∧
      r.final.heads=(fun i => if i=Reuse.output (producer a) then
        (out++Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator).length else 0) ∧
      r.final.tapes (Reuse.output (producer a))=out++Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
        (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator ∧
      (∀ i,r.final.tapes (Reuse.work (producer a) i)=
        List.replicate (Driver.value a row.d row.p row.cuts.length C) false) ∧
      r.final.tapes (Reuse.driver (producer a))=List.replicate (Driver.value a row.d row.p row.cuts.length C) true ∧
      r.final.tapes (Reuse.log (producer a))=List.replicate (Driver.value a row.d row.p row.cuts.length C+1) false := by
  obtain ⟨source,hs,ht,_hm⟩:=Warm.run a row C Q q denominator f select hQ hf hc
  have hb:=Driver.fuel_bound a row C Q hC hQ
  have he:=Warm.split_budget a row C Q
  have hsteps:=runFrom_steps_le _ _ _ _ hs
  have hd : source.steps+1 ≤ Driver.value a row.d row.p row.cuts.length C := by omega
  exact WarmReuse.run (producer a) (Warm.machine a) _ (Warm.budget a row Q)
    (scalarWidth (EquationRow.request row) Q) (Driver.value a row.d row.p row.cuts.length C)
    q _ denominator out source hs ht hd (Driver.append_bound a row C Q hQ)
    (InputSupport.warm a row C Q q denominator select hC hQ)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmActual
