import Proof.CaseAnalysis.CloseoutRowsEstimatorPaidOwnedWarmJoin

/-! Strengthened ownership follows the actual driver and original Warm receipts. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem warm_owned_run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
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
    WarmOwned a (producer a) (warmMachine a) (warmBudget a row C Q)
      (ScannedClean.budget a row C+1+(8*Driver.value a row.d row.p row.cuts.length C+
        40*scalarWidth (EquationRow.request row) Q+74)) (warmEntry a row C Q q denominator select out) row C
      (Driver.value a row.d row.p row.cuts.length C)
      (out++Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
        (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator)
      (WarmFields.words row Q q denominator select) := by
  have hp:=driver_run a row C (WarmFields.words row Q q denominator select) out
  have hq:=WarmPrepared.run a row C Q q denominator f select out hC hQ hf hc
  refine warm_owned_join a (producer a) row C (Driver.value a row.d row.p row.cuts.length C)
    (scalarWidth (EquationRow.request row) Q) _ _ (WarmFields.words row Q q denominator select) out _
    (driver a) (driverEntry a row C (WarmFields.words row Q q denominator select) out)
    (WarmPrepared.machine a) (WarmPrepared.entry a row C Q q denominator select out) hp
    (prepare_config (WarmPrepare.machine (producer a)) (WarmPrepared.last a) _ _) hq ?_ ?_
  · intro extra r hr ht i hi
    obtain ⟨n,hn⟩:=driver_private a row C (WarmFields.words row Q q denominator select) out r hr i hi
    rw [ht] at hn
    exact ⟨n,by simpa only [Fin.addCases_right] using hn⟩
  · intro r hr i hi
    have h:=WarmPrepared.protected_run a (i.castAdd (CloseoutRowsRawRecord.tapes (producer a))) hi _ _ r hr
    have he : WarmPrepared.entry a row C Q q denominator select out=
        ⟨(WarmPrepared.machine a).start,WarmPrepare.heads (producer a) out,
          publicInput (producer a) row C (Driver.value a row.d row.p row.cuts.length C)
            (WarmFields.words row Q q denominator select) out⟩:=
      prepare_config (WarmPrepare.machine (producer a)) (WarmPrepared.last a) _ _
    rw [he] at h
    exact h.trans (public_old (producer a) row C _ _ out i)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
