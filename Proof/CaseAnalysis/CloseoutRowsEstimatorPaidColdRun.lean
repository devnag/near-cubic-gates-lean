import Proof.CaseAnalysis.CloseoutRowsEstimatorPaidColdJoin

/-! The original native append input reaches the scalar consumer through
the mandatory scan, actual D allocation, paid copies, Warm and retirement. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def retiredMachine (a : WilliamsAlgorithm):=Composition.machine (warmMachine a) (retire a (producer a))
noncomputable def machine (a : WilliamsAlgorithm):=Composition.machine (scanner a (producer a)) (retiredMachine a)
noncomputable def entry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) (out : List Bool):=
  prefixEntry (retiredMachine a) (scanEntry a (producer a) row C (WarmFields.words row Q q denominator select) out)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ):=
  Scanned.budget row C+1+(warmBudget a row C Q+1+(2*Driver.value a row.d row.p row.cuts.length C+4))
noncomputable def bound (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ):=
  Scanned.budget row C+1+(ScannedClean.budget a row C+1+
    (8*Driver.value a row.d row.p row.cuts.length C+40*scalarWidth (EquationRow.request row) Q+74)+
    1+(2*Driver.value a row.d row.p row.cuts.length C+4))

theorem nested_start {n s t u : ℕ} (first : Machine n s) (second : Machine n t)
    (third : Machine n u) (H : Fin n → ℕ) (A : Fin n → List Bool) :
    Composition.leftConfig u (WarmPrepared.startWith first second H A)=
      (⟨(Composition.machine (Composition.machine first second) third).start,H,A⟩ : Configuration n (s+t+u)) := rfl

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
        (f i.divNat i.modNat)) :
    RetiredJoined a (producer a) (machine a) (budget a row C Q) (bound a row C Q)
      (entry a row C Q q denominator select out) (Driver.value a row.d row.p row.cuts.length C)
      (out++Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
        (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator)
      (WarmFields.words row Q q denominator select) := by
  have hw:=warm_run a row C Q q denominator f select out hC hQ hf hc
  have hr:=retire_join a (producer a) (Driver.value a row.d row.p row.cuts.length C) _ _ _ _
    (warmMachine a) (warmEntry a row C Q q denominator select out) hw
  exact cold_join a (producer a) row C (Driver.value a row.d row.p row.cuts.length C) _ _ out _
    (WarmFields.words row Q q denominator select) (retiredMachine a)
    (Composition.leftConfig 5 (warmEntry a row C Q q denominator select out))
    (nested_start (driver a) (warm a) (retire a (producer a)) _ _) hC hr

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
