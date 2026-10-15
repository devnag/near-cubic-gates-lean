import Proof.MachineModel.ClosureScannedRow
import Proof.CaseAnalysis.FinalSupplierTable

/-! Consume the common-bank transaction at the paper's actual hardwired row.
A.12.1 fixes Q = K+1; A.13.9/A.13.10 select entries of this exact table.
The native header and mask are physical inputs, whose upstream production is
still required. The selected count is computed, never an input word.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.ActualRow
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RepairOrdinary
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler
open SourceInterfaces RepairSource RepairSource.CloseoutFinal
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients
open CompetitorSelectedCount CompetitorCountMask C10SupplierRowInput
open CompetitorCrossScheduler (producer)

theorem run {q : Nat} (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : Nat)
    (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
    (C D : Nat) (est : CompetitorValidity.Estimate) (den : Nat)
    (select :
      Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U →
      Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U → Bool)
    (old : Fin (WholePrefix.tapes (producer printer)) → List Bool) (out : List Bool)
    (hcapacity : old (Retained.capacity (producer printer)) = List.replicate C true)
    (hC : (Header.stream (rowInput a live occ s harity P w hs hmon hpos hload)).length ≤ C)
    (hCD : C ≤ D)
    (hd : (rowInput a live occ s harity P w hs hmon hpos hload).d ≤ D)
    (hp : (rowInput a live occ s harity P w hs hmon hpos hload).p ≤ D)
    (hDpos : 1 ≤ D)
    (hD : Driver.value printer
      (rowInput a live occ s harity P w hs hmon hpos hload).d
      (rowInput a live occ s harity P w hs hmon hpos hload).p
      (rowInput a live occ s harity P w hs hmon hpos hload).cuts.length C ≤ D) :
    let row := rowInput a live occ s harity P w hs hmon hpos hload
    let word := Stream.recordWord (scalarWidth (EquationRow.request row) (live.card+1)) est
      (selected (CompetitorSelectedCells.cells row.odd
        (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload) select)).sum den
    Step (ScannedRow.machine printer) (ScannedRow.budget printer row D (live.card+1))
      (ScannedRow.heads (producer printer) out)
      (ScannedRow.input (producer printer) row C D (live.card+1) est den select old out)
      (ScannedRow.heads (producer printer) (out++word))
      (ScannedRow.output (producer printer) row C D (live.card+1) est den select (out++word)) ∧
    ScannedRow.budget printer row D (live.card+1) ≤ 11*D+80 := by
  dsimp only
  have hQ := rowInput_p a live occ s harity P w hs hmon hpos hload
  exact ⟨ScannedRow.run printer _ C D (live.card+1) est den
    (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload) select old out
    hcapacity hCD hd hp hDpos hC hQ
    (C10SupplierTable.table_lt a live occ s harity P w hs hmon hpos hload)
    (fun i => C10SupplierTable.table_modEq a live occ s harity P w hs hmon hpos hload
      i.divNat i.modNat) hD,
    ScannedRow.budget_le printer _ C D (live.card+1) hC hQ hD⟩

/-- At the actual row's envelope the native input cost and printer cost add.+No multiplication of the native description by the residual table occurs. -/
theorem additive_budget (printer : WilliamsAlgorithm) (row : EquationRow.Input)
    (C Q : Nat) (hC : (Header.stream row).length ≤ C)
    (hQ : Q ≤ (EquationRow.request row).p) :
    ScannedRow.budget printer row (Driver.value printer row.d row.p row.cuts.length C) Q ≤
      704*(C+1)+22000000*(row.d+row.p+row.cuts.length+1)^3+
      11*Driver.tableValue printer row.d row.p+80 := by
  have h := ScannedRow.budget_le printer row C
    (Driver.value printer row.d row.p row.cuts.length C) Q hC hQ le_rfl
  calc
    _ ≤ 11*Driver.value printer row.d row.p row.cuts.length C+80 := h
    _ = _ := by unfold Driver.value; ring

end NearCubicWires.P1Closure.ActualRow
