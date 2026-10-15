import Proof.MachineModel.PlanDirectCount
import Proof.CaseAnalysis.RowsCommonInput
import Proof.Supplier.RowOccurrenceReusable

/-! Test the paper's repair at the actual table consumer before changing the
native emitter. A.12 uses a per-equation bit bound and a per-monomial degree,
not the length of the global live-assignment cache. Existing commonInput
already accepts those separate bounds and the existing count machine works
unchanged. Producing the compact serialized input is still an obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactRow
open LocalBitMultitape RepairOrdinary RepairRepresentation SupplierPrinter
open SupplierPipeline SupplierEstimator ThresholdCompiler SupplierPrime
open ThresholdAlignedEnvelope MatrixScoreBatch EquationRow RowBinLift
open CompetitorSelectedCount CompetitorCountMask CompetitorCrossScheduler

variable (s w degree Q : Nat)
  (rows : List (List (List (Equation ((s+1)/2) (s/2)))))
  (hs : 67 ≤ s) (hg : (RowBinLift.batch Q rows).length^100 ≤ 2^s)
  (hd : ∀ ms∈rows, ∀ m∈ms, m.length≤degree)
  (hw : ∀ ms∈rows, ∀ e∈ms.flatten, equationMagnitudeBound e<2^w)

theorem width :
    (CloseoutRows.commonInput s w degree Q rows hs hg hd hw).p = w*(degree*Q)+Q := rfl

theorem table_modEq
    (i j : Fin (EquationRow.request (CloseoutRows.commonInput s w degree Q rows hs hg hd hw)).U) :
    let row := CloseoutRows.commonInput s w degree Q rows hs hg hd hw
    Int.ModEq ((2 : Int)^Q)
      (weightedDominance (leftScore (request row)) (rightScore (request row))
        (weight (request row)) i j)
      (CompetitorCountTable.rowValues rows row i j) := by
  apply CompetitorRowCountMeaning.request_modEq_perm w Q rows _
  · exact CloseoutRows.ordered_batch_perm w Q rows
  · exact hw

theorem count_run (a : WilliamsAlgorithm) (hn : rows.length<2^Q)
    (select : Fin (EquationRow.request (CloseoutRows.commonInput s w degree Q rows hs hg hd hw)).U →
      Fin (EquationRow.request (CloseoutRows.commonInput s w degree Q rows hs hg hd hw)).U → Bool) :
    let row := CloseoutRows.commonInput s w degree Q rows hs hg hd hw
    let counts := CompetitorSelectedCells.cells row.odd (CompetitorCountTable.rowValues rows row) select
    ∃ actual, run (P1Plan.DirectCount.machine a)
      (P1Plan.DirectCount.budget a (request row) Q)
      (P1Plan.DirectCount.input (producer a) (request row) Q row.odd counts) = some actual ∧
      actual.steps ≤ P1Plan.DirectCount.budget a (request row) Q ∧
      (∀ i, actual.final.heads (CompetitorSelectedTable.slot (producer a) i) =
        CompetitorSelectedRequestCount.outputHeads Q ((request row).U*(request row).U) i) ∧
      actual.final.tapes (CompetitorSelectedTable.slot (producer a) 86) =
        frame (SignedSortKey.binary (scalarWidth (request row) Q) (selected counts).sum) ∧
      actual.final.tapes (CompetitorSelectedTable.slot (producer a) 0) = physicalInput (request row) := by
  dsimp only
  apply P1Plan.DirectCount.run
  · rw [CompetitorSameBucketColdDense.width_eq]
    change Q ≤ (s+1)/2+2*(w*(degree*Q)+Q+1)+3
    omega
  · exact CompetitorRowCountMeaning.odd_even_size _
  · intro i j
    exact CompetitorRowCountMeaning.count_fit Q rows hn i.val j.val
  · intro i
    exact table_modEq s w degree Q rows hs hg hd hw i.divNat i.modNat

end NearCubicWires.P1Closure.CompactRow

namespace NearCubicWires.P1Closure.CompactEmitter
open LocalBitMultitape RepairOrdinary RepairRepresentation Streaming

/- The existing physical machine accepts an independent bit bound. This
application supplies its reset capacities; it does not supply the source
cache, occurrence word, or the bound for the actual C.10 family. -/
theorem occurrence_run {n : Nat} (gs : List (ExactThresholdGate n))
    (i : Nat) (hi : i<gs.length) (j : Nat) (hj : j≤n) (b : Nat)
    (hb : natBitLength (RowCachedCoordinateAppend.value gs i hi j hj).natAbs≤b)
    (pre tail positive negative : List Bool) :
    let C := RowCachedCoordinateBounds.inner b
    let D := RowCachedCoordinateBounds.outer gs b
    let source := pre++RowIndexField.word i++tail
    let P := positive++marks (RowPowerNativeReusable.block b
      (RowCachedCoordinateAppend.value gs i hi j hj) false)
    let N := negative++marks (RowPowerNativeReusable.block b
      (RowCachedCoordinateAppend.value gs i hi j hj) true)
    ∃ r, runFrom RowOccurrenceReusable.machine
      (RowOccurrenceReusable.budget gs i hi j hj b C D)
      (RowOccurrenceReusable.entry gs j b C D source pre.length positive negative)=some r ∧
      r.final.heads=(RowOccurrenceReusable.entry gs j b C D source (pre.length+i+1) P N).heads ∧
      r.final.tapes=(RowOccurrenceReusable.entry gs j b C D source (pre.length+i+1) P N).tapes ∧
      r.steps=RowOccurrenceReusable.budget gs i hi j hj b C D := by
  dsimp only
  apply RowOccurrenceReusable.reusable_run
  · exact RowCachedCoordinateBounds.inner_fits _ _ hb
  · exact RowCachedCoordinateBounds.outer_fits gs i hi j hj b hb
  · unfold RowCachedCoordinateBounds.outer RowCachedCoordinateBounds.size
    nlinarith

end NearCubicWires.P1Closure.CompactEmitter
