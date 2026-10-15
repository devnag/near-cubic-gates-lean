import Proof.Supplier.RowOffsetFamilies
import Proof.Hierarchy.CompetitorCountTableRecordRow

/-! Actual residual-cell selectors for the cropped matrix-count consumer.
The physical row carries the larger external RIGHT half and the column the
smaller external LEFT half. Offsets are summed, with no cardinality divisor. -/
namespace NearCubicWires.RepairOrdinary.RowExternalSelection
open SupplierPipeline SupplierEstimator SupplierPrime CompetitorCountMask CompetitorSelectedCells
open CompetitorFinalTable
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def input {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale row column : ℕ) : BitInput q :=
  normalizedSplitInput (normalizedLiveSet occurrences liveScale) (fun _=>false)
    (fun i=>column.testBit i.val) (fun i=>row.testBit i.val)

theorem input_left {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale row column : ℕ)
    (i : Fin (normalizedExternalLeftCount (normalizedLiveSet occurrences liveScale))) :
    input occurrences liveScale row column
      (normalizedExternalLeftCoordinate (normalizedLiveSet occurrences liveScale) i)=column.testBit i.val :=
  normalizedSplitInput_externalLeft _ _ _ _ i

theorem input_right {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale row column : ℕ)
    (i : Fin (normalizedExternalRightCount (normalizedLiveSet occurrences liveScale))) :
    input occurrences liveScale row column
      (normalizedExternalRightCoordinate (normalizedLiveSet occurrences liveScale) i)=row.testBit i.val :=
  normalizedSplitInput_externalRight _ _ _ _ i

def symmetricOffset (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale row column : ℕ) :=
  RowOffsets.symmetricOffsets r liveScale (input (symmetricFourfoldOccurrences r) liveScale row column)

def thresholdOffset {q cutoff : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (equation : LabelledEquation (Fin occurrences.length))
    (prime : PrimeIndex cutoff) (row column : ℕ) :=
  RowOffsets.thresholdOffset occurrences liveScale (input occurrences liveScale row column) equation prime

def select {α : Type} [DecidableEq α] {u : ℕ}
    (offset : Fin u→Fin u→α) (wanted : α) (i j : Fin u) : Bool := decide (offset i j=wanted)

def total {u : ℕ} (odd : Bool) (f : Fin u→Fin u→ℕ) : ℕ :=
  if odd then ∑ i,∑ j : Fin (u/2),f i (lowerColumn j) else ∑ i,∑ j,f i j

theorem rect_selected_sum {u v : ℕ} (f : Fin u→Fin v→ℕ) (s : Fin u→Fin v→Bool) :
    (selected (rect f s)).sum=∑ i,∑ j,if s i j then f i j else 0 := by
  simp [selected,rect,List.map_flatten,List.map_ofFn,List.sum_flatten,List.sum_ofFn,Function.comp_def]

theorem cells_selected_sum {u : ℕ} (odd : Bool) (f : Fin u→Fin u→ℕ) (s : Fin u→Fin u→Bool) :
    (selected (cells odd f s)).sum=total odd (fun i j=>if s i j then f i j else 0) := by
  cases odd <;> simp [cells,total,rect_selected_sum]

theorem offset_sum {α : Type} [Fintype α] [DecidableEq α] {u : ℕ}
    (odd : Bool) (offset : Fin u→Fin u→α) (f : α→Fin u→Fin u→ℕ) :
    (∑ wanted,(selected (cells odd (f wanted) (select offset wanted))).sum)=
      total odd (fun i j=>f (offset i j) i j) := by
  simp only [cells_selected_sum,select,decide_eq_true_eq]
  cases odd
  all_goals
    simp only [total,Bool.false_eq_true,ite_false,ite_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp

def symmetricSelect {u : ℕ} (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) (wanted : RowOffsets.SymmetricOffsets r) : Fin u→Fin u→Bool :=
  select (fun i j=>symmetricOffset r liveScale i.val j.val) wanted

def thresholdSelect {q cutoff u : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (equation : LabelledEquation (Fin occurrences.length))
    (prime : PrimeIndex cutoff) (wanted : Fin prime.val) : Fin u→Fin u→Bool :=
  select (fun i j=>thresholdOffset occurrences liveScale equation prime i.val j.val) wanted

theorem symmetric_sum {u : ℕ} (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) (odd : Bool) (f : RowOffsets.SymmetricOffsets r→Fin u→Fin u→ℕ) :
    (∑ wanted,(selected (cells odd (f wanted) (symmetricSelect r liveScale wanted))).sum)=
      total odd (fun i j=>f (symmetricOffset r liveScale i.val j.val) i j) :=
  offset_sum odd _ f

theorem threshold_sum {q cutoff u : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (equation : LabelledEquation (Fin occurrences.length))
    (prime : PrimeIndex cutoff) (odd : Bool) (f : Fin prime.val→Fin u→Fin u→ℕ) :
    (∑ wanted,(selected (cells odd (f wanted) (thresholdSelect occurrences liveScale equation prime wanted))).sum)=
      total odd (fun i j=>f (thresholdOffset occurrences liveScale equation prime i.val j.val) i j) :=
  offset_sum odd _ f

end
end NearCubicWires.RepairOrdinary.RowExternalSelection
