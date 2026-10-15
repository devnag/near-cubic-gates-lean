import Proof.Supplier.RowCoefficientReusable

/-! One uniform local coefficient workspace and budget, derived from actual
cache bytes, native arity, cached child count and ordered occurrence count.
This removes the local capacity premise; cold driver production is separate. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientBounds
open LocalBitMultitape RepairRepresentation Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) (m : ℕ) :=
  16384*(m+1)*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+40

theorem call_fits {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    RowCoefficientStream.budget gs j hj indices+1 ≤ capacity gs indices.length := by
  have h := RowCoefficientStream.budget_bound gs j hj indices
  unfold capacity
  nlinarith

theorem inner_fits {n : ℕ} (gs : List (ExactThresholdGate n)) (m : ℕ) :
    RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ capacity gs m := by
  unfold RowCachedCoordinateBounds.outer capacity
  nlinarith

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    2*RowCoefficientStream.budget gs j hj indices+2*capacity gs indices.length+7 ≤
      65536*(indices.length+1)*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+165 := by
  have h := RowCoefficientStream.budget_bound gs j hj indices
  unfold capacity
  nlinarith

theorem reusable_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom RowCoefficientStreamClear.machine
      (2*RowCoefficientStream.budget gs j hj indices+2*capacity gs indices.length+7)
      (RowCoefficientStreamClear.entry gs j (capacity gs indices.length) tail out indices)=some r ∧
      r.final.heads=(RowCoefficientStreamClear.entry gs j (capacity gs indices.length) tail
        (out++frame (RowCoefficientStream.field gs j hj indices)) indices).heads ∧
      r.final.tapes=(RowCoefficientStreamClear.entry gs j (capacity gs indices.length) tail
        (out++frame (RowCoefficientStream.field gs j hj indices)) indices).tapes ∧
      r.steps ≤ 65536*(indices.length+1)*
        RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+165 := by
  obtain ⟨r,hr,rh,rt,rs⟩ := RowCoefficientReusable.reusable_run gs j hj (capacity gs indices.length)
    tail out indices (call_fits gs j hj indices) (inner_fits gs indices.length)
  exact ⟨r,hr,rh,rt,rs.trans (budget_bound gs j hj indices)⟩

end NearCubicWires.RepairOrdinary.RowCoefficientBounds
