import Proof.Supplier.RowCommonReusable

/-! A single explicit allocation pays the common-width coefficient and its
complete physical cleanup. The remaining cold caller must produce these
raw counters; no local capacity inequality survives this endpoint. -/
namespace NearCubicWires.RepairOrdinary.RowCommonBounds
open LocalBitMultitape RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) (m p : ℕ) :=
  16384*(m+1)*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+16*p+64
def bound {n : ℕ} (gs : List (ExactThresholdGate n)) (m p : ℕ) :=
  65536*(m+1)*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+64*p+256

theorem call_fits {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p : ℕ)
    (indices : List (Fin gs.length)) :
    RowCommonCoefficient.budget gs j hj p indices+1 ≤ capacity gs indices.length p := by
  have h := RowCoefficientWhole.budget_bound gs j hj indices
  unfold RowCommonCoefficient.budget capacity
  nlinarith

theorem padding_fits {n : ℕ} (gs : List (ExactThresholdGate n)) (m p : ℕ) :
    2*p+5 ≤ capacity gs m p := by unfold capacity; omega

theorem inner_fits {n : ℕ} (gs : List (ExactThresholdGate n)) (m p : ℕ) :
    RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ capacity gs m p := by
  unfold RowCachedCoordinateBounds.outer capacity
  nlinarith

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p : ℕ)
    (indices : List (Fin gs.length)) :
    2*RowCommonCoefficient.budget gs j hj p indices+2*capacity gs indices.length p+7 ≤
      bound gs indices.length p := by
  have h := RowCoefficientWhole.budget_bound gs j hj indices
  unfold RowCommonCoefficient.budget capacity bound
  nlinarith

theorem reusable_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : RowCoordinateLoop.width gs indices ≤ p) :
    ∃ r,runFrom RowCommonClear.machine (bound gs indices.length p)
      (RowCommonClear.entry gs j p (capacity gs indices.length p) tail out indices)=some r ∧
      r.final.heads=(RowCommonClear.entry gs j p (capacity gs indices.length p) tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices).heads ∧
      r.final.tapes=(RowCommonClear.entry gs j p (capacity gs indices.length p) tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices).tapes ∧
      r.steps ≤ bound gs indices.length p := by
  obtain ⟨r,hr,rh,rt,rs⟩ := RowCommonReusable.reusable_run gs j hj p (capacity gs indices.length p)
    tail out indices hp (call_fits gs j hj p indices) (padding_fits gs indices.length p)
    (inner_fits gs indices.length p)
  have hb := budget_bound gs j hj p indices
  have more := runFrom_moreFuel RowCommonClear.machine _
    (bound gs indices.length p-(2*RowCommonCoefficient.budget gs j hj p indices+2*capacity gs indices.length p+7)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,rh,rt,rs.trans hb⟩

end NearCubicWires.RepairOrdinary.RowCommonBounds
