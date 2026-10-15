import Proof.Hierarchy.CompetitorCountRecordAppend

namespace NearCubicWires.RepairOrdinary.CompetitorCountRecordAppend
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (b : ℕ) : budget b≤41100*(b+1)^2 := by
  have h := CompetitorDimensions.budget_bound b
  unfold budget CompetitorCountRecordPrepare.budget CompetitorRationalDecision.width
  unfold CompetitorReusableDecision.capacity at h
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorCountRecordAppend
