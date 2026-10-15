import Proof.Hierarchy.CompetitorSelectedRequestFields

namespace NearCubicWires.RepairOrdinary.CompetitorSelectedRequestFields
open MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (r : Request) : budget r≤5020*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hb := CompetitorCrossRequestFields.budget_bound r
  have hs : r.d+r.p+1≤(r.d+r.p+1)^2 := Nat.le_self_pow (by decide) _
  have hu : 1≤(r.U+1)^2 := by
    have h : 0 < (r.U+1)^2 := by positivity
    omega
  have hm : (r.d+r.p+1)^2≤(r.U+1)^2*(r.d+r.p+1)^2 := by nlinarith
  unfold budget
  rw [CompetitorSelectedCount.extraWidth_eq]
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSelectedRequestFields
