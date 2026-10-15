import Proof.Hierarchy.CompetitorSelectedCount

/-! The physical selector and exact SUM preserve linear dependence on the
number of residual cells. Only bit widths enter the remaining factor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedCount
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_eq (b w n : ℕ) : budget b w n=8*b*n+16*w*n+34*n+4*w+54 := by
  unfold budget prefixBudget CompetitorCountMask.budget MatrixMaskPad.budget
    MatrixMaskPad.forwardBudget MatrixMaskExpand.nativeBudget MatrixMaskAndPass.budget
    MatrixMaskAndLoop.nativeBudget CompetitorCountProducer.budget
  ring

theorem budget_bound (b w n : ℕ) : budget b w n≤64*(n+1)*(b+w+1) := by
  rw [budget_eq]
  nlinarith [Nat.zero_le (b*n),Nat.zero_le (w*n)]

end NearCubicWires.RepairOrdinary.CompetitorSelectedCount
