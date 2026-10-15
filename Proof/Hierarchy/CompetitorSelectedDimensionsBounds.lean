import Proof.Hierarchy.CompetitorSelectedDimensions

namespace NearCubicWires.RepairOrdinary.CompetitorSelectedDimensions
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_eq (Q M N : ℕ) : budget Q M N=6*Q*N+10*Q+2*N+2*M+56 := by
  unfold budget WilliamsUnaryProduct.budget
  ring

theorem budget_bound (Q M N : ℕ) : budget Q M N≤128*(N+1)*(Q+M+1) := by
  rw [budget_eq]
  nlinarith [Nat.zero_le (Q*N),Nat.zero_le (M*N)]

end NearCubicWires.RepairOrdinary.CompetitorSelectedDimensions
