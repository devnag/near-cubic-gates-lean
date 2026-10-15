import Proof.Hierarchy.CompetitorSameBucketGroup

/-! Whole cold grouping bound, including capacity production, allocation,
scalar/driver preparation, every record cycle and the final global rewind. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupCold
open CompetitorSameBucketGroup
open CompetitorSameBucketGroupColdDimensions (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem preparation_bound (w p m : ℕ) :
    CompetitorSameBucketGroupColdEntry.budget w p m ≤ 50000*(w+p+m+1)^2 := by
  have hd := CompetitorDimensions.budget_bound (w+p+m)
  have hsq : w+p+m+1 ≤ (w+p+m+1)^2 := Nat.le_self_pow (by decide) _
  unfold CompetitorSameBucketGroupColdEntry.budget CompetitorSameBucketGroupColdDrivers.budget
    CompetitorSameBucketGroupColdScalars.budget CompetitorSameBucketGroupColdAllocate.budget
    CompetitorSameBucketGroupColdDimensions.budget capacity RepairSource.ProjectionNormalization.Counter.budget
    RepairSource.ProjectionNormalization.DriverAtoms.productBudget
  unfold CompetitorReusableDecision.capacity at hd ⊢
  omega

theorem cycle_bound (w p m : ℕ) :
    CompetitorSameBucketGroupMachine.cycleBound (capacity w p m) w p m ≤ 8400*(w+p+m+1)^2 := by
  have hsq : w+p+m+1 ≤ (w+p+m+1)^2 := Nat.le_self_pow (by decide) _
  unfold CompetitorSameBucketGroupMachine.cycleBound capacity CompetitorReusableDecision.capacity
  omega

theorem length_budget_bound (w p m : ℕ) (es : List Entry) :
    budget w p m es ≤ (16800*es.length+101000)*(w+p+m+1)^2 := by
  have hp := preparation_bound w p m
  have hc := Nat.mul_le_mul_left es.length (cycle_bound w p m)
  have hsq : w+p+m+1 ≤ (w+p+m+1)^2 := Nat.le_self_pow (by decide) _
  unfold budget rawBudget CompetitorSameBucketGroupMachine.streamBudget
  nlinarith

theorem budget_bound (w u p m : ℕ) (es : List Entry) (hlen : es.length ≤ 26*u^2) :
    budget w p m es ≤ 600000*(u+1)^2*(w+p+m+1)^2 := by
  have hcoef : 16800*es.length+101000 ≤ 600000*(u+1)^2 := by
    rw [show (u+1)^2=u^2+2*u+1 by ring]
    omega
  exact (length_budget_bound w p m es).trans (Nat.mul_le_mul_right ((w+p+m+1)^2) hcoef)

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupCold
