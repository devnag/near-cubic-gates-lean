import Proof.MachineModel.OrdinaryMatrixScoreBatchCodec
import Proof.MachineModel.OrdinaryWilliamsPower
import Proof.MachineModel.OrdinaryWilliamsPaddedRequest
import Proof.Amplification.RecoveryScratchErase

namespace NearCubicWires.RepairOrdinary.MatrixBucketDimensions
open LocalBitMultitape SourceInterfaces SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (U : ℕ) := rectangularInnerDimension U
def bucketBudget (U gates : ℕ) := stableCapacityBucketBudget (capacity U) gates
def bucketSize (U gates : ℕ) := stableCapacityBucketSize U U (capacity U) gates
def width (U gates : ℕ) := bucketSize U gates+1
def buckets (U gates : ℕ) := stableDominanceBucketCount U U (bucketSize U gates)

theorem capacity_positive (U : ℕ) (hU : 1 ≤ U) : 1 ≤ capacity U :=
  WilliamsPaddedRequest.inner_positive U hU
theorem capacity_le (U : ℕ) : capacity U ≤ U := WilliamsPaddedRequest.inner_le U
theorem capacity_power (U : ℕ) (hU : 1 ≤ U) : (capacity U)^10 ≤ 1024*U :=
  WilliamsPaddedRequest.dimension_le U hU
theorem root_stop (U c : ℕ) : U ≤ c^10 ↔ capacity U ≤ c :=
  (integerCeilRoot_le_iff (by decide : 0<10)).symm
theorem before_root (U c : ℕ) (hc : c<capacity U) : c^10<U := by
  have hn : ¬ U ≤ c^10 := by rw [root_stop]; omega
  omega
theorem visited_power (U c : ℕ) (hU : 1 ≤ U) (hc : c ≤ capacity U) : c^10 ≤ 1024*U :=
  (Nat.pow_le_pow_left hc 10).trans (capacity_power U hU)

theorem budget_zero (U : ℕ) : bucketBudget U 0=1 := by simp [bucketBudget,stableCapacityBucketBudget]
theorem budget_positive (U gates : ℕ) (hgate : gates*gates ≤ capacity U) :
    1 ≤ bucketBudget U gates := by
  by_cases hg : gates=0
  · simp [hg,budget_zero]
  · have hpos : 0<gates := by omega
    have hle : gates ≤ capacity U/gates := (Nat.le_div_iff_mul_le hpos).2 hgate
    simp only [bucketBudget,stableCapacityBucketBudget,hg,if_false]
    omega

theorem bucketSize_le (U gates : ℕ) : bucketSize U gates ≤ 2*U := by
  unfold bucketSize stableCapacityBucketSize
  dsimp only
  split
  · omega
  · have h := Nat.div_le_self (U+U) (stableCapacityBucketBudget (capacity U) gates-1)
    omega
theorem width_positive (U gates : ℕ) : 1 ≤ width U gates := by unfold width; omega
theorem width_le (U gates : ℕ) : width U gates ≤ 2*U+1 := by
  have h := bucketSize_le U gates
  unfold width
  omega
theorem buckets_positive (U gates : ℕ) : 1 ≤ buckets U gates := by
  unfold buckets stableDominanceBucketCount
  exact Nat.succ_le_succ (Nat.zero_le _)
theorem buckets_le (U gates : ℕ) : buckets U gates ≤ 2*U+1 := by
  have h := Nat.div_le_self (U+U) (bucketSize U gates+1)
  unfold buckets stableDominanceBucketCount
  omega
theorem used_le (U gates : ℕ) (hgate : gates*gates ≤ capacity U) :
    gates*buckets U gates ≤ capacity U :=
  stableCapacityBucketDimension_le U U (capacity U) gates hgate

def scratchCapacity (U : ℕ) := 104000*(U+1)
theorem power_budget (U c : ℕ) (hU : 1 ≤ U) (hc : c ≤ capacity U) :
    WilliamsPower.budget 10 c+2+1 ≤ scratchCapacity U := by
  have hp := visited_power U c hU hc
  unfold WilliamsPower.budget WilliamsPower.stepBudget scratchCapacity
  omega

end NearCubicWires.RepairOrdinary.MatrixBucketDimensions
