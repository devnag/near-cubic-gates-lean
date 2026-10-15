import Proof.PCP.ProjectionDimensionsFromInput
import Proof.PCP.ProjectionDimensionBounds

namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionsFromInput
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clock_bitLength (N : ℕ) : natBitLength (UAggregateClock.time N)=ClockEnvelope.exponent 23 5 N+1 := by
  change Nat.log 2 (2^ClockEnvelope.exponent 23 5 N)+1=_
  rw [Nat.log_pow (by decide)]

theorem budget_bound (p q C : ℕ) (bits : List Bool) : budget p q C bits ≤
    11658*(bits.length+1)*PCPResourceLedger.q bits.length^2+1+
      DimensionProducer.coefficient p q C*
        (natBitLength (UAggregateClock.time bits.length)+1)^DimensionProducer.degree p q := by
  have h := DimensionProducer.budget_bound p q C (ClockEnvelope.exponent 23 5 bits.length)
  have hc : ClockTotal.budget 23 5 bits=11658*(bits.length+1)*PCPResourceLedger.q bits.length^2 := by
    norm_num [ClockTotal.budget]
  unfold budget
  rw [hc,clock_bitLength]
  exact Nat.add_le_add_left h _

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionsFromInput
