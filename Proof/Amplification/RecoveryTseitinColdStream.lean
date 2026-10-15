import Proof.Amplification.RecoveryTseitinOutput
import Proof.Amplification.RecoveryTseitinJoin
import Proof.Amplification.RecoveryTseitinDrivers

/-! Whole cold tautology-prefix producer. Its only input is the actual unary
number of free variables. Capacity, repetition driver, blank scratch and
binary indices are all physically produced before the original stream runs. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization VerifierDecoding CircuitInputCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def streamMachine := RecoveryFocus.machine streamSlots preparedMachine
noncomputable def machine := Composition.machine driversMachine streamMachine
def budget (count : Nat) := driversBudget count+1+preparedBudget (driverCapacity count) count

theorem cold_run (count : Nat) : ∃ r,
    run machine (budget count) (driversInput count)=some r ∧
      r.final.tapes 239=RecoveryFormulaPayload.input (circuitInputTautologies count) ∧
      r.final.heads 239=(RecoveryFormulaPayload.input (circuitInputTautologies count)).length ∧
      r.final.tapes 241=CompareMachine.word count ∧ r.final.heads 241=1 ∧
      r.final.tapes 242=List.replicate count true ∧ r.final.heads 242=0 ∧
      r.steps≤budget count := join_run driversMachine preparedMachine (driversInput count) (driverCapacity count) count
        (driversBudget count) (preparedBudget (driverCapacity count) count)
        (RecoveryFormulaPayload.input (circuitInputTautologies count)) (drivers_run count)
        (prepared_output (driverCapacity count) count (driver_capacity count))

theorem budget_bound (count : Nat) : budget count≤4294967296*(count+1)^3 := by
  unfold budget driversBudget preparedBudget driverCapacity PCPSerializerCapacity.Power.budget Counter.budget
  simp only [DimensionPower.cost,WilliamsUnaryProduct.budget,pow_zero,pow_one,Nat.mul_one]
  nlinarith

end NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
