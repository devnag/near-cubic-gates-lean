import Proof.Amplification.RecoveryTseitinNativePrefixCore

/-! Four original raw inputs physically produce the common capacity,
node-count sentinel and original tautology prefix on the shared formula tape.
Every native scratch tape is bounded and all its heads have been returned. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tautProgram:=RecoveryFocus.machine tautSlots tautMachine
noncomputable def prefixMachine:=Composition.machine driversMachine tautProgram
def prefixBudget (n count : Nat) := driversBudget n count+1+tautBudget n

theorem prefix_run (n count output : Nat) (word : List Bool) : ∃ r,
    run prefixMachine (prefixBudget n count) (input n count output word)=some r ∧
      r.final.tapes 1333=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n) ∧
      r.final.heads 1333=(RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n)).length ∧
      (∀ i,i≠1333 → r.final.heads i=0) ∧
      (∀ i,retained i → r.final.tapes i=preparedData n count output word i) ∧
      (∀ j,(r.final.tapes ((Reuse.scratch j).castAdd 34)).length ≤ Reuse.capacity n count) ∧
      r.steps ≤ prefixBudget n count := by
  exact prefix_core driversMachine tautMachine (driversBudget n count) (tautBudget n)
    (Reuse.capacity n count) (RecoveryTseitinTautology.Cold.budget n) n count output word
    (taut_capacity n count) (drivers_run n count output word) (taut_run n)

end NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
