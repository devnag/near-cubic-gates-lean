import Proof.Amplification.RecoveryTseitinPrepared

/-! Scalar output boundary of the completed prepared stream. Consumers can
compose against these tape equations without normalizing its controller. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open VerifierDecoding CircuitInputCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prepared_output (cap count : Nat) (hc : uniformCapacity count≤cap) : ∃ r,
    runFrom preparedMachine (preparedBudget cap count)
      ⟨preparedMachine.start,fun _=>0,bankInput cap count []⟩=some r ∧
      r.final.tapes 239=RecoveryFormulaPayload.input (circuitInputTautologies count) ∧
      r.final.heads 239=(RecoveryFormulaPayload.input (circuitInputTautologies count)).length ∧
      r.final.tapes 241=CompareMachine.word count ∧ r.final.heads 241=1 ∧
      r.steps≤preparedBudget cap count := by
  obtain ⟨after,r,hr,rh,rt,_rv,rs⟩ := prepared_run cap count [] hc
  have he : bankHeads []=(fun _ : Fin 242=>0) := by funext i; simp [bankHeads]
  rw [he] at hr
  refine ⟨r,hr,?_,?_,?_,?_,rs⟩
  · rw [rt]
    rfl
  · rw [rh]
    rfl
  · rw [rt]
    rfl
  · rw [rh]
    rfl

end NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
