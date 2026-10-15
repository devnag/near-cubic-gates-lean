import Proof.Amplification.RecoveryCaseOnePaddedOrdinaryRun
import Proof.Assembly.SelectedRecoveryIntegration

/-! The checked padded word program computes the canonical Case-1 hard core
of the very same selected outer PCP. No arbitrary dichotomy witness selects
the computed table. -/
namespace NearCubicWires.RepairSource.CloseoutCaseOne
open RepairOrdinary SourceInterfaces ProjectionNormalization RecoveryPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem selected_pcp (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) :
    RecoveryCaseOnePaddedBit.pcp (SelectedRecoveryIntegration.fixedProjection sources)
      (sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
      (SelectedRecoveryIntegration.padding sources k clock) (Nat.le_max_right _ _)=
      (SelectedRecoveryIntegration.outer sources k clock).result.pcp := rfl

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
variable {c d k : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
  (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad)
  (r : InputRequest)

theorem generated_core
    (hq : 1≤(RecoveryCaseOnePaddedBit.pcp source H Cpad hpad).nativeWidth r.1)
    (complete : ∃ proof, ∀ randomness,
      (RecoveryCaseOnePaddedBit.pcp source H Cpad hpad).accepts r.2 proof randomness)
    (noSmall : ∀ circuit : BooleanCircuit
      ((RecoveryCaseOnePaddedBit.pcp source H Cpad hpad).nativeWidth r.1),
      circuit.size≤RecoveryScheduleEnvelope.oracleSizeBound d
        ((RecoveryCaseOnePaddedBit.pcp source H Cpad hpad).nativeWidth r.1) →
      ¬∀ randomness,OuterPCPRecovery.acceptsOracleCircuit
        (RecoveryCaseOnePaddedBit.pcp source H Cpad hpad) r.2 circuit randomness) :
    RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r=
      let core:=scheduledAmplifierCore amplifier.toScheduleAmplifier
        (RecoveryCaseOnePaddedBit.pcp source H Cpad hpad) r.2 hq complete noSmall
      (⟨core.arity,core.function⟩ : AmplifierOutput) := by
  unfold RecoveryCaseOnePaddedBit.generated
  rw [RecoveryCaseOneRequest.request_canonical _ r.2 complete]
  rfl

end
end NearCubicWires.RepairSource.CloseoutCaseOne
