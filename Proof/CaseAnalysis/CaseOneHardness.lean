import Proof.CaseAnalysis.CaseOneBounds
import Proof.CaseAnalysis.Language

/-! Both physical hardness bounds for the Case-1 branch of the same
canonical language core, using its actually searched proof table. -/
namespace NearCubicWires.RepairSource.CloseoutCaseOne
open SourceInterfaces RepairRepresentation RecoveryPipeline OuterPCPRecovery
open RecoveryScheduleEnvelope ComponentwiseTransfer PhysicalRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem core_hardness {M : TimedDecisionMachine} {T : Nat→Nat} {c d n : Nat}
    (pcp : ProjectionPCP M T) (a : PointwisePCPPAlgorithm)
    (amplifier : OrdinaryScheduleAmplifier c d) (input : BitInput n)
    (copies clauseBits target symCap thrCap : Nat)
    (normalization : ThresholdNormalizationContract)
    (hq : 1 ≤ pcp.nativeWidth n)
    (complete : ∃ proof, ∀ randomness, pcp.accepts input proof randomness)
    (hsmall : ¬RecoveryChoice.SmallOracle pcp d input)
    (hfit : (amplifier.output (RecoveryCaseOneRequest.request pcp input).inputArity
      (RecoveryCaseOneRequest.request pcp input).function).arity ≤ target)
    (hsym : 40*(target+symCap+2)^4 ≤ integerFloorRoot c (oracleSizeBound d (pcp.nativeWidth n)))
    (hthr : 50*(target+thrCap+2)^4 ≤ integerFloorRoot c (oracleSizeBound d (pcp.nativeWidth n)))
    (gamma : ℝ)
    (hadv : Real.rpow (oracleSizeBound d (pcp.nativeWidth n) : ℝ) (-(1 : ℝ)/c) < gamma) :
    (∀ circuit : SymmetricThresholdCircuit target, circuit.wireCount ≤ symCap →
      agreement circuit.eval (CloseoutLanguage.core pcp a amplifier input copies clauseBits target) < 1/2+gamma) ∧
    (∀ circuit : ThresholdThresholdCircuit target, circuit.wireCount ≤ thrCap →
      agreement circuit.eval (CloseoutLanguage.core pcp a amplifier input copies clauseBits target) < 1/2+gamma) := by
  have noSmall : ∀ circuit : BooleanCircuit (pcp.nativeWidth n),
      circuit.size ≤ oracleSizeBound d (pcp.nativeWidth n) →
      ¬∀ randomness, acceptsOracleCircuit pcp input circuit randomness := by
    intro circuit hsize haccept
    exact hsmall ⟨circuit,hsize,haccept⟩
  let hard:=scheduledAmplifierCore amplifier.toScheduleAmplifier pcp input hq complete noSmall
  have hhard : hard.arity ≤ target := by
    rw [RecoveryCaseOneRequest.request_canonical pcp input complete] at hfit
    exact hfit
  have heq : CloseoutLanguage.core pcp a amplifier input copies clauseBits target=
      (padAmplifierCore hard target hhard).function := by
    rw [CloseoutLanguage.core_case_one pcp a amplifier input copies clauseBits target hsmall hfit]
    change padCore (amplifier.output (RecoveryCaseOneRequest.request pcp input).inputArity
      (RecoveryCaseOneRequest.request pcp input).function).function hfit=padCore hard.function hhard
    revert hfit
    rw [RecoveryCaseOneRequest.request_canonical pcp input complete]
    intro hfit
    rfl
  have hs:=symmetricAverageHard_of_boolean normalization (padAmplifierCore hard target hhard) symCap hsym
  have ht:=thresholdAverageHard_of_boolean normalization (padAmplifierCore hard target hhard) thrCap hthr
  have hstrict : 1/2+(padAmplifierCore hard target hhard).advantage < 1/2+gamma := by
    change 1/2+Real.rpow (oracleSizeBound d (pcp.nativeWidth n) : ℝ) (-(1 : ℝ)/c) < 1/2+gamma
    linarith
  rw [heq]
  constructor
  · intro circuit hcap
    exact (hs circuit.eval ⟨circuit,hcap,rfl⟩).trans_lt hstrict
  · intro circuit hcap
    exact (ht circuit.eval ⟨circuit,hcap,rfl⟩).trans_lt hstrict

end
end NearCubicWires.RepairSource.CloseoutCaseOne
