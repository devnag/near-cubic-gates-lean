import Proof.Circuits.TotalSelectorDrivenCircuitEncodingRuns
import Proof.Circuits.InverseSubstitutionRequestWordClosure

/-! # Onset-free selector occurrence-encoding contracts -/

namespace NearCubicWires.TotalSelectorDrivenOccurrenceEncodingContracts

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.ScheduledRecovery

/-- The recovered oracle code paired with the selector-computed substitution
request tail under a live Case-two branch. -/
def TotalInverseSubstitutionRequestWord
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (requestProgram : NPOracleProgram) (requestBits requestFuel : ℕ → ℕ) :
    Prop :=
  ∀ (target : ℕ)
    (hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
            advantageExponent target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target)),
    inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes = .caseTwo caseTwo →
    runNPOracleProgram requestProgram (requestBits target) (requestFuel target)
        (initialNPOracleState target target) =
      some
        (Nat.pair (encodeBooleanCircuit caseTwo.circuit)
          (Nat.pair
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
              (sourceLength
                (BankRegisterCaseOneChain.inverseChainSourceIndex contracts
                  clockDepth advantageExponent target)))
            (Nat.pair
              (sourceLength
                (BankRegisterCaseOneChain.inverseChainSourceIndex contracts
                  clockDepth advantageExponent target))
              (encodeBitInput
                (inverseRefuterInput contracts
                  (publishedHierarchyOuterPCP contracts clockDepth) machine
                  advantageExponent target)))))

/-- The substituted-circuit encoding under a live Case-two branch, with no
external target-onset premise. -/
def TotalInverseScheduledOccurrenceEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (encodingProgram : NPOracleProgram)
    (encodingBits encodingFuel : ℕ → ℕ) : Prop :=
  ∀ (target : ℕ)
    (hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
            advantageExponent target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target)),
    inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes = .caseTwo caseTwo →
    runNPOracleProgram encodingProgram (encodingBits target)
        (encodingFuel target) (initialNPOracleState target target) =
      some (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo))

end NearCubicWires.TotalSelectorDrivenOccurrenceEncodingContracts
