import Proof.Circuits.TotalSelectorDrivenAtomStreamRuns
import Proof.MachineModel.RuntimeCaseTwoCircuitEncodingClosure

/-! # Onset-free selector circuit-encoding contracts -/

namespace NearCubicWires.TotalSelectorDrivenCircuitEncodingContracts

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoCanonicalCircuitEncoder
open NearCubicWires.CanonicalDescriptionGroupingDecoder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
open NearCubicWires.RuntimeCaseTwoRequestWordFrame
open NearCubicWires.ScheduledRecovery

/-- The computed description frame at every target. -/
def TotalInverseDescriptionFrameRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (adapter : NPOracleProgram) (adapterBits adapterFuel : ℕ → ℕ) : Prop :=
  ∀ target : ℕ,
    runNPOracleProgram adapter (adapterBits target) (adapterFuel target)
        (initialNPOracleState target target) =
      some
        (canonicalCircuitEncoderInput
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target)
          (inverseOracleSizeBound contracts advantageExponent))

/-- The recovered oracle's own circuit encoding under a live Case-two branch,
without an external target-onset argument. -/
def TotalInverseScheduledCircuitEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (circuitProgram : NPOracleProgram) (circuitBits circuitFuel : ℕ → ℕ) :
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
    runNPOracleProgram circuitProgram (circuitBits target) (circuitFuel target)
        (initialNPOracleState target target) =
      some (encodeBooleanCircuit caseTwo.circuit)

end NearCubicWires.TotalSelectorDrivenCircuitEncodingContracts
