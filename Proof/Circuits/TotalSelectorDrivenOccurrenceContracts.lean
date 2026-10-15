import Proof.Circuits.TotalSelectorDrivenOccurrenceEncodingRuns
import Proof.Circuits.InverseSelectorOccurrenceEncodingClosure

/-! # Onset-free selector occurrence contracts -/

namespace NearCubicWires.TotalSelectorDrivenOccurrenceContracts

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.ScheduledRecovery

/-- The three oracle-derived occurrence numerals under a live Case-two branch.
-/
def TotalInverseScheduledOccurrenceTriple
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (tripleProgram : NPOracleProgram) (tripleBits tripleFuel : ℕ → ℕ) : Prop :=
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
    runNPOracleProgram tripleProgram (tripleBits target) (tripleFuel target)
        (initialNPOracleState target target) =
      some
        (inverseOccurrenceTripleWord contracts clockDepth machine
          advantageExponent target caseTwo)

/-- The complete seven-field occurrence packet under a live Case-two branch.
-/
def TotalInverseScheduledOccurrencePacket
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (packetProgram : NPOracleProgram) (packetBits packetFuel : ℕ → ℕ) : Prop :=
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
    runNPOracleProgram packetProgram (packetBits target) (packetFuel target)
        (initialNPOracleState target target) =
      some
        (inverseCaseTwoOccurrencePacket contracts clockDepth machine
          advantageExponent target caseTwo)

/-- The per-block occurrence callee under a live Case-two branch, without an
external target-onset premise. -/
def TotalInverseScheduledOccurrenceRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (occurrence : NPOracleProgram)
    (occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ) : Prop :=
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
    ∀ (point : BitInput target) (block : ℕ),
      block < inverseChainTwoCopies contracts clockDepth advantageExponent
        target →
      runNPOracleProgram occurrence (occurrenceBits target block)
          (occurrenceFuel target block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point) block).toNat

end NearCubicWires.TotalSelectorDrivenOccurrenceContracts
