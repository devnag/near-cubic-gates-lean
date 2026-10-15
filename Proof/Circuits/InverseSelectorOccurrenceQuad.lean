import Proof.Circuits.InverseLengthStage
import Proof.MachineModel.RuntimeCaseTwoOccurrencePacketSplit

/-!
# The inverse occurrence schedule quad at the selector-driven length

The inverse length program computes the selected source length from the public
target.  A native call then runs the frozen occurrence-quad program at that
length.  This supplies the four schedule numerals without identifying the
public target with the scheduled source length.
-/

namespace NearCubicWires.InverseSelectorOccurrenceQuad

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseLengthStage
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.RuntimeScheduleQuadNumeralProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

noncomputable def inverseSelectorOccurrenceQuadCoreProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) : NPOracleProgram :=
  occurrenceQuadProgram
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program
    clockDepth
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
    (publishedHierarchyOuterPCP contracts clockDepth).proofExponent
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (publishedHierarchyOuterPCP contracts clockDepth).substitution.sizeCoefficient
    (publishedHierarchyOuterPCP contracts clockDepth).substitutionExponent
    (publishedPointwisePCPP contracts).coefficient
    (publishedPointwisePCPP contracts).degree

noncomputable def inverseSelectorOccurrenceQuadProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) : NPOracleProgram :=
  linkPrograms (inverseLengthProgram contracts clockDepth advantageExponent) <|
    linkPrograms quadTakeLeftProgram <|
      linkPrograms duplicateProgram <|
        nativeCallProgram
          (inverseSelectorOccurrenceQuadCoreProgram contracts clockDepth
            advantageExponent)

noncomputable def inverseSelectorOccurrenceQuadCoreBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrenceQuadBits
    (inverseScheduleLength contracts clockDepth advantageExponent target)
    clockDepth
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
    (publishedHierarchyOuterPCP contracts clockDepth).proofExponent
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (publishedHierarchyOuterPCP contracts clockDepth).substitution.sizeCoefficient
    (publishedHierarchyOuterPCP contracts clockDepth).substitutionExponent
    (publishedPointwisePCPP contracts).coefficient
    (publishedPointwisePCPP contracts).degree
    (inverseScheduleLength contracts clockDepth advantageExponent target)
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget
      (inverseScheduleLength contracts clockDepth advantageExponent target))
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.execute
      (inverseScheduleLength contracts clockDepth advantageExponent target))

noncomputable def inverseSelectorOccurrenceQuadCoreFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrenceQuadFuel
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program
    clockDepth
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
    (publishedHierarchyOuterPCP contracts clockDepth).proofExponent
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (publishedHierarchyOuterPCP contracts clockDepth).substitution.sizeCoefficient
    (publishedHierarchyOuterPCP contracts clockDepth).substitutionExponent
    (publishedPointwisePCPP contracts).coefficient
    (publishedPointwisePCPP contracts).degree
    (inverseScheduleLength contracts clockDepth advantageExponent target)
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget
      (inverseScheduleLength contracts clockDepth advantageExponent target))

noncomputable def inverseSelectorOccurrenceQuadBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  let sourceLen :=
    inverseScheduleLength contracts clockDepth advantageExponent target
  let selectorInput : BitInput target := fun bit => target.testBit bit.val
  occurrenceStageBits target
    (inverseLengthBits contracts clockDepth advantageExponent
      ⟨target, selectorInput⟩) <|
    occurrenceStageBits target (quadTakeLeftBits sourceLen target) <|
      occurrenceStageBits target (duplicateBits sourceLen) <|
        nativeCallBits target sourceLen sourceLen
          (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
            target)
          (inverseSelectorOccurrenceQuadCoreBits contracts clockDepth
            advantageExponent target)

noncomputable def inverseSelectorOccurrenceQuadFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  let sourceLen :=
    inverseScheduleLength contracts clockDepth advantageExponent target
  let selectorInput : BitInput target := fun bit => target.testBit bit.val
  linkFuel
    (linkPrograms quadTakeLeftProgram <|
      linkPrograms duplicateProgram <|
        nativeCallProgram
          (inverseSelectorOccurrenceQuadCoreProgram contracts clockDepth
            advantageExponent))
    (inverseLengthFuel contracts clockDepth advantageExponent
      ⟨target, selectorInput⟩) <|
    linkFuel
      (linkPrograms duplicateProgram <|
        nativeCallProgram
          (inverseSelectorOccurrenceQuadCoreProgram contracts clockDepth
            advantageExponent))
      2 <|
      linkFuel
        (nativeCallProgram
          (inverseSelectorOccurrenceQuadCoreProgram contracts clockDepth
            advantageExponent))
        2 <|
        nativeCallFuel
          (inverseSelectorOccurrenceQuadCoreProgram contracts clockDepth
            advantageExponent)
          (inverseSelectorOccurrenceQuadCoreFuel contracts clockDepth
            advantageExponent target)
          sourceLen sourceLen

set_option maxHeartbeats 1600000 in
-- The four nested executable stages expose the full selector schedule term.
theorem run_inverseSelectorOccurrenceQuadProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) :
    runNPOracleProgram
        (inverseSelectorOccurrenceQuadProgram contracts clockDepth
          advantageExponent)
        (inverseSelectorOccurrenceQuadBits contracts clockDepth
          advantageExponent target)
        (inverseSelectorOccurrenceQuadFuel contracts clockDepth
          advantageExponent target)
        (initialNPOracleState target target) =
      some
        (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
          target) := by
  let sourceLen :=
    inverseScheduleLength contracts clockDepth advantageExponent target
  let selectorInput : BitInput target := fun bit => target.testBit bit.val
  have htarget : encodeBitInput selectorInput = target := by
    exact encodeBitInput_testBit Nat.lt_two_pow_self
  have hlength := run_inverseLengthProgram contracts clockDepth
    advantageExponent target selectorInput
  rw [htarget] at hlength
  have hcore :
      runNPOracleProgram
          (inverseSelectorOccurrenceQuadCoreProgram contracts clockDepth
            advantageExponent)
          (inverseSelectorOccurrenceQuadCoreBits contracts clockDepth
            advantageExponent target)
          (inverseSelectorOccurrenceQuadCoreFuel contracts clockDepth
            advantageExponent target)
          (initialNPOracleState sourceLen sourceLen) =
        some
          (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
            target) := by
    rw [inverseOccurrenceQuadWord,
      seedArity_eq_sum (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent))
        (inverseChainSourceIndex contracts clockDepth advantageExponent target)]
    exact run_occurrenceQuadProgram
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.program
      sourceLen clockDepth
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
      (publishedHierarchyOuterPCP contracts clockDepth).proofExponent
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (publishedHierarchyOuterPCP contracts clockDepth).substitution.sizeCoefficient
      (publishedHierarchyOuterPCP contracts clockDepth).substitutionExponent
      (publishedPointwisePCPP contracts).coefficient
      (publishedPointwisePCPP contracts).degree
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget
        sourceLen)
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.budget
        sourceLen)
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.execute
        sourceLen)
      (publishedWidthBudget_positive
        (publishedHierarchyOuterPCP contracts clockDepth) sourceLen)
      (publishedPointwisePCPP contracts).coefficientPositive
      (run_publishedShapeProgram
        (publishedHierarchyOuterPCP contracts clockDepth) sourceLen)
  exact run_occurrenceStage hlength <|
    run_occurrenceStage (run_quadTakeLeftProgram target sourceLen target) <|
      run_occurrenceStage (run_duplicateProgram target sourceLen) <|
        run_nativeCallProgram
          (inverseSelectorOccurrenceQuadCoreProgram contracts clockDepth
            advantageExponent)
          target sourceLen sourceLen
          (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
            target)
          (inverseSelectorOccurrenceQuadCoreBits contracts clockDepth
            advantageExponent target)
          (inverseSelectorOccurrenceQuadCoreFuel contracts clockDepth
            advantageExponent target)
          hcore

/-! ## Pair the selector quad with an oracle triple -/

noncomputable def inverseSelectorOccurrencePacketProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (tripleProgram : NPOracleProgram) :
    NPOracleProgram :=
  occurrencePacketPairProgram
    (inverseSelectorOccurrenceQuadProgram contracts clockDepth
      advantageExponent)
    tripleProgram

noncomputable def inverseSelectorOccurrencePacketFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (tripleProgram : NPOracleProgram)
    (tripleFuel : ℕ → ℕ) (target : ℕ) : ℕ :=
  occurrencePacketPairFuel
    (inverseSelectorOccurrenceQuadProgram contracts clockDepth
      advantageExponent)
    tripleProgram
    (inverseSelectorOccurrenceQuadFuel contracts clockDepth advantageExponent
      target)
    (tripleFuel target)

open Classical in
noncomputable def inverseSelectorOccurrencePacketBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (tripleBits : ℕ → ℕ) (target : ℕ) : ℕ :=
  if hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target) then
    match inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes with
    | .caseOne _ => 0
    | .caseTwo caseTwo =>
        occurrencePacketPairBits target
          (inverseSelectorOccurrenceQuadBits contracts clockDepth
            advantageExponent target)
          (tripleBits target)
          (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
            target)
          (inverseOccurrenceTripleWord contracts clockDepth machine
            advantageExponent target caseTwo)
  else 0

set_option maxHeartbeats 1600000 in
-- The paired packet carries its dependent Case-2 oracle in both envelopes.
theorem inverseScheduledOccurrencePacket_ofSelectorTriple
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (tripleProgram : NPOracleProgram) (tripleBits tripleFuel : ℕ → ℕ)
    (htriples :
      InverseScheduledOccurrenceTriple contracts clockDepth machine
        advantageExponent tripleProgram tripleBits tripleFuel) :
    InverseScheduledOccurrencePacket contracts clockDepth machine
      advantageExponent
      (inverseSelectorOccurrencePacketProgram contracts clockDepth
        advantageExponent tripleProgram)
      (inverseSelectorOccurrencePacketBits contracts clockDepth machine
        advantageExponent tripleBits)
      (inverseSelectorOccurrencePacketFuel contracts clockDepth
        advantageExponent tripleProgram tripleFuel) := by
  intro target hlarge hyes caseTwo hbranch
  have hquad := run_inverseSelectorOccurrenceQuadProgram contracts clockDepth
    advantageExponent target
  have htriple := htriples target hlarge hyes caseTwo hbranch
  have hbits :
      inverseSelectorOccurrencePacketBits contracts clockDepth machine
          advantageExponent tripleBits target =
        occurrencePacketPairBits target
          (inverseSelectorOccurrenceQuadBits contracts clockDepth
            advantageExponent target)
          (tripleBits target)
          (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
            target)
          (inverseOccurrenceTripleWord contracts clockDepth machine
            advantageExponent target caseTwo) := by
    simp only [inverseSelectorOccurrencePacketBits]
    rw [dif_pos hyes, hbranch]
  have hpacket :
      inverseCaseTwoOccurrencePacket contracts clockDepth machine
          advantageExponent target caseTwo =
        Nat.pair
          (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
            target)
          (inverseOccurrenceTripleWord contracts clockDepth machine
            advantageExponent target caseTwo) := rfl
  rw [hbits, hpacket, inverseSelectorOccurrencePacketProgram,
    inverseSelectorOccurrencePacketFuel]
  exact run_occurrencePacketPairProgram
    (inverseSelectorOccurrenceQuadProgram contracts clockDepth
      advantageExponent)
    tripleProgram target
    (inverseSelectorOccurrenceQuadBits contracts clockDepth advantageExponent
      target)
    (inverseSelectorOccurrenceQuadFuel contracts clockDepth advantageExponent
      target)
    (tripleBits target) (tripleFuel target)
    (inverseOccurrenceQuadWord contracts clockDepth advantageExponent target)
    (inverseOccurrenceTripleWord contracts clockDepth machine advantageExponent
      target caseTwo)
    hquad htriple

end NearCubicWires.InverseSelectorOccurrenceQuad
