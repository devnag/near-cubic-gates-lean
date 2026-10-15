import Proof.MachineModel.OuterProofRecoveryFormulaSeedProgram
import Proof.MachineModel.RecoveredProofCaseOneProgram
import Proof.MachineModel.RefuterWordFrameProgram

/-!
# The Case-1 branch of the canonical target language, from the request alone

Three fixed stages now separate a `LanguageEvaluationRequest`'s point code from
the canonical Case-1 target bit:

* `RefuterWordFrameProgram` builds the refuter-word frame with one published
  refuter call;
* `OuterProofRecoveryFormulaSeedProgram` builds the C.12 recovery seed from
  that frame's word, modulo the single named decision-row stage;
* `RecoveredProofCaseOneProgram` compiles the recovery request list, encodes
  the recovered proof, calls the published amplifier's construction program,
  and runs the fixed target-bit dispatcher.

This module links the first stage onto the last two.  The composed program is
parameterized only by numerals — the machine description, the scheduled source
length, and the scheduled width — plus the one named row stage; the sole
remaining hypothesis of its exact-execution theorem is that row stage's own run
theorem together with the already published target-bit run.
-/

namespace NearCubicWires.CaseOneTargetLanguageClosure

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveredProofCaseOneProgram
open NearCubicWires.RecoveredProofRequestCompilerProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RefuterWordFrameProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-- The published refuter's own word at one scheduled source length.  This is
the sole machine-dependent datum of the whole Case-1 path. -/
def scheduledRefuterWord {clockDepth : ℕ}
    (source : ExecutableRefuterSource (pairClock clockDepth))
    (machine : ExecutableWeakNondeterministicMachine) (sourceIndex : ℕ) :
    BitInput (sourceLength sourceIndex) :=
  source.refuter.output machine (sourceLength sourceIndex)

/-- One fixed program computing the Case-1 canonical target bit from the
requested point code alone. -/
def caseOneTargetBitFromPointProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (refuterProgram row : NPOracleProgram)
    (description sourceLen width : ℕ) : NPOracleProgram :=
  linkPrograms (refuterWordFrameProgram refuterProgram description sourceLen)
    (caseOneTargetBitProgram algorithm
      (outerProofFormulaSeedProgram row width))

def caseOneTargetBitFromPointFuel
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (row : NPOracleProgram) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (sourceIndex : ℕ) (rowFuel : ℕ → ℕ) (targetFuel : ℕ) : ℕ :=
  linkFuel
    (caseOneTargetBitProgram algorithm
      (outerProofFormulaSeedProgram row (scheduledWidth outer sourceIndex)))
    (refuterWordFrameFuel source.refuter machine (sourceLength sourceIndex))
    (caseOneTargetBitFuel algorithm
      (outerProofFormulaSeedProgram row (scheduledWidth outer sourceIndex))
      outer sourceIndex (scheduledRefuterWord source machine sourceIndex)
      (outerProofFormulaSeedFuel row (paddedOuterPCP outer)
        (scheduledRefuterWord source machine sourceIndex) rowFuel)
      targetFuel)

def caseOneTargetBitFromPointBits
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (sourceIndex target pointCode targetBits : ℕ)
    (rowBits : ℕ → ℕ) : ℕ :=
  max 1 <|
    max (natBitLength target) <|
      max
        (refuterWordFrameBits source.refuter machine target
          (sourceLength sourceIndex) pointCode)
        (caseOneTargetBitBits algorithm outer sourceIndex
          (scheduledRefuterWord source machine sourceIndex)
          (outerProofFormulaSeedBits (paddedOuterPCP outer)
            (scheduledRefuterWord source machine sourceIndex) rowBits)
          target pointCode targetBits)

/-- Both stages that this module adds in front of the published Case-1
compiler are oracle-free: every SAT query of the Case-1 path still happens
inside `RecoveredProofEncodingProgram`. -/
theorem caseOneTargetBitFromPointPrefix_oracleFree
    {refuterProgram row : NPOracleProgram}
    (hrefuter : OracleFree refuterProgram) (hrow : OracleFree row)
    (description sourceLen width : ℕ) :
    OracleFree
        (refuterWordFrameProgram refuterProgram description sourceLen) ∧
      OracleFree (outerProofFormulaSeedProgram row width) :=
  ⟨refuterWordFrameProgram_oracleFree hrefuter description sourceLen,
    outerProofFormulaSeedProgram_oracleFree hrow width⟩

/-- Exact Case-1 execution from the request's point code.  Only two hypotheses
remain: the single named decision-row stage of the C.12 recovery formula, and
the already published target-bit run of the fixed dispatcher. -/
theorem run_caseOneTargetBitFromPointProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (row : NPOracleProgram) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (sourceIndex target pointCode targetBits targetFuel value : ℕ)
    (rowBits rowFuel : ℕ → ℕ)
    (hrow : ∀ code, code < 2 ^ scheduledWidth outer sourceIndex →
      runNPOracleProgram row (rowBits code) (rowFuel code)
          (initialNPOracleState (sourceLength sourceIndex)
            (Nat.pair code
              (Nat.pair (scheduledWidth outer sourceIndex)
                (encodeBitInput
                  (scheduledRefuterWord source machine sourceIndex))))) =
        some
          (encodeTaggedList
            (outerProofRowStream (paddedOuterPCP outer)
              (scheduledRefuterWord source machine sourceIndex) code)))
    (htarget :
      runNPOracleProgram (targetBitProgram algorithm) targetBits targetFuel
          (initialNPOracleState target
            (targetBitCaseOneInput
              (algorithm.outputArity
                (scheduledAmplifierRequest outer sourceIndex
                  (scheduledRefuterWord source machine sourceIndex)))
              (algorithm.descriptor
                (scheduledAmplifierRequest outer sourceIndex
                  (scheduledRefuterWord source machine sourceIndex)))
              pointCode)) =
        some value) :
    runNPOracleProgram
        (caseOneTargetBitFromPointProgram algorithm
          source.refuter.runner.program row machine.description
          (sourceLength sourceIndex) (scheduledWidth outer sourceIndex))
        (caseOneTargetBitFromPointBits algorithm outer machine sourceIndex
          target pointCode targetBits rowBits)
        (caseOneTargetBitFromPointFuel algorithm row outer machine sourceIndex
          rowFuel targetFuel)
        (initialNPOracleState target pointCode) =
      some value := by
  have hpositive :
      1 ≤ caseOneTargetBitFromPointBits algorithm outer machine sourceIndex
        target pointCode targetBits rowBits :=
    Nat.le_max_left _ _
  have htargetBits :
      natBitLength target ≤
        caseOneTargetBitFromPointBits algorithm outer machine sourceIndex
          target pointCode targetBits rowBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hframeBits :
      refuterWordFrameBits source.refuter machine target
          (sourceLength sourceIndex) pointCode ≤
        caseOneTargetBitFromPointBits algorithm outer machine sourceIndex
          target pointCode targetBits rowBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcaseOneBits :
      caseOneTargetBitBits algorithm outer sourceIndex
          (scheduledRefuterWord source machine sourceIndex)
          (outerProofFormulaSeedBits (paddedOuterPCP outer)
            (scheduledRefuterWord source machine sourceIndex) rowBits)
          target pointCode targetBits ≤
        caseOneTargetBitFromPointBits algorithm outer machine sourceIndex
          target pointCode targetBits rowBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hframe :=
    run_bits_mono
      (run_refuterWordFrameProgram source.refuter machine target
        (sourceLength sourceIndex) pointCode)
      hframeBits
  have hseed :=
    run_outerProofRecoveryFormulaSeedProgram row outer sourceIndex
      (scheduledRefuterWord source machine sourceIndex) rowBits rowFuel hrow
  have hcaseOne :=
    run_bits_mono
      (run_caseOneTargetBitProgram algorithm
        (outerProofFormulaSeedProgram row (scheduledWidth outer sourceIndex))
        outer sourceIndex (scheduledRefuterWord source machine sourceIndex)
        (outerProofFormulaSeedBits (paddedOuterPCP outer)
          (scheduledRefuterWord source machine sourceIndex) rowBits)
        (outerProofFormulaSeedFuel row (paddedOuterPCP outer)
          (scheduledRefuterWord source machine sourceIndex) rowFuel)
        target pointCode targetBits targetFuel value hseed htarget)
      hcaseOneBits
  exact run_linkPrograms hpositive htargetBits hframe hcaseOne

end NearCubicWires.CaseOneTargetLanguageClosure
