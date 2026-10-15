import Proof.CaseAnalysis.CaseTwoOccurrenceCoordinates

/-!
# The Case-2 branch of the canonical target language, from the request alone

`CanonicalTargetLanguageProgram.run_targetBitProgram_caseTwo_xorPower` shows
that the already fixed target-bit dispatcher returns exactly the XOR-amplified
seed bit once the seed block values are data on its input.  The public
pointwise exports
`CaseTwoRecoveryAssembly.inverseCanonicalTargetFunction_caseTwo_apply` and its
fixed-rate counterpart identify that XOR power with the canonical target on
the Case-2 branch.

This module links the two.  Exactly as `CaseOneTargetLanguageClosure` leaves
its single named decision-row stage as a hypothesis, the block stage — the
loop that evaluates the scheduled Case-2 seed once per XOR copy, whose
per-copy value is
`CaseTwoOccurrenceCoordinates.caseTwoSeed_apply_occurrenceCodeValue` and whose
per-copy execution is
`CaseTwoOccurrenceProgram.run_caseTwoOccurrenceProgram` — is a parameter here.
Everything downstream of it is closed: one link, one dispatcher run, and the
published branch value theorem.
-/

namespace NearCubicWires.CaseTwoTargetLanguageClosure

open NearCubicWires
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The seed block values of one XOR power -/

/-- The seed values the Case-2 branch of the fixed dispatcher folds: one per
XOR copy, each read on that copy's block of the requested point. -/
noncomputable def caseTwoBlockValues (arity copies : ℕ)
    (seed : BoolFunction arity) (point : BitInput (copies * arity)) :
    List Bool :=
  (Finset.univ : Finset (Fin copies)).toList.map
    fun block => seed (blockInput point block)

/-! ## 2. One link onto the fixed dispatcher -/

/-- One fixed program computing a Case-2 target bit from the requested point
code: the supplied block stage, then the published target-bit dispatcher. -/
def caseTwoTargetBitFromPointProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (blocks : NPOracleProgram) : NPOracleProgram :=
  linkPrograms blocks (targetBitProgram algorithm)

theorem caseTwoTargetBitFromPointProgram_oracleFree
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    {blocks : NPOracleProgram} (hblocks : OracleFree blocks) :
    OracleFree (caseTwoTargetBitFromPointProgram algorithm blocks) :=
  oracleFree_linkPrograms hblocks (targetBitProgram_oracleFree algorithm)

noncomputable def caseTwoTargetBitFromPointFuel
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm) (blockFuel : ℕ)
    (arity copies : ℕ) (seed : BoolFunction arity)
    (point : BitInput (copies * arity)) : ℕ :=
  linkFuel (targetBitProgram algorithm) blockFuel
    (targetBitCaseTwoFuel (caseTwoBlockValues arity copies seed point))

noncomputable def caseTwoTargetBitFromPointBits
    (inputLength blockBits arity copies : ℕ) (seed : BoolFunction arity)
    (point : BitInput (copies * arity)) : ℕ :=
  occurrenceStageBits inputLength blockBits
    (targetBitCaseTwoBits inputLength
      (caseTwoBlockValues arity copies seed point))

/-- Exact execution of the Case-2 target bit from the requested point code.
The single remaining hypothesis is the block stage's own run theorem. -/
theorem run_caseTwoTargetBitFromPointProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (blocks : NPOracleProgram)
    (inputLength pointCode blockBits blockFuel arity copies : ℕ)
    (seed : BoolFunction arity) (point : BitInput (copies * arity))
    (hblocks :
      runNPOracleProgram blocks blockBits blockFuel
          (initialNPOracleState inputLength pointCode) =
        some
          (targetBitCaseTwoInput
            (caseTwoBlockValues arity copies seed point))) :
    runNPOracleProgram (caseTwoTargetBitFromPointProgram algorithm blocks)
        (caseTwoTargetBitFromPointBits inputLength blockBits arity copies seed
          point)
        (caseTwoTargetBitFromPointFuel algorithm blockFuel arity copies seed
          point)
        (initialNPOracleState inputLength pointCode) =
      some (xorPower seed copies point).toNat :=
  run_occurrenceStage hblocks
    (run_targetBitProgram_caseTwo_xorPower algorithm inputLength arity copies
      seed point)

/-! ## 3. The inverse-schedule Case-2 target -/

/-- The low raw-core coordinates of a requested point, on which the
inverse-schedule Case-2 target reads its XOR power. -/
def inverseCaseTwoPoint
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target)
    (point : BitInput target) :
    BitInput
      (inverseCopies outer (publishedPointwisePCPP contracts)
          (inverseRate contracts (inverseCoreAdvantagePower advantageExponent))
          (inverseSourceIndex
            (inverseSelectedSource contracts outer
              (inverseCoreAdvantagePower advantageExponent) target)) *
        seedArity outer (publishedPointwisePCPP contracts)
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          (inverseSourceIndex
            (inverseSelectedSource contracts outer
              (inverseCoreAdvantagePower advantageExponent) target))) :=
  fun index =>
    point
      ⟨index.val,
        index.isLt.trans_le
          (inverseCaseTwoRawArity_le_target contracts outer
            (inverseCoreAdvantagePower advantageExponent) target
            (inverseCaseOneTargetOnset_ready contracts outer advantageExponent
              target hlarge).1)⟩

/-- **Exact inverse-schedule Case-2 execution.**  Whenever the genuine outer
split returns the canonical accepting oracle, the fixed target-bit dispatcher,
driven by a block stage that produces the scheduled Case-2 seed values of the
requested point, returns exactly the canonical Case-1/Case-2 target bit. -/
theorem run_caseTwoTargetBitFromPointProgram_inverse
    (blocks : NPOracleProgram)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hrejects : ¬machine.toSemantic.accepts
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (paddedOuterPCP outer)
        (inverseRefuterInput contracts outer machine advantageExponent target),
      InverseCaseTwoAcceptance contracts outer
        (inverseCoreAdvantagePower advantageExponent)
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)
        caseTwo machine)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP outer)
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hbranch :
      inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseTwo caseTwo)
    (point : BitInput target) (pointCode blockBits blockFuel : ℕ)
    (hblocks :
      runNPOracleProgram blocks blockBits blockFuel
          (initialNPOracleState target pointCode) =
        some
          (targetBitCaseTwoInput
            (caseTwoBlockValues
              (seedArity outer (publishedPointwisePCPP contracts)
                (inverseRequiredDegree contracts
                  (inverseCoreAdvantagePower advantageExponent))
                (inverseSourceIndex
                  (inverseSelectedSource contracts outer
                    (inverseCoreAdvantagePower advantageExponent) target)))
              (inverseCopies outer (publishedPointwisePCPP contracts)
                (inverseRate contracts
                  (inverseCoreAdvantagePower advantageExponent))
                (inverseSourceIndex
                  (inverseSelectedSource contracts outer
                    (inverseCoreAdvantagePower advantageExponent) target)))
              (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
              (inverseCaseTwoPoint contracts outer advantageExponent target
                hlarge point)))) :
    runNPOracleProgram
        (caseTwoTargetBitFromPointProgram
          (publishedAmplifier contracts).algorithm blocks)
        (caseTwoTargetBitFromPointBits target blockBits
          (seedArity outer (publishedPointwisePCPP contracts)
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)))
          (inverseCopies outer (publishedPointwisePCPP contracts)
            (inverseRate contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)))
          (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
          (inverseCaseTwoPoint contracts outer advantageExponent target hlarge
            point))
        (caseTwoTargetBitFromPointFuel (publishedAmplifier contracts).algorithm
          blockFuel
          (seedArity outer (publishedPointwisePCPP contracts)
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)))
          (inverseCopies outer (publishedPointwisePCPP contracts)
            (inverseRate contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)))
          (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
          (inverseCaseTwoPoint contracts outer advantageExponent target hlarge
            point))
        (initialNPOracleState target pointCode) =
      some
        (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts
          point).toNat := by
  rw [inverseCanonicalTargetFunction_caseTwo_apply contracts outer machine
    advantageExponent target hlarge hyes hrejects haccepts caseTwo hbranch
    point]
  exact run_caseTwoTargetBitFromPointProgram
    (publishedAmplifier contracts).algorithm blocks target pointCode blockBits
    blockFuel
    (seedArity outer (publishedPointwisePCPP contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
    (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    (inverseCaseTwoPoint contracts outer advantageExponent target hlarge point)
    hblocks

/-! ## 4. The fixed-rate Case-2 target -/

/-- Fixed-rate counterpart of `inverseCaseTwoPoint`. -/
def fixedCaseTwoPoint
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ)
    (hlarge : fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (point : BitInput target) :
    BitInput
      (fixedCopies (publishedPointwisePCPP contracts) (fixedRate contracts requestedRate) *
        seedArity outer (publishedPointwisePCPP contracts)
          (fixedRequiredDegree contracts requestedRate)
          (fixedSelectedSource contracts outer requestedRate target)) :=
  fun index =>
    point
      ⟨index.val,
        index.isLt.trans_le
          (fixedCaseTwoRawArity_le_target contracts outer requestedRate target
            (fixedCaseOneTargetOnset_ready contracts outer requestedRate target
              hlarge).1)⟩

/-- Fixed-rate counterpart of
`run_caseTwoTargetBitFromPointProgram_inverse`. -/
theorem run_caseTwoTargetBitFromPointProgram_fixed
    (blocks : NPOracleProgram)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge : fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hrejects : ¬machine.toSemantic.accepts
      (fixedRefuterInput contracts outer machine requestedRate target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP outer)
        (fixedRefuterInput contracts outer machine requestedRate target),
      FixedCaseTwoAcceptance contracts outer requestedRate
        (fixedSelectedSource contracts outer requestedRate target)
        caseTwo machine)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hbranch :
      fixedTargetBranch contracts outer machine requestedRate target hyes =
        .caseTwo caseTwo)
    (point : BitInput target) (pointCode blockBits blockFuel : ℕ)
    (hblocks :
      runNPOracleProgram blocks blockBits blockFuel
          (initialNPOracleState target pointCode) =
        some
          (targetBitCaseTwoInput
            (caseTwoBlockValues
              (seedArity outer (publishedPointwisePCPP contracts)
                (fixedRequiredDegree contracts requestedRate)
                (fixedSelectedSource contracts outer requestedRate target))
              (fixedCopies (publishedPointwisePCPP contracts) (fixedRate contracts requestedRate))
              (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
              (fixedCaseTwoPoint contracts outer requestedRate target hlarge
                point)))) :
    runNPOracleProgram
        (caseTwoTargetBitFromPointProgram
          (publishedAmplifier contracts).algorithm blocks)
        (caseTwoTargetBitFromPointBits target blockBits
          (seedArity outer (publishedPointwisePCPP contracts)
            (fixedRequiredDegree contracts requestedRate)
            (fixedSelectedSource contracts outer requestedRate target))
          (fixedCopies (publishedPointwisePCPP contracts) (fixedRate contracts requestedRate))
          (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
          (fixedCaseTwoPoint contracts outer requestedRate target hlarge point))
        (caseTwoTargetBitFromPointFuel (publishedAmplifier contracts).algorithm
          blockFuel
          (seedArity outer (publishedPointwisePCPP contracts)
            (fixedRequiredDegree contracts requestedRate)
            (fixedSelectedSource contracts outer requestedRate target))
          (fixedCopies (publishedPointwisePCPP contracts) (fixedRate contracts requestedRate))
          (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
          (fixedCaseTwoPoint contracts outer requestedRate target hlarge point))
        (initialNPOracleState target pointCode) =
      some
        (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat := by
  rw [fixedCanonicalTargetFunction_caseTwo_apply contracts outer machine
    requestedRate target hlarge hyes hrejects haccepts caseTwo hbranch point]
  exact run_caseTwoTargetBitFromPointProgram
    (publishedAmplifier contracts).algorithm blocks target pointCode blockBits
    blockFuel
    (seedArity outer (publishedPointwisePCPP contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target))
    (fixedCopies (publishedPointwisePCPP contracts) (fixedRate contracts requestedRate))
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    (fixedCaseTwoPoint contracts outer requestedRate target hlarge point)
    hblocks

end NearCubicWires.CaseTwoTargetLanguageClosure
