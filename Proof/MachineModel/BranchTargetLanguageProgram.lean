import Proof.CaseAnalysis.CaseOneTargetLanguageClosure
import Proof.MachineModel.CaseTwoSeedBlockListProgram
import Proof.MachineModel.OuterProofRowStageProgram

namespace NearCubicWires.BranchTargetLanguageProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseOneTargetLanguageClosure
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRowStageProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveredProofCaseOneProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## 1. The Case-1 value of the canonical target -/

/-- Case-1 counterpart of
`CaseTwoRecoveryAssembly.inverseCanonicalTargetFunction_caseTwo_apply`. -/
theorem inverseCanonicalTargetFunction_caseOne_apply
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
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hbranch :
      inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseOne data)
    (point : BitInput target) :
    inverseCanonicalTargetFunction contracts outer machine advantageExponent
        target hlarge hyes hrejects haccepts point =
      inverseCaseOneTargetFunction contracts outer advantageExponent target
        (inverseCaseOneTargetOnset_ready contracts outer advantageExponent
          target hlarge).1
        data hyes
        (inverseCaseOneTargetOnset_ready contracts outer advantageExponent
          target hlarge).2.1
        point := by
  unfold inverseCanonicalTargetFunction
  rw [hbranch]

/-- Fixed-rate counterpart of
`inverseCanonicalTargetFunction_caseOne_apply`. -/
theorem fixedCanonicalTargetFunction_caseOne_apply
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
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hbranch :
      fixedTargetBranch contracts outer machine requestedRate target hyes =
        .caseOne data)
    (point : BitInput target) :
    fixedCanonicalTargetFunction contracts outer machine requestedRate target
        hlarge hyes hrejects haccepts point =
      fixedCaseOneTargetFunction contracts outer requestedRate target
        (fixedCaseOneTargetOnset_ready contracts outer requestedRate target
          hlarge).1
        data hyes
        (fixedCaseOneTargetOnset_ready contracts outer requestedRate target
          hlarge).2
        point := by
  unfold fixedCanonicalTargetFunction
  rw [hbranch]

/-! ## 2. The Case-1 chain from the requested point code, at both schedules -/

/-! ### The inverse schedule -/

/-- The closed Case-1 chain of the inverse schedule: one published refuter
call, the fixed decision-row stage, the C.12 recovery seed, the amplifier
construction call, and the fixed target-bit dispatcher. -/
noncomputable def inverseCaseOneChainProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : NPOracleProgram :=
  caseOneTargetBitFromPointProgram (publishedAmplifier contracts).algorithm
    source.refuter.runner.program
    (outerProofRowScheduledProgram outer)
    machine.description (sourceLength (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target)))
    (scheduledWidth outer (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target)))

noncomputable def inverseCaseOneChainBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) (point : BitInput target) : ℕ :=
  caseOneTargetBitFromPointBits (publishedAmplifier contracts).algorithm outer
    machine (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target)) target (encodeBitInput point)
    (targetBitCaseOneBits (publishedAmplifier contracts).algorithm target
      ((publishedAmplifier contracts).algorithm.outputArity
        (scheduledAmplifierRequest outer
        (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))
        (inverseRefuterInput contracts outer machine advantageExponent target)))
      ((publishedAmplifier contracts).algorithm.descriptor
        (scheduledAmplifierRequest outer
        (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))
        (inverseRefuterInput contracts outer machine advantageExponent target)))
      (encodeBitInput point))
    (outerProofRowScheduledBits outer (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))
      (inverseRefuterInput contracts outer machine advantageExponent target))

noncomputable def inverseCaseOneChainFuel
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) (point : BitInput target) : ℕ :=
  caseOneTargetBitFromPointFuel (publishedAmplifier contracts).algorithm
    (outerProofRowScheduledProgram outer)
    outer machine (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))
    (outerProofRowScheduledFuel outer (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (targetBitCaseOneFuel (publishedAmplifier contracts).algorithm
      ((publishedAmplifier contracts).algorithm.outputArity
        (scheduledAmplifierRequest outer
        (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))
        (inverseRefuterInput contracts outer machine advantageExponent target)))
      ((publishedAmplifier contracts).algorithm.descriptor
        (scheduledAmplifierRequest outer
        (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))
        (inverseRefuterInput contracts outer machine advantageExponent target)))
      (encodeBitInput point))

/-! ### The fixed schedule -/

/-- The closed Case-1 chain of the fixed schedule: one published refuter
call, the fixed decision-row stage, the C.12 recovery seed, the amplifier
construction call, and the fixed target-bit dispatcher. -/
noncomputable def fixedCaseOneChainProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) : NPOracleProgram :=
  caseOneTargetBitFromPointProgram (publishedAmplifier contracts).algorithm
    source.refuter.runner.program
    (outerProofRowScheduledProgram outer)
    machine.description (sourceLength (fixedSelectedSource contracts outer requestedRate target))
    (scheduledWidth outer (fixedSelectedSource contracts outer requestedRate target))

noncomputable def fixedCaseOneChainBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) (point : BitInput target) : ℕ :=
  caseOneTargetBitFromPointBits (publishedAmplifier contracts).algorithm outer
    machine (fixedSelectedSource contracts outer requestedRate target) target (encodeBitInput point)
    (targetBitCaseOneBits (publishedAmplifier contracts).algorithm target
      ((publishedAmplifier contracts).algorithm.outputArity
        (scheduledAmplifierRequest outer
        (fixedSelectedSource contracts outer requestedRate target)
        (fixedRefuterInput contracts outer machine requestedRate target)))
      ((publishedAmplifier contracts).algorithm.descriptor
        (scheduledAmplifierRequest outer
        (fixedSelectedSource contracts outer requestedRate target)
        (fixedRefuterInput contracts outer machine requestedRate target)))
      (encodeBitInput point))
    (outerProofRowScheduledBits outer
      (fixedSelectedSource contracts outer requestedRate target)
      (fixedRefuterInput contracts outer machine requestedRate target))

noncomputable def fixedCaseOneChainFuel
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) (point : BitInput target) : ℕ :=
  caseOneTargetBitFromPointFuel (publishedAmplifier contracts).algorithm
    (outerProofRowScheduledProgram outer)
    outer machine (fixedSelectedSource contracts outer requestedRate target)
    (outerProofRowScheduledFuel outer
      (fixedSelectedSource contracts outer requestedRate target)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (targetBitCaseOneFuel (publishedAmplifier contracts).algorithm
      ((publishedAmplifier contracts).algorithm.outputArity
        (scheduledAmplifierRequest outer
        (fixedSelectedSource contracts outer requestedRate target)
        (fixedRefuterInput contracts outer machine requestedRate target)))
      ((publishedAmplifier contracts).algorithm.descriptor
        (scheduledAmplifierRequest outer
        (fixedSelectedSource contracts outer requestedRate target)
        (fixedRefuterInput contracts outer machine requestedRate target)))
      (encodeBitInput point))

/-- **The inverse schedule's Case-1 target bit, from the requested point code
alone.**  The whole C.12 recovery side is the fixed program of
`OuterProofRowStageProgram`; the scheduled query-count positivity is the only
side condition. -/
theorem run_inverseCaseOneChainProgram
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
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hbranch : inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseOne data)
    (point : BitInput target)
    (hcount :
      0 < outer.pcp.queryCount (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))) :
    runNPOracleProgram
        (inverseCaseOneChainProgram contracts outer machine advantageExponent target)
        (inverseCaseOneChainBits contracts outer machine advantageExponent target point)
        (inverseCaseOneChainFuel contracts outer machine advantageExponent target point)
        (initialNPOracleState target (encodeBitInput point)) =
      some (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat := by
  rw [inverseCanonicalTargetFunction_caseOne_apply contracts outer machine
    advantageExponent target hlarge hyes hrejects haccepts data
    hbranch point]
  exact run_caseOneTargetBitFromPointProgram_closed
    (publishedAmplifier contracts).algorithm outer machine (inverseSourceIndex
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target))
    target (encodeBitInput point) _ _ _ hcount
    (run_targetBitProgram_inverseCaseOne contracts outer advantageExponent target
      (inverseCaseOneTargetOnset_ready contracts outer advantageExponent target
        hlarge).1
      data hyes
      (inverseCaseOneTargetOnset_ready contracts outer advantageExponent target
        hlarge).2.1
      point)

/-- The Case-2 chain of the inverse schedule, parameterized by the per-block
occurrence callee. -/
noncomputable def inverseCaseTwoChainProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ) (target : ℕ) (occurrence : NPOracleProgram) : NPOracleProgram :=
  caseTwoTargetBitFromPointRangeProgram (publishedAmplifier contracts).algorithm
    occurrence (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))

noncomputable def inverseCaseTwoChainBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP outer)
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (occurrenceBits : ℕ → ℕ) (point : BitInput target) : ℕ :=
  caseTwoTargetBitFromPointRangeBits target (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
    (encodeBitInput point) occurrenceBits
    (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
      (encodeBitInput point))
    ((List.range (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))).map
      (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
      (encodeBitInput point)))

noncomputable def inverseCaseTwoChainFuel
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP outer)
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (occurrence : NPOracleProgram) (occurrenceFuel : ℕ → ℕ)
    (point : BitInput target) : ℕ :=
  caseTwoTargetBitFromPointRangeFuel (publishedAmplifier contracts).algorithm
    occurrence target (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
    (encodeBitInput point) occurrenceFuel
    ((List.range (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))).map
      (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
      (encodeBitInput point)))

/-- **The inverse schedule's Case-2 target bit, from the requested point code
alone.**  Modulo the single per-block occurrence callee, the chain of
`CaseTwoSeedBlockListProgram` returns the canonical target on the Case-2
branch. -/
theorem run_inverseCaseTwoChainProgram
    (occurrence : NPOracleProgram)
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
    (hbranch : inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseTwo caseTwo)
    (point : BitInput target) (occurrenceBits occurrenceFuel : ℕ → ℕ)
    (hoccurrence : ∀ block, block < (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))) →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
            (encodeBitInput point) block).toNat) :
    runNPOracleProgram
        (inverseCaseTwoChainProgram contracts outer advantageExponent target occurrence)
        (inverseCaseTwoChainBits contracts outer machine advantageExponent target caseTwo
          occurrenceBits point)
        (inverseCaseTwoChainFuel contracts outer machine advantageExponent target caseTwo
          occurrence occurrenceFuel point)
        (initialNPOracleState target (encodeBitInput point)) =
      some (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat :=
  run_caseTwoTargetBitFromPointRangeProgram_inverse occurrence contracts outer machine
    advantageExponent target hlarge hyes hrejects haccepts caseTwo hbranch point
    occurrenceBits occurrenceFuel hoccurrence

/-- **The fixed schedule's Case-1 target bit, from the requested point code
alone.**  The whole C.12 recovery side is the fixed program of
`OuterProofRowStageProgram`; the scheduled query-count positivity is the only
side condition. -/
theorem run_fixedCaseOneChainProgram
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
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hbranch : fixedTargetBranch contracts outer machine requestedRate target hyes = .caseOne data)
    (point : BitInput target)
    (hcount :
      0 < outer.pcp.queryCount
        (sourceLength
          (fixedSelectedSource contracts outer requestedRate target))) :
    runNPOracleProgram
        (fixedCaseOneChainProgram contracts outer machine requestedRate target)
        (fixedCaseOneChainBits contracts outer machine requestedRate target point)
        (fixedCaseOneChainFuel contracts outer machine requestedRate target point)
        (initialNPOracleState target (encodeBitInput point)) =
      some (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat := by
  rw [fixedCanonicalTargetFunction_caseOne_apply contracts outer machine requestedRate
    target hlarge hyes hrejects haccepts data
    hbranch point]
  exact run_caseOneTargetBitFromPointProgram_closed
    (publishedAmplifier contracts).algorithm outer machine
    (fixedSelectedSource contracts outer requestedRate target)
    target (encodeBitInput point) _ _ _ hcount
    (run_targetBitProgram_fixedCaseOne contracts outer requestedRate target
      (fixedCaseOneTargetOnset_ready contracts outer requestedRate target
        hlarge).1
      data hyes
      (fixedCaseOneTargetOnset_ready contracts outer requestedRate target
        hlarge).2
      point)

/-- The Case-2 chain of the fixed schedule, parameterized by the per-block
occurrence callee. -/
noncomputable def fixedCaseTwoChainProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (_outer : HierarchyOuterPCP source)
    (requestedRate _target : ℕ) (occurrence : NPOracleProgram) :
    NPOracleProgram :=
  caseTwoTargetBitFromPointRangeProgram (publishedAmplifier contracts).algorithm
    occurrence (fixedCopies (publishedPointwisePCPP contracts)
        (fixedRate contracts requestedRate))

noncomputable def fixedCaseTwoChainBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (occurrenceBits : ℕ → ℕ) (point : BitInput target) : ℕ :=
  caseTwoTargetBitFromPointRangeBits target (fixedCopies (publishedPointwisePCPP contracts)
        (fixedRate contracts requestedRate))
    (encodeBitInput point) occurrenceBits
    (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
      (encodeBitInput point))
    ((List.range (fixedCopies (publishedPointwisePCPP contracts)
        (fixedRate contracts requestedRate))).map
      (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
      (encodeBitInput point)))

noncomputable def fixedCaseTwoChainFuel
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (occurrence : NPOracleProgram) (occurrenceFuel : ℕ → ℕ)
    (point : BitInput target) : ℕ :=
  caseTwoTargetBitFromPointRangeFuel (publishedAmplifier contracts).algorithm
    occurrence target (fixedCopies (publishedPointwisePCPP contracts)
        (fixedRate contracts requestedRate))
    (encodeBitInput point) occurrenceFuel
    ((List.range (fixedCopies (publishedPointwisePCPP contracts)
        (fixedRate contracts requestedRate))).map
      (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
      (encodeBitInput point)))

/-- **The fixed schedule's Case-2 target bit, from the requested point code
alone.**  Modulo the single per-block occurrence callee, the chain of
`CaseTwoSeedBlockListProgram` returns the canonical target on the Case-2
branch. -/
theorem run_fixedCaseTwoChainProgram
    (occurrence : NPOracleProgram)
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
    (point : BitInput target) (occurrenceBits occurrenceFuel : ℕ → ℕ)
    (hoccurrence : ∀ block, block < (fixedCopies (publishedPointwisePCPP contracts)
        (fixedRate contracts requestedRate)) →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
            (encodeBitInput point) block).toNat) :
    runNPOracleProgram
        (fixedCaseTwoChainProgram contracts outer requestedRate target occurrence)
        (fixedCaseTwoChainBits contracts outer machine requestedRate target caseTwo
          occurrenceBits point)
        (fixedCaseTwoChainFuel contracts outer machine requestedRate target caseTwo
          occurrence occurrenceFuel point)
        (initialNPOracleState target (encodeBitInput point)) =
      some (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat :=
  run_caseTwoTargetBitFromPointRangeProgram_fixed occurrence contracts outer machine
    requestedRate target hlarge hyes hrejects haccepts caseTwo hbranch point
    occurrenceBits occurrenceFuel hoccurrence

/-! ## 3. The fixed tag dispatcher -/

/-- One branch-dispatched target program: the branch selector, then the fixed
tag dispatcher over the two chains.  The selector is the only oracle-using
stage — it is exactly the one SAT query of
`CanonicalTargetLanguageProgram.scheduledCaseTwo_iff_encodedSat`. -/
def branchTargetBitProgram (selector first second : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms selector (taggedProgramChoice first second)

def branchTargetBitFuel (first second : NPOracleProgram)
    (selectorFuel bodyFuel : ℕ) : ℕ :=
  linkFuel (taggedProgramChoice first second) selectorFuel
    (taggedProgramChoiceFuel bodyFuel)

/-- Register width of the tag dispatcher alone: the tagged request, either
body, and the shared output. -/
def branchChoiceBits (inputLength tag pointCode bodyBits output : ℕ) : ℕ :=
  max (natBitLength (Nat.pair inputLength (Nat.pair tag pointCode)))
    (max bodyBits (natBitLength output))

def branchTargetBitBits
    (inputLength tag pointCode selectorBits bodyBits output : ℕ) : ℕ :=
  occurrenceStageBits inputLength selectorBits
    (branchChoiceBits inputLength tag pointCode bodyBits output)

/-- Exact execution on the zero tag. -/
theorem run_branchTargetBitProgram_caseOne
    (selector first second : NPOracleProgram)
    (inputLength pointCode selectorBits selectorFuel bodyBits bodyFuel
      output : ℕ)
    (hselector :
      runNPOracleProgram selector selectorBits selectorFuel
          (initialNPOracleState inputLength pointCode) =
        some (Nat.pair 0 pointCode))
    (hfirst :
      runNPOracleProgram first bodyBits bodyFuel
          (initialNPOracleState inputLength pointCode) = some output) :
    runNPOracleProgram (branchTargetBitProgram selector first second)
        (branchTargetBitBits inputLength 0 pointCode selectorBits bodyBits
          output)
        (branchTargetBitFuel first second selectorFuel bodyFuel)
        (initialNPOracleState inputLength pointCode) = some output := by
  have hinput :
      natBitLength (Nat.pair inputLength (Nat.pair 0 pointCode)) ≤
        branchChoiceBits inputLength 0 pointCode bodyBits output :=
    Nat.le_max_left _ _
  have hbody :
      bodyBits ≤ branchChoiceBits inputLength 0 pointCode bodyBits output :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have houtput :
      natBitLength output ≤
        branchChoiceBits inputLength 0 pointCode bodyBits output :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact run_occurrenceStage hselector
    (run_taggedProgramChoice_zero first second inputLength pointCode
      (branchChoiceBits inputLength 0 pointCode bodyBits output) bodyFuel
      output hinput (run_bits_mono hfirst hbody) houtput)

/-- Exact execution on every nonzero tag. -/
theorem run_branchTargetBitProgram_caseTwo
    (selector first second : NPOracleProgram)
    (inputLength pointCode tag selectorBits selectorFuel bodyBits bodyFuel
      output : ℕ)
    (htag : tag ≠ 0)
    (hselector :
      runNPOracleProgram selector selectorBits selectorFuel
          (initialNPOracleState inputLength pointCode) =
        some (Nat.pair tag pointCode))
    (hsecond :
      runNPOracleProgram second bodyBits bodyFuel
          (initialNPOracleState inputLength pointCode) = some output) :
    runNPOracleProgram (branchTargetBitProgram selector first second)
        (branchTargetBitBits inputLength tag pointCode selectorBits bodyBits
          output)
        (branchTargetBitFuel first second selectorFuel bodyFuel)
        (initialNPOracleState inputLength pointCode) = some output := by
  have hinput :
      natBitLength (Nat.pair inputLength (Nat.pair tag pointCode)) ≤
        branchChoiceBits inputLength tag pointCode bodyBits output :=
    Nat.le_max_left _ _
  have hbody :
      bodyBits ≤ branchChoiceBits inputLength tag pointCode bodyBits output :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have houtput :
      natBitLength output ≤
        branchChoiceBits inputLength tag pointCode bodyBits output :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact run_occurrenceStage hselector
    (run_taggedProgramChoice_nonzero first second inputLength tag pointCode
      (branchChoiceBits inputLength tag pointCode bodyBits output) bodyFuel
      output htag hinput (run_bits_mono hsecond hbody) houtput)

/-! ## 4. The branch-dispatched target at both published schedules -/

/-- The inverse schedule's whole target program: one branch selector and the
two closed chains. -/
noncomputable def inverseTargetProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) (selector occurrence : NPOracleProgram) :
    NPOracleProgram :=
  branchTargetBitProgram selector
    (inverseCaseOneChainProgram contracts outer machine advantageExponent target)
    (inverseCaseTwoChainProgram contracts outer advantageExponent target occurrence)

/-- **The inverse schedule's canonical target, on the Case-1 branch.** -/
theorem run_inverseTargetProgram_caseOne
    (selector occurrence : NPOracleProgram)
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
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hbranch : inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseOne data)
    (point : BitInput target) (selectorBits selectorFuel : ℕ)
    (hselector :
      runNPOracleProgram selector selectorBits selectorFuel
          (initialNPOracleState target (encodeBitInput point)) =
        some (Nat.pair 0 (encodeBitInput point)))
    (hcount :
      0 < outer.pcp.queryCount (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))) :
    runNPOracleProgram
        (inverseTargetProgram contracts outer machine advantageExponent target selector
          occurrence)
        (branchTargetBitBits target 0 (encodeBitInput point) selectorBits
          (inverseCaseOneChainBits contracts outer machine advantageExponent target point)
          (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (inverseCaseOneChainProgram contracts outer machine advantageExponent target)
          (inverseCaseTwoChainProgram contracts outer advantageExponent target occurrence)
          selectorFuel
          (inverseCaseOneChainFuel contracts outer machine advantageExponent target point))
        (initialNPOracleState target (encodeBitInput point)) =
      some (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat :=
  run_branchTargetBitProgram_caseOne selector
    (inverseCaseOneChainProgram contracts outer machine advantageExponent target)
    (inverseCaseTwoChainProgram contracts outer advantageExponent target occurrence)
    target (encodeBitInput point) selectorBits selectorFuel _ _ _ hselector
    (run_inverseCaseOneChainProgram contracts outer machine advantageExponent target hlarge
      hyes hrejects haccepts data hbranch point hcount)

/-- **The inverse schedule's canonical target, on the Case-2 branch.** -/
theorem run_inverseTargetProgram_caseTwo
    (selector occurrence : NPOracleProgram)
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
    (hbranch : inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseTwo caseTwo)
    (point : BitInput target) (selectorBits selectorFuel tag : ℕ)
    (occurrenceBits occurrenceFuel : ℕ → ℕ) (htag : tag ≠ 0)
    (hselector :
      runNPOracleProgram selector selectorBits selectorFuel
          (initialNPOracleState target (encodeBitInput point)) =
        some (Nat.pair tag (encodeBitInput point)))
    (hoccurrence : ∀ block, block < (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))) →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
            (encodeBitInput point) block).toNat) :
    runNPOracleProgram
        (inverseTargetProgram contracts outer machine advantageExponent target selector
          occurrence)
        (branchTargetBitBits target tag (encodeBitInput point) selectorBits
          (inverseCaseTwoChainBits contracts outer machine advantageExponent target caseTwo
            occurrenceBits point)
          (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (inverseCaseOneChainProgram contracts outer machine advantageExponent target)
          (inverseCaseTwoChainProgram contracts outer advantageExponent target occurrence)
          selectorFuel
          (inverseCaseTwoChainFuel contracts outer machine advantageExponent target caseTwo
            occurrence occurrenceFuel point))
        (initialNPOracleState target (encodeBitInput point)) =
      some (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat :=
  run_branchTargetBitProgram_caseTwo selector
    (inverseCaseOneChainProgram contracts outer machine advantageExponent target)
    (inverseCaseTwoChainProgram contracts outer advantageExponent target occurrence)
    target (encodeBitInput point) tag selectorBits selectorFuel _ _ _ htag
    hselector
    (run_inverseCaseTwoChainProgram occurrence contracts outer machine
      advantageExponent target hlarge hyes hrejects haccepts caseTwo hbranch point
      occurrenceBits occurrenceFuel hoccurrence)

/-- The fixed schedule's whole target program: one branch selector and the
two closed chains. -/
noncomputable def fixedTargetProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) (selector occurrence : NPOracleProgram) :
    NPOracleProgram :=
  branchTargetBitProgram selector
    (fixedCaseOneChainProgram contracts outer machine requestedRate target)
    (fixedCaseTwoChainProgram contracts outer requestedRate target occurrence)

/-- **The fixed schedule's canonical target, on the Case-1 branch.** -/
theorem run_fixedTargetProgram_caseOne
    (selector occurrence : NPOracleProgram)
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
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hbranch : fixedTargetBranch contracts outer machine requestedRate target hyes = .caseOne data)
    (point : BitInput target) (selectorBits selectorFuel : ℕ)
    (hselector :
      runNPOracleProgram selector selectorBits selectorFuel
          (initialNPOracleState target (encodeBitInput point)) =
        some (Nat.pair 0 (encodeBitInput point)))
    (hcount :
      0 < outer.pcp.queryCount
        (sourceLength
          (fixedSelectedSource contracts outer requestedRate target))) :
    runNPOracleProgram
        (fixedTargetProgram contracts outer machine requestedRate target selector
          occurrence)
        (branchTargetBitBits target 0 (encodeBitInput point) selectorBits
          (fixedCaseOneChainBits contracts outer machine requestedRate target point)
          (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (fixedCaseOneChainProgram contracts outer machine requestedRate target)
          (fixedCaseTwoChainProgram contracts outer requestedRate target occurrence)
          selectorFuel
          (fixedCaseOneChainFuel contracts outer machine requestedRate target point))
        (initialNPOracleState target (encodeBitInput point)) =
      some (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat :=
  run_branchTargetBitProgram_caseOne selector
    (fixedCaseOneChainProgram contracts outer machine requestedRate target)
    (fixedCaseTwoChainProgram contracts outer requestedRate target occurrence)
    target (encodeBitInput point) selectorBits selectorFuel _ _ _ hselector
    (run_fixedCaseOneChainProgram contracts outer machine requestedRate target hlarge
      hyes hrejects haccepts data hbranch point hcount)

/-- **The fixed schedule's canonical target, on the Case-2 branch.** -/
theorem run_fixedTargetProgram_caseTwo
    (selector occurrence : NPOracleProgram)
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
    (point : BitInput target) (selectorBits selectorFuel tag : ℕ)
    (occurrenceBits occurrenceFuel : ℕ → ℕ) (htag : tag ≠ 0)
    (hselector :
      runNPOracleProgram selector selectorBits selectorFuel
          (initialNPOracleState target (encodeBitInput point)) =
        some (Nat.pair tag (encodeBitInput point)))
    (hoccurrence : ∀ block, block < (fixedCopies (publishedPointwisePCPP contracts)
        (fixedRate contracts requestedRate)) →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
            (encodeBitInput point) block).toNat) :
    runNPOracleProgram
        (fixedTargetProgram contracts outer machine requestedRate target selector
          occurrence)
        (branchTargetBitBits target tag (encodeBitInput point) selectorBits
          (fixedCaseTwoChainBits contracts outer machine requestedRate target caseTwo
            occurrenceBits point)
          (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (fixedCaseOneChainProgram contracts outer machine requestedRate target)
          (fixedCaseTwoChainProgram contracts outer requestedRate target occurrence)
          selectorFuel
          (fixedCaseTwoChainFuel contracts outer machine requestedRate target caseTwo
            occurrence occurrenceFuel point))
        (initialNPOracleState target (encodeBitInput point)) =
      some (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat :=
  run_branchTargetBitProgram_caseTwo selector
    (fixedCaseOneChainProgram contracts outer machine requestedRate target)
    (fixedCaseTwoChainProgram contracts outer requestedRate target occurrence)
    target (encodeBitInput point) tag selectorBits selectorFuel _ _ _ htag
    hselector
    (run_fixedCaseTwoChainProgram occurrence contracts outer machine
      requestedRate target hlarge hyes hrejects haccepts caseTwo hbranch point
      occurrenceBits occurrenceFuel hoccurrence)

end NearCubicWires.BranchTargetLanguageProgram
