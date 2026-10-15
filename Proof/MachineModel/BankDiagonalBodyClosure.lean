import Proof.MachineModel.BankAtomContextRegisters
import Proof.MachineModel.BankFramedTargetChains

/-!
# The bank/diagonal cluster of `bodyRun`, assembled

`PaddedProjectionPresentation.inverse_bodyRun_ofPresentation` consumes eleven
named premises.  Three of them belong to the numeral bank and the schedule's
diagonal: the frame-lowering adapter `hadapter` and the two chain premises
`hchainOne`/`hchainTwo`, each stated at `publishedBankFrame`.  This module
instantiates the consumer so that all three are replaced by statements from
which the bank has been removed:

* `BankAtomContextRegisters.InverseAtomTableRuns` — the projection runner's
  balanced table at the bank's frame.  The count is executed
  (`BankAtomShapeCountStage`) under the *existing* compiler premise at index
  `0`; the width, query count and size cap are the bank's own registers
  (`BankAtomContextRegisters` §4); the frame retention is
  `BankFrameLoweringAdapter` §3.
* `BankFramedTargetChains.InverseCaseOnePointRuns` /
  `InverseCaseTwoPointRuns` — the two chains at the requested point code.  The
  bank frame is projected away unconditionally by the four right projections of
  `BankFramedTargetChains` §2.

Everything else passes through untouched: the presentation premise, the six
width budgets, and `InverseCompilerRuns`.

## The two hypotheses that are threaded, not discharged

`hpresentation` and `hdiagonal`.  The diagonal is used in exactly one place —
`BankAtomContextRegisters.inverseAtomContext_ofRegisters` — and
`BankScheduleDiagonal` records why it cannot be asserted: the consumer of
`bodyRun` quantifies over every target above one onset and never pins the
request's public length to a scheduled source length.  Both chains are frame
free and therefore need neither.
-/

namespace NearCubicWires.BankDiagonalBodyClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The atom-shape stage of the diagonal cluster -/

/-- The context stage, then the count-and-pair stage. -/
noncomputable def inverseDiagonalShapeProgram
    (contracts : PublishedContracts) (advantageExponent : ℝ)
    (table : NPOracleProgram) : NPOracleProgram :=
  inverseAtomShapeProgram
    (inverseAtomContextProgram
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      table)

noncomputable def inverseDiagonalShapeBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (tableBits : LanguageEvaluationRequest → ℕ) (compilerBits : ℕ → ℕ → ℕ) :
    LanguageEvaluationRequest → ℕ :=
  inverseAtomShapeBits contracts clockDepth machine advantageExponent pcp
    (inverseAtomContextBits contracts clockDepth machine advantageExponent pcp
      tableBits)
    compilerBits

noncomputable def inverseDiagonalShapeFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (table : NPOracleProgram) (tableFuel : LanguageEvaluationRequest → ℕ)
    (compilerFuel : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  inverseAtomShapeFuel contracts clockDepth machine advantageExponent pcp
    (inverseAtomContextFuel contracts advantageExponent table tableFuel)
    compilerFuel

/-! ## 2. The frame-lowering adapter of the diagonal cluster -/

noncomputable def inverseDiagonalAdapterProgram
    (contracts : PublishedContracts) (advantageExponent : ℝ)
    (table : NPOracleProgram) : NPOracleProgram :=
  inverseFrameAdapterProgram
    (inverseDiagonalShapeProgram contracts advantageExponent table)

noncomputable def inverseDiagonalAdapterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (tableBits : LanguageEvaluationRequest → ℕ) (compilerBits : ℕ → ℕ → ℕ) :
    LanguageEvaluationRequest → ℕ :=
  inverseFrameAdapterBits contracts clockDepth machine advantageExponent pcp
    (inverseDiagonalShapeBits contracts clockDepth machine advantageExponent pcp
      tableBits compilerBits)

noncomputable def inverseDiagonalAdapterFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (table : NPOracleProgram) (tableFuel : LanguageEvaluationRequest → ℕ)
    (compilerFuel : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  inverseFrameAdapterFuel
    (inverseDiagonalShapeProgram contracts advantageExponent table)
    (inverseDiagonalShapeFuel contracts clockDepth machine advantageExponent pcp
      table tableFuel compilerFuel)

/-! ## 3. `bodyRun` from the cluster's frame-free residuals -/

set_option maxHeartbeats 1600000 in
-- The dispatched body's envelopes are nested link terms over the whole stream.
/-- **The inverse schedule's `bodyRun`, from the diagonal cluster's residuals.**
`inverse_bodyRun_ofPresentation` with its adapter premise and its two chain
premises replaced by statements in which the numeral bank does not appear. -/
theorem inverse_bodyRun_ofDiagonalCluster
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (table caseOne caseTwo : NPOracleProgram)
    (tableBits tableFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (htable :
      InverseAtomTableRuns contracts clockDepth machine advantageExponent pcp
        table tableBits tableFuel)
    (hpositive : ∀ target, 1 ≤ rangeBits target)
    (hlengthBits : ∀ target, natBitLength target ≤ rangeBits target)
    (hrangeBits : ∀ target,
      generatedBalancedRangeRequiredBits target
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target) ≤
        rangeBits target)
    (hlistBits : ∀ target,
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms target
              (inverseAtomContext contracts clockDepth machine advantageExponent
                pcp target)
              0
              (inverseAtomCount contracts clockDepth machine advantageExponent
                pcp target))) ≤
        rangeBits target)
    (hcallBits : ∀ target,
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent target)
              (inverseScheduleBound contracts clockDepth advantageExponent
                target)
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms target
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target)
            0
            (inverseAtomCount contracts clockDepth machine advantageExponent pcp
              target)) ≤
        rangeBits target)
    (hcalleeBits : ∀ target index,
      index <
        inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target →
      structuralAtomCalleeBits target
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (pcp.queryCount
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (inverseScheduleBound contracts clockDepth advantageExponent target)
          index (compilerBits target index) ≤
        rangeBits target)
    (hcompiler :
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel)
    (hchainOne :
      InverseCaseOnePointRuns contracts clockDepth machine advantageExponent
        caseOne chainBits chainFuel)
    (hchainTwo :
      InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
        caseTwo chainBits chainFuel) :
    ∀ target
      (hlarge :
        inverseCaseOneTargetOnset contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          advantageExponent ≤ target)
      (hyes :
        (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
          (sourceLength (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target)))
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target))
      (hrejects :
        ¬machine.toSemantic.accepts
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target))
      (haccepts :
        ∀ branchTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent)))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target),
          InverseCaseTwoAcceptance contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent)
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target)
            branchTwo machine),
      ∀ input : BitInput target,
        runNPOracleProgram
            (bankDispatchedBodyProgram
              (emittedBranchSelectorProgram
                (inverseBankEmitterProgram (inverseDiagonalAdapterProgram contracts
                  advantageExponent table)))
              (bankFramedChainProgram caseOne) (bankFramedChainProgram caseTwo))
            (bankDispatchedBodyBits contracts clockDepth advantageExponent
              (inverseBankSelectorBits contracts clockDepth machine
                advantageExponent
                (inverseBankEmitterBits contracts clockDepth machine
                  advantageExponent pcp (inverseDiagonalAdapterBits contracts
                    clockDepth machine advantageExponent pcp tableBits
                    compilerBits) rangeBits))
              (bankFramedChainBits contracts clockDepth
                advantageExponent chainBits) ⟨target, input⟩)
            (bankDispatchedBodyFuel (bankFramedChainProgram caseOne)
              (bankFramedChainProgram caseTwo)
              (inverseBankSelectorFuel contracts clockDepth machine
                advantageExponent
                (inverseBankEmitterFuel contracts clockDepth machine
                  advantageExponent pcp (inverseDiagonalAdapterFuel contracts
                    clockDepth machine advantageExponent pcp table tableFuel
                    compilerFuel) compilerFuel))
              (bankFramedChainFuel caseOne caseTwo chainFuel) ⟨target, input⟩)
            (initialNPOracleState target
              (publishedBankFrame
                (publishedHierarchyOuterPCP contracts clockDepth)
                (publishedPointwisePCPP contracts)
                (inverseBankRate contracts advantageExponent) target
                (encodeBitInput input))) =
          some
            (inverseCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target hlarge hyes hrejects haccepts
              input).toNat :=
  inverse_bodyRun_ofPresentation contracts clockDepth machine advantageExponent
    pcp hpresentation
    (inverseDiagonalAdapterProgram contracts advantageExponent table)
    (bankFramedChainProgram caseOne) (bankFramedChainProgram caseTwo)
    (inverseDiagonalAdapterBits contracts clockDepth machine advantageExponent
      pcp tableBits compilerBits)
    (inverseDiagonalAdapterFuel contracts clockDepth machine advantageExponent
      pcp table tableFuel compilerFuel)
    (bankFramedChainBits contracts clockDepth advantageExponent chainBits)
    (bankFramedChainFuel caseOne caseTwo chainFuel)
    rangeBits compilerBits compilerFuel
    (inverseFrameAdapterRuns_ofShape contracts clockDepth machine
      advantageExponent pcp
      (inverseDiagonalShapeProgram contracts advantageExponent table)
      (inverseDiagonalShapeBits contracts clockDepth machine advantageExponent
        pcp tableBits compilerBits)
      (inverseDiagonalShapeFuel contracts clockDepth machine advantageExponent
        pcp table tableFuel compilerFuel)
      (inverseAtomShapeRuns_ofContext contracts clockDepth machine
        advantageExponent pcp
        (inverseAtomContextProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          table)
        (inverseAtomContextBits contracts clockDepth machine advantageExponent
          pcp tableBits)
        (inverseAtomContextFuel contracts advantageExponent table tableFuel)
        compilerBits compilerFuel
        (inverseAtomContextRuns_ofTable contracts clockDepth machine
          advantageExponent pcp hpresentation hdiagonal table tableBits
          tableFuel htable)
        hcompiler))
    hpositive hlengthBits hrangeBits hlistBits hcallBits hcalleeBits hcompiler
    (inverse_chainOne_ofPointRuns contracts clockDepth machine advantageExponent
      caseOne caseTwo chainBits chainFuel hchainOne)
    (inverse_chainTwo_ofPointRuns contracts clockDepth machine advantageExponent
      caseOne caseTwo chainBits chainFuel hchainTwo)

end NearCubicWires.BankDiagonalBodyClosure
