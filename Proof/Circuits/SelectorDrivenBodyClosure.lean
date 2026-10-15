import Proof.PCP.SelectorDrivenProjectionPresentation
import Proof.PCP.SelectorDrivenProjectionTableStage

/-!
# The inverse body closure at the selector-driven bank

Site 4 assembles the table, context, shape, retained-frame adapter, emitter and
dispatcher entirely at `inverseSelectorAdapterFrame`.  The executable
presentation supplies the relocated table stage, so the old schedule diagonal
does not occur.  The two target-chain runs are intentionally left as the only
frame-layer premises; Site 5 addresses them separately.
-/

namespace NearCubicWires.SelectorDrivenBodyClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankFrameLoweringAdapter
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
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenBodyDispatch
open NearCubicWires.SelectorDrivenEmitterRuns
open NearCubicWires.SelectorDrivenProjectionPresentation
open NearCubicWires.SelectorDrivenProjectionTableStage
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The selector-frame shape and retained-frame adapter -/

noncomputable def inverseSelectorBodyShapeProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  inverseAtomShapeProgram
    (inverseAtomContextProgram
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSelectorBankTableProgram contracts clockDepth machine pcp))

noncomputable def inverseSelectorBodyShapeBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  inverseAtomShapeBits contracts clockDepth machine advantageExponent pcp
    (inverseSelectorAtomContextBits contracts clockDepth machine
      advantageExponent pcp
      (inverseSelectorBankTableBits contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)))
    compilerBits

noncomputable def inverseSelectorBodyShapeFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  inverseAtomShapeFuel contracts clockDepth machine advantageExponent pcp
    (inverseAtomContextFuel contracts advantageExponent
      (inverseSelectorBankTableProgram contracts clockDepth machine pcp)
      (inverseSelectorBankTableFuel contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)))
    compilerFuel

noncomputable def inverseSelectorBodyAdapterProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  inverseFrameAdapterProgram
    (inverseSelectorBodyShapeProgram contracts clockDepth machine
      advantageExponent pcp)

noncomputable def inverseSelectorBodyAdapterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  inverseSelectorFrameAdapterBits contracts clockDepth machine
    advantageExponent pcp
    (inverseSelectorBodyShapeBits contracts clockDepth machine
      advantageExponent pcp compilerBits)

noncomputable def inverseSelectorBodyAdapterFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  inverseFrameAdapterFuel
    (inverseSelectorBodyShapeProgram contracts clockDepth machine
      advantageExponent pcp)
    (inverseSelectorBodyShapeFuel contracts clockDepth machine
      advantageExponent pcp compilerFuel)

/-! ## 2. The adapter premise, discharged from presentation -/

set_option maxHeartbeats 1600000 in
-- The selector-frame functions contain the noncomputable scheduled index.
theorem inverseSelectorBodyAdapterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hcompiler :
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel) :
    InverseSelectorFrameAdapterRuns contracts clockDepth machine
      advantageExponent pcp
      (inverseSelectorBodyAdapterProgram contracts clockDepth machine
        advantageExponent pcp)
      (inverseSelectorBodyAdapterBits contracts clockDepth machine
        advantageExponent pcp compilerBits)
      (inverseSelectorBodyAdapterFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel) :=
  inverseSelectorFrameAdapterRuns_ofShape contracts clockDepth machine
    advantageExponent pcp
    (inverseSelectorBodyShapeProgram contracts clockDepth machine
      advantageExponent pcp)
    (inverseSelectorBodyShapeBits contracts clockDepth machine
      advantageExponent pcp compilerBits)
    (inverseSelectorBodyShapeFuel contracts clockDepth machine
      advantageExponent pcp compilerFuel)
    (inverseSelectorAtomShapeRuns_ofContext contracts clockDepth machine
      advantageExponent pcp
      (inverseAtomContextProgram
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent))
        (inverseSelectorBankTableProgram contracts clockDepth machine pcp))
      (inverseSelectorAtomContextBits contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorBankTableBits contracts clockDepth machine
          advantageExponent pcp
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)))
      (inverseAtomContextFuel contracts advantageExponent
        (inverseSelectorBankTableProgram contracts clockDepth machine pcp)
        (inverseSelectorBankTableFuel contracts clockDepth machine
          advantageExponent pcp
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)))
      compilerBits compilerFuel
      (inverseSelectorAtomContextRuns_ofTable contracts clockDepth machine
        advantageExponent pcp hpresentation
        (inverseSelectorBankTableProgram contracts clockDepth machine pcp)
        (inverseSelectorBankTableBits contracts clockDepth machine
          advantageExponent pcp
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent))
        (inverseSelectorBankTableFuel contracts clockDepth machine
          advantageExponent pcp
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent))
        (inverseSelectorAtomTableRuns_ofPresentation contracts clockDepth machine
          advantageExponent pcp hpresentation))
      hcompiler)

/-! ## 3. The selector-bank body closure -/

set_option maxHeartbeats 1600000 in
-- The final composition contains the full dependent canonical target output.
theorem inverse_bodyRun_ofSelectorBank
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (caseOne caseTwo : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ)
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
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
    (hchainOne : ∀ target
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
              branchTwo machine)
        (data : ScheduledCaseOneData
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedAmplifier contracts)
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target))
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target)),
        inverseTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hyes = .caseOne data →
        ∀ input : BitInput target,
          runNPOracleProgram caseOne (chainBits ⟨target, input⟩)
              (chainFuel ⟨target, input⟩)
              (initialNPOracleState target
                (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
                  ⟨target, input⟩)) =
            some
              (inverseCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                advantageExponent target hlarge hyes hrejects haccepts
                input).toNat)
    (hchainTwo : ∀ target
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
              branchTwo machine)
        (branchTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent)))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target)),
        inverseTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hyes = .caseTwo branchTwo →
        ∀ input : BitInput target,
          runNPOracleProgram caseTwo (chainBits ⟨target, input⟩)
              (chainFuel ⟨target, input⟩)
              (initialNPOracleState target
                (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
                  ⟨target, input⟩)) =
            some
              (inverseCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                advantageExponent target hlarge hyes hrejects haccepts
                input).toNat) :
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
                (inverseBankEmitterProgram
                  (inverseSelectorBodyAdapterProgram contracts clockDepth
                    machine advantageExponent pcp)))
              caseOne caseTwo)
            (bankDispatchedBodyBitsAtFrame
              (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
              (inverseBankSelectorBitsAtFrame contracts clockDepth machine
                advantageExponent
                (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
                (inverseSelectorBankEmitterBits contracts clockDepth machine
                  advantageExponent pcp (inverseSelectorBodyAdapterBits contracts clockDepth machine
      advantageExponent pcp compilerBits) rangeBits))
              chainBits ⟨target, input⟩)
            (bankDispatchedBodyFuel caseOne caseTwo
              (inverseBankSelectorFuel contracts clockDepth machine
                advantageExponent
                (inverseBankEmitterFuel contracts clockDepth machine
                  advantageExponent pcp (inverseSelectorBodyAdapterFuel contracts clockDepth machine
      advantageExponent pcp compilerFuel) compilerFuel))
              chainFuel ⟨target, input⟩)
            (initialNPOracleState target
              (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
                  ⟨target, input⟩)) =
          some
            (inverseCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target hlarge hyes hrejects haccepts
              input).toNat :=
  inverse_bodyRun_of_emitterRuns_atFrame contracts clockDepth machine
    advantageExponent
    (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
    (inverseBankEmitterProgram (inverseSelectorBodyAdapterProgram contracts clockDepth machine
      advantageExponent pcp)) caseOne caseTwo
    (inverseSelectorBankEmitterBits contracts clockDepth machine advantageExponent pcp
      (inverseSelectorBodyAdapterBits contracts clockDepth machine
      advantageExponent pcp compilerBits) rangeBits)
    (inverseBankEmitterFuel contracts clockDepth machine advantageExponent pcp
      (inverseSelectorBodyAdapterFuel contracts clockDepth machine
      advantageExponent pcp compilerFuel) compilerFuel)
    chainBits chainFuel
    (inverseSelectorEmitterRuns_ofCompiler contracts clockDepth machine
      advantageExponent pcp
      (inverseScheduleAtoms_of_presentation contracts clockDepth machine
        advantageExponent pcp hpresentation)
      (inverseSelectorBodyAdapterProgram contracts clockDepth machine
      advantageExponent pcp) (inverseSelectorBodyAdapterBits contracts clockDepth machine
      advantageExponent pcp compilerBits)
      (inverseSelectorBodyAdapterFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel) rangeBits
      compilerBits compilerFuel
      (inverseSelectorBodyAdapterRuns contracts clockDepth machine
        advantageExponent pcp hpresentation compilerBits compilerFuel hcompiler)
      hpositive hlengthBits hrangeBits
      hlistBits hcallBits hcalleeBits hcompiler)
    hchainOne hchainTwo

end NearCubicWires.SelectorDrivenBodyClosure
