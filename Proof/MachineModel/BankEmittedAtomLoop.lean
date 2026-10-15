import Proof.MachineModel.BankEmittedBranchSelector
import Proof.MachineModel.StructuralAtomCalleeProgram

namespace NearCubicWires.BankEmittedAtomLoop

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The schedule's PCP request -/

/-- The scheduled source length at one target. -/
noncomputable def inverseScheduleLength
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  sourceLength
    (inverseSourceIndex
      (inverseSelectedSource contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseCoreAdvantagePower advantageExponent) target))

/-- The scheduled PCP input at one target. -/
noncomputable def inverseScheduleInput
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target : ℕ) :
    BitInput (inverseScheduleLength contracts clockDepth advantageExponent
      target) :=
  inverseRefuterInput contracts (publishedHierarchyOuterPCP contracts clockDepth)
    machine advantageExponent target

/-- The scheduled bounded-oracle size bound at one target. -/
noncomputable def inverseScheduleBound
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  oracleSizeBound
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
      (inverseSourceIndex
        (inverseSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseCoreAdvantagePower advantageExponent) target)))

theorem inverseSelectorAtoms_eq
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target : ℕ) :
    inverseSelectorAtoms contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target =
      boundedOracleStructuralFormulaAtoms
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          target)
        (inverseScheduleBound contracts clockDepth advantageExponent target) :=
  rfl

/-! ## 2. The loop's generated range at the schedule -/

/-- The number of global formula indices at one target. -/
noncomputable def inverseAtomCount
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) : ℕ :=
  structuralAtomCount pcp
    (inverseScheduleInput contracts clockDepth machine advantageExponent target)
    (inverseScheduleBound contracts clockDepth advantageExponent target)

/-- The shared public context of every generated request at one target. -/
noncomputable def inverseAtomContext
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) : ℕ :=
  structuralAtomContext pcp
    (inverseScheduleInput contracts clockDepth machine advantageExponent target)
    (inverseScheduleBound contracts clockDepth advantageExponent target)

/-! ## 3. The two named hypotheses -/

/-- **The presentation premise.**  The executable projection PCP presents the
schedule's atom stream: at every target its canonical structural atoms are the
inverse schedule's own.  A full `toSemantic` equality gives this immediately
(`inverseScheduleAtoms_of_semantic`); it is stated at the atom level because an
executable presentation must declare its own polynomial shape budget, which the
semantic padding does not fix. -/
def InverseScheduleAtomsAgree
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : Prop :=
  ∀ target : ℕ,
    boundedOracleStructuralFormulaAtoms pcp.toSemantic
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          target)
        (inverseScheduleBound contracts clockDepth advantageExponent target) =
      inverseSelectorAtoms contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target

/-- An executable presentation of the padded outer PCP presents its atoms. -/
theorem inverseScheduleAtoms_of_semantic
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hsemantic :
      pcp.toSemantic =
        paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth)) :
    InverseScheduleAtomsAgree contracts clockDepth machine advantageExponent
      pcp := by
  intro target
  rw [hsemantic, inverseSelectorAtoms_eq]

/-- **The frame-lowering premise.**  One stage takes the bank's frame to the
atom loop's input frame and retains the bank's frame as the point code.  The
target binder is restricted to the Case-1 onset: `bodyRun` is only ever asked
about onset-large targets, so nothing downstream of this premise — the schedule
diagonal in particular — has to be supplied below the onset. -/
def InverseFrameAdapterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapter : NPOracleProgram)
    (adapterBits adapterFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (input : BitInput target),
    runNPOracleProgram adapter (adapterBits ⟨target, input⟩)
        (adapterFuel ⟨target, input⟩)
        (initialNPOracleState target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target
            (encodeBitInput input))) =
      some
        (Nat.pair
          (generatedBalancedRangeInput
            (inverseAtomCount contracts clockDepth machine advantageExponent pcp
              target)
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target))
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target
            (encodeBitInput input)))

def InverseCompilerRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits compilerFuel : ℕ → ℕ → ℕ) : Prop :=
  ∀ (target index : ℕ),
    index <
      inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target →
    StructuralCompilerRunsAt pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target)
      target (inverseScheduleBound contracts clockDepth advantageExponent target)
      index (compilerBits target index) (compilerFuel target index)

/-! ## 4. The emitter and its resource envelopes -/

/-- **The bank-framed emitter.**  One fixed stream: the frame-lowering stage,
then the generated atom loop over the pointwise structural callee. -/
def inverseBankEmitterProgram (adapter : NPOracleProgram) : NPOracleProgram :=
  linkPrograms adapter
    (structuralAtomEmitterProgram structuralAtomCalleeProgram)

noncomputable def inverseBankEmitterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapterBits : LanguageEvaluationRequest → ℕ) (rangeBits : ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (adapterBits request)
    (structuralAtomEmitterBits
      (rangeBits (LanguageEvaluationRequest.length request))
      (LanguageEvaluationRequest.length request)
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        (LanguageEvaluationRequest.length request))
      (inverseAtomContext contracts clockDepth machine advantageExponent pcp
        (LanguageEvaluationRequest.length request))
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (LanguageEvaluationRequest.length request)
        (LanguageEvaluationRequest.code request))
      (inverseSelectorAtoms contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent (LanguageEvaluationRequest.length request)))

noncomputable def inverseBankEmitterFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapterFuel : LanguageEvaluationRequest → ℕ) (compilerFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel (structuralAtomEmitterProgram structuralAtomCalleeProgram)
    (adapterFuel request)
    (structuralAtomEmitterFuel structuralAtomCalleeProgram
      (LanguageEvaluationRequest.length request)
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        (LanguageEvaluationRequest.length request))
      (inverseAtomContext contracts clockDepth machine advantageExponent pcp
        (LanguageEvaluationRequest.length request))
      (structuralAtomCalleeRequestFuel
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            (LanguageEvaluationRequest.length request)))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request)))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request)))
        (inverseScheduleBound contracts clockDepth advantageExponent
          (LanguageEvaluationRequest.length request))
        (compilerFuel (LanguageEvaluationRequest.length request)))
      (inverseSelectorAtoms contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent (LanguageEvaluationRequest.length request)))

/-! ## 5. The emitter premise, discharged -/

/-- **The selector's emitter premise, from the compiler's run.**  Given an
executable presentation of the padded outer PCP and the frame-lowering stage,
the bank-framed emitter returns the tagged inverse-schedule atom stream beside
the bank's frame — modulo the nested compiler's own run, once per global
formula index. -/
theorem inverseEmitterRuns_ofCompiler
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hatoms :
      InverseScheduleAtomsAgree contracts clockDepth machine advantageExponent
        pcp)
    (adapter : NPOracleProgram)
    (adapterBits adapterFuel : LanguageEvaluationRequest → ℕ)
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hadapter :
      InverseFrameAdapterRuns contracts clockDepth machine advantageExponent pcp
        adapter adapterBits adapterFuel)
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
        compilerBits compilerFuel) :
    InverseEmitterRuns contracts clockDepth machine advantageExponent
      (inverseBankEmitterProgram adapter)
      (inverseBankEmitterBits contracts clockDepth machine advantageExponent pcp
        adapterBits rangeBits)
      (inverseBankEmitterFuel contracts clockDepth machine advantageExponent pcp
        adapterFuel compilerFuel) := by
  intro target hlarge input
  have hloop :=
    run_structuralAtomEmitterProgram_ofCompiler pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target)
      target
      (inverseScheduleBound contracts clockDepth advantageExponent target)
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target
        (encodeBitInput input))
      (compilerBits target) (compilerFuel target) (hpositive target)
      (hlengthBits target) (hrangeBits target) (hlistBits target)
      (hcallBits target) (hcalleeBits target) (hcompiler target)
  rw [hatoms target] at hloop
  exact run_occurrenceStage (hadapter target hlarge input) hloop

/-! ## 6. `bodyRun` from the compiler's run -/

/-- **The inverse schedule's `bodyRun`, from the compiler's run.**  Composing
§5 with `BankEmittedBranchSelector.inverse_bodyRun_of_emitterRuns`: the premise
`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` consumes is discharged
for one fixed dispatched stream from the two chain premises, the frame-lowering
stage, an executable presentation of the padded outer PCP, and the nested
structural compiler's own run.  No recovery-code immediate, no branch-query
immediate, and no list-valued emitter premise remains. -/
theorem inverse_bodyRun_ofCompiler
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hsemantic :
      pcp.toSemantic =
        paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (adapter caseOne caseTwo : NPOracleProgram)
    (adapterBits adapterFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hadapter :
      InverseFrameAdapterRuns contracts clockDepth machine advantageExponent pcp
        adapter adapterBits adapterFuel)
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
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (inverseBankRate contracts advantageExponent) target
                  (encodeBitInput input))) =
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
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (inverseBankRate contracts advantageExponent) target
                  (encodeBitInput input))) =
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
                (inverseBankEmitterProgram adapter))
              caseOne caseTwo)
            (bankDispatchedBodyBits contracts clockDepth advantageExponent
              (inverseBankSelectorBits contracts clockDepth machine
                advantageExponent
                (inverseBankEmitterBits contracts clockDepth machine
                  advantageExponent pcp adapterBits rangeBits))
              chainBits ⟨target, input⟩)
            (bankDispatchedBodyFuel caseOne caseTwo
              (inverseBankSelectorFuel contracts clockDepth machine
                advantageExponent
                (inverseBankEmitterFuel contracts clockDepth machine
                  advantageExponent pcp adapterFuel compilerFuel))
              chainFuel ⟨target, input⟩)
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
  inverse_bodyRun_of_emitterRuns contracts clockDepth machine advantageExponent
    (inverseBankEmitterProgram adapter) caseOne caseTwo
    (inverseBankEmitterBits contracts clockDepth machine advantageExponent pcp
      adapterBits rangeBits)
    (inverseBankEmitterFuel contracts clockDepth machine advantageExponent pcp
      adapterFuel compilerFuel)
    chainBits chainFuel
    (inverseEmitterRuns_ofCompiler contracts clockDepth machine
      advantageExponent pcp
      (inverseScheduleAtoms_of_semantic contracts clockDepth machine
        advantageExponent pcp hsemantic)
      adapter adapterBits adapterFuel rangeBits
      compilerBits compilerFuel hadapter hpositive hlengthBits hrangeBits
      hlistBits hcallBits hcalleeBits hcompiler)
    hchainOne hchainTwo

end NearCubicWires.BankEmittedAtomLoop
