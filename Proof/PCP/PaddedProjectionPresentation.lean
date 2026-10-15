import Proof.MachineModel.BankEmittedAtomLoop

/-!
# An executable presentation of the padded outer PCP

`BankEmittedAtomLoop.inverse_bodyRun_ofCompiler` consumes the presentation
premise as a full semantic equality

`pcp.toSemantic = paddedOuterPCP outer`,

and that equality is **not available to any executable presentation**:
`ExecutableProjectionPCP.toSemantic` declares `constructionSteps` to be the
presentation's *own* shape budget, while `paddedOuterPCP outer` inherits the
source PCP's, and the padded shape program — which must also evaluate
`Nat.log 2 (widthBudget outer …)` — cannot halt inside the source budget.  The
two cost declarations therefore differ, and no executable presentation can
satisfy the equality on the nose.

`BankEmittedAtomLoop` already anticipates this and weakens the consumer's
hypothesis to `InverseScheduleAtomsAgree`, an equality of *atom streams*.  What
was missing is the bridge: the atom stream is a function of the four semantic
fields alone, so a budget-mismatched presentation suffices.  §1 proves exactly
that.

The obstruction to proving it by `rfl` is real: `compileCountCases` and
`compileVerifierRows` recurse over `List.ofFn id` and `allRandomness`, both of
which are stuck at a symbolic width, so the definitional unfolder compares the
two projection PCPs *as arguments* of a blocked recursor and fails.  §1
therefore performs the two list inductions explicitly.  The dependent step of
each induction is packaged as one named combinator (`andStepAt`, `orStepAt`) so
that the inductive hypothesis can be applied with `congrArg`: a bare `rw` fails
with `motive is not type correct`, because the compiler's anonymous
`CompiledWire` literal is indexed by the very predicate being rewritten.

§2 records the extensionality of `ProjectionPCP` and §3 states the residual
premise

`PresentsPaddedOuterPCP outer pcp : pcp.toSemantic =
  withConstructionSteps (paddedOuterPCP outer) pcp.shape.budget`,

which — unlike the equality it replaces — is *not* refuted by the cost
mismatch, and discharges `InverseScheduleAtomsAgree` from it.  §4 restates
`inverse_bodyRun_ofCompiler` against the new premise.
-/

namespace NearCubicWires.PaddedProjectionPresentation

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
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
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The atom stream does not read the declared construction cost -/

/-- One projection PCP with its declared construction cost replaced.  Every
other field — and therefore every semantic obligation of the verifier — is
untouched. -/
@[reducible] def withConstructionSteps
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (steps : ℕ → ℕ) :
    ProjectionPCP machine timeBound :=
  { pcp with constructionSteps := steps }

/-- The conjunction step of the structural compiler, named so that a tail
equality can be transported through it by `congrArg`. -/
private def andStepAt {width : ℕ} {builder : BooleanDAGBuilder width}
    {head : BoolFunction width} (first : CompiledWire builder head)
    {tail : BoolFunction width} (second : CompiledWire first.final tail) :
    CompiledWire builder (fun description =>
      head description && tail description) :=
  CompiledWire.prepend (first.extension.trans second.extension)
    (compileAnd second.final (first.live.lift second.extension) second.live)

/-- The disjunction step of the structural compiler, named for the same
reason. -/
private def orStepAt {width : ℕ} {builder : BooleanDAGBuilder width}
    {head : BoolFunction width} (first : CompiledWire builder head)
    {tail : BoolFunction width} (second : CompiledWire first.final tail) :
    CompiledWire builder (fun description =>
      head description || tail description) :=
  CompiledWire.prepend (first.extension.trans second.extension)
    (compileOr second.final (first.live.lift second.extension) second.live)

private theorem compileVerifierRows_withConstructionSteps
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (steps : ℕ → ℕ) {n bound : ℕ}
    (input : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    ∀ (rows : List (BitInput (pcp.nativeWidth n)))
      (builder :
        BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound)),
      compileVerifierRows (withConstructionSteps pcp steps) input count hcount
          builder rows =
        compileVerifierRows pcp input count hcount builder rows := by
  intro rows
  induction rows with
  | nil => intro builder; rfl
  | cons randomness rest ih =>
      intro builder
      exact congrArg
        (andStepAt
          (compileVerifierRow pcp input builder count hcount randomness).compiled)
        (ih _)

private theorem compileFixedCount_withConstructionSteps
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (steps : ℕ → ℕ) {n bound : ℕ}
    (input : BitInput n)
    (builder : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count : Fin bound) :
    compileFixedCount (withConstructionSteps pcp steps) input builder count =
      compileFixedCount pcp input builder count :=
  congrArg
    (andStepAt
      (compileExpr builder
        (fixedCountGrammarExpr (n := pcp.nativeWidth n) count)))
    (compileVerifierRows_withConstructionSteps pcp steps input (count.val + 1)
      (by omega) _ _)

private theorem compileCountCases_withConstructionSteps
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (steps : ℕ → ℕ) {n bound : ℕ}
    (input : BitInput n) :
    ∀ (counts : List (Fin bound))
      (builder :
        BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound)),
      compileCountCases (withConstructionSteps pcp steps) input builder counts =
        compileCountCases pcp input builder counts := by
  intro counts
  induction counts with
  | nil => intro builder; rfl
  | cons count rest ih =>
      intro builder
      exact
        (congrArg
            (orStepAt
              (compileFixedCount (withConstructionSteps pcp steps) input builder
                count))
            (ih
              (compileFixedCount (withConstructionSteps pcp steps) input builder
                count).final)).trans
          (congrArg
            (fun first =>
              orStepAt first
                (compileCountCases pcp input (CompiledWire.final first) rest))
            (compileFixedCount_withConstructionSteps pcp steps input builder
              count))

/-- The canonical bounded-oracle verifier circuit does not read the declared
construction cost. -/
theorem boundedOracleVerifierCircuit_withConstructionSteps
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (steps : ℕ → ℕ) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    boundedOracleVerifierCircuit (withConstructionSteps pcp steps) input bound =
      boundedOracleVerifierCircuit pcp input bound :=
  congrArg
    (fun compiled =>
      BooleanDAGBuilder.finish (CompiledWire.final compiled)
        (CompiledWire.output compiled))
    (compileCountCases_withConstructionSteps pcp steps input (List.ofFn id)
      (BooleanDAGBuilder.empty (descriptionWidth (pcp.nativeWidth n) bound)))

/-- **The presentation bridge.**  The canonical structural atom stream is a
function of the four semantic fields alone: replacing the declared construction
cost leaves it unchanged.  This is the statement that lets a budget-mismatched
executable presentation discharge `InverseScheduleAtomsAgree`. -/
theorem boundedOracleStructuralFormulaAtoms_withConstructionSteps
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (steps : ℕ → ℕ) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    boundedOracleStructuralFormulaAtoms (withConstructionSteps pcp steps) input
        bound =
      boundedOracleStructuralFormulaAtoms pcp input bound := by
  rw [boundedOracleStructuralFormulaAtoms_eq,
    boundedOracleStructuralFormulaAtoms_eq,
    boundedOracleVerifierCircuit_withConstructionSteps]

/-! ## 2. Extensionality of the semantic projection PCP -/

/-- Two projection PCPs agreeing in all five fields are equal.  The two
dependent fields are compared with `HEq`, which is the only way to state their
agreement before the two width fields have been identified. -/
theorem projectionPCP_ext
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (left right : ProjectionPCP machine timeBound)
    (hwidth : left.nativeWidth = right.nativeWidth)
    (hcount : left.queryCount = right.queryCount)
    (hquery :
      HEq (@ProjectionPCP.queryAddressBits machine timeBound left)
        (@ProjectionPCP.queryAddressBits machine timeBound right))
    (hdecision :
      HEq (@ProjectionPCP.decision machine timeBound left)
        (@ProjectionPCP.decision machine timeBound right))
    (hsteps : left.constructionSteps = right.constructionSteps) :
    left = right := by
  obtain ⟨leftWidth, leftCount, leftQuery, leftDecision, leftSteps⟩ := left
  obtain ⟨rightWidth, rightCount, rightQuery, rightDecision, rightSteps⟩ :=
    right
  have hwidthField : leftWidth = rightWidth := hwidth
  have hcountField : leftCount = rightCount := hcount
  have hstepsField : leftSteps = rightSteps := hsteps
  subst hwidthField
  subst hcountField
  subst hstepsField
  dsimp only at hquery hdecision
  obtain rfl := eq_of_heq hquery
  obtain rfl := eq_of_heq hdecision
  rfl

/-! ## 3. The residual premise and the atom agreement -/

/-- **The executable presentation premise.**  An executable projection PCP
presents the padded outer PCP when its semantics agree with `paddedOuterPCP`
in every field *except* the declared construction cost, which an executable
presentation is obliged to declare as its own shape budget.

This is the honest weakening of `pcp.toSemantic = paddedOuterPCP outer`: that
equality is refuted by the cost declarations, this one is not. -/
def PresentsPaddedOuterPCP
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcp :
      ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth)) :
    Prop :=
  pcp.toSemantic = withConstructionSteps (paddedOuterPCP outer) pcp.shape.budget

/-- The presentation premise is exactly the four field agreements. -/
theorem presentsPaddedOuterPCP_of_fields
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcp :
      ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth))
    (hwidth : pcp.toSemantic.nativeWidth = (paddedOuterPCP outer).nativeWidth)
    (hcount : pcp.toSemantic.queryCount = (paddedOuterPCP outer).queryCount)
    (hquery :
      HEq
        (@ProjectionPCP.queryAddressBits source.hierarchyMachine
          (pairClock clockDepth) pcp.toSemantic)
        (@ProjectionPCP.queryAddressBits source.hierarchyMachine
          (pairClock clockDepth) (paddedOuterPCP outer)))
    (hdecision :
      HEq
        (@ProjectionPCP.decision source.hierarchyMachine (pairClock clockDepth)
          pcp.toSemantic)
        (@ProjectionPCP.decision source.hierarchyMachine (pairClock clockDepth)
          (paddedOuterPCP outer))) :
    PresentsPaddedOuterPCP outer pcp :=
  projectionPCP_ext pcp.toSemantic
    (withConstructionSteps (paddedOuterPCP outer) pcp.shape.budget)
    hwidth hcount hquery hdecision rfl

/-- The presented PCP's width function is the schedule's width envelope.  This
is the identification a register-driven frame-lowering stage needs in order to
read the bank's width register as the presented PCP's own numeral. -/
theorem presentsPaddedOuterPCP_nativeWidth
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {pcp :
      ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth)}
    (hpresentation : PresentsPaddedOuterPCP outer pcp) :
    pcp.nativeWidth = widthEnvelope outer :=
  congrArg ProjectionPCP.nativeWidth hpresentation

/-- The presented PCP's query count is the published outer PCP's own. -/
theorem presentsPaddedOuterPCP_queryCount
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {pcp :
      ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth)}
    (hpresentation : PresentsPaddedOuterPCP outer pcp) :
    pcp.queryCount = outer.pcp.queryCount :=
  congrArg ProjectionPCP.queryCount hpresentation

/-- At a scheduled source length the presented PCP's width is the numeral the
numeral bank emits in its width register. -/
theorem presentsPaddedOuterPCP_scheduledWidth
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {pcp :
      ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth)}
    (hpresentation : PresentsPaddedOuterPCP outer pcp) (sourceIndex : ℕ) :
    pcp.nativeWidth (sourceLength sourceIndex) =
      scheduledWidth outer sourceIndex :=
  congrFun (presentsPaddedOuterPCP_nativeWidth hpresentation)
    (sourceLength sourceIndex)

/-- **The presentation premise discharges the atom agreement.**  This is the
statement `BankEmittedAtomLoop.inverseScheduleAtoms_of_semantic` produces from
an equality that no executable presentation can supply. -/
theorem inverseScheduleAtoms_of_presentation
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp) :
    InverseScheduleAtomsAgree contracts clockDepth machine advantageExponent
      pcp := by
  intro target
  rw [hpresentation, boundedOracleStructuralFormulaAtoms_withConstructionSteps,
    inverseSelectorAtoms_eq]

/-! ## 4. `bodyRun` from the executable presentation -/

/-- **The inverse schedule's `bodyRun`, from an executable presentation.**
`BankEmittedAtomLoop.inverse_bodyRun_ofCompiler` with its unprovable semantic
equality replaced by the presentation premise of §3.  Everything else is
unchanged. -/
theorem inverse_bodyRun_ofPresentation
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
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
      (inverseScheduleAtoms_of_presentation contracts clockDepth machine
        advantageExponent pcp hpresentation)
      adapter adapterBits adapterFuel rangeBits
      compilerBits compilerFuel hadapter hpositive hlengthBits hrangeBits
      hlistBits hcallBits hcalleeBits hcompiler)
    hchainOne hchainTwo

end NearCubicWires.PaddedProjectionPresentation
