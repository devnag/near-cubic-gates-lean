import Proof.MachineModel.BankProjectionTableStage
import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.Circuits.SelectorDrivenAtomContextRuns

/-!
# Projection table execution at the selector-driven frame

The selector frame contains the scheduled PCP input length, but the outer
request still has public length `target`.  The frozen table stage therefore
cannot be reused directly: its runner invocation requires those lengths to be
equal.  This adapter reads the scheduled length from the frame and invokes the
entire frozen table stage through the native-call ABI at that length.  No
schedule diagonal is required.
-/

namespace NearCubicWires.SelectorDrivenProjectionTableStage

open NearCubicWires
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Turn the selector frame into one native request -/

/-- From `scheduleNumeralBankOutput sourceLen ...`, retain the whole frame and
place its first register in front as the native callee input length. -/
private def selectorTableNativeRequestProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .pair 2 0 0 2
  , .halt 0
  ]

@[simp] private theorem selectorTableNativeRequestProgram_oracleFree :
    OracleFree selectorTableNativeRequestProgram := by
  rfl

private def selectorTableNativeRequestBits (sourceLen frame : ℕ) : ℕ :=
  natBitLength (nativeInputRequest sourceLen frame)

private theorem run_selectorTableNativeRequestProgram
    (inputLength sourceLen width queryCount copies code : ℕ) :
    runNPOracleProgram selectorTableNativeRequestProgram
        (selectorTableNativeRequestBits sourceLen
          (scheduleNumeralBankOutput sourceLen width queryCount copies code))
        3
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies code)) =
      some
        (nativeInputRequest sourceLen
          (scheduleNumeralBankOutput sourceLen width queryCount copies code)) := by
  let frame := scheduleNumeralBankOutput sourceLen width queryCount copies code
  have houtput :
      natBitLength (nativeInputRequest sourceLen frame) ≤
        selectorTableNativeRequestBits sourceLen frame :=
    le_refl _
  have hframe :
      natBitLength frame ≤ selectorTableNativeRequestBits sourceLen frame :=
    (natBitLength_mono (Nat.right_le_pair sourceLen frame)).trans houtput
  have hsource :
      natBitLength sourceLen ≤ selectorTableNativeRequestBits sourceLen frame :=
    (natBitLength_mono (Nat.left_le_pair sourceLen frame)).trans houtput
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sourceLen) (by rfl) rfl
    (by simp [initialNPOracleState, scheduleNumeralBankOutput]) hsource]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := nativeInputRequest sourceLen frame)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      nativeInputRequest, frame]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frame]) houtput

/-! ## 2. The relocated table stage -/

/-- A three-instruction request adapter followed by one native call of the
already verified bank table stage. -/
noncomputable def inverseSelectorBankTableProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  linkPrograms selectorTableNativeRequestProgram
    (nativeCallProgram
      (inverseBankTableProgram contracts clockDepth machine pcp))

theorem inverseSelectorBankTableProgram_oracleFree
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hrefuter :
      OracleFree
        (publishedRefuterSource contracts clockDepth).refuter.runner.program) :
    OracleFree
      (inverseSelectorBankTableProgram contracts clockDepth machine pcp) :=
  oracleFree_linkPrograms selectorTableNativeRequestProgram_oracleFree
    (nativeCallProgram_oracleFree
      (inverseBankTableProgram_oracleFree contracts clockDepth machine pcp
        hrefuter))

private def selectorBankTableCallBits
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound)
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (inputLength sourceLen copies code pointCode output : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (selectorTableNativeRequestBits sourceLen pointCode)
    (nativeCallBits inputLength sourceLen pointCode output
      (bankProjectionTableBits pcp refuter machine sourceLen sourceLen copies
        code))

private def selectorBankTableCallFuel
    {sourceMachine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP sourceMachine timeBound)
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (callee : NPOracleProgram) (sourceLen copies code : ℕ) : ℕ :=
  linkFuel (nativeCallProgram callee) 3
    (nativeCallFuel callee
      (bankProjectionTableFuel pcp refuter machine sourceLen)
      sourceLen
      (scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
        (pcp.queryCount sourceLen) copies code))

noncomputable def inverseSelectorBankTableBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (pointCode : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  selectorBankTableCallBits pcp
    (publishedRefuterSource contracts clockDepth).refuter machine
    (LanguageEvaluationRequest.length request)
    (inverseScheduleLength contracts clockDepth advantageExponent
      (LanguageEvaluationRequest.length request))
    (inverseBankTableCopies contracts clockDepth advantageExponent
      (LanguageEvaluationRequest.length request))
    (LanguageEvaluationRequest.code request) (pointCode request)
    (encodeBalancedList
      (projectionRunnerCallOutputs pcp
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          (LanguageEvaluationRequest.length request))))

noncomputable def inverseSelectorBankTableFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (_pointCode : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  selectorBankTableCallFuel pcp
    (publishedRefuterSource contracts clockDepth).refuter machine
    (inverseBankTableProgram contracts clockDepth machine pcp)
    (inverseScheduleLength contracts clockDepth advantageExponent
      (LanguageEvaluationRequest.length request))
    (inverseBankTableCopies contracts clockDepth advantageExponent
      (LanguageEvaluationRequest.length request))
    (LanguageEvaluationRequest.code request)

/-! ## 3. Site 3: the table residual, with no diagonal -/

private theorem run_selectorBankTableNativeCall
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (inputLength sourceLen copies code : ℕ) :
    runNPOracleProgram
        (inverseSelectorBankTableProgram contracts clockDepth machine pcp)
        (selectorBankTableCallBits pcp
          (publishedRefuterSource contracts clockDepth).refuter machine
          inputLength sourceLen copies code
          (scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
            (pcp.queryCount sourceLen) copies code)
          (encodeBalancedList
            (projectionRunnerCallOutputs pcp
              ((publishedRefuterSource contracts clockDepth).refuter.output
                machine sourceLen))))
        (selectorBankTableCallFuel pcp
          (publishedRefuterSource contracts clockDepth).refuter machine
          (inverseBankTableProgram contracts clockDepth machine pcp)
          sourceLen copies code)
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
            (pcp.queryCount sourceLen) copies code)) =
      some
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            ((publishedRefuterSource contracts clockDepth).refuter.output
              machine sourceLen))) := by
  have hcallee :=
    run_bankProjectionTableProgram pcp
      (publishedRefuterSource contracts clockDepth).refuter machine
      sourceLen sourceLen copies code rfl
  have hnative :=
    run_nativeCallProgram
      (inverseBankTableProgram contracts clockDepth machine pcp)
      inputLength sourceLen
      (scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
        (pcp.queryCount sourceLen) copies code)
      (encodeBalancedList
        (projectionRunnerCallOutputs pcp
          ((publishedRefuterSource contracts clockDepth).refuter.output machine
            sourceLen)))
      (bankProjectionTableBits pcp
        (publishedRefuterSource contracts clockDepth).refuter machine
        sourceLen sourceLen copies code)
      (bankProjectionTableFuel pcp
        (publishedRefuterSource contracts clockDepth).refuter machine sourceLen)
      hcallee
  simpa only [inverseSelectorBankTableProgram, selectorBankTableCallBits,
    selectorBankTableCallFuel] using
      (run_occurrenceStage
        (run_selectorTableNativeRequestProgram inputLength sourceLen
          (pcp.nativeWidth sourceLen) (pcp.queryCount sourceLen) copies code)
        hnative)

set_option maxHeartbeats 1600000 in
-- The frozen table stage has a large dependent output type at the native call.
theorem run_inverseSelectorBankTableProgram_atFrame
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (pointCode : LanguageEvaluationRequest → ℕ)
    (target : ℕ) (input : BitInput target)
    (hframe :
      pointCode ⟨target, input⟩ =
        scheduleNumeralBankOutput
          (inverseScheduleLength contracts clockDepth advantageExponent target)
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (pcp.queryCount
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (inverseBankTableCopies contracts clockDepth advantageExponent target)
          (encodeBitInput input)) :
    runNPOracleProgram
        (inverseSelectorBankTableProgram contracts clockDepth machine pcp)
        (inverseSelectorBankTableBits contracts clockDepth machine
          advantageExponent pcp pointCode ⟨target, input⟩)
        (inverseSelectorBankTableFuel contracts clockDepth machine
          advantageExponent pcp pointCode ⟨target, input⟩)
        (initialNPOracleState target (pointCode ⟨target, input⟩)) =
      some
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine
              advantageExponent target))) := by
  let sourceLen :=
    inverseScheduleLength contracts clockDepth advantageExponent target
  let copies :=
    inverseBankTableCopies contracts clockDepth advantageExponent target
  let code := encodeBitInput input
  have hinput :
      inverseScheduleInput contracts clockDepth machine advantageExponent
          target =
        (publishedRefuterSource contracts clockDepth).refuter.output machine
          sourceLen := by
    rfl
  have hbits :
      inverseSelectorBankTableBits contracts clockDepth machine
          advantageExponent pcp pointCode ⟨target, input⟩ =
        selectorBankTableCallBits pcp
          (publishedRefuterSource contracts clockDepth).refuter machine
          target sourceLen copies code
          (scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
            (pcp.queryCount sourceLen) copies code)
          (encodeBalancedList
            (projectionRunnerCallOutputs pcp
              ((publishedRefuterSource contracts clockDepth).refuter.output
                machine sourceLen))) := by
    rw [inverseSelectorBankTableBits, hframe]
    simp only [LanguageEvaluationRequest.length, LanguageEvaluationRequest.code,
      sourceLen, copies, code]
    rw [hinput]
  have hfuel :
      inverseSelectorBankTableFuel contracts clockDepth machine
          advantageExponent pcp pointCode ⟨target, input⟩ =
        selectorBankTableCallFuel pcp
          (publishedRefuterSource contracts clockDepth).refuter machine
          (inverseBankTableProgram contracts clockDepth machine pcp)
          sourceLen copies code := by
    rfl
  rw [hbits, hfuel, hframe, hinput]
  exact run_selectorBankTableNativeCall contracts clockDepth machine pcp target
    sourceLen copies code

set_option maxHeartbeats 1600000 in
-- The concrete selector frame contains a noncomputable schedule-index scan.
/-- The selector bank's scheduled-length register relocates the frozen table
stage to its native public length.  Presentation identifies the selector
bank's width and query-count registers with the executable PCP's registers. -/
theorem inverseSelectorAtomTableRuns_ofPresentation
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp) :
    InverseSelectorAtomTableRuns contracts clockDepth machine advantageExponent
      pcp (inverseSelectorBankTableProgram contracts clockDepth machine pcp)
      (inverseSelectorBankTableBits contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent))
      (inverseSelectorBankTableFuel contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)) := by
  intro target _hlarge input
  let sourceLen :=
    inverseScheduleLength contracts clockDepth advantageExponent target
  let copies :=
    inverseBankTableCopies contracts clockDepth advantageExponent target
  let code := encodeBitInput input
  have hwidth :
      inverseSelectorBankWidth contracts clockDepth advantageExponent target =
        pcp.nativeWidth sourceLen := by
    rw [inverseSelectorBankWidth]
    exact (presentsPaddedOuterPCP_scheduledWidth hpresentation _).symm
  have hquery :
      inverseSelectorBankQueryCount contracts clockDepth advantageExponent
          target =
        pcp.queryCount sourceLen := by
    rw [inverseSelectorBankQueryCount]
    exact (congrFun (presentsPaddedOuterPCP_queryCount hpresentation) _).symm
  have hframe :
      inverseSelectorAdapterFrame contracts clockDepth advantageExponent
          ⟨target, input⟩ =
        scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
          (pcp.queryCount sourceLen) copies code := by
    calc
      inverseSelectorAdapterFrame contracts clockDepth advantageExponent
          ⟨target, input⟩ =
          selectorDrivenBankFrame
            (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              target)
            code := rfl
      _ = scheduleNumeralBankOutput sourceLen
            (inverseSelectorBankWidth contracts clockDepth advantageExponent
              target)
            (inverseSelectorBankQueryCount contracts clockDepth
              advantageExponent target)
            (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (inverseBankRate contracts advantageExponent)
              (inverseChainSourceIndex contracts clockDepth advantageExponent
                target))
            code :=
        selectorDrivenBankFrame_eq contracts clockDepth advantageExponent
          target code
      _ = scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
            (pcp.queryCount sourceLen) copies code := by
        rw [hwidth, hquery]
        rfl
  exact run_inverseSelectorBankTableProgram_atFrame contracts clockDepth machine
    advantageExponent pcp
    (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
    target input hframe

end NearCubicWires.SelectorDrivenProjectionTableStage
