import Proof.PCP.SelectorDrivenProjectionTableStage
import Proof.Circuits.FixedSelectorAtomContextRuns
import Proof.PCP.FixedProjectionTableStage

/-!
# Projection-table execution at the fixed selector frame

The native-call relocation is schedule-parametric.  This module instantiates
the already verified relocation at the fixed selector's own scheduled length.
The outer request keeps public length `target`; the callee reads
`fixedScheduleLength … target` from the selector frame.  No diagonal equality
is used.
-/

namespace NearCubicWires.FixedSelectorProjectionTableStage

open NearCubicWires
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedProjectionTableStage
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.FixedSelectorAtomContextReplay
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SelectorDrivenProjectionTableStage
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank

open private selectorBankTableCallBits selectorBankTableCallFuel
  run_selectorBankTableNativeCall
  from Proof.PCP.SelectorDrivenProjectionTableStage

/-! ## 1. Fixed instantiation of the relocated table program -/

/-- The relocated table program is schedule-free; this fixed name records its
use by the fixed selector replay. -/
noncomputable def fixedSelectorBankTableProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  inverseSelectorBankTableProgram contracts clockDepth machine pcp

theorem fixedSelectorBankTableProgram_oracleFree
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
      (fixedSelectorBankTableProgram contracts clockDepth machine pcp) :=
  inverseSelectorBankTableProgram_oracleFree contracts clockDepth machine pcp
    hrefuter

noncomputable def fixedSelectorBankTableBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (pointCode : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  selectorBankTableCallBits pcp
    (publishedRefuterSource contracts clockDepth).refuter machine
    (LanguageEvaluationRequest.length request)
    (fixedScheduleLength contracts clockDepth requestedRate
      (LanguageEvaluationRequest.length request))
    (fixedBankTableCopies contracts clockDepth requestedRate
      (LanguageEvaluationRequest.length request))
    (LanguageEvaluationRequest.code request) (pointCode request)
    (encodeBalancedList
      (projectionRunnerCallOutputs pcp
        (fixedScheduleInput contracts clockDepth machine requestedRate
          (LanguageEvaluationRequest.length request))))

noncomputable def fixedSelectorBankTableFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (_pointCode : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  selectorBankTableCallFuel pcp
    (publishedRefuterSource contracts clockDepth).refuter machine
    (inverseBankTableProgram contracts clockDepth machine pcp)
    (fixedScheduleLength contracts clockDepth requestedRate
      (LanguageEvaluationRequest.length request))
    (fixedBankTableCopies contracts clockDepth requestedRate
      (LanguageEvaluationRequest.length request))
    (LanguageEvaluationRequest.code request)

/-! ## 2. The fixed selector frame is the callee's native frame -/

theorem fixedSelectorBankFrame_eq
    (contracts : PublishedContracts) (clockDepth requestedRate target : ℕ)
    (input : BitInput target) :
    fixedSelectorAdapterFrame contracts clockDepth requestedRate
        ⟨target, input⟩ =
      scheduleNumeralBankOutput
        (fixedScheduleLength contracts clockDepth requestedRate target)
        (fixedSelectorBankWidth contracts clockDepth requestedRate target)
        (fixedSelectorBankQueryCount contracts clockDepth requestedRate target)
        (fixedBankTableCopies contracts clockDepth requestedRate target)
        (encodeBitInput input) :=
  rfl

set_option maxHeartbeats 1600000 in
-- The fixed selector frame contains a noncomputable schedule-index scan.
theorem run_fixedSelectorBankTableProgram_atFrame
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (pointCode : LanguageEvaluationRequest → ℕ)
    (target : ℕ) (input : BitInput target)
    (hframe :
      pointCode ⟨target, input⟩ =
        scheduleNumeralBankOutput
          (fixedScheduleLength contracts clockDepth requestedRate target)
          (pcp.nativeWidth
            (fixedScheduleLength contracts clockDepth requestedRate target))
          (pcp.queryCount
            (fixedScheduleLength contracts clockDepth requestedRate target))
          (fixedBankTableCopies contracts clockDepth requestedRate target)
          (encodeBitInput input)) :
    runNPOracleProgram
        (fixedSelectorBankTableProgram contracts clockDepth machine pcp)
        (fixedSelectorBankTableBits contracts clockDepth machine requestedRate
          pcp pointCode ⟨target, input⟩)
        (fixedSelectorBankTableFuel contracts clockDepth machine requestedRate
          pcp pointCode ⟨target, input⟩)
        (initialNPOracleState target (pointCode ⟨target, input⟩)) =
      some
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (fixedScheduleInput contracts clockDepth machine requestedRate
              target))) := by
  let sourceLen := fixedScheduleLength contracts clockDepth requestedRate target
  let copies := fixedBankTableCopies contracts clockDepth requestedRate target
  let code := encodeBitInput input
  have hinput :
      fixedScheduleInput contracts clockDepth machine requestedRate target =
        (publishedRefuterSource contracts clockDepth).refuter.output machine
          sourceLen := by
    rfl
  have hbits :
      fixedSelectorBankTableBits contracts clockDepth machine requestedRate pcp
          pointCode ⟨target, input⟩ =
        selectorBankTableCallBits pcp
          (publishedRefuterSource contracts clockDepth).refuter machine
          target sourceLen copies code
          (scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
            (pcp.queryCount sourceLen) copies code)
          (encodeBalancedList
            (projectionRunnerCallOutputs pcp
              ((publishedRefuterSource contracts clockDepth).refuter.output
                machine sourceLen))) := by
    rw [fixedSelectorBankTableBits, hframe]
    simp only [LanguageEvaluationRequest.length,
      LanguageEvaluationRequest.code, sourceLen, copies, code]
    rw [hinput]
  have hfuel :
      fixedSelectorBankTableFuel contracts clockDepth machine requestedRate pcp
          pointCode ⟨target, input⟩ =
        selectorBankTableCallFuel pcp
          (publishedRefuterSource contracts clockDepth).refuter machine
          (inverseBankTableProgram contracts clockDepth machine pcp)
          sourceLen copies code := by
    rfl
  rw [fixedSelectorBankTableProgram, hbits, hfuel, hframe, hinput]
  exact run_selectorBankTableNativeCall contracts clockDepth machine pcp target
    sourceLen copies code

/-! ## 3. The fixed selector table residual -/

set_option maxHeartbeats 1600000 in
-- Presentation rewrites two noncomputable indexed frame registers.
theorem fixedSelectorAtomTableRuns_ofPresentation
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp) :
    FixedSelectorAtomTableRuns contracts clockDepth machine requestedRate pcp
      (fixedSelectorBankTableProgram contracts clockDepth machine pcp)
      (fixedSelectorBankTableBits contracts clockDepth machine requestedRate pcp
        (fixedSelectorAdapterFrame contracts clockDepth requestedRate))
      (fixedSelectorBankTableFuel contracts clockDepth machine requestedRate pcp
        (fixedSelectorAdapterFrame contracts clockDepth requestedRate)) := by
  intro target _hlarge input
  let sourceLen := fixedScheduleLength contracts clockDepth requestedRate target
  let copies := fixedBankTableCopies contracts clockDepth requestedRate target
  let code := encodeBitInput input
  have hwidth :
      fixedSelectorBankWidth contracts clockDepth requestedRate target =
        pcp.nativeWidth sourceLen := by
    rw [fixedSelectorBankWidth]
    exact (presentsPaddedOuterPCP_scheduledWidth hpresentation _).symm
  have hquery :
      fixedSelectorBankQueryCount contracts clockDepth requestedRate target =
        pcp.queryCount sourceLen := by
    rw [fixedSelectorBankQueryCount]
    exact (congrFun (presentsPaddedOuterPCP_queryCount hpresentation) _).symm
  have hframe :
      fixedSelectorAdapterFrame contracts clockDepth requestedRate
          ⟨target, input⟩ =
        scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
          (pcp.queryCount sourceLen) copies code := by
    calc
      fixedSelectorAdapterFrame contracts clockDepth requestedRate
          ⟨target, input⟩ =
          scheduleNumeralBankOutput sourceLen
            (fixedSelectorBankWidth contracts clockDepth requestedRate target)
            (fixedSelectorBankQueryCount contracts clockDepth requestedRate
              target)
            copies code :=
        fixedSelectorBankFrame_eq contracts clockDepth requestedRate target input
      _ = scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
            (pcp.queryCount sourceLen) copies code := by
        rw [hwidth, hquery]
  exact run_fixedSelectorBankTableProgram_atFrame contracts clockDepth machine
    requestedRate pcp
    (fixedSelectorAdapterFrame contracts clockDepth requestedRate)
    target input hframe

end NearCubicWires.FixedSelectorProjectionTableStage
