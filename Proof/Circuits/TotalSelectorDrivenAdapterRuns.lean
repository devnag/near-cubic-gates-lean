import Proof.PCP.SelectorDrivenProjectionTableStage
import Proof.Circuits.TotalSelectorDrivenAdapterContracts
import Proof.Circuits.TotalSelectorBodyAdapter

/-!
# All-request selector adapter contracts

These are totality counterparts of the onset-indexed selector propositions.
They expose the same programs, resources, and outputs but quantify over every
language request, including target zero and malformed raw codes.
-/

namespace NearCubicWires.TotalSelectorDrivenAdapterRuns

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenProjectionTableStage
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.TotalSelectorBodyAdapter
open NearCubicWires.TotalSelectorDrivenAdapterContracts
open NearCubicWires.UniformTargetLanguageBank

set_option maxHeartbeats 1600000 in
-- The selector frame contains a noncomputable schedule-index scan.
theorem totalInverseSelectorAtomTableRuns_ofPresentation
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp) :
    TotalInverseSelectorAtomTableRuns contracts clockDepth machine
      advantageExponent pcp
      (inverseSelectorBankTableProgram contracts clockDepth machine pcp)
      (inverseSelectorBankTableBits contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent))
      (inverseSelectorBankTableFuel contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)) := by
  intro request
  let sourceLen :=
    inverseScheduleLength contracts clockDepth advantageExponent request.length
  let copies :=
    inverseBankTableCopies contracts clockDepth advantageExponent request.length
  let code := request.code
  have hwidth :
      inverseSelectorBankWidth contracts clockDepth advantageExponent
          request.length =
        pcp.nativeWidth sourceLen := by
    rw [inverseSelectorBankWidth]
    exact (presentsPaddedOuterPCP_scheduledWidth hpresentation _).symm
  have hquery :
      inverseSelectorBankQueryCount contracts clockDepth advantageExponent
          request.length =
        pcp.queryCount sourceLen := by
    rw [inverseSelectorBankQueryCount]
    exact (congrFun (presentsPaddedOuterPCP_queryCount hpresentation) _).symm
  have hframe :
      inverseSelectorAdapterFrame contracts clockDepth advantageExponent
          request =
        scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
          (pcp.queryCount sourceLen) copies code := by
    calc
      inverseSelectorAdapterFrame contracts clockDepth advantageExponent
          request =
          selectorDrivenBankFrame
            (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              request.length)
            code := rfl
      _ = scheduleNumeralBankOutput sourceLen
            (inverseSelectorBankWidth contracts clockDepth advantageExponent
              request.length)
            (inverseSelectorBankQueryCount contracts clockDepth
              advantageExponent request.length)
            (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (inverseBankRate contracts advantageExponent)
              (inverseChainSourceIndex contracts clockDepth advantageExponent
                request.length))
            code :=
        selectorDrivenBankFrame_eq contracts clockDepth advantageExponent
          request.length code
      _ = scheduleNumeralBankOutput sourceLen (pcp.nativeWidth sourceLen)
            (pcp.queryCount sourceLen) copies code := by
        rw [hwidth, hquery]
        rfl
  exact run_inverseSelectorBankTableProgram_atFrame contracts clockDepth machine
    advantageExponent pcp
    (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
    request.length request.input hframe

end NearCubicWires.TotalSelectorDrivenAdapterRuns
