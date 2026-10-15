import Proof.MachineModel.BankProjectionTableStage
import Proof.Circuits.FixedScheduleDiagonalClosure

/-!
# The projection-runner table stage at the fixed schedule

`BankProjectionTableStage` closes `BankAtomContextRegisters.InverseAtomTableRuns`
from the executable presentation and the onset-restricted schedule diagonal.  The
stage itself — `bankProjectionTableProgram` and its two envelopes — is schedule
free: `run_bankProjectionTableProgram` takes the identification of the request's
public length with a source length as its *only* hypothesis and says nothing
about which schedule produced that length.

This module replays the last two steps of that argument at the fixed-rate
schedule, so that `FixedScheduleDiagonalClosure.FixedAtomTableRuns` is discharged
from exactly the same two facts:

* §1 names the stage and its two envelopes at the fixed schedule.
* §2 is the join fact: on the fixed diagonal the numeral bank's frame is the
  fixed chain's own five registers, the fixed chain's index being
  `CaseOneRecoveryAssembly.fixedSelectedSource` itself.
* §3 discharges `FixedAtomTableRuns`.

Nothing here is new mathematics; the fixed side's diagonal bridge
`BankScheduleDiagonal.publishedBankFrame_at_fixedDiagonal` and the schedule-free
run theorem were both already green.
-/

namespace NearCubicWires.FixedProjectionTableStage

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.FixedScheduleDiagonalClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The stage at the published fixed schedule -/

/-- The stage at the published fixed-rate schedule. -/
noncomputable def fixedBankTableProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  bankProjectionTableProgram pcp
    (publishedRefuterSource contracts clockDepth).refuter.runner.program
    machine.description

theorem fixedBankTableProgram_oracleFree
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hrefuter :
      OracleFree
        (publishedRefuterSource contracts clockDepth).refuter.runner.program) :
    OracleFree (fixedBankTableProgram contracts clockDepth machine pcp) :=
  bankProjectionTableProgram_oracleFree pcp hrefuter machine.description

/-- The bank's copy-count register at the fixed schedule's own index. -/
noncomputable def fixedBankTableCopies
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (requestedRate target : ℕ) : ℕ :=
  inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (fixedBankRate contracts requestedRate)
    (fixedSelectedSource contracts
      (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target)

/-- Width of the stage at one request. -/
noncomputable def fixedBankTableBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (request : LanguageEvaluationRequest) : ℕ :=
  bankProjectionTableBits pcp
    (publishedRefuterSource contracts clockDepth).refuter machine
    (LanguageEvaluationRequest.length request)
    (fixedScheduleLength contracts clockDepth requestedRate
      (LanguageEvaluationRequest.length request))
    (fixedBankTableCopies contracts clockDepth requestedRate
      (LanguageEvaluationRequest.length request))
    (LanguageEvaluationRequest.code request)

/-- Fuel of the stage at one request. -/
noncomputable def fixedBankTableFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (request : LanguageEvaluationRequest) : ℕ :=
  bankProjectionTableFuel pcp
    (publishedRefuterSource contracts clockDepth).refuter machine
    (fixedScheduleLength contracts clockDepth requestedRate
      (LanguageEvaluationRequest.length request))

/-! ## 2. The join fact at the fixed diagonal -/

/-- **The join fact.**  On the fixed schedule's diagonal, and for a presented
PCP, the numeral bank's frame is the fixed chain's own five registers at the
selected source length, with the PCP's own width and query count in the two
shape positions.  The fixed chain's index is `fixedSelectedSource` itself, with
no `RecoveryScheduleEnvelope.inverseSourceIndex` in front of it. -/
theorem fixedAdapterFrame_ofRegisters
    (contracts : PublishedContracts) (clockDepth : ℕ) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    {target : ℕ} (input : BitInput target)
    (hdiagonal :
      target =
        sourceLength
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target)) :
    fixedAdapterFrame contracts clockDepth requestedRate ⟨target, input⟩ =
      scheduleNumeralBankOutput
        (sourceLength
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target))
        (pcp.nativeWidth
          (sourceLength
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target)))
        (pcp.queryCount
          (sourceLength
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target)))
        (fixedBankTableCopies contracts clockDepth requestedRate target)
        (encodeBitInput input) := by
  have hwidth :=
    presentsPaddedOuterPCP_scheduledWidth hpresentation
      (fixedSelectedSource contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target)
  have hquery :=
    congrFun (presentsPaddedOuterPCP_queryCount hpresentation)
      (sourceLength
        (fixedSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
          target))
  simp only [fixedAdapterFrame, fixedBankTableCopies]
  rw [hwidth, hquery]
  exact publishedBankFrame_at_fixedDiagonal contracts clockDepth requestedRate
    target (encodeBitInput input) hdiagonal

/-! ## 3. `FixedAtomTableRuns`, discharged on the diagonal -/

/-- **The fixed adapter's last residual, discharged.**  From the numeral bank's
frame the linked stage returns the balanced encoding of the projection runner's
call outputs at the fixed schedule's PCP input.  The two hypotheses are exactly
the two `FixedScheduleDiagonalClosure` already threads — the executable
presentation and the onset-restricted schedule diagonal. -/
theorem fixedAtomTableRuns_ofDiagonal
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hdiagonal : ∀ target : ℕ,
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target →
      target =
        fixedScheduleLength contracts clockDepth requestedRate target) :
    FixedAtomTableRuns contracts clockDepth machine requestedRate pcp
      (fixedBankTableProgram contracts clockDepth machine pcp)
      (fixedBankTableBits contracts clockDepth machine requestedRate pcp)
      (fixedBankTableFuel contracts clockDepth machine requestedRate pcp) := by
  intro target hlarge input
  rw [fixedAdapterFrame_ofRegisters contracts clockDepth requestedRate pcp
    hpresentation input (hdiagonal target hlarge)]
  exact run_bankProjectionTableProgram pcp
    (publishedRefuterSource contracts clockDepth).refuter machine target
    (sourceLength
      (fixedSelectedSource contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target))
    (fixedBankTableCopies contracts clockDepth requestedRate target)
    (encodeBitInput input) (hdiagonal target hlarge)

end NearCubicWires.FixedProjectionTableStage
