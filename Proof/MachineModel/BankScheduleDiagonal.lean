import Proof.MachineModel.UniformTargetLanguageBank

/-!
# The schedule-index diagonal

`RuntimeScheduleNumeralBank` decodes its source index from the *public length*
of the request, through `RecoveryScheduleEnvelope.sourceIndexOfLength`, while
the two chains of `BranchTargetLanguageProgram` work at the *schedule's* index:
`inverseSourceIndex (inverseSelectedSource …)` on the inverse schedule and
`fixedSelectedSource …` on the fixed one.  `UniformTargetLanguageBank` records
that the two agree on the diagonal and leaves the identification inside
`bodyRun`.

This module supplies the identification as an explicit, reusable hypothesis.

## The identification is conditional, and provably so

The `hexecutes` binder of `PublishedRecoveryClosure` quantifies over *every*
target above one onset — `inverseCaseOneTargetOnset … ≤ target` — and nothing
in `hlarge`, `hyes`, `hrejects` or `haccepts` constrains `target` to be a
scheduled source length.  The consumer therefore does **not** pin
`target = sourceLength (inverseSourceIndex …)`, and the identification cannot
be asserted unconditionally: off the diagonal `sourceIndexOfLength target` is
the rounded-down decode of the request's own length, whereas the chain's index
is chosen by the executable envelope selector at that target, and the two are
different functions of `target`.

What is available — and what a register-driven body applies — is the diagonal
bridge below: on a request whose public length *is* the chain's scheduled
source length, every numeral the bank emits is the chain's own numeral at the
chain's own index.  §3 states it at both published schedules.
-/

namespace NearCubicWires.BankScheduleDiagonal

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank

/-! ## 1. Decoding a scheduled length -/

/-- **The diagonal identification.**  A public length that is a scheduled
source length decodes to that source's own index. -/
theorem sourceIndexOfLength_of_eq_sourceLength
    {target sourceIndex : ℕ} (hdiagonal : target = sourceLength sourceIndex) :
    sourceIndexOfLength target = sourceIndex := by
  subst hdiagonal
  exact sourceIndexOfLength_sourceLength sourceIndex

/-- The bank's scheduled-length register at such a request. -/
theorem bankSourceLength_of_eq_sourceLength
    {target sourceIndex : ℕ} (hdiagonal : target = sourceLength sourceIndex) :
    bankSourceLength target = sourceLength sourceIndex := by
  subst hdiagonal
  exact bankSourceLength_sourceLength sourceIndex

/-! ## 2. The bank's frame on the diagonal -/

/-- **The bridging lemma.**  On a request whose public length is the scheduled
source length of `sourceIndex`, the bank's frame is literally the chain's own
numerals at `sourceIndex`: the scheduled length, the scheduled width, the
scheduled query count and the scheduled copy count, beside the retained point
code. -/
theorem publishedBankFrame_of_eq_sourceLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ)
    {target sourceIndex : ℕ} (code : ℕ)
    (hdiagonal : target = sourceLength sourceIndex) :
    publishedBankFrame outer pcppSource rate target code =
      scheduleNumeralBankOutput (sourceLength sourceIndex)
        (scheduledWidth outer sourceIndex)
        (outer.pcp.queryCount (sourceLength sourceIndex))
        (inverseCopies outer pcppSource rate sourceIndex) code := by
  subst hdiagonal
  exact publishedBankFrame_at_sourceLength outer pcppSource rate sourceIndex
    code

/-! ## 3. The two published schedules -/

/-- **The inverse schedule's diagonal bridge.**  The hypothesis is exactly the
statement that the request's public length is the source length the inverse
chain works at; under it, the bank's frame is that chain's frame. -/
theorem publishedBankFrame_at_inverseDiagonal
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target code : ℕ)
    (hdiagonal :
      target =
        sourceLength (inverseSourceIndex
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent) target))) :
    publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target code =
      scheduleNumeralBankOutput
        (sourceLength (inverseSourceIndex
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent) target)))
        (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target)))
        ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
          (sourceLength (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target))))
        (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent)
          (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target)))
        code :=
  publishedBankFrame_of_eq_sourceLength
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent) code hdiagonal

/-- **The fixed schedule's diagonal bridge.**  The fixed chain's index is the
selected source itself, with no `inverseSourceIndex` in front of it. -/
theorem publishedBankFrame_at_fixedDiagonal
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (requestedRate target code : ℕ)
    (hdiagonal :
      target =
        sourceLength
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target)) :
    publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (fixedBankRate contracts requestedRate) target code =
      scheduleNumeralBankOutput
        (sourceLength
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target))
        (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target))
        ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
          (sourceLength
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target)))
        (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (fixedBankRate contracts requestedRate)
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target))
        code :=
  publishedBankFrame_of_eq_sourceLength
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (fixedBankRate contracts requestedRate) code hdiagonal

end NearCubicWires.BankScheduleDiagonal
