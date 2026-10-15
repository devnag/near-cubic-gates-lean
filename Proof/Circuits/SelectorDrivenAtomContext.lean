import Proof.MachineModel.BankAtomContextRegisters
import Proof.Circuits.FixedScheduleDiagonalClosure
import Proof.MachineModel.SourceDrivenNumeralBank

/-!
# The atom-shape context from the selector-driven registers

`BankAtomContextRegisters.inverseAtomContext_ofRegisters` is the *only* place in
the inverse cluster that consumes the schedule diagonal, and
`BankAtomContextRegisters`'s own header says so: "§5 is the only place in the
reduction that needs a hypothesis, and it needs two — the presentation premise
and the diagonal".

`SourceDrivenNumeralBank` removes the reason for the second one.  Its bank is
driven by a supplied scheduled length, so the registers a consumer reads are
already indexed by the *chain's* source index rather than by
`RecoveryScheduleEnvelope.sourceIndexOfLength` of the request.  This module
restates §5 at those registers.

The restatement is the same proof with two steps deleted.  The old proof opened
with

```
hindex   : sourceIndexOfLength target = inverseSourceIndex (inverseSelectedSource … target)
hlength  : bankSourceLength target = inverseScheduleLength … target
```

both derived from `hdiagonal`.  At the selector-driven registers those two facts
are `rfl` — the width register *is* `scheduledWidth outer (inverseSourceIndex …)`
and the length register *is* `inverseScheduleLength …` — so the hypothesis has
no work left to do and is dropped from the signature.  The size-cap step, which
previously needed `hindex` before its `rfl`, is now `rfl` outright.

**Output contract unchanged.**  `inverseAtomContext_ofSelectorRegisters` proves
the identical equation against the identical right-hand side
(`BankEmittedAtomLoop.inverseAtomContext`); only the register names on the left
and the premise list change.
-/

namespace NearCubicWires.SelectorDrivenAtomContext

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces

/-! ## 1. The selector-driven registers -/

/-- The inverse chain's own source index at one target.  Written out verbatim:
re-aliasing it breaks the definitional joins below. -/
noncomputable def inverseChainSourceIndex
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (target : ℕ) : ℕ :=
  inverseSourceIndex
    (inverseSelectedSource contracts
      (publishedHierarchyOuterPCP contracts clockDepth)
      (inverseCoreAdvantagePower advantageExponent) target)

/-- The width register of the selector-driven bank at one target. -/
noncomputable def inverseSelectorBankWidth
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseSourceIndex
      (inverseSelectedSource contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseCoreAdvantagePower advantageExponent) target))

/-- The query-count register of the selector-driven bank at one target. -/
noncomputable def inverseSelectorBankQueryCount
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  (publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
    (inverseScheduleLength contracts clockDepth advantageExponent target)

/-- The selector-driven frame's registers are the frame's own components: this
is the join between `SourceDrivenNumeralBank.selectorDrivenBankFrame` and the
two registers above, and it is `rfl`. -/
theorem selectorDrivenBankFrame_eq
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target code : ℕ) :
    selectorDrivenBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (UniformTargetLanguageBank.inverseBankRate contracts advantageExponent)
        (inverseChainSourceIndex contracts clockDepth advantageExponent target)
        code =
      RuntimeScheduleNumeralBank.scheduleNumeralBankOutput
        (inverseScheduleLength contracts clockDepth advantageExponent target)
        (inverseSelectorBankWidth contracts clockDepth advantageExponent target)
        (inverseSelectorBankQueryCount contracts clockDepth advantageExponent
          target)
        (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.inverseBankRate contracts
            advantageExponent)
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        code :=
  rfl

/-! ## 2. §5 of `BankAtomContextRegisters`, without the diagonal -/

/-- **The join fact, restated at the selector-driven registers.**  Identical
conclusion to `BankAtomContextRegisters.inverseAtomContext_ofRegisters`; the
diagonal premise is gone, because the registers are already the chain's.  The
presentation premise is the only hypothesis left. -/
theorem inverseAtomContext_ofSelectorRegisters
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (target : ℕ) :
    Nat.pair
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target)))
        (bankShapeNumerals
          (oracleSizeBound
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSelectorBankWidth contracts clockDepth advantageExponent
              target))
          (inverseSelectorBankWidth contracts clockDepth advantageExponent
            target)
          (inverseSelectorBankQueryCount contracts clockDepth advantageExponent
            target)) =
      inverseAtomContext contracts clockDepth machine advantageExponent pcp
        target := by
  have hwidth :
      inverseSelectorBankWidth contracts clockDepth advantageExponent target =
        pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent
            target) := by
    rw [inverseSelectorBankWidth]
    exact (presentsPaddedOuterPCP_scheduledWidth hpresentation _).symm
  have hquery :
      inverseSelectorBankQueryCount contracts clockDepth advantageExponent
          target =
        pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            target) := by
    rw [inverseSelectorBankQueryCount]
    exact (congrFun (presentsPaddedOuterPCP_queryCount hpresentation) _).symm
  have hbound :
      oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          (inverseSelectorBankWidth contracts clockDepth advantageExponent
            target) =
        inverseScheduleBound contracts clockDepth advantageExponent target :=
    rfl
  rw [inverseAtomContext_eq, bankShapeNumerals, hbound, hwidth, hquery]

/-! ## 3. The fixed schedule's twin

The fixed chain's index is the selected source itself, with no
`inverseSourceIndex` in front of it, so the same two registers are one
application shorter.  `FixedScheduleDiagonalClosure.fixedAtomContext_ofRegisters`
loses its diagonal in exactly the same way.
-/

/-- The width register of the fixed schedule's selector-driven bank. -/
noncomputable def fixedSelectorBankWidth
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (requestedRate target : ℕ) : ℕ :=
  scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
    (fixedSelectedSource contracts
      (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target)

/-- The query-count register of the fixed schedule's selector-driven bank. -/
noncomputable def fixedSelectorBankQueryCount
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (requestedRate target : ℕ) : ℕ :=
  (publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
    (fixedScheduleLength contracts clockDepth requestedRate target)

/-- **The fixed schedule's join fact, without the diagonal.** -/
theorem fixedAtomContext_ofSelectorRegisters
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (target : ℕ) :
    Nat.pair
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (fixedScheduleInput contracts clockDepth machine requestedRate
              target)))
        (bankShapeNumerals
          (oracleSizeBound (fixedRequiredDegree contracts requestedRate)
            (fixedSelectorBankWidth contracts clockDepth requestedRate target))
          (fixedSelectorBankWidth contracts clockDepth requestedRate target)
          (fixedSelectorBankQueryCount contracts clockDepth requestedRate
            target)) =
      FixedScheduleAtomLoop.fixedAtomContext contracts clockDepth machine
        requestedRate pcp target := by
  have hwidth :
      fixedSelectorBankWidth contracts clockDepth requestedRate target =
        pcp.nativeWidth
          (fixedScheduleLength contracts clockDepth requestedRate target) := by
    rw [fixedSelectorBankWidth]
    exact (presentsPaddedOuterPCP_scheduledWidth hpresentation _).symm
  have hquery :
      fixedSelectorBankQueryCount contracts clockDepth requestedRate target =
        pcp.queryCount
          (fixedScheduleLength contracts clockDepth requestedRate target) := by
    rw [fixedSelectorBankQueryCount]
    exact (congrFun (presentsPaddedOuterPCP_queryCount hpresentation) _).symm
  have hbound :
      oracleSizeBound (fixedRequiredDegree contracts requestedRate)
          (fixedSelectorBankWidth contracts clockDepth requestedRate target) =
        fixedScheduleBound contracts clockDepth requestedRate target :=
    rfl
  rw [FixedScheduleDiagonalClosure.fixedAtomContext_eq, bankShapeNumerals,
    hbound, hwidth, hquery]

end NearCubicWires.SelectorDrivenAtomContext
