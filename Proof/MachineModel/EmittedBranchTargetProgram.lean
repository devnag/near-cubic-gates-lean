import Proof.MachineModel.BankRecoveryCodeProgram

/-!
# The branch-dispatched target with the query computed

`CanonicalBranchSelectorProgram.run_inverseTargetProgram_caseOne_closed` and
its three siblings discharge the branch selector of
`BranchTargetLanguageProgram` by supplying `branchSelectorProgram` at the
scheduled recovery code — a `set` immediate chosen from the request's own
target.  `BankRecoveryCodeProgram` replaces that immediate by the assembler of
the recovery code, leaving one program parameter (the structural atom emitter)
and one run hypothesis.

This module carries that replacement through the dispatcher: the four theorems
below are the four closed theorems of `CanonicalBranchSelectorProgram` with the
selector's query immediate removed.  After them, the target-derived data still
baked into the two chains are exactly the four schedule numerals the numeral
bank of `RuntimeScheduleNumeralBank` emits — plus, on the Case-2 branch, the
substituted circuit recovered from the accepting oracle.

## The fixed schedule's Case-2 chain carries no target

§1 records a small but load-bearing fact: `fixedCaseTwoChainProgram` ignores its
target argument outright, because `RecoveryScheduleEnvelope.fixedCopies` is a
frozen numeral.  On the fixed schedule the Case-2 branch therefore has *no*
schedule immediate at all, and the per-block occurrence callee is its only
request-dependent part.
-/

namespace NearCubicWires.EmittedBranchTargetProgram

open NearCubicWires
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The fixed schedule's Case-2 chain is request-independent -/

/-- **The fixed schedule's Case-2 chain does not depend on the target.**  Its
only schedule numeral is the frozen `fixedCopies`; the request enters solely
through the per-block occurrence callee. -/
theorem fixedCaseTwoChainProgram_target_independent
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target target' : ℕ) (occurrence : NPOracleProgram) :
    fixedCaseTwoChainProgram contracts outer requestedRate target occurrence =
      fixedCaseTwoChainProgram contracts outer requestedRate target'
        occurrence :=
  rfl

/-! ## 2. The emitter's atom schedules at the two published splits -/

/-- The structural atom schedule the inverse schedule's branch query is the
encoding of. -/
noncomputable def inverseSelectorAtoms
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : List ℕ :=
  boundedOracleStructuralFormulaAtoms (paddedOuterPCP outer)
    (inverseRefuterInput contracts outer machine advantageExponent target)
    (oracleSizeBound
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (scheduledWidth outer
        (inverseSourceIndex
          (inverseSelectedSource contracts outer
            (inverseCoreAdvantagePower advantageExponent) target))))

/-- The fixed schedule's counterpart. -/
noncomputable def fixedSelectorAtoms
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) : List ℕ :=
  boundedOracleStructuralFormulaAtoms (paddedOuterPCP outer)
    (fixedRefuterInput contracts outer machine requestedRate target)
    (oracleSizeBound (fixedRequiredDegree contracts requestedRate)
      (scheduledWidth outer
        (fixedSelectedSource contracts outer requestedRate target)))

noncomputable def inverseEmittedSelectorBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) (point : BitInput target)
    (emitterBits : ℕ) : ℕ :=
  emittedBranchSelectorBits (paddedOuterPCP outer)
    (inverseRefuterInput contracts outer machine advantageExponent target)
    (oracleSizeBound
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (scheduledWidth outer
        (inverseSourceIndex
          (inverseSelectedSource contracts outer
            (inverseCoreAdvantagePower advantageExponent) target))))
    target (encodeBitInput point) emitterBits

noncomputable def inverseEmittedSelectorFuel
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target emitterFuel : ℕ) : ℕ :=
  emittedBranchSelectorFuel (paddedOuterPCP outer)
    (inverseRefuterInput contracts outer machine advantageExponent target)
    (oracleSizeBound
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (scheduledWidth outer
        (inverseSourceIndex
          (inverseSelectedSource contracts outer
            (inverseCoreAdvantagePower advantageExponent) target))))
    emitterFuel

noncomputable def fixedEmittedSelectorBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) (point : BitInput target) (emitterBits : ℕ) :
    ℕ :=
  emittedBranchSelectorBits (paddedOuterPCP outer)
    (fixedRefuterInput contracts outer machine requestedRate target)
    (oracleSizeBound (fixedRequiredDegree contracts requestedRate)
      (scheduledWidth outer
        (fixedSelectedSource contracts outer requestedRate target)))
    target (encodeBitInput point) emitterBits

noncomputable def fixedEmittedSelectorFuel
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target emitterFuel : ℕ) : ℕ :=
  emittedBranchSelectorFuel (paddedOuterPCP outer)
    (fixedRefuterInput contracts outer machine requestedRate target)
    (oracleSizeBound (fixedRequiredDegree contracts requestedRate)
      (scheduledWidth outer
        (fixedSelectedSource contracts outer requestedRate target)))
    emitterFuel

/-! ## 3. The inverse schedule -/

set_option maxHeartbeats 800000 in
-- The dispatcher's resource envelopes are nested link terms; elaborating the
-- substituted selector width and fuel exceeds the default budget.
/-- **The inverse schedule's canonical target on the Case-1 branch, with the
query computed.**  The selector is the emitted assembler of
`BankRecoveryCodeProgram`; no recovery-code immediate appears anywhere in the
dispatched stream. -/
theorem run_inverseTargetProgram_caseOne_emitted
    (emitter occurrence : NPOracleProgram)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hrejects : ¬machine.toSemantic.accepts
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (paddedOuterPCP outer)
        (inverseRefuterInput contracts outer machine advantageExponent target),
      InverseCaseTwoAcceptance contracts outer
        (inverseCoreAdvantagePower advantageExponent)
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)
        caseTwo machine)
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hbranch :
      inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseOne data)
    (point : BitInput target) (emitterBits emitterFuel : ℕ)
    (hemitter :
      runNPOracleProgram emitter emitterBits emitterFuel
          (initialNPOracleState target (encodeBitInput point)) =
        some
          (Nat.pair
            (encodeTaggedList
              (inverseSelectorAtoms contracts outer machine advantageExponent
                target))
            (encodeBitInput point)))
    (hcount :
      0 < outer.pcp.queryCount (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))) :
    runNPOracleProgram
        (inverseTargetProgram contracts outer machine advantageExponent target
          (emittedBranchSelectorProgram emitter) occurrence)
        (branchTargetBitBits target 0 (encodeBitInput point)
          (inverseEmittedSelectorBits contracts outer machine advantageExponent
            target point emitterBits)
          (inverseCaseOneChainBits contracts outer machine advantageExponent
            target point)
          (inverseCanonicalTargetFunction contracts outer machine
            advantageExponent target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (inverseCaseOneChainProgram contracts outer machine advantageExponent
            target)
          (inverseCaseTwoChainProgram contracts outer advantageExponent target
            occurrence)
          (inverseEmittedSelectorFuel contracts outer machine advantageExponent
            target emitterFuel)
          (inverseCaseOneChainFuel contracts outer machine advantageExponent
            target point))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat :=
  run_inverseTargetProgram_caseOne (emittedBranchSelectorProgram emitter)
    occurrence contracts outer machine advantageExponent target hlarge hyes
    hrejects haccepts data hbranch point
    (inverseEmittedSelectorBits contracts outer machine advantageExponent target
      point emitterBits)
    (inverseEmittedSelectorFuel contracts outer machine advantageExponent target
      emitterFuel)
    (run_emittedBranchSelectorProgram_caseOne data target (encodeBitInput point)
      (encodeBitInput point) emitterBits emitterFuel emitter hemitter)
    hcount

set_option maxHeartbeats 800000 in
-- The dispatcher's resource envelopes are nested link terms; elaborating the
-- substituted selector width and fuel exceeds the default budget.
/-- **The inverse schedule's canonical target on the Case-2 branch, with the
query computed.** -/
theorem run_inverseTargetProgram_caseTwo_emitted
    (emitter occurrence : NPOracleProgram)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hrejects : ¬machine.toSemantic.accepts
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (paddedOuterPCP outer)
        (inverseRefuterInput contracts outer machine advantageExponent target),
      InverseCaseTwoAcceptance contracts outer
        (inverseCoreAdvantagePower advantageExponent)
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)
        caseTwo machine)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP outer)
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hbranch :
      inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseTwo caseTwo)
    (point : BitInput target) (emitterBits emitterFuel : ℕ)
    (occurrenceBits occurrenceFuel : ℕ → ℕ)
    (hemitter :
      runNPOracleProgram emitter emitterBits emitterFuel
          (initialNPOracleState target (encodeBitInput point)) =
        some
          (Nat.pair
            (encodeTaggedList
              (inverseSelectorAtoms contracts outer machine advantageExponent
                target))
            (encodeBitInput point)))
    (hoccurrence : ∀ block,
      block <
        inverseCopies outer (publishedPointwisePCPP contracts)
          (inverseRate contracts
            (inverseCoreAdvantagePower advantageExponent))
          (inverseSourceIndex
            (inverseSelectedSource contracts outer
              (inverseCoreAdvantagePower advantageExponent) target)) →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
            (encodeBitInput point) block).toNat) :
    runNPOracleProgram
        (inverseTargetProgram contracts outer machine advantageExponent target
          (emittedBranchSelectorProgram emitter) occurrence)
        (branchTargetBitBits target 1 (encodeBitInput point)
          (inverseEmittedSelectorBits contracts outer machine advantageExponent
            target point emitterBits)
          (inverseCaseTwoChainBits contracts outer machine advantageExponent
            target caseTwo occurrenceBits point)
          (inverseCanonicalTargetFunction contracts outer machine
            advantageExponent target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (inverseCaseOneChainProgram contracts outer machine advantageExponent
            target)
          (inverseCaseTwoChainProgram contracts outer advantageExponent target
            occurrence)
          (inverseEmittedSelectorFuel contracts outer machine advantageExponent
            target emitterFuel)
          (inverseCaseTwoChainFuel contracts outer machine advantageExponent
            target caseTwo occurrence occurrenceFuel point))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat :=
  run_inverseTargetProgram_caseTwo (emittedBranchSelectorProgram emitter)
    occurrence contracts outer machine advantageExponent target hlarge hyes
    hrejects haccepts caseTwo hbranch point
    (inverseEmittedSelectorBits contracts outer machine advantageExponent target
      point emitterBits)
    (inverseEmittedSelectorFuel contracts outer machine advantageExponent target
      emitterFuel)
    1 occurrenceBits occurrenceFuel Nat.one_ne_zero
    (run_emittedBranchSelectorProgram_caseTwo caseTwo target
      (encodeBitInput point) (encodeBitInput point) emitterBits emitterFuel
      emitter hemitter)
    hoccurrence

/-! ## 4. The fixed schedule -/

set_option maxHeartbeats 800000 in
-- The dispatcher's resource envelopes are nested link terms; elaborating the
-- substituted selector width and fuel exceeds the default budget.
/-- **The fixed schedule's canonical target on the Case-1 branch, with the
query computed.** -/
theorem run_fixedTargetProgram_caseOne_emitted
    (emitter occurrence : NPOracleProgram)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge : fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (fixedSelectedSource contracts outer requestedRate target))
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hrejects : ¬machine.toSemantic.accepts
      (fixedRefuterInput contracts outer machine requestedRate target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP outer)
        (fixedRefuterInput contracts outer machine requestedRate target),
      FixedCaseTwoAcceptance contracts outer requestedRate
        (fixedSelectedSource contracts outer requestedRate target)
        caseTwo machine)
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hbranch :
      fixedTargetBranch contracts outer machine requestedRate target hyes =
        .caseOne data)
    (point : BitInput target) (emitterBits emitterFuel : ℕ)
    (hemitter :
      runNPOracleProgram emitter emitterBits emitterFuel
          (initialNPOracleState target (encodeBitInput point)) =
        some
          (Nat.pair
            (encodeTaggedList
              (fixedSelectorAtoms contracts outer machine requestedRate target))
            (encodeBitInput point)))
    (hcount :
      0 < outer.pcp.queryCount
        (sourceLength
          (fixedSelectedSource contracts outer requestedRate target))) :
    runNPOracleProgram
        (fixedTargetProgram contracts outer machine requestedRate target
          (emittedBranchSelectorProgram emitter) occurrence)
        (branchTargetBitBits target 0 (encodeBitInput point)
          (fixedEmittedSelectorBits contracts outer machine requestedRate target
            point emitterBits)
          (fixedCaseOneChainBits contracts outer machine requestedRate target
            point)
          (fixedCanonicalTargetFunction contracts outer machine requestedRate
            target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (fixedCaseOneChainProgram contracts outer machine requestedRate
            target)
          (fixedCaseTwoChainProgram contracts outer requestedRate target
            occurrence)
          (fixedEmittedSelectorFuel contracts outer machine requestedRate target
            emitterFuel)
          (fixedCaseOneChainFuel contracts outer machine requestedRate target
            point))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat :=
  run_fixedTargetProgram_caseOne (emittedBranchSelectorProgram emitter)
    occurrence contracts outer machine requestedRate target hlarge hyes
    hrejects haccepts data hbranch point
    (fixedEmittedSelectorBits contracts outer machine requestedRate target point
      emitterBits)
    (fixedEmittedSelectorFuel contracts outer machine requestedRate target
      emitterFuel)
    (run_emittedBranchSelectorProgram_caseOne data target (encodeBitInput point)
      (encodeBitInput point) emitterBits emitterFuel emitter hemitter)
    hcount

set_option maxHeartbeats 800000 in
-- The dispatcher's resource envelopes are nested link terms; elaborating the
-- substituted selector width and fuel exceeds the default budget.
/-- **The fixed schedule's canonical target on the Case-2 branch, with the
query computed.** -/
theorem run_fixedTargetProgram_caseTwo_emitted
    (emitter occurrence : NPOracleProgram)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge : fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (fixedSelectedSource contracts outer requestedRate target))
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hrejects : ¬machine.toSemantic.accepts
      (fixedRefuterInput contracts outer machine requestedRate target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP outer)
        (fixedRefuterInput contracts outer machine requestedRate target),
      FixedCaseTwoAcceptance contracts outer requestedRate
        (fixedSelectedSource contracts outer requestedRate target)
        caseTwo machine)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hbranch :
      fixedTargetBranch contracts outer machine requestedRate target hyes =
        .caseTwo caseTwo)
    (point : BitInput target) (emitterBits emitterFuel : ℕ)
    (occurrenceBits occurrenceFuel : ℕ → ℕ)
    (hemitter :
      runNPOracleProgram emitter emitterBits emitterFuel
          (initialNPOracleState target (encodeBitInput point)) =
        some
          (Nat.pair
            (encodeTaggedList
              (fixedSelectorAtoms contracts outer machine requestedRate target))
            (encodeBitInput point)))
    (hoccurrence : ∀ block,
      block <
        fixedCopies (publishedPointwisePCPP contracts)
          (fixedRate contracts requestedRate) →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
            (encodeBitInput point) block).toNat) :
    runNPOracleProgram
        (fixedTargetProgram contracts outer machine requestedRate target
          (emittedBranchSelectorProgram emitter) occurrence)
        (branchTargetBitBits target 1 (encodeBitInput point)
          (fixedEmittedSelectorBits contracts outer machine requestedRate target
            point emitterBits)
          (fixedCaseTwoChainBits contracts outer machine requestedRate target
            caseTwo occurrenceBits point)
          (fixedCanonicalTargetFunction contracts outer machine requestedRate
            target hlarge hyes hrejects haccepts point).toNat)
        (branchTargetBitFuel
          (fixedCaseOneChainProgram contracts outer machine requestedRate
            target)
          (fixedCaseTwoChainProgram contracts outer requestedRate target
            occurrence)
          (fixedEmittedSelectorFuel contracts outer machine requestedRate target
            emitterFuel)
          (fixedCaseTwoChainFuel contracts outer machine requestedRate target
            caseTwo occurrence occurrenceFuel point))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat :=
  run_fixedTargetProgram_caseTwo (emittedBranchSelectorProgram emitter)
    occurrence contracts outer machine requestedRate target hlarge hyes
    hrejects haccepts caseTwo hbranch point
    (fixedEmittedSelectorBits contracts outer machine requestedRate target point
      emitterBits)
    (fixedEmittedSelectorFuel contracts outer machine requestedRate target
      emitterFuel)
    1 occurrenceBits occurrenceFuel Nat.one_ne_zero
    (run_emittedBranchSelectorProgram_caseTwo caseTwo target
      (encodeBitInput point) (encodeBitInput point) emitterBits emitterFuel
      emitter hemitter)
    hoccurrence

end NearCubicWires.EmittedBranchTargetProgram
