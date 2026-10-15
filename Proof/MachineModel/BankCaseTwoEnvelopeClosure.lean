import Proof.MachineModel.BankResidualClusterClosure
import Proof.MachineModel.BankScheduledRowStageClosure

/-!
# The Case-2 bank envelopes, discharged

`BankRegisterCaseTwoChain` left two residuals.  This module discharges the
resource one, `InverseCaseTwoBankEnvelopes`, for *every* per-block occurrence
callee and both of its envelopes, and records what the cluster closure of
`BankResidualClusterClosure` then still needs.

## The binding hazard

The Case-2 body's own width and fuel are functions of the recovered accepting
oracle `caseTwo`, and `caseTwo` is bound *inside* `InverseCaseTwoBankEnvelopes`
— it is introduced by the branch equation, not by the request.  So neither
envelope can be written as an expression in the request alone by simply naming
the Case-2 body's cost.

It can be written as a *branch read*.  `CaseOneRecoveryAssembly.inverseTargetBranch`
is a total function of the request and one acceptance proof, and
`ScheduledRecovery.ScheduledOuterBranch` is a two-constructor inductive, so a
public `LanguageEvaluationRequest → ℕ` may decide acceptance classically, match
on the branch, and quote the Case-2 body's cost at whichever oracle the branch
itself carries.  Proof irrelevance makes the acceptance proof in the definition
the very proof the premise supplies, and constructor injectivity makes the
matched oracle the very oracle the premise supplies, so the domination the
premise asks for holds as an *equality* — no slack, no new bound.

That is `§1`; `§2` discharges the premise, and `§3` records the cluster's
remaining obligations.

## What `InverseScheduledOccurrenceRuns` still needs

`CaseTwoBlockOccurrenceProgram.caseTwoScheduledOccurrenceProgram` is the callee
at the scheduled coordinates, and its stream carries seven immediates.  Four
are schedule numerals and are removable by the register discipline
`OuterProofRowStageProgram` now uses — reload the public length from register
one and run a published runner:

* `outer.pcp.nativeWidth (sourceLength sourceIndex)` — the shape runner's left
  component, exactly as in `OuterProofRowStageProgram`;
* `ProjectionWidthEnvelope.widthEnvelope outer (sourceLength sourceIndex)` —
  `RuntimeScheduleNumeralBank.widthEnvelopeProgram`;
* `clauseBitsEnvelope outer pcppSource _ (sourceLength sourceIndex)` and
* `seedArity outer pcppSource requiredDegree sourceIndex`.

Three are *oracle* numerals and are not removable that way:

* `(caseTwoSubstitutedCircuit caseTwo).size`,
* `encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)`,
* `(caseTwoFactoryPCPP pcppSource caseTwo).clauseBits`.

`CanonicalTargetLanguageProgram.caseTwoSubstitutedCircuit` is
`outer.pcppCircuit input (restrictPaddedOracle caseTwo.circuit _)`, i.e.
`(outer.substitution.circuit ⟨_, input, oracle⟩).padToArity`.  The published
interface *does* execute the outer half of that:
`ExecutableInterfaces.ExecutableProjectionSubstitution.computes` runs
`outer.substitution.runner.program` and returns
`encodeBooleanCircuit (circuit request)` — but its request already contains the
oracle.  The oracle itself is what
`BoundedOracleRecoveryProgram` recovers, one description coordinate at a time
by SAT self-reduction; no module in the tree assembles those coordinates into
`encodeBooleanCircuit (restrictPaddedOracle caseTwo.circuit _)`, and none
executes `padToArity` or `restrictPaddedOracle`.

So the occurrence residual is one encoder (recovered description bits to a
padded, restricted circuit encoding) plus an internals pass over
`CaseTwoBlockOccurrenceProgram` turning its seven immediates into frame reads.
Neither is attempted here.
-/

namespace NearCubicWires.BankCaseTwoEnvelopeClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankCaseTwoSeedBlockListProgram
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.BankResidualClusterClosure
open NearCubicWires.BankScheduledRowStageClosure
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The Case-2 body's cost, read off the branch -/

open Classical in
/-- The Case-2 body's width at one target and point code, quoted at the oracle
the schedule's own branch carries. -/
noncomputable def inverseCaseTwoBranchBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (occurrenceBits : ℕ → ℕ → ℕ) (target pointCode : ℕ) : ℕ :=
  if hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target) then
    match
      inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes with
    | .caseOne _ => 0
    | .caseTwo caseTwo =>
        bankCaseTwoTargetBitBits target
          (sourceLength
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              target))
          (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              target))
          ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
            (sourceLength
              (inverseChainSourceIndex contracts clockDepth advantageExponent
                target)))
          (inverseChainTwoCopies contracts clockDepth advantageExponent target)
          pointCode (occurrenceBits target)
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo pointCode)
          ((List.range
            (inverseChainTwoCopies contracts clockDepth advantageExponent
              target)).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo pointCode))
  else 0

open Classical in
/-- The Case-2 body's fuel at one target and point code, quoted at the oracle
the schedule's own branch carries. -/
noncomputable def inverseCaseTwoBranchFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (occurrence : NPOracleProgram) (occurrenceFuel : ℕ → ℕ → ℕ)
    (target pointCode : ℕ) : ℕ :=
  if hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target) then
    match
      inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes with
    | .caseOne _ => 0
    | .caseTwo caseTwo =>
        bankCaseTwoTargetBitFuel (publishedAmplifier contracts).algorithm
          occurrence target
          (inverseChainTwoCopies contracts clockDepth advantageExponent target)
          pointCode (occurrenceFuel target)
          ((List.range
            (inverseChainTwoCopies contracts clockDepth advantageExponent
              target)).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo pointCode))
  else 0

/-- The Case-2 body's width as a public request function. -/
noncomputable def inverseCaseTwoBodyBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (occurrenceBits : ℕ → ℕ → ℕ) (request : LanguageEvaluationRequest) : ℕ :=
  inverseCaseTwoBranchBits contracts clockDepth machine advantageExponent
    occurrenceBits (LanguageEvaluationRequest.length request)
    (LanguageEvaluationRequest.code request)

/-- The Case-2 body's fuel as a public request function. -/
noncomputable def inverseCaseTwoBodyFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (occurrence : NPOracleProgram) (occurrenceFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  inverseCaseTwoBranchFuel contracts clockDepth machine advantageExponent
    occurrence occurrenceFuel (LanguageEvaluationRequest.length request)
    (LanguageEvaluationRequest.code request)

/-! ## 2. `InverseCaseTwoBankEnvelopes`, discharged -/

/-- **The Case-2 chain's resource residual, discharged.**  For every per-block
occurrence callee and both of its envelopes, the branch-read body cost is a
public function of the request that dominates the register-driven Case-2 cost
at every request — with equality, since it is that cost. -/
theorem inverseCaseTwoBankEnvelopes_ofBranch
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (occurrence : NPOracleProgram)
    (occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ) :
    InverseCaseTwoBankEnvelopes contracts clockDepth machine advantageExponent
      occurrence occurrenceBits occurrenceFuel
      (inverseCaseTwoBodyBits contracts clockDepth machine advantageExponent
        occurrenceBits)
      (inverseCaseTwoBodyFuel contracts clockDepth machine advantageExponent
        occurrence occurrenceFuel) := by
  intro target hyes caseTwo hbranch point
  have hbits :
      inverseCaseTwoBodyBits contracts clockDepth machine advantageExponent
          occurrenceBits ⟨target, point⟩ =
        bankCaseTwoTargetBitBits target
          (sourceLength
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              target))
          (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              target))
          ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
            (sourceLength
              (inverseChainSourceIndex contracts clockDepth advantageExponent
                target)))
          (inverseChainTwoCopies contracts clockDepth advantageExponent target)
          (encodeBitInput point) (occurrenceBits target)
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point))
          ((List.range
            (inverseChainTwoCopies contracts clockDepth advantageExponent
              target)).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))) := by
    simp only [inverseCaseTwoBodyBits, inverseCaseTwoBranchBits,
      LanguageEvaluationRequest.length, LanguageEvaluationRequest.code]
    rw [dif_pos hyes, hbranch]
  have hfuel :
      inverseCaseTwoBodyFuel contracts clockDepth machine advantageExponent
          occurrence occurrenceFuel ⟨target, point⟩ =
        bankCaseTwoTargetBitFuel (publishedAmplifier contracts).algorithm
          occurrence target
          (inverseChainTwoCopies contracts clockDepth advantageExponent target)
          (encodeBitInput point) (occurrenceFuel target)
          ((List.range
            (inverseChainTwoCopies contracts clockDepth advantageExponent
              target)).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))) := by
    simp only [inverseCaseTwoBodyFuel, inverseCaseTwoBranchFuel,
      LanguageEvaluationRequest.length, LanguageEvaluationRequest.code]
    rw [dif_pos hyes, hbranch]
  exact ⟨hbits.ge, hfuel.ge⟩

/-! ## 3. What the cluster closure still needs -/

set_option maxHeartbeats 1600000 in
-- The statement is the cluster's whole three-way conjunction at one shared
-- envelope, so elaborating it alone exceeds the default budget.
/-- **The bank/diagonal cluster's three residuals, from the occurrence callee
alone.**  `BankResidualClusterClosure.inverse_clusterResiduals_discharged`
carried three cluster premises beside the presentation and the diagonal.  The
row runs are supplied by `BankScheduledRowStageClosure`, the Case-2 envelopes
by §2, and what is left of the three is exactly
`InverseScheduledOccurrenceRuns` — the per-block occurrence callee — beside the
scheduled query-count positivity the published interface does not provide. -/
theorem inverse_clusterResiduals_ofOccurrence
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (occurrence : NPOracleProgram)
    (occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ)
    (hcounts :
      InverseScheduledQueryCounts contracts clockDepth advantageExponent)
    (hoccurrence :
      InverseScheduledOccurrenceRuns contracts clockDepth machine
        advantageExponent occurrence occurrenceBits occurrenceFuel) :
    InverseAtomTableRuns contracts clockDepth machine advantageExponent pcp
        (inverseBankTableProgram contracts clockDepth machine pcp)
        (inverseBankTableBits contracts clockDepth machine advantageExponent
          pcp)
        (inverseBankTableFuel contracts clockDepth machine advantageExponent
          pcp) ∧
      InverseCaseOnePointRuns contracts clockDepth machine advantageExponent
        (inverseChainOneProgram contracts clockDepth machine advantageExponent
          (inverseScheduledRowProgram contracts clockDepth))
        (residualChainBits contracts clockDepth machine advantageExponent
          (inverseScheduledRowBits contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyBits contracts clockDepth machine
            advantageExponent occurrenceBits))
        (residualChainFuel contracts clockDepth machine advantageExponent
          (inverseScheduledRowProgram contracts clockDepth) occurrence
          (inverseScheduledRowFuel contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyFuel contracts clockDepth machine
            advantageExponent occurrence occurrenceFuel)) ∧
      InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
        (inverseChainTwoProgram contracts clockDepth advantageExponent
          occurrence)
        (residualChainBits contracts clockDepth machine advantageExponent
          (inverseScheduledRowBits contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyBits contracts clockDepth machine
            advantageExponent occurrenceBits))
        (residualChainFuel contracts clockDepth machine advantageExponent
          (inverseScheduledRowProgram contracts clockDepth) occurrence
          (inverseScheduledRowFuel contracts clockDepth machine
            advantageExponent)
          (inverseCaseTwoBodyFuel contracts clockDepth machine
            advantageExponent occurrence occurrenceFuel)) :=
  inverse_clusterResiduals_discharged contracts clockDepth machine
    advantageExponent pcp hpresentation hdiagonal
    (inverseScheduledRowProgram contracts clockDepth) occurrence
    (inverseScheduledRowBits contracts clockDepth machine advantageExponent)
    (inverseScheduledRowFuel contracts clockDepth machine advantageExponent)
    occurrenceBits occurrenceFuel
    (inverseCaseTwoBodyBits contracts clockDepth machine advantageExponent
      occurrenceBits)
    (inverseCaseTwoBodyFuel contracts clockDepth machine advantageExponent
      occurrence occurrenceFuel)
    (inverseScheduledRowRuns_ofQueryCounts contracts clockDepth machine
      advantageExponent hcounts)
    hoccurrence
    (inverseCaseTwoBankEnvelopes_ofBranch contracts clockDepth machine
      advantageExponent occurrence occurrenceBits occurrenceFuel)

end NearCubicWires.BankCaseTwoEnvelopeClosure
