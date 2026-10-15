import Proof.CaseAnalysis.CaseTwoCanonicalCircuitEncoder
import Proof.MachineModel.RuntimeCaseTwoRequestWordFrame

/-!
# The recovered oracle's own code, at the scheduled branch

`RuntimeCaseTwoRequestWordFrame.inverseSubstitutionRequestWord_ofCircuitEncoding`
cut the Case-2 request word down to `InverseScheduledCircuitEncoding`: one
program emitting `encodeBooleanCircuit caseTwo.circuit` from the public length.
`CaseTwoCanonicalCircuitEncoder.run_canonicalCircuitEncoderProgram` builds that
program out of the published prefix-SAT reducer and one *oracle-free* grouping
decoder, once its own request word

> `pair (generatedBalancedRangeInput descriptionWidth atomStream)
>   (pair nativeWidth sizeBound)`

is on the table.  This module links the two.

The request word above is exactly the frame-lowering stage that
`BankEmittedAtomLoop.InverseFrameAdapterRuns` already names on the selector
side — the coordinate count, the emitter's atom stream and two numerals, all
read from the schedule.  It enters here as one named premise with the same
shape, so the resulting statement is honest about what is still open: the
description frame and the grouping decoder, and nothing else.
-/

namespace NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoCanonicalCircuitEncoder
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeCaseTwoRequestWordFrame
open NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The description frame -/

/-- The scheduled bounded-oracle size bound, as a function of the padded
outer PCP's native width. -/
noncomputable def inverseOracleSizeBound
    (contracts : PublishedContracts) (advantageExponent : ℝ) : ℕ → ℕ :=
  oracleSizeBound
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))

/-- **The description-frame premise.**  One stage that, from the requested
public length alone, emits the description pool's own request word: the
coordinate count and the emitter's atom stream, beside the padded native width
and the scheduled size bound.

Nothing in this premise mentions the branch: the frame is a function of the
target, exactly as `BankEmittedAtomLoop.InverseFrameAdapterRuns` is on the
selector side. -/
def InverseDescriptionFrameRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (adapter : NPOracleProgram) (adapterBits adapterFuel : ℕ → ℕ) : Prop :=
  ∀ (target : ℕ),
    inverseCaseOneTargetOnset contracts
      (publishedHierarchyOuterPCP contracts clockDepth)
      advantageExponent ≤ target →
    runNPOracleProgram adapter (adapterBits target) (adapterFuel target)
        (initialNPOracleState target target) =
      some
        (canonicalCircuitEncoderInput
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target)
          (inverseOracleSizeBound contracts advantageExponent))

/-! ## 2. The encoder at the schedule -/

/-- The published circuit-code stream: the description frame, then the pooled
encoder of `CaseTwoCanonicalCircuitEncoder`. -/
def inverseCircuitEncodingProgram (adapter decoder : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms adapter (canonicalCircuitEncoderProgram decoder)

open Classical in
/-- The encoder's clock at one target, a branch read because the pool's own
budgets are stated at the oracle the branch carries. -/
noncomputable def inverseCircuitEncodingFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (decoder : NPOracleProgram) (decoderFuel : ℕ → ℕ → ℕ)
    (adapterFuel : ℕ → ℕ) (target : ℕ) : ℕ :=
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
        linkFuel (canonicalCircuitEncoderProgram decoder) (adapterFuel target)
          (canonicalCircuitEncoderFuel
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo decoder decoderFuel target)
  else 0

open Classical in
/-- The encoder's width at one target, a branch read for the same reason. -/
noncomputable def inverseCircuitEncodingBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (decoderBits : ℕ → ℕ → ℕ) (adapterBits : ℕ → ℕ) (target : ℕ) : ℕ :=
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
        occurrenceStageBits target (adapterBits target)
          (canonicalCircuitEncoderBits
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo decoderBits target)
  else 0

set_option maxHeartbeats 800000 in
-- The statement carries the linked encoder and both branch envelopes at one
-- target, so elaborating it alone exceeds the default budget.
/-- **The recovered oracle's own code, from two premises.**  Given the
description frame and the oracle-free grouping decoder, one fixed stream emits
`encodeBooleanCircuit caseTwo.circuit` from the requested public length.  Every
SAT query in it is the published prefix-SAT reducer's. -/
theorem inverseScheduledCircuitEncoding_ofDecoder
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (adapter decoder : NPOracleProgram) (adapterBits adapterFuel : ℕ → ℕ)
    (decoderBits decoderFuel : ℕ → ℕ → ℕ)
    (hadapter :
      InverseDescriptionFrameRuns contracts clockDepth machine advantageExponent
        adapter adapterBits adapterFuel)
    (hdecoder : CanonicalDescriptionDecoder decoder decoderBits decoderFuel) :
    InverseScheduledCircuitEncoding contracts clockDepth machine
      advantageExponent (inverseCircuitEncodingProgram adapter decoder)
      (inverseCircuitEncodingBits contracts clockDepth machine advantageExponent
        decoderBits adapterBits)
      (inverseCircuitEncodingFuel contracts clockDepth machine advantageExponent
        decoder decoderFuel adapterFuel) := by
  intro target hlarge hyes caseTwo hbranch
  have hframe := hadapter target hlarge
  have hencoder :=
    run_canonicalCircuitEncoderProgram
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target)
      caseTwo decoder decoderBits decoderFuel hdecoder target
  have hbits :
      inverseCircuitEncodingBits contracts clockDepth machine advantageExponent
          decoderBits adapterBits target =
        occurrenceStageBits target (adapterBits target)
          (canonicalCircuitEncoderBits
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo decoderBits target) := by
    simp only [inverseCircuitEncodingBits]
    rw [dif_pos hyes, hbranch]
  have hfuel :
      inverseCircuitEncodingFuel contracts clockDepth machine advantageExponent
          decoder decoderFuel adapterFuel target =
        linkFuel (canonicalCircuitEncoderProgram decoder) (adapterFuel target)
          (canonicalCircuitEncoderFuel
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo decoder decoderFuel target) := by
    simp only [inverseCircuitEncodingFuel]
    rw [dif_pos hyes, hbranch]
  rw [hbits, hfuel, inverseCircuitEncodingProgram]
  exact run_occurrenceStage hframe hencoder

/-! ## 3. The request word, from the same two premises -/

set_option maxHeartbeats 1600000 in
-- The statement is the whole request word at the linked encoder, so
-- elaborating it alone exceeds the default budget.
/-- **The Case-2 request word, from the description frame and the decoder.**
Composing §2 with `RuntimeCaseTwoRequestWordFrame`: the request word
`InverseSubstitutionRequestWord` needs the schedule diagonal, one description
frame and one oracle-free grouping decoder — no substitution, no restriction,
no arity padding, and no numeral of its own. -/
theorem inverseSubstitutionRequestWord_ofDecoder
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target =
        sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
    (adapter decoder : NPOracleProgram) (adapterBits adapterFuel : ℕ → ℕ)
    (decoderBits decoderFuel : ℕ → ℕ → ℕ)
    (hadapter :
      InverseDescriptionFrameRuns contracts clockDepth machine advantageExponent
        adapter adapterBits adapterFuel)
    (hdecoder : CanonicalDescriptionDecoder decoder decoderBits decoderFuel) :
    InverseSubstitutionRequestWord contracts clockDepth machine
      advantageExponent
      (inverseSubstitutionRequestProgram contracts clockDepth machine
        advantageExponent (inverseCircuitEncodingProgram adapter decoder))
      (inverseSubstitutionRequestBits contracts clockDepth machine
        advantageExponent
        (inverseCircuitEncodingBits contracts clockDepth machine
          advantageExponent decoderBits adapterBits))
      (inverseSubstitutionRequestFuel contracts clockDepth machine
        advantageExponent (inverseCircuitEncodingProgram adapter decoder)
        (inverseCircuitEncodingFuel contracts clockDepth machine
          advantageExponent decoder decoderFuel adapterFuel)) :=
  inverseSubstitutionRequestWord_ofCircuitEncoding contracts clockDepth machine
    advantageExponent hdiagonal (inverseCircuitEncodingProgram adapter decoder)
    (inverseCircuitEncodingBits contracts clockDepth machine advantageExponent
      decoderBits adapterBits)
    (inverseCircuitEncodingFuel contracts clockDepth machine advantageExponent
      decoder decoderFuel adapterFuel)
    (inverseScheduledCircuitEncoding_ofDecoder contracts clockDepth machine
      advantageExponent adapter decoder adapterBits adapterFuel decoderBits
      decoderFuel hadapter hdecoder)

/-! ## 4. The bank cluster's encoder premise -/

set_option maxHeartbeats 1600000 in
-- The statement is the cluster's encoder premise at the whole linked stream,
-- so elaborating it alone exceeds the default budget.
/-- **The cluster's encoder premise, from the description frame and the
decoder.**  This is the premise
`RuntimeCaseTwoOccurrenceEncodingClosure.inverse_clusterResiduals_ofEncoding`
consumes, and the diagonal hypothesis is stated in the cluster's own form, so
no new hypothesis is introduced between the two.  Restriction, substitution,
arity padding, the three request numerals and the per-coordinate SAT recovery
are all discharged; what remains of the Case-2 encoder is the description frame
and one oracle-free grouping decoder. -/
theorem inverseScheduledOccurrenceEncoding_ofDecoder
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (adapter decoder : NPOracleProgram) (adapterBits adapterFuel : ℕ → ℕ)
    (decoderBits decoderFuel : ℕ → ℕ → ℕ)
    (hadapter :
      InverseDescriptionFrameRuns contracts clockDepth machine advantageExponent
        adapter adapterBits adapterFuel)
    (hdecoder : CanonicalDescriptionDecoder decoder decoderBits decoderFuel) :
    InverseScheduledOccurrenceEncoding contracts clockDepth machine
      advantageExponent
      (inverseSubstitutedEncodingProgram contracts clockDepth
        (inverseSubstitutionRequestProgram contracts clockDepth machine
          advantageExponent (inverseCircuitEncodingProgram adapter decoder)))
      (inverseSubstitutedEncodingBits contracts clockDepth machine
        advantageExponent
        (inverseSubstitutionRequestBits contracts clockDepth machine
          advantageExponent
          (inverseCircuitEncodingBits contracts clockDepth machine
            advantageExponent decoderBits adapterBits)))
      (inverseSubstitutedEncodingFuel contracts clockDepth machine
        advantageExponent
        (inverseSubstitutionRequestFuel contracts clockDepth machine
          advantageExponent (inverseCircuitEncodingProgram adapter decoder)
          (inverseCircuitEncodingFuel contracts clockDepth machine
            advantageExponent decoder decoderFuel adapterFuel))) :=
  inverseScheduledOccurrenceEncoding_ofRequestWord contracts clockDepth machine
    advantageExponent
    (inverseSubstitutionRequestProgram contracts clockDepth machine
      advantageExponent (inverseCircuitEncodingProgram adapter decoder))
    (inverseSubstitutionRequestBits contracts clockDepth machine
      advantageExponent
      (inverseCircuitEncodingBits contracts clockDepth machine
        advantageExponent decoderBits adapterBits))
    (inverseSubstitutionRequestFuel contracts clockDepth machine
      advantageExponent (inverseCircuitEncodingProgram adapter decoder)
      (inverseCircuitEncodingFuel contracts clockDepth machine
        advantageExponent decoder decoderFuel adapterFuel))
    (inverseSubstitutionRequestWord_ofDecoder contracts clockDepth machine
      advantageExponent hdiagonal adapter decoder adapterBits adapterFuel
      decoderBits decoderFuel hadapter hdecoder)

end NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
