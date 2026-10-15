import Proof.Foundations.CanonicalBinary
import Proof.Foundations.RecoveryScheduleEnvelope

/-!
# Canonical q-bit branch provenance

The outer split in this module is performed only after padding the hierarchy
PCP to the canonical width envelope.  Case 1 stores the literal failure of
every small q-bit accepting oracle and derives its amplifier input internally.
Case 2 stores the least accepting q-bit oracle and derives the one source PCPP
table on its native zero-face restriction.  Thus neither branch can substitute
an unrelated hard function, oracle, or occurrence table.
-/

namespace NearCubicWires.ScheduledRecovery

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PhysicalHardness
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduleArithmetic
open NearCubicWires.SourceInterfaces

/-- The sole padded outer PCP used by both branches. -/
def paddedOuterPCP
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    ProjectionPCP source.hierarchyMachine (pairClock clockDepth) :=
  padProjectionPCP outer.pcp.toSemantic
    (widthEnvelope outer) (nativeWidth_le_widthEnvelope outer)

@[simp] theorem paddedOuterPCP_nativeWidth
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (n : ℕ) :
    (paddedOuterPCP outer).nativeWidth n = widthEnvelope outer n :=
  rfl

theorem paddedOuterPCP_complete
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    {n : ℕ} (input : BitInput n)
    (hyes : source.hierarchyMachine.accepts n input) :
    ∃ proof, ∀ randomness,
      (paddedOuterPCP outer).accepts input proof randomness := by
  exact padProjectionPCP_complete outer.pcp.toSemantic
    (widthEnvelope outer) (nativeWidth_le_widthEnvelope outer)
    input (outer.complete n input hyes)

/-- Case 1 retains the exact negation used by the canonical outer split.  Its
amplifier input is derived below, so no hard function is stored independently.
-/
structure ScheduledCaseOneData
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (amplifier : AmplifierWitness)
    (requiredDegree sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) where
  noSmallAcceptingOracle :
    ∀ circuit : BooleanCircuit (scheduledWidth outer sourceIndex),
      circuit.size ≤
          oracleSizeBound requiredDegree
            (scheduledWidth outer sourceIndex) →
        ¬∀ randomness,
          acceptsOracleCircuit (paddedOuterPCP outer)
            input circuit randomness

noncomputable def ScheduledCaseOneData.amplifierInput
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes :
      source.hierarchyMachine.accepts (sourceLength sourceIndex) input) :
    CaseOneInput amplifier :=
  caseOneInputOfNoSmallAcceptingCircuit
    (paddedOuterPCP outer) amplifier
    (oracleSizeBoundConstructible requiredDegree)
    input (paddedOuterPCP_complete outer input hyes)
    data.noSmallAcceptingOracle

@[simp] theorem ScheduledCaseOneData.amplifierInput_seedArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes :
      source.hierarchyMachine.accepts (sourceLength sourceIndex) input) :
    (data.amplifierInput hyes).seedArity =
      scheduledWidth outer sourceIndex := by
  rfl

/-- The canonical q-bit split.  Both alternatives carry their exact source;
there is no public branch-builder callback. -/
inductive ScheduledOuterBranch
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (amplifier : AmplifierWitness)
    (requiredDegree sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) where
  | caseOne :
      ScheduledCaseOneData outer amplifier
        requiredDegree sourceIndex input →
      ScheduledOuterBranch outer amplifier
        requiredDegree sourceIndex input
  | caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input →
      ScheduledOuterBranch outer amplifier
        requiredDegree sourceIndex input

/-- Decide the genuine outer split once, using the least accepting oracle in
Case 2 and the literal negation of its existence in Case 1. -/
noncomputable def scheduledOuterBranch
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (amplifier : AmplifierWitness)
    (requiredDegree sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex))
    (_hyes :
      source.hierarchyMachine.accepts (sourceLength sourceIndex) input) :
    ScheduledOuterBranch outer amplifier
      requiredDegree sourceIndex input := by
  classical
  by_cases hsmall :
      ∃ circuit : BooleanCircuit (scheduledWidth outer sourceIndex),
        circuit.size ≤
            oracleSizeBound requiredDegree
              (scheduledWidth outer sourceIndex) ∧
          ∀ randomness,
            acceptsOracleCircuit (paddedOuterPCP outer)
              input circuit randomness
  · exact .caseTwo <| Classical.choice <|
      existsCanonicalAcceptingOracle
        (paddedOuterPCP outer) input hsmall
  · apply ScheduledOuterBranch.caseOne
    exact
      { noSmallAcceptingOracle := by
          intro circuit hsize haccepts
          exact hsmall ⟨circuit, hsize, haccepts⟩ }

theorem ScheduledCaseOneData.hardCore_arity_le_scaledWidth
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes :
      source.hierarchyMachine.accepts (sourceLength sourceIndex) input) :
    (hardCoreFromCaseOne (data.amplifierInput hyes)).arity ≤
      amplifier.arityCoefficient * scheduledWidth outer sourceIndex := by
  have hsound :=
    amplifier.sound
      (data.amplifierInput hyes).sizeBound
      (data.amplifierInput hyes).constructible
      (data.amplifierInput hyes).seedArity
      (data.amplifierInput hyes).seed
      (data.amplifierInput hyes).worstCaseHard
  rw [hardCoreFromCaseOne_arity]
  calc
    _ ≤ amplifier.arityCoefficient *
        (data.amplifierInput hyes).seedArity := hsound.1
    _ = amplifier.arityCoefficient *
        scheduledWidth outer sourceIndex := by
      rw [data.amplifierInput_seedArity hyes]

theorem rate_le_inverseCopies
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate sourceIndex : ℕ) :
    rate ≤ inverseCopies outer pcppSource rate sourceIndex := by
  have hlog :
      1 ≤ logScale (scheduledWidth outer sourceIndex) :=
    logScale_positive _
  have hblock : 1 ≤ recoveryBlock pcppSource :=
    recoveryBlock_positive pcppSource
  have hstep :
      rate ≤
        recoveryBlock pcppSource *
          (rate * logScale (scheduledWidth outer sourceIndex)) := by
    calc
      rate = 1 * (rate * 1) := by ring
      _ ≤ recoveryBlock pcppSource *
            (rate * logScale (scheduledWidth outer sourceIndex)) :=
        Nat.mul_le_mul hblock (Nat.mul_le_mul_left rate hlog)
  rw [inverseCopies_eq]
  omega

theorem rate_le_fixedCopies
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) :
    rate ≤ fixedCopies pcppSource rate := by
  have hstep : rate ≤ recoveryBlock pcppSource * rate :=
    Nat.le_mul_of_pos_left rate (recoveryBlock_positive pcppSource)
  rw [fixedCopies_eq]
  omega

theorem ScheduledCaseOneData.hardCore_arity_le_inverseEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {amplifier : AmplifierWitness}
    {pcppSource : UniformPointwisePCPPSource}
    {requiredDegree rate scheduleIndex : ℕ}
    {input :
      BitInput (sourceLength (inverseSourceIndex scheduleIndex))}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree (inverseSourceIndex scheduleIndex) input)
    (hyes :
      source.hierarchyMachine.accepts
        (sourceLength (inverseSourceIndex scheduleIndex)) input)
    (hrate : amplifier.arityCoefficient ≤ rate) :
    (hardCoreFromCaseOne (data.amplifierInput hyes)).arity ≤
      (inverseCoreEnvelope outer pcppSource requiredDegree rate).coreArity
        scheduleIndex := by
  have hseed :
      scheduledWidth outer (inverseSourceIndex scheduleIndex) ≤
        seedArity outer pcppSource requiredDegree
          (inverseSourceIndex scheduleIndex) := by
    rw [RecoveryScheduleEnvelope.seedArity]
    omega
  have hraw :
      amplifier.arityCoefficient *
          scheduledWidth outer (inverseSourceIndex scheduleIndex) ≤
        inverseRawCoreArity outer pcppSource
          requiredDegree rate (inverseSourceIndex scheduleIndex) := by
    rw [inverseRawCoreArity]
    exact Nat.mul_le_mul
      (hrate.trans
        (rate_le_inverseCopies
          outer pcppSource rate (inverseSourceIndex scheduleIndex)))
      hseed
  exact
    (data.hardCore_arity_le_scaledWidth hyes).trans <|
      hraw.trans <|
        (inverseCoreEnvelope outer pcppSource
          requiredDegree rate).rawArity_le_coreArity scheduleIndex

theorem ScheduledCaseOneData.hardCore_arity_le_fixedEnvelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {amplifier : AmplifierWitness}
    {pcppSource : UniformPointwisePCPPSource}
    {requiredDegree rate sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes :
      source.hierarchyMachine.accepts (sourceLength sourceIndex) input)
    (hrate : amplifier.arityCoefficient ≤ rate) :
    (hardCoreFromCaseOne (data.amplifierInput hyes)).arity ≤
      (fixedCoreEnvelope outer pcppSource requiredDegree rate).coreArity
        sourceIndex := by
  have hseed :
      scheduledWidth outer sourceIndex ≤
        seedArity outer pcppSource requiredDegree sourceIndex := by
    rw [RecoveryScheduleEnvelope.seedArity]
    omega
  have hraw :
      amplifier.arityCoefficient * scheduledWidth outer sourceIndex ≤
        fixedRawCoreArity outer pcppSource
          requiredDegree rate sourceIndex := by
    rw [fixedRawCoreArity]
    exact Nat.mul_le_mul
      (hrate.trans (rate_le_fixedCopies pcppSource rate))
      hseed
  exact
    (data.hardCore_arity_le_scaledWidth hyes).trans <|
      hraw.trans <|
        (fixedCoreEnvelope outer pcppSource
          requiredDegree rate).rawArity_le_coreArity sourceIndex

/-- The one PCPP table instantiated on the padded oracle's native zero face.
The factory and all quantitative constants remain those selected before the
oracle. -/
noncomputable def caseTwoTable
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    (pcppSource : UniformPointwisePCPPSource)
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    SourceHonestPCPPTable pcppSource
      (outer.pcppCircuit input
        (restrictPaddedOracle caseTwo.circuit
          (nativeWidth_le_widthEnvelope outer
            (sourceLength sourceIndex)))) :=
  Classical.choice <|
    existsSourceHonestPCPPTable pcppSource
      (outer.pcppCircuit input
        (restrictPaddedOracle caseTwo.circuit
          (nativeWidth_le_widthEnvelope outer
            (sourceLength sourceIndex))))
      (outer.pcppCircuit_arity_le_size input
        (restrictPaddedOracle caseTwo.circuit
          (nativeWidth_le_widthEnvelope outer
            (sourceLength sourceIndex))))

/-- The exact Case-2 seed.  Its type is definitionally the source-only arity
used by the common schedule. -/
noncomputable def caseTwoSeed
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    (pcppSource : UniformPointwisePCPPSource)
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    BoolFunction
      (seedArity outer pcppSource requiredDegree sourceIndex) := by
  simpa only [seedArity, scheduledWidth,
    scheduledClauseBits_eq_envelope] using
    (caseTwoTable pcppSource caseTwo).paddedFunction
      outer pcppSource (oracleSizeBound requiredDegree)
      input caseTwo.circuit caseTwo.sizeBounded

theorem caseTwoSeed_complete
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    (pcppSource : UniformPointwisePCPPSource)
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    ∀ randomness : BitInput (scheduledWidth outer sourceIndex),
      let table := caseTwoTable pcppSource caseTwo
      let hclause :=
        table.clauseBits_le_envelope_of_paddedOracle outer pcppSource
          (oracleSizeBound requiredDegree) input caseTwo.circuit
          caseTwo.sizeBounded
      (padClauses table.table.semantic
          (clauseBitsEnvelope outer pcppSource
            (oracleSizeBound requiredDegree) (sourceLength sourceIndex))
          hclause).satisfiedFraction
            (prefixBits
              (nativeWidth_le_widthEnvelope outer
                (sourceLength sourceIndex))
              randomness)
            (table.table.semantic.honestAuxiliary
              (prefixBits
                (nativeWidth_le_widthEnvelope outer
                  (sourceLength sourceIndex))
                randomness)) ≥
        table.table.completeness := by
  intro randomness
  dsimp only
  have hcomplete :=
    (caseTwoTable pcppSource caseTwo).paddedComplete
      outer pcppSource (oracleSizeBound requiredDegree)
      input caseTwo.circuit caseTwo.sizeBounded caseTwo.accepts randomness
  convert hcomplete using 1
  rfl

/-! ## Selector provenance -/

/-- An executable selector for one already-derived smooth envelope.  The
interpreter output is required to equal the canonical first crossing, which
ties all four decoded fields to the same source indices and core function.
This is deliberately stronger than a standalone tuple of jump inequalities.
-/
structure ExecutableEnvelopeSchedule
    {rawArity : ℕ → ℕ} (envelope : SmoothCoreEnvelope rawArity) where
  selector : ExponentialNatProgram ℕ id encodeUnary (fun target => target + 1)
  output_eq : ∀ (target)
    (htarget : envelope.targetOnset ≤ target),
    ExecutableScheduleSelection.decode (selector.execute target) =
      firstCrossingSelection
        (envelope.firstCrossingData target htarget)

def ExecutableEnvelopeSchedule.output
    {rawArity : ℕ → ℕ} {envelope : SmoothCoreEnvelope rawArity}
    (schedule : ExecutableEnvelopeSchedule envelope)
    (target : ℕ) : ExecutableScheduleSelection :=
  ExecutableScheduleSelection.decode (schedule.selector.execute target)

theorem ExecutableEnvelopeSchedule.output_source_succ
    {rawArity : ℕ → ℕ} {envelope : SmoothCoreEnvelope rawArity}
    (schedule : ExecutableEnvelopeSchedule envelope)
    (target : ℕ) (htarget : envelope.targetOnset ≤ target) :
    (schedule.output target).source + 1 =
      (schedule.output target).nextSource := by
  change
    (ExecutableScheduleSelection.decode
        (schedule.selector.execute target)).source + 1 =
      (ExecutableScheduleSelection.decode
        (schedule.selector.execute target)).nextSource
  rw [schedule.output_eq target htarget]
  exact (envelope.firstCrossingData target htarget).source_succ

theorem ExecutableEnvelopeSchedule.output_core_eq
    {rawArity : ℕ → ℕ} {envelope : SmoothCoreEnvelope rawArity}
    (schedule : ExecutableEnvelopeSchedule envelope)
    (target : ℕ) (htarget : envelope.targetOnset ≤ target) :
    (schedule.output target).core =
        envelope.coreArity (schedule.output target).source ∧
      (schedule.output target).nextCore =
        envelope.coreArity (schedule.output target).nextSource := by
  change
    (ExecutableScheduleSelection.decode
        (schedule.selector.execute target)).core =
        envelope.coreArity
          (ExecutableScheduleSelection.decode
            (schedule.selector.execute target)).source ∧
      (ExecutableScheduleSelection.decode
        (schedule.selector.execute target)).nextCore =
        envelope.coreArity
          (ExecutableScheduleSelection.decode
            (schedule.selector.execute target)).nextSource
  rw [schedule.output_eq target htarget]
  exact ⟨rfl, rfl⟩

/-- The selected predecessor is the largest scheduled core still at or below
half the target.  Exposing the stronger inequality keeps the executable
selector aligned with the manuscript's `m ≤ n / 2` schedule, while the
padding layer may continue to consume the weaker `core ≤ target` projection. -/
theorem ExecutableEnvelopeSchedule.output_core_double_le
    {rawArity : ℕ → ℕ} {envelope : SmoothCoreEnvelope rawArity}
    (schedule : ExecutableEnvelopeSchedule envelope)
    (target : ℕ) (htarget : envelope.targetOnset ≤ target) :
    2 * (schedule.output target).core ≤ target := by
  change
    2 * (ExecutableScheduleSelection.decode
      (schedule.selector.execute target)).core ≤ target
  rw [schedule.output_eq target htarget]
  exact (envelope.firstCrossingData target htarget).sourceBelowHalf

/-- The actual interpreter run returns the exact decoded envelope selection. -/
theorem ExecutableEnvelopeSchedule.run_selector
    {rawArity : ℕ → ℕ} {envelope : SmoothCoreEnvelope rawArity}
    (schedule : ExecutableEnvelopeSchedule envelope) (target : ℕ) :
    runNPOracleProgram schedule.selector.program
        (schedule.selector.budget target)
        (schedule.selector.budget target)
        (initialNPOracleState target (encodeUnary target)) =
      some (schedule.output target).code := by
  rw [ExecutableEnvelopeSchedule.output,
    ExecutableScheduleSelection.code_decode]
  exact schedule.selector.run_eq_execute target

/-- The padding consumer sees only the tuple decoded from the fixed selector;
its three inequalities are consequences of the exact first-crossing theorem.
-/
def ExecutableEnvelopeSchedule.select
    {rawArity : ℕ → ℕ} {envelope : SmoothCoreEnvelope rawArity}
    (schedule : ExecutableEnvelopeSchedule envelope)
    (target : ℕ) (htarget : envelope.targetOnset ≤ target) :
    BoundedJumpSelection target where
  core := (schedule.output target).core
  next := (schedule.output target).nextCore
  coreAtMostTarget := by
    change
      (ExecutableScheduleSelection.decode
          (schedule.selector.execute target)).core ≤ target
    rw [schedule.output_eq target htarget]
    exact (envelope.firstCrossingData target htarget).coreAtMostTarget
  crossesHalf := by
    change target < 2 *
      (ExecutableScheduleSelection.decode
        (schedule.selector.execute target)).nextCore
    rw [schedule.output_eq target htarget]
    exact (envelope.firstCrossingData target htarget).crossesHalf
  jumpAtMostSixth := by
    change
      6 * (ExecutableScheduleSelection.decode
          (schedule.selector.execute target)).nextCore ≤
        6 * (ExecutableScheduleSelection.decode
          (schedule.selector.execute target)).core + target
    rw [schedule.output_eq target htarget]
    exact (envelope.firstCrossingData target htarget).jumpAtMostSixth

/-- Opaque projections keep downstream consumers from unfolding the selector
interpreter merely to recover the two public padding inequalities. -/
theorem ExecutableEnvelopeSchedule.output_core_le_target
    {rawArity : ℕ → ℕ} {envelope : SmoothCoreEnvelope rawArity}
    (schedule : ExecutableEnvelopeSchedule envelope)
    (target : ℕ) (htarget : envelope.targetOnset ≤ target) :
    (schedule.output target).core ≤ target :=
  (schedule.select target htarget).coreAtMostTarget

theorem ExecutableEnvelopeSchedule.output_target_lt_three_core
    {rawArity : ℕ → ℕ} {envelope : SmoothCoreEnvelope rawArity}
    (schedule : ExecutableEnvelopeSchedule envelope)
    (target : ℕ) (htarget : envelope.targetOnset ≤ target) :
    target < 3 * (schedule.output target).core :=
  (schedule.select target htarget).target_lt_three_core

/-- The decoded successor is the first core crossing half the target. -/
theorem ExecutableEnvelopeSchedule.output_crosses_half
    {rawArity : ℕ → ℕ} {envelope : SmoothCoreEnvelope rawArity}
    (schedule : ExecutableEnvelopeSchedule envelope)
    (target : ℕ) (htarget : envelope.targetOnset ≤ target) :
    target < 2 * (schedule.output target).nextCore :=
  (schedule.select target htarget).crossesHalf

/-- A target beyond twice the core at a requested source forces the executable
first-crossing selector to choose that source or a later one. -/
theorem ExecutableEnvelopeSchedule.output_source_ge
    {rawArity : ℕ → ℕ} {envelope : SmoothCoreEnvelope rawArity}
    (schedule : ExecutableEnvelopeSchedule envelope)
    (target : ℕ) (htarget : envelope.targetOnset ≤ target)
    (requestedSource : ℕ)
    (hlarge :
      2 * envelope.coreArity requestedSource ≤ target) :
    requestedSource ≤ (schedule.output target).source := by
  by_contra hsource
  have hnextSource :
      (schedule.output target).nextSource ≤ requestedSource := by
    rw [← schedule.output_source_succ target htarget]
    omega
  have hnextCore :
      (schedule.output target).nextCore ≤
        envelope.coreArity requestedSource := by
    rw [(schedule.output_core_eq target htarget).2]
    exact envelope.coreArity_monotone hnextSource
  have hcross := schedule.output_crosses_half target htarget
  omega

end NearCubicWires.ScheduledRecovery
