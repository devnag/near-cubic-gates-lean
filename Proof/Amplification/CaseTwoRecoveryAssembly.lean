import Proof.Amplification.CaseOneRecoveryAssembly

/-!
# Published Case-2 recovery assembly

This module isolates the only semantic bridge required from the concrete
balanced approximation machine.  Once that machine accepts every legal
approximation of the scheduled seed and rejects the selected refuter word, the
published XOR contract produces one common hard core for both circuit families.
-/

namespace NearCubicWires.CaseTwoRecoveryAssembly

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseOneScheduleLedger
open NearCubicWires.CircuitRestriction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PhysicalHardness
open NearCubicWires.PhysicalRecovery
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-- The unique XOR witness selected from the published joint refuter row. -/
noncomputable def publishedXorWitness
    (contracts : PublishedContracts) : XorAmplificationWitness :=
  Classical.choice <|
    existsXorAmplificationWitness contracts.refuterAndXor.2

/-- **The published Case-2 approximation radius.**  It is the repaired radius
of the pointwise-PCPP source the schedule selects, i.e. the validity constant
of the parameter package the componentwise verifier runs at.  The fixed literal
`RecoveryScheduleEnvelope.recoveryDelta = 1 / 4` cannot serve here: it violates
the verifier's completeness seam by a factor above `576`
(`VerifierThresholdSeam.recoveryDelta_not_le_threeZeta`). -/
noncomputable def publishedRecoveryDelta (contracts : PublishedContracts) : ℝ :=
  repairedDelta (publishedPointwisePCPP contracts)

theorem publishedRecoveryDelta_nonnegative (contracts : PublishedContracts) :
    0 ≤ publishedRecoveryDelta contracts :=
  repairedDelta_nonnegative (publishedPointwisePCPP contracts)

theorem publishedRecoveryDelta_belowHalf (contracts : PublishedContracts) :
    publishedRecoveryDelta contracts < 1 / 2 :=
  repairedDelta_belowHalf (publishedPointwisePCPP contracts)

theorem publishedRecoveryDelta_le_quarter (contracts : PublishedContracts) :
    publishedRecoveryDelta contracts ≤ 1 / 4 :=
  repairedDelta_le_quarter (publishedPointwisePCPP contracts)

/-- The migration is not a no-op: the published radius is strictly below the
retired literal. -/
theorem publishedRecoveryDelta_ne_recoveryDelta
    (contracts : PublishedContracts) :
    publishedRecoveryDelta contracts ≠ recoveryDelta :=
  repairedDelta_ne_recoveryDelta (publishedPointwisePCPP contracts)

/-- Exact disjoint union decoded by the concrete balanced machine.  Naming
this proposition keeps the executable witness policy and the semantic
acceptance obligation on one shared set of limits. -/
noncomputable def PublishedLegalApproximation
    (contracts : PublishedContracts)
    {seedArity : ℕ} (seed : BoolFunction seedArity)
    (copies symmetricSize thresholdSize : ℕ)
    : Prop :=
  HasEitherLegalApproximation symmetricWireFamily thresholdWireFamily seed
      symmetricSize
        ⌈(publishedXorWitness contracts).termCoefficient
              (publishedRecoveryDelta contracts) *
            seedArity /
          xorEpsilon (publishedRecoveryDelta contracts) copies ^ 2⌉₊
        (xorCoefficientBitBound
          (publishedXorWitness contracts).coefficientBitCoefficient
          (publishedXorWitness contracts).coefficientBitDegree
          (publishedRecoveryDelta contracts)
          seedArity)
      thresholdSize
        ⌈(publishedXorWitness contracts).termCoefficient
              (publishedRecoveryDelta contracts) *
            seedArity /
          xorEpsilon (publishedRecoveryDelta contracts) copies ^ 2⌉₊
        (xorCoefficientBitBound
          (publishedXorWitness contracts).coefficientBitCoefficient
          (publishedXorWitness contracts).coefficientBitDegree
          (publishedRecoveryDelta contracts)
          seedArity)
      ((publishedXorWitness contracts).massCoefficient
          (publishedRecoveryDelta contracts) /
        xorEpsilon (publishedRecoveryDelta contracts) copies)
      ((publishedXorWitness contracts).massCoefficient
          (publishedRecoveryDelta contracts) /
        xorEpsilon (publishedRecoveryDelta contracts) copies)
      (publishedRecoveryDelta contracts)

/-- Exact semantic obligation of the concrete balanced machine.  It must turn
either legal componentwise approximation of this seed into acceptance of the
same encoded refuter input; no independent semantic callback is admitted. -/
noncomputable def PublishedApproximationAcceptance
    (contracts : PublishedContracts)
    {seedArity inputArity : ℕ} (seed : BoolFunction seedArity)
    (copies symmetricSize thresholdSize : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (input : BitInput inputArity) : Prop :=
  PublishedLegalApproximation contracts seed copies symmetricSize
      thresholdSize →
    machine.toSemantic.accepts input

/-- Rejection converts the concrete machine's single acceptance theorem into
the two simultaneous far-from-sums premises consumed by the XOR theorem. -/
private noncomputable def publishedCommonCoreOfMachineRejection
    (contracts : PublishedContracts)
    {seedArity inputArity : ℕ} (seed : BoolFunction seedArity)
    (copies symmetricSize thresholdSize : ℕ)
    (hcopies : 1 ≤ copies)
    (machine : ExecutableWeakNondeterministicMachine)
    (input : BitInput inputArity)
    (haccepts : PublishedApproximationAcceptance contracts seed copies
      symmetricSize thresholdSize machine input)
    (hrejects : ¬machine.toSemantic.accepts input) :
    CommonHardCore symmetricWireFamily thresholdWireFamily :=
  commonHardCoreFromXor
    (commonXorInputOfMachineRejection (publishedXorWitness contracts) seed
      copies symmetricSize thresholdSize (publishedRecoveryDelta contracts)
      (publishedRecoveryDelta_nonnegative contracts)
      (publishedRecoveryDelta_belowHalf contracts) hcopies machine input
      haccepts hrejects)
    symmetricWireFamily_restrictionClosed.toSourceFamily
    thresholdWireFamily_restrictionClosed.toSourceFamily
    symmetricWireFamily_negationClosed
    thresholdWireFamily_negationClosed

@[simp] private theorem publishedCommonCoreOfMachineRejection_arity
    (contracts : PublishedContracts)
    {seedArity inputArity : ℕ} (seed : BoolFunction seedArity)
    (copies symmetricSize thresholdSize : ℕ)
    (hcopies : 1 ≤ copies)
    (machine : ExecutableWeakNondeterministicMachine)
    (input : BitInput inputArity)
    (haccepts : PublishedApproximationAcceptance contracts seed copies
      symmetricSize thresholdSize machine input)
    (hrejects : ¬machine.toSemantic.accepts input) :
    (publishedCommonCoreOfMachineRejection contracts seed copies symmetricSize
      thresholdSize hcopies machine input haccepts hrejects).arity =
        copies * seedArity := by
  rfl

@[simp] private theorem publishedCommonCoreOfMachineRejection_advantage
    (contracts : PublishedContracts)
    {seedArity inputArity : ℕ} (seed : BoolFunction seedArity)
    (copies symmetricSize thresholdSize : ℕ)
    (hcopies : 1 ≤ copies)
    (machine : ExecutableWeakNondeterministicMachine)
    (input : BitInput inputArity)
    (haccepts : PublishedApproximationAcceptance contracts seed copies
      symmetricSize thresholdSize machine input)
    (hrejects : ¬machine.toSemantic.accepts input) :
    (publishedCommonCoreOfMachineRejection contracts seed copies symmetricSize
      thresholdSize hcopies machine input haccepts hrejects).advantage =
        xorEpsilon (publishedRecoveryDelta contracts) copies := by
  rfl

/-- Exact per-family caps requested from the inverse-schedule approximation
machine.  They are stated at the smooth common arity used by the language. -/
noncomputable def inverseCaseTwoSymmetricSize
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ) : ℕ :=
  ⌊wireScale (inversePhysicalCoefficient contracts outer advantagePower) 10
    ((inverseEnvelope contracts outer advantagePower).coreArity
      scheduleIndex)⌋₊

noncomputable def inverseCaseTwoThresholdSize
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ) : ℕ :=
  ⌊wireScale (inversePhysicalCoefficient contracts outer advantagePower) 12
    ((inverseEnvelope contracts outer advantagePower).coreArity
      scheduleIndex)⌋₊

/-- Schedule-specialized form of the sole concrete-machine obligation. -/
noncomputable def InverseCaseTwoAcceptance
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine) : Prop :=
  PublishedApproximationAcceptance contracts
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts advantagePower)
      (inverseSourceIndex scheduleIndex))
    (inverseCaseTwoSymmetricSize contracts outer advantagePower scheduleIndex)
    (inverseCaseTwoThresholdSize contracts outer advantagePower scheduleIndex)
    machine input

/-- Raw scheduled Case-2 core.  Its only proof input is the exact acceptance
theorem of the concrete machine; rejection comes from the published refuter. -/
private noncomputable def inverseCaseTwoCommonCore
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : InverseCaseTwoAcceptance contracts outer advantagePower
      scheduleIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    CommonHardCore symmetricWireFamily thresholdWireFamily :=
  publishedCommonCoreOfMachineRejection contracts
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    (inverseCopies outer (publishedPointwisePCPP contracts)
      (inverseRate contracts advantagePower)
      (inverseSourceIndex scheduleIndex))
    (inverseCaseTwoSymmetricSize contracts outer advantagePower scheduleIndex)
    (inverseCaseTwoThresholdSize contracts outer advantagePower scheduleIndex)
    (inverseCopies_positive outer (publishedPointwisePCPP contracts)
      (inverseRate contracts advantagePower)
      (inverseSourceIndex scheduleIndex))
    machine input haccepts hrejects

@[simp] private theorem inverseCaseTwoCommonCore_arity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : InverseCaseTwoAcceptance contracts outer advantagePower
      scheduleIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    (inverseCaseTwoCommonCore contracts outer advantagePower scheduleIndex
      caseTwo machine haccepts hrejects).arity =
      inverseScheduledRawCoreArity outer
        (publishedPointwisePCPP contracts)
        (inverseRequiredDegree contracts advantagePower)
        (inverseRate contracts advantagePower) scheduleIndex := by
  rfl

@[simp] private theorem inverseCaseTwoCommonCore_advantage
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : InverseCaseTwoAcceptance contracts outer advantagePower
      scheduleIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    (inverseCaseTwoCommonCore contracts outer advantagePower scheduleIndex
      caseTwo machine haccepts hrejects).advantage =
      xorEpsilon (publishedRecoveryDelta contracts)
        (inverseCopies outer (publishedPointwisePCPP contracts)
          (inverseRate contracts advantagePower)
          (inverseSourceIndex scheduleIndex)) := by
  rfl

/-- Smooth the raw XOR core to the same arity used by Case 1, preserving both
physical size ledgers and the exact XOR advantage. -/
private noncomputable def inversePaddedCaseTwoCommonCore
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : InverseCaseTwoAcceptance contracts outer advantagePower
      scheduleIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    CommonHardCore symmetricWireFamily thresholdWireFamily :=
  let raw := inverseCaseTwoCommonCore contracts outer advantagePower
    scheduleIndex caseTwo machine haccepts hrejects
  padCommonHardCore symmetricWireFamily_restrictionClosed
    thresholdWireFamily_restrictionClosed raw
    ((inverseEnvelope contracts outer advantagePower).coreArity scheduleIndex)
    (by
      rw [inverseCaseTwoCommonCore_arity]
      exact (inverseEnvelope contracts outer advantagePower)
        |>.rawArity_le_coreArity scheduleIndex)

/-- Restrict the padded common core to the exact physical headline caps. -/
private noncomputable def inverseCaseTwoPhysicalCore
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : InverseCaseTwoAcceptance contracts outer advantagePower
      scheduleIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    PhysicalCommonCore
      (inversePhysicalCoefficient contracts outer advantagePower)
      (inversePhysicalCoefficient contracts outer advantagePower)
      10 12
      ((inverseEnvelope contracts outer advantagePower).coreArity
        scheduleIndex) := by
  let padded := inversePaddedCaseTwoCommonCore contracts outer advantagePower
    scheduleIndex caseTwo machine haccepts hrejects
  apply physicalCommonCoreOfCommon padded
    (inversePhysicalCoefficient contracts outer advantagePower)
    (inversePhysicalCoefficient contracts outer advantagePower) 10 12
  · rfl
  · rfl

@[simp] private theorem inverseCaseTwoPhysicalCore_advantage
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : InverseCaseTwoAcceptance contracts outer advantagePower
      scheduleIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    (inverseCaseTwoPhysicalCore contracts outer advantagePower scheduleIndex
      caseTwo machine haccepts hrejects).advantage =
      xorEpsilon (publishedRecoveryDelta contracts)
        (inverseCopies outer (publishedPointwisePCPP contracts)
          (inverseRate contracts advantagePower)
          (inverseSourceIndex scheduleIndex)) := by
  rfl

/-- The inverse XOR schedule pays the same exact smooth-core advantage as the
Case-1 amplifier after the shared numeric onset. -/
private theorem inverseCaseTwoPhysicalCore_advantage_le
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput
      (sourceLength (inverseSourceIndex scheduleIndex))}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : InverseCaseTwoAcceptance contracts outer advantagePower
      scheduleIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input)
    (hready :
      inverseCaseOneOnset contracts outer advantagePower ≤ scheduleIndex) :
    (inverseCaseTwoPhysicalCore contracts outer advantagePower scheduleIndex
      caseTwo machine haccepts hrejects).advantage ≤
      inversePolynomialAdvantage
        ((inverseEnvelope contracts outer advantagePower).coreArity
          scheduleIndex)
        (advantagePower : ℝ) := by
  let pcppSource := publishedPointwisePCPP contracts
  let requiredDegree := inverseRequiredDegree contracts advantagePower
  let rate := inverseRate contracts advantagePower
  let sourceIndex := inverseSourceIndex scheduleIndex
  let width := scheduledWidth outer sourceIndex
  let core :=
    (inverseEnvelope contracts outer advantagePower).coreArity scheduleIndex
  rw [inverseCaseTwoPhysicalCore_advantage]
  change
    xorEpsilon (repairedDelta pcppSource)
        (inverseCopies outer pcppSource rate sourceIndex) ≤
      inversePolynomialAdvantage core (advantagePower : ℝ)
  have hwidth : 0 < width := by
    exact (sourceIndex_succ_le_scheduledWidth outer sourceIndex).trans_lt' <|
      by omega
  have hcore : 0 < core := by
    dsimp only [core, inverseEnvelope]
    rw [inverseCoreEnvelope_coreArity]
    exact Nat.mul_pos
      (inverseTightCoreCoefficient_positive
        outer pcppSource requiredDegree rate) (by omega)
  have honset :
      inverseCaseOnePowerOnset outer pcppSource requiredDegree rate
          advantagePower ≤ scheduleIndex := by
    exact (le_max_right _ _).trans <| (le_max_right 5 _).trans hready
  have hcorePower :
      core ^ advantagePower ≤ width ^ (2 * advantagePower + 1) := by
    exact inverseCore_power_le_scheduledWidth outer pcppSource requiredDegree
      rate scheduleIndex advantagePower honset
  have hexponent : 2 * advantagePower + 1 ≤ rate := by
    exact le_max_right _ _
  have hpower : core ^ advantagePower ≤ width ^ rate :=
    hcorePower.trans (Nat.pow_le_pow_right (by omega) hexponent)
  calc
    xorEpsilon (repairedDelta pcppSource)
          (inverseCopies outer pcppSource rate sourceIndex) ≤
        1 / (2 : ℝ) ^ (rate * logScale width) / 4 := by
      exact xorEpsilon_inverseCopies_le outer pcppSource rate sourceIndex
    _ ≤ inversePolynomialAdvantage width (rate : ℝ) :=
      inverseGeometricBound_le_inversePolynomialAdvantage width rate hwidth
    _ ≤ inversePolynomialAdvantage core (advantagePower : ℝ) :=
      inversePolynomialAdvantage_le_of_pow_le width core rate advantagePower
        hwidth hcore hpower

/-- Fixed-rate physical caps at the shared smooth arity. -/
noncomputable def fixedCaseTwoSymmetricSize
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ) : ℕ :=
  ⌊wireScale (fixedPhysicalCoefficient contracts outer requestedRate) 5
    ((fixedEnvelope contracts outer requestedRate).coreArity sourceIndex)⌋₊

noncomputable def fixedCaseTwoThresholdSize
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ) : ℕ :=
  ⌊wireScale (fixedPhysicalCoefficient contracts outer requestedRate) 9
    ((fixedEnvelope contracts outer requestedRate).coreArity sourceIndex)⌋₊

noncomputable def FixedCaseTwoAcceptance
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine) : Prop :=
  PublishedApproximationAcceptance contracts
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    (fixedCopies (publishedPointwisePCPP contracts)
      (fixedRate contracts requestedRate))
    (fixedCaseTwoSymmetricSize contracts outer requestedRate sourceIndex)
    (fixedCaseTwoThresholdSize contracts outer requestedRate sourceIndex)
    machine input

private noncomputable def fixedCaseTwoCommonCore
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : FixedCaseTwoAcceptance contracts outer requestedRate
      sourceIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    CommonHardCore symmetricWireFamily thresholdWireFamily :=
  publishedCommonCoreOfMachineRejection contracts
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    (fixedCopies (publishedPointwisePCPP contracts)
      (fixedRate contracts requestedRate))
    (fixedCaseTwoSymmetricSize contracts outer requestedRate sourceIndex)
    (fixedCaseTwoThresholdSize contracts outer requestedRate sourceIndex)
    (fixedCopies_positive (publishedPointwisePCPP contracts)
      (fixedRate contracts requestedRate))
    machine input haccepts hrejects

@[simp] private theorem fixedCaseTwoCommonCore_arity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : FixedCaseTwoAcceptance contracts outer requestedRate
      sourceIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    (fixedCaseTwoCommonCore contracts outer requestedRate sourceIndex caseTwo
      machine haccepts hrejects).arity =
      fixedRawCoreArity outer (publishedPointwisePCPP contracts)
        (fixedRequiredDegree contracts requestedRate)
        (fixedRate contracts requestedRate) sourceIndex := by
  rfl

@[simp] private theorem fixedCaseTwoCommonCore_advantage
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : FixedCaseTwoAcceptance contracts outer requestedRate
      sourceIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    (fixedCaseTwoCommonCore contracts outer requestedRate sourceIndex caseTwo
      machine haccepts hrejects).advantage =
      xorEpsilon (publishedRecoveryDelta contracts)
        (fixedCopies (publishedPointwisePCPP contracts)
          (fixedRate contracts requestedRate)) := by
  rfl

private noncomputable def fixedPaddedCaseTwoCommonCore
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : FixedCaseTwoAcceptance contracts outer requestedRate
      sourceIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    CommonHardCore symmetricWireFamily thresholdWireFamily :=
  let raw := fixedCaseTwoCommonCore contracts outer requestedRate sourceIndex
    caseTwo machine haccepts hrejects
  padCommonHardCore symmetricWireFamily_restrictionClosed
    thresholdWireFamily_restrictionClosed raw
    ((fixedEnvelope contracts outer requestedRate).coreArity sourceIndex)
    (by
      rw [fixedCaseTwoCommonCore_arity]
      exact (fixedEnvelope contracts outer requestedRate)
        |>.rawArity_le_coreArity sourceIndex)

private noncomputable def fixedCaseTwoPhysicalCore
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : FixedCaseTwoAcceptance contracts outer requestedRate
      sourceIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    PhysicalCommonCore
      (fixedPhysicalCoefficient contracts outer requestedRate)
      (fixedPhysicalCoefficient contracts outer requestedRate)
      5 9
      ((fixedEnvelope contracts outer requestedRate).coreArity sourceIndex) := by
  let padded := fixedPaddedCaseTwoCommonCore contracts outer requestedRate
    sourceIndex caseTwo machine haccepts hrejects
  apply physicalCommonCoreOfCommon padded
    (fixedPhysicalCoefficient contracts outer requestedRate)
    (fixedPhysicalCoefficient contracts outer requestedRate) 5 9
  · rfl
  · rfl

@[simp] private theorem fixedCaseTwoPhysicalCore_advantage
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : FixedCaseTwoAcceptance contracts outer requestedRate
      sourceIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    (fixedCaseTwoPhysicalCore contracts outer requestedRate sourceIndex caseTwo
      machine haccepts hrejects).advantage =
      xorEpsilon (publishedRecoveryDelta contracts)
        (fixedCopies (publishedPointwisePCPP contracts)
          (fixedRate contracts requestedRate)) := by
  rfl

private theorem fixedCaseTwoPhysicalCore_advantage_le
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input)
    (machine : ExecutableWeakNondeterministicMachine)
    (haccepts : FixedCaseTwoAcceptance contracts outer requestedRate
      sourceIndex caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts input) :
    (fixedCaseTwoPhysicalCore contracts outer requestedRate sourceIndex caseTwo
      machine haccepts hrejects).advantage ≤
      1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4 := by
  rw [fixedCaseTwoPhysicalCore_advantage]
  exact xorEpsilon_fixedCopies_le (publishedPointwisePCPP contracts)
    (fixedRate contracts requestedRate)

/-- Target-length inverse Case-2 function, using the identical selector and
padding inequalities as Case 1. -/
private noncomputable def inverseCaseTwoTargetFunction
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (htarget :
      (inverseEnvelope contracts outer
        (inverseCoreAdvantagePower advantageExponent)).targetOnset ≤ target)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP outer)
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (haccepts : InverseCaseTwoAcceptance contracts outer
      (inverseCoreAdvantagePower advantageExponent)
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target)
      caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts
      (inverseRefuterInput contracts outer machine advantageExponent target)) :
    BoolFunction target :=
  let power := inverseCoreAdvantagePower advantageExponent
  let scheduleIndex := inverseSelectedSource contracts outer power target
  let core := inverseCaseTwoPhysicalCore contracts outer power scheduleIndex
    caseTwo machine haccepts hrejects
  padCore core.function
    (inverseSelectedCoreBounds contracts outer power target htarget).1

/-- Complete inverse Case-2 physical hardness once the concrete balanced
machine's single approximation-acceptance theorem is supplied. -/
private theorem inverseCaseTwoTargetHardness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP outer)
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (haccepts : InverseCaseTwoAcceptance contracts outer
      (inverseCoreAdvantagePower advantageExponent)
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target)
      caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts
      (inverseRefuterInput contracts outer machine advantageExponent target)) :
    ∀ mode,
      PaddedPhysicalModeHardness
        (inversePolynomialAdvantage target (advantageExponent + 1))
        (inversePhysicalCoefficient contracts outer
          (inverseCoreAdvantagePower advantageExponent))
        (inversePhysicalCoefficient contracts outer
          (inverseCoreAdvantagePower advantageExponent))
        10 12 mode
        (inverseCaseTwoTargetFunction contracts outer machine
          advantageExponent target
          (inverseCaseOneTargetOnset_ready contracts outer advantageExponent
            target hlarge).1
          caseTwo haccepts hrejects) := by
  let power := inverseCoreAdvantagePower advantageExponent
  let scheduleIndex := inverseSelectedSource contracts outer power target
  let ready :=
    inverseCaseOneTargetOnset_ready contracts outer advantageExponent target
      hlarge
  let bounds :=
    inverseSelectedCoreBounds contracts outer power target ready.1
  let core := inverseCaseTwoPhysicalCore contracts outer power scheduleIndex
    caseTwo machine haccepts hrejects
  have hpadded :=
    padPhysicalCommonCore
      (le_of_lt (inversePhysicalCoefficient_positive contracts outer power))
      (le_of_lt (inversePhysicalCoefficient_positive contracts outer power))
      10 12 target bounds.1 bounds.2 core
  have hcoreAdvantage :
      core.advantage ≤
        inversePolynomialAdvantage
          ((inverseEnvelope contracts outer power).coreArity scheduleIndex)
          (power : ℝ) :=
    inverseCaseTwoPhysicalCore_advantage_le contracts outer power
      scheduleIndex caseTwo machine haccepts hrejects ready.2.1
  have htargetAdvantage :
      inversePolynomialAdvantage
          ((inverseEnvelope contracts outer power).coreArity scheduleIndex)
          (power : ℝ) ≤
        inversePolynomialAdvantage target (advantageExponent + 1) := by
    exact scheduledInverseAdvantage_le_target
      (inverseSchedule contracts outer power) advantageExponent target
      ready.1 ready.2.2
  intro mode
  exact paddedPhysicalModeHardness_mono
    (hcoreAdvantage.trans htargetAdvantage) (hpadded mode)

/-- Fixed-rate Case-2 target function. -/
private noncomputable def fixedCaseTwoTargetFunction
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (htarget :
      (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (haccepts : FixedCaseTwoAcceptance contracts outer requestedRate
      (fixedSelectedSource contracts outer requestedRate target)
      caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts
      (fixedRefuterInput contracts outer machine requestedRate target)) :
    BoolFunction target :=
  let sourceIndex := fixedSelectedSource contracts outer requestedRate target
  let core := fixedCaseTwoPhysicalCore contracts outer requestedRate sourceIndex
    caseTwo machine haccepts hrejects
  padCore core.function
    (fixedSelectedCoreBounds contracts outer requestedRate target htarget).1

private theorem fixedCaseTwoTargetHardness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge :
      fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (haccepts : FixedCaseTwoAcceptance contracts outer requestedRate
      (fixedSelectedSource contracts outer requestedRate target)
      caseTwo machine)
    (hrejects : ¬machine.toSemantic.accepts
      (fixedRefuterInput contracts outer machine requestedRate target)) :
    ∀ mode,
      PaddedPhysicalModeHardness
        (1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4)
        (fixedPhysicalCoefficient contracts outer requestedRate)
        (fixedPhysicalCoefficient contracts outer requestedRate)
        5 9 mode
        (fixedCaseTwoTargetFunction contracts outer machine requestedRate
          target
          (fixedCaseOneTargetOnset_ready contracts outer requestedRate target
            hlarge).1
          caseTwo haccepts hrejects) := by
  let sourceIndex := fixedSelectedSource contracts outer requestedRate target
  let ready :=
    fixedCaseOneTargetOnset_ready contracts outer requestedRate target hlarge
  let bounds :=
    fixedSelectedCoreBounds contracts outer requestedRate target ready.1
  let core := fixedCaseTwoPhysicalCore contracts outer requestedRate sourceIndex
    caseTwo machine haccepts hrejects
  have hpadded :=
    padPhysicalCommonCore
      (le_of_lt
        (fixedPhysicalCoefficient_positive contracts outer requestedRate))
      (le_of_lt
        (fixedPhysicalCoefficient_positive contracts outer requestedRate))
      5 9 target bounds.1 bounds.2 core
  have hadvantage :
      core.advantage ≤
        1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4 :=
    fixedCaseTwoPhysicalCore_advantage_le contracts outer requestedRate
      sourceIndex caseTwo machine haccepts hrejects
  intro mode
  exact paddedPhysicalModeHardness_mono hadvantage (hpadded mode)

/-- Full inverse branch elimination.  The final language linker need only show
that its evaluator returns the displayed canonical function in each branch. -/
private theorem inverseTargetBranch_hardness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
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
        caseTwo machine) :
    match inverseTargetBranch contracts outer machine advantageExponent target
        hyes with
    | .caseOne data =>
        let ready :=
          inverseCaseOneTargetOnset_ready contracts outer advantageExponent
            target hlarge
        ∀ mode,
          PaddedPhysicalModeHardness
            (inversePolynomialAdvantage target (advantageExponent + 1))
            (inversePhysicalCoefficient contracts outer
              (inverseCoreAdvantagePower advantageExponent))
            (inversePhysicalCoefficient contracts outer
              (inverseCoreAdvantagePower advantageExponent))
            10 12 mode
            (inverseCaseOneTargetFunction contracts outer advantageExponent
              target ready.1 data hyes ready.2.1)
    | .caseTwo caseTwo =>
        let ready :=
          inverseCaseOneTargetOnset_ready contracts outer advantageExponent
            target hlarge
        ∀ mode,
          PaddedPhysicalModeHardness
            (inversePolynomialAdvantage target (advantageExponent + 1))
            (inversePhysicalCoefficient contracts outer
              (inverseCoreAdvantagePower advantageExponent))
            (inversePhysicalCoefficient contracts outer
              (inverseCoreAdvantagePower advantageExponent))
            10 12 mode
            (inverseCaseTwoTargetFunction contracts outer machine
              advantageExponent target ready.1 caseTwo
              (haccepts caseTwo) hrejects) := by
  cases hbranch :
      inverseTargetBranch contracts outer machine advantageExponent target
        hyes with
  | caseOne data =>
      exact inverseScheduledCaseOneHardness contracts outer advantageExponent
        target hlarge data hyes
  | caseTwo caseTwo =>
      exact inverseCaseTwoTargetHardness contracts outer machine
        advantageExponent target hlarge caseTwo (haccepts caseTwo) hrejects

/-- Full fixed-rate branch elimination with the identical concrete-machine
acceptance interface. -/
private theorem fixedTargetBranch_hardness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge :
      fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
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
        caseTwo machine) :
    match fixedTargetBranch contracts outer machine requestedRate target hyes with
    | .caseOne data =>
        let ready :=
          fixedCaseOneTargetOnset_ready contracts outer requestedRate target
            hlarge
        ∀ mode,
          PaddedPhysicalModeHardness
            (1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4)
            (fixedPhysicalCoefficient contracts outer requestedRate)
            (fixedPhysicalCoefficient contracts outer requestedRate)
            5 9 mode
            (fixedCaseOneTargetFunction contracts outer requestedRate target
              ready.1 data hyes ready.2)
    | .caseTwo caseTwo =>
        let ready :=
          fixedCaseOneTargetOnset_ready contracts outer requestedRate target
            hlarge
        ∀ mode,
          PaddedPhysicalModeHardness
            (1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4)
            (fixedPhysicalCoefficient contracts outer requestedRate)
            (fixedPhysicalCoefficient contracts outer requestedRate)
            5 9 mode
            (fixedCaseTwoTargetFunction contracts outer machine requestedRate
              target ready.1 caseTwo (haccepts caseTwo) hrejects) := by
  cases hbranch :
      fixedTargetBranch contracts outer machine requestedRate target hyes with
  | caseOne data =>
      exact fixedScheduledCaseOneHardness contracts outer requestedRate target
        hlarge data hyes
  | caseTwo caseTwo =>
      exact fixedCaseTwoTargetHardness contracts outer machine requestedRate
        target hlarge caseTwo (haccepts caseTwo) hrejects

/-! ## One target function at the executable-language seam -/

/-- The inverse schedule has one canonical target after the genuine outer
branch is selected.  Proof arguments only certify the selected function; they
do not create a second evaluator.  Naming this match gives the executable
language linker a single extensional target. -/
noncomputable def inverseCanonicalTargetFunction
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
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
        caseTwo machine) :
    BoolFunction target :=
  match inverseTargetBranch contracts outer machine advantageExponent target
      hyes with
  | .caseOne data =>
      let ready :=
        inverseCaseOneTargetOnset_ready contracts outer advantageExponent
          target hlarge
      inverseCaseOneTargetFunction contracts outer advantageExponent target
        ready.1 data hyes ready.2.1
  | .caseTwo caseTwo =>
      let ready :=
        inverseCaseOneTargetOnset_ready contracts outer advantageExponent
          target hlarge
      inverseCaseTwoTargetFunction contracts outer machine advantageExponent
        target ready.1 caseTwo (haccepts caseTwo) hrejects

/-- Branch elimination stated at the unique inverse target consumed by the
executable language. -/
theorem inverseCanonicalTargetFunction_hardness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
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
        caseTwo machine) :
    ∀ mode,
      PaddedPhysicalModeHardness
        (inversePolynomialAdvantage target (advantageExponent + 1))
        (inversePhysicalCoefficient contracts outer
          (inverseCoreAdvantagePower advantageExponent))
        (inversePhysicalCoefficient contracts outer
          (inverseCoreAdvantagePower advantageExponent))
        10 12 mode
        (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts) := by
  intro mode
  unfold inverseCanonicalTargetFunction
  have hhard :=
    inverseTargetBranch_hardness contracts outer machine advantageExponent
      target hlarge hyes hrejects haccepts
  generalize hbranch :
      inverseTargetBranch contracts outer machine advantageExponent target
        hyes = branch at hhard ⊢
  cases branch <;> exact hhard mode

/-- Fixed-rate counterpart of `inverseCanonicalTargetFunction`. -/
noncomputable def fixedCanonicalTargetFunction
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge :
      fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
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
        caseTwo machine) :
    BoolFunction target :=
  match fixedTargetBranch contracts outer machine requestedRate target hyes with
  | .caseOne data =>
      let ready :=
        fixedCaseOneTargetOnset_ready contracts outer requestedRate target
          hlarge
      fixedCaseOneTargetFunction contracts outer requestedRate target
        ready.1 data hyes ready.2
  | .caseTwo caseTwo =>
      let ready :=
        fixedCaseOneTargetOnset_ready contracts outer requestedRate target
          hlarge
      fixedCaseTwoTargetFunction contracts outer machine requestedRate target
        ready.1 caseTwo (haccepts caseTwo) hrejects

/-- Branch elimination stated at the unique fixed-rate target consumed by the
executable language. -/
theorem fixedCanonicalTargetFunction_hardness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge :
      fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
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
        caseTwo machine) :
    ∀ mode,
      PaddedPhysicalModeHardness
        (1 / (2 : ℝ) ^ (fixedRate contracts requestedRate) / 4)
        (fixedPhysicalCoefficient contracts outer requestedRate)
        (fixedPhysicalCoefficient contracts outer requestedRate)
        5 9 mode
        (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts) := by
  intro mode
  unfold fixedCanonicalTargetFunction
  have hhard :=
    fixedTargetBranch_hardness contracts outer machine requestedRate target
      hlarge hyes hrejects haccepts
  generalize hbranch :
      fixedTargetBranch contracts outer machine requestedRate target hyes =
        branch at hhard ⊢
  cases branch <;> exact hhard mode

/-! ## Public pointwise values of the Case-2 branch

The Case-2 half of the canonical target is assembled from `private`
constructors above.  The two theorems below are the only public window on that
branch: at every requested point the canonical target equals the XOR power of
the scheduled Case-2 seed read on the low raw-core coordinates.  They mention
neither `PaddedPhysicalModeHardness` nor any private declaration, so an
executable language linker can state its `hexecutes` obligation outside this
module. -/

/-- Canonical padding reads exactly the low target coordinates. -/
private theorem padCore_apply_low {core target : ℕ}
    (function : BoolFunction core) (hcore : core ≤ target)
    (point : BitInput target) :
    padCore function hcore point =
      function fun index => point ⟨index.val, index.isLt.trans_le hcore⟩ := by
  simp only [padCore, finSplitEquiv, Equiv.trans_apply]
  rfl

/-- Two successive paddings read the same low coordinates as one. -/
private theorem padCore_padCore_low {core middle target : ℕ}
    (function : BoolFunction core) (hmiddle : core ≤ middle)
    (htarget : middle ≤ target) (point : BitInput target) :
    padCore (padCore function hmiddle) htarget point =
      function fun index =>
        point ⟨index.val, index.isLt.trans_le (hmiddle.trans htarget)⟩ := by
  rw [padCore_apply_low, padCore_apply_low]

/-- The raw inverse-schedule XOR arity fits inside every admissible target
length.  Naming the inequality lets the pointwise theorem below display its
coordinate restriction without an anonymous proof term. -/
theorem inverseCaseTwoRawArity_le_target
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower target : ℕ)
    (htarget :
      (inverseEnvelope contracts outer advantagePower).targetOnset ≤ target) :
    inverseCopies outer (publishedPointwisePCPP contracts)
          (inverseRate contracts advantagePower)
          (inverseSourceIndex
            (inverseSelectedSource contracts outer advantagePower target)) *
        seedArity outer (publishedPointwisePCPP contracts)
          (inverseRequiredDegree contracts advantagePower)
          (inverseSourceIndex
            (inverseSelectedSource contracts outer advantagePower target)) ≤
      target :=
  ((inverseEnvelope contracts outer advantagePower).rawArity_le_coreArity
      (inverseSelectedSource contracts outer advantagePower target)).trans
    (inverseSelectedCoreBounds contracts outer advantagePower target htarget).1

/-- Fixed-rate counterpart of `inverseCaseTwoRawArity_le_target`. -/
theorem fixedCaseTwoRawArity_le_target
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ)
    (htarget :
      (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target) :
    fixedCopies (publishedPointwisePCPP contracts)
          (fixedRate contracts requestedRate) *
        seedArity outer (publishedPointwisePCPP contracts)
          (fixedRequiredDegree contracts requestedRate)
          (fixedSelectedSource contracts outer requestedRate target) ≤
      target :=
  ((fixedEnvelope contracts outer requestedRate).rawArity_le_coreArity
      (fixedSelectedSource contracts outer requestedRate target)).trans
    (fixedSelectedCoreBounds contracts outer requestedRate target htarget).1

/-- Exact inverse-schedule Case-2 value.  Whenever the genuine outer split
returns the canonical accepting oracle, the unique canonical target is the XOR
power of the scheduled Case-2 seed evaluated on the low raw-core coordinates
of the requested point. -/
theorem inverseCanonicalTargetFunction_caseTwo_apply
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
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
    (point : BitInput target) :
    inverseCanonicalTargetFunction contracts outer machine advantageExponent
        target hlarge hyes hrejects haccepts point =
      xorPower (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (inverseCopies outer (publishedPointwisePCPP contracts)
          (inverseRate contracts
            (inverseCoreAdvantagePower advantageExponent))
          (inverseSourceIndex
            (inverseSelectedSource contracts outer
              (inverseCoreAdvantagePower advantageExponent) target)))
        (fun index =>
          point
            ⟨index.val,
              index.isLt.trans_le
                (inverseCaseTwoRawArity_le_target contracts outer
                  (inverseCoreAdvantagePower advantageExponent) target
                  (inverseCaseOneTargetOnset_ready contracts outer
                    advantageExponent target hlarge).1)⟩) := by
  have hraw :=
    (inverseEnvelope contracts outer
        (inverseCoreAdvantagePower advantageExponent)).rawArity_le_coreArity
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target)
  have hcore :=
    (inverseSelectedCoreBounds contracts outer
      (inverseCoreAdvantagePower advantageExponent) target
      (inverseCaseOneTargetOnset_ready contracts outer advantageExponent
        target hlarge).1).1
  have hvalue :
      inverseCaseTwoTargetFunction contracts outer machine advantageExponent
          target
          (inverseCaseOneTargetOnset_ready contracts outer advantageExponent
            target hlarge).1
          caseTwo (haccepts caseTwo) hrejects =
        padCore
          (padCore
            (xorPower (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
              (inverseCopies outer (publishedPointwisePCPP contracts)
                (inverseRate contracts
                  (inverseCoreAdvantagePower advantageExponent))
                (inverseSourceIndex
                  (inverseSelectedSource contracts outer
                    (inverseCoreAdvantagePower advantageExponent) target))))
            hraw)
          hcore :=
    rfl
  unfold inverseCanonicalTargetFunction
  simp only [hbranch, hvalue]
  exact padCore_padCore_low _ hraw hcore point

/-- Fixed-rate counterpart of `inverseCanonicalTargetFunction_caseTwo_apply`. -/
theorem fixedCanonicalTargetFunction_caseTwo_apply
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge :
      fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
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
    (point : BitInput target) :
    fixedCanonicalTargetFunction contracts outer machine requestedRate target
        hlarge hyes hrejects haccepts point =
      xorPower (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (fixedCopies (publishedPointwisePCPP contracts)
          (fixedRate contracts requestedRate))
        (fun index =>
          point
            ⟨index.val,
              index.isLt.trans_le
                (fixedCaseTwoRawArity_le_target contracts outer requestedRate
                  target
                  (fixedCaseOneTargetOnset_ready contracts outer requestedRate
                    target hlarge).1)⟩) := by
  have hraw :=
    (fixedEnvelope contracts outer requestedRate).rawArity_le_coreArity
      (fixedSelectedSource contracts outer requestedRate target)
  have hcore :=
    (fixedSelectedCoreBounds contracts outer requestedRate target
      (fixedCaseOneTargetOnset_ready contracts outer requestedRate target
        hlarge).1).1
  have hvalue :
      fixedCaseTwoTargetFunction contracts outer machine requestedRate target
          (fixedCaseOneTargetOnset_ready contracts outer requestedRate target
            hlarge).1
          caseTwo (haccepts caseTwo) hrejects =
        padCore
          (padCore
            (xorPower (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
              (fixedCopies (publishedPointwisePCPP contracts)
                (fixedRate contracts requestedRate)))
            hraw)
          hcore :=
    rfl
  unfold fixedCanonicalTargetFunction
  simp only [hbranch, hvalue]
  exact padCore_padCore_low _ hraw hcore point

end NearCubicWires.CaseTwoRecoveryAssembly
