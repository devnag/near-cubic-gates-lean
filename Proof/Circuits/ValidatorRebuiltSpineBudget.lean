import Proof.MachineModel.ValidatorEndpointRebuildProgram

namespace NearCubicWires.ValidatorRebuiltSpineBudget

open NearCubicWires
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.ValidatorCircuitRebuildLedger
open NearCubicWires.ValidatorEndpointRebuildProgram
open NearCubicWires.ValidatorOracleCallWidth
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

def recoveryValidatorMaximumStageRebuildFuel
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max recoveryValidatorStructuralPrefixFuel <|
    max (recoveryOracleValidationRebuildFuel
      (recoveryValidatorStructuralPrefixOutput limits raw)) <|
      max (recoveryLegalSumEnvelopeFuel inputLength
        (recoveryValidatorOraclePrefixOutput limits raw))
        recoveryValidatorModeRawFuel

def recoveryValidatorMaximumStageRebuildBits
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryValidatorStructuralPrefixBits inputLength limits raw) <|
      max (recoveryOracleValidationRebuildBits inputLength
        (recoveryValidatorStructuralPrefixOutput limits raw)) <|
        max (recoveryLegalSumEnvelopeBits inputLength
          (recoveryValidatorOraclePrefixOutput limits raw))
          (recoveryValidatorModeRawBits inputLength
            (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))

/-- The coefficient the rebuilt validator's three-node spine produces from one
uniform stage coefficient.  Never evaluated: the three spans are closed
naturals over whole linked programs. -/
def recoveryValidatorRebuildSpineCoefficient (stageCoefficient : ℕ) : ℕ :=
  programRegisterSpan recoveryValidatorModeRawProgram + 5 +
      (programRegisterSpan recoveryLegalSumEnvelopeProgram + 5 +
          (programRegisterSpan recoveryOracleValidationRebuildProgram + 5 +
            stageCoefficient + stageCoefficient) +
        stageCoefficient) +
    stageCoefficient

private theorem le_rebuildSpineCoefficient
    (modeRawSpan envelopeSpan oracleSpan coefficient : ℕ) :
    coefficient ≤
      modeRawSpan + 5 +
        (envelopeSpan + 5 + (oracleSpan + 5 + coefficient + coefficient) +
          coefficient) + coefficient := by
  omega

/-! ## §2 The rebuilt spine, dominated -/

/-- **Fuel side of the rebuilt spine, dominated.** -/
theorem recoveryWitnessValidatorRebuildFuel_polyBounded
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure stageCoefficient degree : ℕ}
    (hstage :
      PolyBounded
        (recoveryValidatorMaximumStageRebuildFuel inputLength limits raw)
        measure stageCoefficient degree) :
    PolyBounded (recoveryWitnessValidatorRebuildFuel inputLength limits raw)
      measure (recoveryValidatorRebuildSpineCoefficient stageCoefficient)
      degree := by
  have hstructural :
      PolyBounded recoveryValidatorStructuralPrefixFuel measure
        stageCoefficient degree := by
    refine hstage.mono ?_
    rw [recoveryValidatorMaximumStageRebuildFuel]
    exact le_max_left _ _
  have horacle :
      PolyBounded (recoveryOracleValidationRebuildFuel
        (recoveryValidatorStructuralPrefixOutput limits raw)) measure
        stageCoefficient degree := by
    refine hstage.mono ?_
    rw [recoveryValidatorMaximumStageRebuildFuel]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have henvelope :
      PolyBounded (recoveryLegalSumEnvelopeFuel inputLength
        (recoveryValidatorOraclePrefixOutput limits raw)) measure
        stageCoefficient degree := by
    refine hstage.mono ?_
    rw [recoveryValidatorMaximumStageRebuildFuel]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hmodeRaw :
      PolyBounded recoveryValidatorModeRawFuel measure stageCoefficient
        degree := by
    refine hstage.mono ?_
    rw [recoveryValidatorMaximumStageRebuildFuel]
    exact
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have horaclePrefix :
      PolyBounded (recoveryValidatorOraclePrefixRebuildFuel limits raw) measure
        (programRegisterSpan recoveryOracleValidationRebuildProgram + 5 +
          stageCoefficient + stageCoefficient) degree := by
    rw [recoveryValidatorOraclePrefixRebuildFuel]
    exact linkFuel_polyBounded hstructural horacle
  have hlegalSumPrefix :
      PolyBounded
        (recoveryValidatorLegalSumPrefixRebuildFuel inputLength limits raw)
        measure
        (programRegisterSpan recoveryLegalSumEnvelopeProgram + 5 +
          (programRegisterSpan recoveryOracleValidationRebuildProgram + 5 +
            stageCoefficient + stageCoefficient) + stageCoefficient)
        degree := by
    rw [recoveryValidatorLegalSumPrefixRebuildFuel]
    exact linkFuel_polyBounded horaclePrefix henvelope
  rw [recoveryWitnessValidatorRebuildFuel,
    recoveryValidatorRebuildSpineCoefficient]
  exact linkFuel_polyBounded hlegalSumPrefix hmodeRaw

/-- **The rebuilt width ledger.**  Register width is a pure maximum along the
rebuilt spine. -/
theorem recoveryWitnessValidatorRebuildBits_le_maximumStage
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryWitnessValidatorRebuildBits inputLength limits raw ≤
      recoveryValidatorMaximumStageRebuildBits inputLength limits raw := by
  have hlength :
      natBitLength inputLength ≤
        recoveryValidatorMaximumStageRebuildBits inputLength limits raw := by
    rw [recoveryValidatorMaximumStageRebuildBits]
    exact le_max_left _ _
  have hstructural :
      recoveryValidatorStructuralPrefixBits inputLength limits raw ≤
        recoveryValidatorMaximumStageRebuildBits inputLength limits raw := by
    rw [recoveryValidatorMaximumStageRebuildBits]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have horacle :
      recoveryOracleValidationRebuildBits inputLength
          (recoveryValidatorStructuralPrefixOutput limits raw) ≤
        recoveryValidatorMaximumStageRebuildBits inputLength limits raw := by
    rw [recoveryValidatorMaximumStageRebuildBits]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have henvelope :
      recoveryLegalSumEnvelopeBits inputLength
          (recoveryValidatorOraclePrefixOutput limits raw) ≤
        recoveryValidatorMaximumStageRebuildBits inputLength limits raw := by
    rw [recoveryValidatorMaximumStageRebuildBits]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hmodeRaw :
      recoveryValidatorModeRawBits inputLength
          (recoveryValidatorLegalSumPrefixOutput inputLength limits raw) ≤
        recoveryValidatorMaximumStageRebuildBits inputLength limits raw := by
    rw [recoveryValidatorMaximumStageRebuildBits]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  rw [recoveryWitnessValidatorRebuildBits,
    recoveryValidatorLegalSumPrefixRebuildBits,
    recoveryValidatorOraclePrefixRebuildBits]
  exact max_le hlength (max_le (max_le hlength (max_le
    (max_le hlength (max_le hstructural horacle)) henvelope)) hmodeRaw)

/-- **Width side of the rebuilt spine, dominated.** -/
theorem recoveryWitnessValidatorRebuildBits_polyBounded
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure stageCoefficient degree : ℕ}
    (hstage :
      PolyBounded
        (recoveryValidatorMaximumStageRebuildBits inputLength limits raw)
        measure stageCoefficient degree) :
    PolyBounded (recoveryWitnessValidatorRebuildBits inputLength limits raw)
      measure stageCoefficient degree :=
  hstage.mono
    (recoveryWitnessValidatorRebuildBits_le_maximumStage inputLength limits raw)

/-! ## §3 The rebuilt oracle-validation stage, dominated -/

/-- **The rebuilt oracle call, dominated.**  One native contextual call into
the *rebuilt* Boolean-circuit validator. -/
theorem recoveryOracleCallRebuildFuel_polyBounded
    {handoff measure circuitCoefficient degree : ℕ}
    (hcircuit :
      PolyBounded
        (booleanCircuitValidationRebuildFuel (handoffOracleArity handoff)
          (handoffOracleCode handoff)) measure circuitCoefficient degree) :
    PolyBounded (recoveryOracleCallRebuildFuel handoff) measure
      (nativeContextCallOverhead booleanCircuitValidationRebuildProgram +
        circuitCoefficient) degree := by
  have hdefinition :
      recoveryOracleCallRebuildFuel handoff =
        nativeContextCallFuel booleanCircuitValidationRebuildProgram
          (booleanCircuitValidationRebuildFuel (handoffOracleArity handoff)
            (handoffOracleCode handoff))
          (handoffOracleArity handoff) (handoffOracleCode handoff) := rfl
  exact (nativeContextCallFuel_polyBounded hcircuit).mono
    (Nat.le_of_eq hdefinition)

/-- The closed fuel coefficient the rebuilt oracle-validation stage produces
from one circuit coefficient and one stage-width coefficient. -/
def recoveryOracleValidationRebuildFuelCoefficient
    (circuitCoefficient stageCoefficient : ℕ) : ℕ :=
  programRegisterSpan
      (linkPrograms recoveryOracleCallRebuildProgram <|
        linkPrograms recoveryOracleBoundLoweringProgram
          recoveryBoundedContextCheckProgram) + 5 +
      recoveryOracleCallLoweringFuel +
    (programRegisterSpan
        (linkPrograms recoveryOracleBoundLoweringProgram
          recoveryBoundedContextCheckProgram) + 5 +
        (nativeContextCallOverhead booleanCircuitValidationRebuildProgram +
          circuitCoefficient) +
      (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
          recoveryOracleBoundLoweringFuel + (36 * stageCoefficient + 24)))

/-- **The rebuilt oracle-validation stage, dominated.** -/
theorem recoveryOracleValidationRebuildFuel_polyBounded
    {handoff measure circuitCoefficient resultCoefficient handoffCoefficient
      degree : ℕ}
    (hcircuit :
      PolyBounded
        (booleanCircuitValidationRebuildFuel (handoffOracleArity handoff)
          (handoffOracleCode handoff)) measure circuitCoefficient degree)
    (hresult :
      PolyBounded (natBitLength (recoveryOracleValidationResult handoff))
        measure resultCoefficient degree)
    (hhandoff :
      PolyBounded (natBitLength handoff) measure handoffCoefficient degree) :
    PolyBounded (recoveryOracleValidationRebuildFuel handoff) measure
      (recoveryOracleValidationRebuildFuelCoefficient circuitCoefficient
        (max resultCoefficient handoffCoefficient))
      degree := by
  have hcheck :
      PolyBounded
        (recoveryBoundedContextCheckFuel (recoveryOracleBoundValue handoff)
          (recoveryOracleBoundCap handoff)) measure
        (36 * max resultCoefficient handoffCoefficient + 24) degree :=
    recoveryBoundedContextCheckFuel_polyBounded
      (polyBounded_natBitLength_of_le hresult
        (recoveryOracleBoundValue_le handoff))
      (polyBounded_natBitLength_of_le hhandoff
        (recoveryOracleBoundCap_le handoff))
  have htail :
      PolyBounded (recoveryOracleValidationRebuildTailFuel handoff) measure
        (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
            recoveryOracleBoundLoweringFuel +
          (36 * max resultCoefficient handoffCoefficient + 24)) degree := by
    rw [recoveryOracleValidationRebuildTailFuel]
    exact linkFuel_polyBounded
      (polyBounded_const recoveryOracleBoundLoweringFuel measure degree) hcheck
  have hcallTail :
      PolyBounded (recoveryOracleValidationRebuildCallTailFuel handoff) measure
        (programRegisterSpan
            (linkPrograms recoveryOracleBoundLoweringProgram
              recoveryBoundedContextCheckProgram) + 5 +
            (nativeContextCallOverhead booleanCircuitValidationRebuildProgram +
              circuitCoefficient) +
          (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
              recoveryOracleBoundLoweringFuel +
            (36 * max resultCoefficient handoffCoefficient + 24))) degree := by
    rw [recoveryOracleValidationRebuildCallTailFuel]
    exact linkFuel_polyBounded
      (recoveryOracleCallRebuildFuel_polyBounded hcircuit) htail
  rw [recoveryOracleValidationRebuildFuel,
    recoveryOracleValidationRebuildFuelCoefficient]
  exact linkFuel_polyBounded
    (polyBounded_const recoveryOracleCallLoweringFuel measure degree) hcallTail

theorem recoveryOracleValidationRebuildBits_polyBounded
    {inputLength handoff measure lengthCoefficient widthCoefficient
      callCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hwidth :
      PolyBounded (recoveryOracleStageWidth handoff) measure widthCoefficient
        degree)
    (hcall :
      PolyBounded (recoveryOracleCallRebuildBits inputLength handoff) measure
        callCoefficient degree) :
    PolyBounded (recoveryOracleValidationRebuildBits inputLength handoff)
      measure
      (max (max lengthCoefficient (4 * widthCoefficient)) callCoefficient)
      degree := by
  set coefficient :=
    max (max lengthCoefficient (4 * widthCoefficient)) callCoefficient
    with hcoefficient
  have hscaled :
      PolyBounded (4 * recoveryOracleStageWidth handoff) measure
        (4 * widthCoefficient) degree := hwidth.const_mul 4
  have hlengthAt : PolyBounded (natBitLength inputLength) measure coefficient
      degree := hlength.coefficient_mono (by omega)
  have hloweringAt :
      PolyBounded (recoveryOracleCallLoweringBits handoff) measure coefficient
        degree :=
    (hscaled.mono (recoveryOracleCallLoweringBits_le handoff)).coefficient_mono
      (by omega)
  have hcallAt :
      PolyBounded (recoveryOracleCallRebuildBits inputLength handoff) measure
        coefficient degree := hcall.coefficient_mono (by omega)
  have hboundAt :
      PolyBounded (recoveryOracleBoundLoweringBits handoff) measure coefficient
        degree :=
    (hscaled.mono (recoveryOracleBoundLoweringBits_le handoff)).coefficient_mono
      (by omega)
  have hcheckAt :
      PolyBounded
        (recoveryBoundedContextCheckBits inputLength
          (recoveryOracleBoundValue handoff) (recoveryOracleBoundCap handoff)
          (recoveryOracleBoundContext handoff)) measure coefficient degree :=
    ((hlength.max hscaled).mono
      (recoveryBoundedContextCheckBits_le inputLength handoff)).coefficient_mono
      (by omega)
  change recoveryOracleValidationRebuildBits inputLength handoff ≤
    coefficient * (measure + 1) ^ degree
  rw [recoveryOracleValidationRebuildBits]
  exact max_le hlengthAt (max_le hloweringAt (max_le hcallAt
    (max_le hboundAt hcheckAt)))

theorem recoveryValidatorMaximumStageRebuildFuel_polyBounded
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure circuitCoefficient resultCoefficient handoffCoefficient
      envelopeCoefficient degree : ℕ}
    (hcircuit :
      PolyBounded
        (booleanCircuitValidationRebuildFuel
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput limits raw))
          (handoffOracleCode
            (recoveryValidatorStructuralPrefixOutput limits raw))) measure
        circuitCoefficient degree)
    (hresult :
      PolyBounded
        (natBitLength
          (recoveryOracleValidationResult
            (recoveryValidatorStructuralPrefixOutput limits raw))) measure
        resultCoefficient degree)
    (hhandoff :
      PolyBounded
        (natBitLength (recoveryValidatorStructuralPrefixOutput limits raw))
        measure handoffCoefficient degree)
    (henvelope :
      PolyBounded
        (recoveryLegalSumEnvelopeFuel inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) measure
        envelopeCoefficient degree) :
    PolyBounded
      (recoveryValidatorMaximumStageRebuildFuel inputLength limits raw) measure
      (max recoveryValidatorStructuralPrefixFuel <|
        max
          (recoveryOracleValidationRebuildFuelCoefficient circuitCoefficient
            (max resultCoefficient handoffCoefficient)) <|
          max envelopeCoefficient recoveryValidatorModeRawFuel)
      degree := by
  have hstructural :
      PolyBounded recoveryValidatorStructuralPrefixFuel measure
        recoveryValidatorStructuralPrefixFuel degree :=
    polyBounded_const _ _ _
  have horacle :=
    recoveryOracleValidationRebuildFuel_polyBounded hcircuit hresult hhandoff
  have hmodeRaw :
      PolyBounded recoveryValidatorModeRawFuel measure
        recoveryValidatorModeRawFuel degree := polyBounded_const _ _ _
  exact hstructural.max (horacle.max (henvelope.max hmodeRaw))

theorem recoveryValidatorMaximumStageRebuildBits_polyBounded
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure lengthCoefficient prefixCoefficient stageCoefficient
      callCoefficient envelopeCoefficient modeCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hprefix :
      PolyBounded (recoveryValidatorPrefixWidth limits raw) measure
        prefixCoefficient degree)
    (hstage :
      PolyBounded
        (recoveryOracleStageWidth
          (recoveryValidatorStructuralPrefixOutput limits raw)) measure
        stageCoefficient degree)
    (hcall :
      PolyBounded
        (recoveryOracleCallRebuildBits inputLength
          (recoveryValidatorStructuralPrefixOutput limits raw)) measure
        callCoefficient degree)
    (henvelope :
      PolyBounded
        (recoveryLegalSumEnvelopeBits inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) measure
        envelopeCoefficient degree)
    (hmode :
      PolyBounded
        (natBitLength
          (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))
        measure modeCoefficient degree) :
    PolyBounded
      (recoveryValidatorMaximumStageRebuildBits inputLength limits raw) measure
      (max lengthCoefficient <|
        max (max lengthCoefficient (16 * prefixCoefficient)) <|
          max (max (max lengthCoefficient (4 * stageCoefficient))
            callCoefficient) <|
            max envelopeCoefficient
              (max lengthCoefficient (2 * modeCoefficient)))
      degree := by
  have hprefixBits :=
    recoveryValidatorStructuralPrefixBits_polyBounded hlength hprefix
  have horacleBits :=
    recoveryOracleValidationRebuildBits_polyBounded hlength hstage hcall
  have hmodeBits :
      PolyBounded
        (recoveryValidatorModeRawBits inputLength
          (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))
        measure (max lengthCoefficient (2 * modeCoefficient)) degree :=
    (hlength.max (hmode.const_mul 2)).mono
      (recoveryValidatorModeRawBits_le inputLength
        (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))
  exact hlength.max (hprefixBits.max (horacleBits.max
    (henvelope.max hmodeBits)))

/-! ## §5 Both machine premises at one coefficient -/

/-- **`hvalidatorFuel`, at the rebuilt names.** -/
theorem hvalidatorRebuildFuel_of_stageFuel
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (stageCoefficient degree : ℕ) (hdegree : degree ≤ recoveryVerifierDegree)
    (hstage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryValidatorMaximumStageRebuildFuel
          (WeakVerifierRequest.length request) (limitsOf request.inputArity)
          (encodeBitInput request.witness))
        request.measure stageCoefficient degree)
    (request : WeakVerifierRequest) :
    recoveryWitnessValidatorRebuildFuel (WeakVerifierRequest.length request)
        (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
      polynomialBudget
        (recoveryValidatorRebuildSpineCoefficient stageCoefficient)
        recoveryVerifierDegree request.measure :=
  ((recoveryWitnessValidatorRebuildFuel_polyBounded
    (hstage request)).degree_mono hdegree).le_polynomialBudget

/-- **`hvalidatorBits`, at the rebuilt names.** -/
theorem hvalidatorRebuildBits_of_stageBits
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (stageCoefficient degree : ℕ) (hdegree : degree ≤ recoveryVerifierDegree)
    (hstage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryValidatorMaximumStageRebuildBits
          (WeakVerifierRequest.length request) (limitsOf request.inputArity)
          (encodeBitInput request.witness))
        request.measure stageCoefficient degree)
    (request : WeakVerifierRequest) :
    recoveryWitnessValidatorRebuildBits (WeakVerifierRequest.length request)
        (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
      polynomialBudget stageCoefficient recoveryVerifierDegree
        request.measure :=
  ((recoveryWitnessValidatorRebuildBits_polyBounded
    (hstage request)).degree_mono hdegree).le_polynomialBudget

/-- **Both rebuilt premises at one coefficient**, in exactly the shape the
rebuilt machine assembly consumes. -/
theorem hvalidatorRebuild_of_stageFrontier
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (stageCoefficient degree : ℕ) (hdegree : degree ≤ recoveryVerifierDegree)
    (hfuel : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryValidatorMaximumStageRebuildFuel
          (WeakVerifierRequest.length request) (limitsOf request.inputArity)
          (encodeBitInput request.witness))
        request.measure stageCoefficient degree)
    (hbits : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryValidatorMaximumStageRebuildBits
          (WeakVerifierRequest.length request) (limitsOf request.inputArity)
          (encodeBitInput request.witness))
        request.measure stageCoefficient degree) :
    (∀ request : WeakVerifierRequest,
      recoveryWitnessValidatorRebuildBits (WeakVerifierRequest.length request)
          (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
        polynomialBudget
          (recoveryValidatorRebuildSpineCoefficient stageCoefficient)
          recoveryVerifierDegree request.measure) ∧
      ∀ request : WeakVerifierRequest,
        recoveryWitnessValidatorRebuildFuel (WeakVerifierRequest.length request)
            (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
          polynomialBudget
            (recoveryValidatorRebuildSpineCoefficient stageCoefficient)
            recoveryVerifierDegree request.measure := by
  refine ⟨fun request => ?_, fun request => ?_⟩
  · refine (hvalidatorRebuildBits_of_stageBits limitsOf stageCoefficient degree
      hdegree hbits request).trans ?_
    rw [recoveryValidatorRebuildSpineCoefficient]
    exact Nat.mul_le_mul_right _ (le_rebuildSpineCoefficient _ _ _ _)
  · exact hvalidatorRebuildFuel_of_stageFuel limitsOf stageCoefficient degree
      hdegree hfuel request

end NearCubicWires.ValidatorRebuiltSpineBudget
