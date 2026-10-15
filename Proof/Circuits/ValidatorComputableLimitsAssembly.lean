import Proof.Circuits.ValidatorResidualLeafBudget

namespace NearCubicWires.ValidatorComputableLimitsAssembly

open NearCubicWires
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.RecoveryLimitsFrontEndProgram
open NearCubicWires.RecoveryVerifierResourceEnvelope
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 The computable family as a limits function

The machine consumes a `limitsOf : ℕ → RecoveryWitnessLimits`; the computable
family is that function once its six parameters are given as functions of the
arity.  Nothing below constrains those parameter functions — they are exactly
where the schedule enters. -/

/-- The computable recovery policy, presented as the machine's `limitsOf`. -/
def computableLimitsOf (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ) (arity : ℕ) : RecoveryWitnessLimits :=
  computableXorRecoveryWitnessLimits profile (copyBound arity)
    (oracleArity arity) (oracleSizeCap arity) (sumArity arity)
    (symmetricWireCap arity) (thresholdWireCap arity)

/-- The family's own width parameter, at one arity. -/
def computableLimitsWidthParameter (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ) (arity : ℕ) : ℕ :=
  computableRecoveryWitnessLimitsWidthParameter profile (copyBound arity)
    (oracleArity arity) (oracleSizeCap arity) (sumArity arity)
    (symmetricWireCap arity) (thresholdWireCap arity)

/-- **The serialized policy's width, unconditionally.**  No schedule
hypothesis: only the arithmetic shape of the family. -/
theorem natBitLength_encodeComputableLimits_le
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ) (arity : ℕ) :
    natBitLength
        (encodeRecoveryWitnessLimits
          (computableLimitsOf profile copyBound oracleArity oracleSizeCap
            sumArity symmetricWireCap thresholdWireCap arity)) ≤
      recoveryWitnessLimitsCodeBitBound
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap arity) :=
  natBitLength_encodeComputableXorRecoveryWitnessLimits_le profile
    (copyBound arity) (oracleArity arity) (oracleSizeCap arity)
    (sumArity arity) (symmetricWireCap arity) (thresholdWireCap arity)

/-! ## §2 The two width premises the validator cannot pay

`hlength` is free: the request codec caps the public input length's width at
`4 · (measure + 1)`.  `hprefix` reduces to a statement about the family's own
serialized width — which §1 bounds by an explicit expression in the family's
parameters, so what is left mentions no validator definition at all. -/

/-- **`hprefix`, discharged at the computable family.**  The remaining
hypothesis is about the family's parameters only. -/
theorem polyBounded_computableLimits_prefixWidth
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    {policyCoefficient degree : ℕ}
    (hdegree : 1 ≤ degree)
    (hpolicy : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryWitnessLimitsCodeBitBound
          (computableLimitsWidthParameter profile copyBound oracleArity
            oracleSizeCap sumArity symmetricWireCap thresholdWireCap
            request.inputArity))
        request.measure policyCoefficient degree)
    (request : WeakVerifierRequest) :
    PolyBounded
      (recoveryValidatorPrefixWidth
        (computableLimitsOf profile copyBound oracleArity oracleSizeCap sumArity
          symmetricWireCap thresholdWireCap request.inputArity)
        (encodeBitInput request.witness))
      request.measure (max 4 policyCoefficient) degree := by
  have hwitness :
      PolyBounded (natBitLength (encodeBitInput request.witness))
        request.measure 4 degree :=
    (polyBounded_witnessWidth request).degree_mono hdegree
  have hserialized :
      PolyBounded
        (natBitLength
          (encodeRecoveryWitnessLimits
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)))
        request.measure policyCoefficient degree :=
    (hpolicy request).mono
      (natBitLength_encodeComputableLimits_le profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        request.inputArity)
  exact hwitness.max hserialized

/-- **`hlength`, discharged.**  Free from the request codec at every degree at
or above the anchor's. -/
theorem polyBounded_requestLengthWidth_at
    {degree : ℕ} (hdegree : 1 ≤ degree) (request : WeakVerifierRequest) :
    PolyBounded (natBitLength (WeakVerifierRequest.length request))
      request.measure 4 degree :=
  (polyBounded_requestLengthWidth request).degree_mono hdegree

theorem hvalidator_at_computableLimits
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier stageCoefficient degree : ℕ)
    (hdegreeLow : 1 ≤ degree) (hdegreeHigh : degree ≤ recoveryVerifierDegree)
    (hfour : 4 ≤ frontier)
    (hcoefficientFuel :
      (max recoveryValidatorStructuralPrefixFuel <|
        max
          (programRegisterSpan
              (linkPrograms recoveryOracleCallProgram <|
                linkPrograms recoveryOracleBoundLoweringProgram
                  recoveryBoundedContextCheckProgram) + 5 +
              recoveryOracleCallLoweringFuel +
            (programRegisterSpan
                (linkPrograms recoveryOracleBoundLoweringProgram
                  recoveryBoundedContextCheckProgram) + 5 +
                (nativeContextCallOverhead booleanCircuitValidationProgram +
                  frontier) +
              (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
                  recoveryOracleBoundLoweringFuel +
                (36 * max frontier frontier + 24)))) <|
          max frontier recoveryValidatorModeRawFuel) ≤ stageCoefficient)
    (hcoefficientBits :
      (max frontier <|
        max (max frontier (16 * frontier)) <|
          max (max (max frontier (4 * frontier)) frontier) <|
            max frontier (max frontier (2 * frontier))) ≤ stageCoefficient)
    (hpolicy : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryWitnessLimitsCodeBitBound
          (computableLimitsWidthParameter profile copyBound oracleArity
            oracleSizeCap sumArity symmetricWireCap thresholdWireCap
            request.inputArity))
        request.measure frontier degree)
    (hcircuit : ∀ request : WeakVerifierRequest,
      PolyBounded
        (booleanCircuitValidationFuel
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (handoffOracleCode
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness))))
        request.measure frontier degree)
    (hresult : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryOracleValidationResult
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness))))
        request.measure frontier degree)
    (hhandoff : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorStructuralPrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier degree)
    (henvelopeFuel : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeFuel (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier degree)
    (hstage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleStageWidth
          (recoveryValidatorStructuralPrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier degree)
    (hcall : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleCallBits (WeakVerifierRequest.length request)
          (recoveryValidatorStructuralPrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier degree)
    (henvelopeBits : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeBits (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier degree)
    (hmode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorLegalSumPrefixOutput
            (WeakVerifierRequest.length request)
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier degree) :
    (∀ request : WeakVerifierRequest,
      recoveryWitnessValidatorBits (WeakVerifierRequest.length request)
          (computableLimitsOf profile copyBound oracleArity oracleSizeCap
            sumArity symmetricWireCap thresholdWireCap request.inputArity)
          (encodeBitInput request.witness) ≤
        polynomialBudget (recoveryValidatorSpineCoefficient stageCoefficient)
          recoveryVerifierDegree request.measure) ∧
      ∀ request : WeakVerifierRequest,
        recoveryWitnessValidatorFuel (WeakVerifierRequest.length request)
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness) ≤
          polynomialBudget (recoveryValidatorSpineCoefficient stageCoefficient)
            recoveryVerifierDegree request.measure :=
  hvalidator_of_stageFrontier
    (computableLimitsOf profile copyBound oracleArity oracleSizeCap sumArity
      symmetricWireCap thresholdWireCap)
    stageCoefficient degree hdegreeHigh
    (fun request =>
      recoveryValidatorMaximumStageFuel_polyBounded_uniform hcoefficientFuel
        (hcircuit request) (hresult request) (hhandoff request)
        (henvelopeFuel request))
    (fun request =>
      recoveryValidatorMaximumStageBits_polyBounded_uniform hcoefficientBits
        ((polyBounded_requestLengthWidth_at hdegreeLow request).coefficient_mono
          hfour)
        ((polyBounded_computableLimits_prefixWidth profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap hdegreeLow
          hpolicy request).coefficient_mono (by omega))
        (hstage request) (hcall request) (henvelopeBits request)
        (hmode request))

/-- **The executable recovery machine at the computable limits family, with the
validator's budget discharged.** -/
def executableRecoveryMachineOfComputableLimits
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient : ℕ)
    (hlimitsCode : ∀ request : WeakVerifierRequest,
      runNPOracleProgram limitsCodeProgram (limitsCodeBits request)
          (limitsCodeFuel request)
          (initialNPOracleState (WeakVerifierRequest.length request)
            (encodeBitInput request.witness)) =
        some
          (encodeRecoveryWitnessLimits
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)))
    (hsemanticStage : ∀ request : WeakVerifierRequest,
      runNPOracleProgram semanticStage (semanticBits request)
          (semanticFuel request)
          (initialNPOracleState (WeakVerifierRequest.length request)
            (recoveryWitnessValidatorRequestOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              request)) =
        some (semanticOutput request))
    (hfrontEndBits : ∀ request : WeakVerifierRequest,
      recoveryLimitsFrontEndRequestBits limitsCodeBits
          (computableLimitsOf profile copyBound oracleArity oracleSizeCap
            sumArity symmetricWireCap thresholdWireCap) request ≤
        polynomialBudget frontEndCoefficient recoveryVerifierDegree
          request.measure)
    (hsemanticBits : ∀ request : WeakVerifierRequest,
      semanticBits request ≤
        polynomialBudget semanticCoefficient recoveryVerifierDegree
          request.measure)
    (hfrontEndFuel : ∀ request : WeakVerifierRequest,
      recoveryLimitsFrontEndRequestFuel limitsCodeProgram limitsCodeFuel
          request ≤
        polynomialBudget frontEndCoefficient recoveryVerifierDegree
          request.measure)
    (hsemanticFuel : ∀ request : WeakVerifierRequest,
      semanticFuel request ≤
        polynomialBudget semanticCoefficient recoveryVerifierDegree
          request.measure)
    (hvalidator :
      (∀ request : WeakVerifierRequest,
        recoveryWitnessValidatorBits (WeakVerifierRequest.length request)
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness) ≤
          polynomialBudget (recoveryValidatorSpineCoefficient stageCoefficient)
            recoveryVerifierDegree request.measure) ∧
        ∀ request : WeakVerifierRequest,
          recoveryWitnessValidatorFuel (WeakVerifierRequest.length request)
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness) ≤
            polynomialBudget
              (recoveryValidatorSpineCoefficient stageCoefficient)
              recoveryVerifierDegree request.measure)
    (hlimitsCodeFree : OracleFree limitsCodeProgram)
    (hsemanticFree : OracleFree semanticStage) :
    ExecutableWeakNondeterministicMachine :=
  executableRecoveryMachineOfValidatorFrontier
    (computableLimitsOf profile copyBound oracleArity oracleSizeCap sumArity
      symmetricWireCap thresholdWireCap)
    limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel semanticBits
    semanticFuel semanticOutput frontEndCoefficient semanticCoefficient
    stageCoefficient hlimitsCode hsemanticStage hfrontEndBits hsemanticBits
    hfrontEndFuel hsemanticFuel hvalidator hlimitsCodeFree hsemanticFree

/-- The machine assembled at the computable family charges at the published
degree. -/
theorem executableRecoveryMachineOfComputableLimits_verifier_degree
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient : ℕ)
    (hlimitsCode hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel
      hsemanticFuel hvalidator hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfComputableLimits profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient hlimitsCode hsemanticStage
        hfrontEndBits hsemanticBits hfrontEndFuel hsemanticFuel hvalidator
        hlimitsCodeFree hsemanticFree).verifier.degree =
      honestRecoveryDegree :=
  rfl

/-- The machine assembled at the computable family keeps the recovery witness
shape. -/
theorem executableRecoveryMachineOfComputableLimits_witnessShape
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient : ℕ)
    (hlimitsCode hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel
      hsemanticFuel hvalidator hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfComputableLimits profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient hlimitsCode hsemanticStage
        hfrontEndBits hsemanticBits hfrontEndFuel hsemanticFuel hvalidator
        hlimitsCodeFree hsemanticFree).witnessShape =
      RecoveryWitnessShape.recoveryWitnessShape :=
  rfl

end NearCubicWires.ValidatorComputableLimitsAssembly
