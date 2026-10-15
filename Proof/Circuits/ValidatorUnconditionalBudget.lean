import Proof.Circuits.ValidatorPolicyWidthClosure

namespace NearCubicWires.ValidatorUnconditionalBudget

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
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 The validator's budget from the family's parameter

Everything below `hparameter` is `ValidatorComputableLimitsAssembly` §3
verbatim; the only change is which fact pays for the structural prefix's width
side. -/

theorem hvalidator_at_computableLimits_of_parameter
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier stageCoefficient parameterCoefficient parameterDegree degree : ℕ)
    (hdegreeLow : 1 ≤ degree) (hdegreeHigh : degree ≤ recoveryVerifierDegree)
    (hparameterDegree : 2 * parameterDegree ≤ degree)
    (hfour : 4 ≤ frontier)
    (hpolicyFrontier : 204800 * (parameterCoefficient + 1) ^ 2 ≤ frontier)
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
    (hparameter : ∀ request : WeakVerifierRequest,
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          request.inputArity)
        request.measure parameterCoefficient parameterDegree)
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
        ((polyBounded_computableLimits_prefixWidth_of_parameter profile copyBound
          oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          hdegreeLow hparameterDegree hparameter request).coefficient_mono
          (Nat.max_le.2 ⟨hfour, hpolicyFrontier⟩))
        (hstage request) (hcall request) (henvelopeBits request)
        (hmode request))

/-- **The validator's budget at the published degree, with the policy premise
gone.** -/
theorem hvalidator_at_computableLimits_degree_four
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier stageCoefficient parameterCoefficient : ℕ)
    (hfour : 4 ≤ frontier)
    (hpolicyFrontier : 204800 * (parameterCoefficient + 1) ^ 2 ≤ frontier)
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
    (hparameter : ∀ request : WeakVerifierRequest,
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          request.inputArity)
        request.measure parameterCoefficient 1)
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
        request.measure frontier recoveryVerifierDegree)
    (hresult : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryOracleValidationResult
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness))))
        request.measure frontier recoveryVerifierDegree)
    (hhandoff : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorStructuralPrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (henvelopeFuel : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeFuel (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (hstage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleStageWidth
          (recoveryValidatorStructuralPrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (hcall : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleCallBits (WeakVerifierRequest.length request)
          (recoveryValidatorStructuralPrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (henvelopeBits : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeBits (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (hmode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorLegalSumPrefixOutput
            (WeakVerifierRequest.length request)
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree) :
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
  hvalidator_at_computableLimits_of_parameter profile copyBound oracleArity
    oracleSizeCap sumArity symmetricWireCap thresholdWireCap frontier
    stageCoefficient parameterCoefficient 1 recoveryVerifierDegree
    (by norm_num [recoveryVerifierDegree]) le_rfl
    (by norm_num [recoveryVerifierDegree]) hfour hpolicyFrontier
    hcoefficientFuel hcoefficientBits hparameter hcircuit hresult hhandoff
    henvelopeFuel hstage hcall henvelopeBits hmode

/-- **The executable recovery machine at the computable limits family, with the
validator's budget built rather than assumed.** -/
def executableRecoveryMachineOfComputableLimitsParameter
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      parameterCoefficient : ℕ)
    (hfour : 4 ≤ frontier)
    (hpolicyFrontier : 204800 * (parameterCoefficient + 1) ^ 2 ≤ frontier)
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
    (hparameter : ∀ request : WeakVerifierRequest,
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          request.inputArity)
        request.measure parameterCoefficient 1)
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
        request.measure frontier recoveryVerifierDegree)
    (hresult : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryOracleValidationResult
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness))))
        request.measure frontier recoveryVerifierDegree)
    (hhandoff : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorStructuralPrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (henvelopeFuel : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeFuel (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (hstage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleStageWidth
          (recoveryValidatorStructuralPrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (hcall : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleCallBits (WeakVerifierRequest.length request)
          (recoveryValidatorStructuralPrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (henvelopeBits : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeBits (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (hmode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorLegalSumPrefixOutput
            (WeakVerifierRequest.length request)
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
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
    (hlimitsCodeFree : OracleFree limitsCodeProgram)
    (hsemanticFree : OracleFree semanticStage) :
    ExecutableWeakNondeterministicMachine :=
  executableRecoveryMachineOfComputableLimits profile copyBound oracleArity
    oracleSizeCap sumArity symmetricWireCap thresholdWireCap limitsCodeProgram
    semanticStage limitsCodeBits limitsCodeFuel semanticBits semanticFuel
    semanticOutput frontEndCoefficient semanticCoefficient stageCoefficient
    hlimitsCode hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel
    hsemanticFuel
    (hvalidator_at_computableLimits_degree_four profile copyBound oracleArity
      oracleSizeCap sumArity symmetricWireCap thresholdWireCap frontier
      stageCoefficient parameterCoefficient hfour hpolicyFrontier
      hcoefficientFuel hcoefficientBits hparameter hcircuit hresult hhandoff
      henvelopeFuel hstage hcall henvelopeBits hmode)
    hlimitsCodeFree hsemanticFree

/-- The machine built this way still charges at the published degree. -/
theorem executableRecoveryMachineOfComputableLimitsParameter_verifier_degree
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      parameterCoefficient : ℕ)
    (hfour hpolicyFrontier hcoefficientFuel hcoefficientBits hparameter hcircuit
      hresult hhandoff henvelopeFuel hstage hcall henvelopeBits hmode
      hlimitsCode hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel
      hsemanticFuel hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfComputableLimitsParameter profile copyBound
        oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient frontier parameterCoefficient
        hfour hpolicyFrontier hcoefficientFuel hcoefficientBits hparameter
        hcircuit hresult hhandoff henvelopeFuel hstage hcall henvelopeBits
        hmode hlimitsCode hsemanticStage hfrontEndBits hsemanticBits
        hfrontEndFuel hsemanticFuel hlimitsCodeFree
        hsemanticFree).verifier.degree =
      honestRecoveryDegree :=
  rfl

/-- The machine built this way keeps the recovery witness shape. -/
theorem executableRecoveryMachineOfComputableLimitsParameter_witnessShape
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      parameterCoefficient : ℕ)
    (hfour hpolicyFrontier hcoefficientFuel hcoefficientBits hparameter hcircuit
      hresult hhandoff henvelopeFuel hstage hcall henvelopeBits hmode
      hlimitsCode hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel
      hsemanticFuel hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfComputableLimitsParameter profile copyBound
        oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient frontier parameterCoefficient
        hfour hpolicyFrontier hcoefficientFuel hcoefficientBits hparameter
        hcircuit hresult hhandoff henvelopeFuel hstage hcall henvelopeBits
        hmode hlimitsCode hsemanticStage hfrontEndBits hsemanticBits
        hfrontEndFuel hsemanticFuel hlimitsCodeFree
        hsemanticFree).witnessShape =
      RecoveryWitnessShape.recoveryWitnessShape :=
  rfl

end NearCubicWires.ValidatorUnconditionalBudget
