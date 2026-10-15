import Proof.Circuits.ValidatorCircuitLeafClosure

namespace NearCubicWires.ValidatorThreeLeafClosure

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
open NearCubicWires.ValidatorCircuitLeafClosure
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.ValidatorSweptLeafClosure
open NearCubicWires.VerifiedLinker

noncomputable def circuitLeafFrontier (parameterCoefficient : ℕ) : ℕ :=
  (exists_booleanCircuitValidationFuel_polyBounded 4
    (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2))).choose

theorem circuitLeafFrontier_spec (parameterCoefficient inputLength raw measure : ℕ)
    (hraw : PolyBounded (natBitLength raw) measure 4 1)
    (harity :
      PolyBounded (natBitLength inputLength) measure
        (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2)) 2) :
    PolyBounded (booleanCircuitValidationFuel inputLength raw) measure
      (circuitLeafFrontier parameterCoefficient) 3 :=
  (exists_booleanCircuitValidationFuel_polyBounded 4
      (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2))).choose_spec
    inputLength raw measure hraw harity

theorem hcircuit_at_circuitLeafFrontier
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (parameterCoefficient : ℕ)
    (hparameter : ∀ request : WeakVerifierRequest,
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          request.inputArity)
        request.measure parameterCoefficient 1)
    (request : WeakVerifierRequest) :
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
      request.measure (circuitLeafFrontier parameterCoefficient)
      recoveryVerifierDegree := by
  have hprefix :=
    polyBounded_computableLimits_prefixWidth_of_parameter profile copyBound
      oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
      (by omega : (1 : ℕ) ≤ 2) (by omega : 2 * 1 ≤ 2) hparameter request
  have hcode :=
    polyBounded_handoffOracleCode_structuralPrefixOutput
      (limits :=
        computableLimitsOf profile copyBound oracleArity oracleSizeCap sumArity
          symmetricWireCap thresholdWireCap request.inputArity)
      (polyBounded_witnessWidth request)
  have harity :=
    polyBounded_natBitLength_of_le (polyBounded_structuralPrefixOutput hprefix)
      ((Nat.unpair_left_le _).trans
        ((Nat.unpair_right_le _).trans
          ((Nat.unpair_right_le _).trans
            ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _)))))
  exact (circuitLeafFrontier_spec parameterCoefficient _ _ request.measure hcode
    harity).degree_mono (by norm_num [recoveryVerifierDegree])

theorem hvalidator_at_computableLimits_of_three_leaves
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier stageCoefficient parameterCoefficient : ℕ)
    (hfour : 4 ≤ frontier)
    (hpolicyFrontier : 204800 * (parameterCoefficient + 1) ^ 2 ≤ frontier)
    (hresultFrontier :
      512 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) + 2 ≤ frontier)
    (hcircuitFrontier : circuitLeafFrontier parameterCoefficient ≤ frontier)
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
    (henvelopeFuel : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeFuel (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput
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
  hvalidator_at_computableLimits_of_four_leaves profile copyBound oracleArity
    oracleSizeCap sumArity symmetricWireCap thresholdWireCap frontier
    stageCoefficient parameterCoefficient hfour hpolicyFrontier hresultFrontier
    hcoefficientFuel hcoefficientBits hparameter
    (fun request =>
      (hcircuit_at_circuitLeafFrontier profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        parameterCoefficient hparameter request).coefficient_mono
        hcircuitFrontier)
    henvelopeFuel hcall henvelopeBits

noncomputable def executableRecoveryMachineOfThreeSweptLeaves
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
    (hresultFrontier :
      512 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) + 2 ≤ frontier)
    (hcircuitFrontier : circuitLeafFrontier parameterCoefficient ≤ frontier)
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
    (henvelopeFuel : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeFuel (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput
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
    (hvalidator_at_computableLimits_of_three_leaves profile copyBound
      oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
      frontier stageCoefficient parameterCoefficient hfour hpolicyFrontier
      hresultFrontier hcircuitFrontier hcoefficientFuel hcoefficientBits
      hparameter henvelopeFuel hcall henvelopeBits)
    hlimitsCodeFree hsemanticFree

theorem executableRecoveryMachineOfThreeSweptLeaves_verifier_degree
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      parameterCoefficient : ℕ)
    (hfour hpolicyFrontier hresultFrontier hcircuitFrontier hcoefficientFuel
      hcoefficientBits hparameter henvelopeFuel hcall henvelopeBits hlimitsCode
      hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel hsemanticFuel
      hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfThreeSweptLeaves profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient frontier parameterCoefficient
        hfour hpolicyFrontier hresultFrontier hcircuitFrontier
        hcoefficientFuel hcoefficientBits hparameter henvelopeFuel hcall
        henvelopeBits hlimitsCode hsemanticStage hfrontEndBits hsemanticBits
        hfrontEndFuel hsemanticFuel hlimitsCodeFree
        hsemanticFree).verifier.degree =
      honestRecoveryDegree :=
  rfl

theorem executableRecoveryMachineOfThreeSweptLeaves_witnessShape
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      parameterCoefficient : ℕ)
    (hfour hpolicyFrontier hresultFrontier hcircuitFrontier hcoefficientFuel
      hcoefficientBits hparameter henvelopeFuel hcall henvelopeBits hlimitsCode
      hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel hsemanticFuel
      hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfThreeSweptLeaves profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient frontier parameterCoefficient
        hfour hpolicyFrontier hresultFrontier hcircuitFrontier
        hcoefficientFuel hcoefficientBits hparameter henvelopeFuel hcall
        henvelopeBits hlimitsCode hsemanticStage hfrontEndBits hsemanticBits
        hfrontEndFuel hsemanticFuel hlimitsCodeFree
        hsemanticFree).witnessShape =
      RecoveryWitnessShape.recoveryWitnessShape :=
  rfl

end NearCubicWires.ValidatorThreeLeafClosure
