import Proof.Circuits.ValidatorUnconditionalBudget

namespace NearCubicWires.ValidatorLeafPremiseSweep

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
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.ValidatorUnconditionalBudget
open NearCubicWires.VerifiedLinker

/-! ## §1 The structural prefix's output

The nested-presence guard is a three-way rejection: it returns the handoff
unchanged or the closed numeral `0`.  So the prefix's output never exceeds the
handoff record, and `ValidatorStageEnvelopes` §4's trace ledger applies to it
verbatim. -/

/-- The nested-presence guard never widens its handoff. -/
theorem recoveryValidatorStructuralPrefixOutput_le
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryValidatorStructuralPrefixOutput limits raw ≤
      recoveryValidatorHandoffOutput limits raw := by
  simp only [recoveryValidatorStructuralPrefixOutput,
    recoveryNestedPresenceOutput]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · split
      · exact Nat.zero_le _
      · exact le_rfl

/-- **The structural prefix's output width, unconditionally.**  Sixteen times
the prefix width — the same ledger the prefix's own register requirement is
charged from. -/
theorem natBitLength_recoveryValidatorStructuralPrefixOutput_le
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    natBitLength (recoveryValidatorStructuralPrefixOutput limits raw) ≤
      16 * recoveryValidatorPrefixWidth limits raw :=
  (natBitLength_mono (recoveryValidatorStructuralPrefixOutput_le limits raw)).trans
    ((natBitLength_mono (recoveryValidatorHandoffOutput_le limits raw)).trans
      (recoveryValidatorHandoffBits_le limits raw))

/-- **`hhandoff`, discharged.**  It is the prefix width certificate again. -/
theorem polyBounded_structuralPrefixOutput
    {limits : RecoveryWitnessLimits} {raw measure coefficient degree : ℕ}
    (hwidth :
      PolyBounded (recoveryValidatorPrefixWidth limits raw) measure coefficient
        degree) :
    PolyBounded
      (natBitLength (recoveryValidatorStructuralPrefixOutput limits raw))
      measure (16 * coefficient) degree :=
  (hwidth.const_mul 16).mono
    (natBitLength_recoveryValidatorStructuralPrefixOutput_le limits raw)

/-! ## §2 The oracle stage's width

`recoveryOracleStageWidth` is a two-way maximum whose second entry is the
handoff itself, so §1 pays for half of it and the other half *is* `hresult`. -/

/-- **`hstage`, discharged in favour of `hresult`.** -/
theorem polyBounded_recoveryOracleStageWidth
    {handoff measure coefficient degree : ℕ}
    (hresult :
      PolyBounded (natBitLength (recoveryOracleValidationResult handoff))
        measure coefficient degree)
    (hhandoff : PolyBounded (natBitLength handoff) measure coefficient degree) :
    PolyBounded (recoveryOracleStageWidth handoff) measure coefficient degree :=
  (hresult.max hhandoff).coefficient_mono (le_of_eq (max_self coefficient))

theorem hvalidator_at_computableLimits_swept
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier stageCoefficient parameterCoefficient : ℕ)
    (hfour : 4 ≤ frontier)
    (hpolicyFrontier : 204800 * (parameterCoefficient + 1) ^ 2 ≤ frontier)
    (hhandoffFrontier :
      16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) ≤ frontier)
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
            recoveryVerifierDegree request.measure := by
  have hprefix :
      ∀ request : WeakVerifierRequest,
        PolyBounded
          (recoveryValidatorPrefixWidth
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness))
          request.measure
          (max 4 (204800 * (parameterCoefficient + 1) ^ 2))
          recoveryVerifierDegree :=
    fun request =>
      polyBounded_computableLimits_prefixWidth_of_parameter profile copyBound
        oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        (by norm_num [recoveryVerifierDegree])
        (by norm_num [recoveryVerifierDegree]) hparameter request
  have hhandoff :
      ∀ request : WeakVerifierRequest,
        PolyBounded
          (natBitLength
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          request.measure frontier recoveryVerifierDegree :=
    fun request =>
      (polyBounded_structuralPrefixOutput (hprefix request)).coefficient_mono
        hhandoffFrontier
  exact hvalidator_at_computableLimits_degree_four profile copyBound oracleArity
    oracleSizeCap sumArity symmetricWireCap thresholdWireCap frontier
    stageCoefficient parameterCoefficient hfour hpolicyFrontier
    hcoefficientFuel hcoefficientBits hparameter hcircuit hresult hhandoff
    henvelopeFuel
    (fun request =>
      polyBounded_recoveryOracleStageWidth (hresult request) (hhandoff request))
    hcall henvelopeBits hmode

def executableRecoveryMachineOfSweptLeaves
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
    (hhandoffFrontier :
      16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) ≤ frontier)
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
    (hvalidator_at_computableLimits_swept profile copyBound oracleArity
      oracleSizeCap sumArity symmetricWireCap thresholdWireCap frontier
      stageCoefficient parameterCoefficient hfour hpolicyFrontier
      hhandoffFrontier hcoefficientFuel hcoefficientBits hparameter hcircuit
      hresult henvelopeFuel hcall henvelopeBits hmode)
    hlimitsCodeFree hsemanticFree

/-- The swept machine still charges at the published degree. -/
theorem executableRecoveryMachineOfSweptLeaves_verifier_degree
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      parameterCoefficient : ℕ)
    (hfour hpolicyFrontier hhandoffFrontier hcoefficientFuel hcoefficientBits
      hparameter hcircuit hresult henvelopeFuel hcall henvelopeBits hmode
      hlimitsCode hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel
      hsemanticFuel hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfSweptLeaves profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient frontier parameterCoefficient
        hfour hpolicyFrontier hhandoffFrontier hcoefficientFuel
        hcoefficientBits hparameter hcircuit hresult henvelopeFuel hcall
        henvelopeBits hmode hlimitsCode hsemanticStage hfrontEndBits
        hsemanticBits hfrontEndFuel hsemanticFuel hlimitsCodeFree
        hsemanticFree).verifier.degree =
      honestRecoveryDegree :=
  rfl

/-- The swept machine keeps the recovery witness shape. -/
theorem executableRecoveryMachineOfSweptLeaves_witnessShape
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      parameterCoefficient : ℕ)
    (hfour hpolicyFrontier hhandoffFrontier hcoefficientFuel hcoefficientBits
      hparameter hcircuit hresult henvelopeFuel hcall henvelopeBits hmode
      hlimitsCode hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel
      hsemanticFuel hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfSweptLeaves profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient frontier parameterCoefficient
        hfour hpolicyFrontier hhandoffFrontier hcoefficientFuel
        hcoefficientBits hparameter hcircuit hresult henvelopeFuel hcall
        henvelopeBits hmode hlimitsCode hsemanticStage hfrontEndBits
        hsemanticBits hfrontEndFuel hsemanticFuel hlimitsCodeFree
        hsemanticFree).witnessShape =
      RecoveryWitnessShape.recoveryWitnessShape :=
  rfl

end NearCubicWires.ValidatorLeafPremiseSweep
