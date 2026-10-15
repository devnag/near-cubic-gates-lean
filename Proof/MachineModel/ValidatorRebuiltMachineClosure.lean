import Proof.MachineModel.ValidatorRebuiltMachineSpine
import Proof.Circuits.ValidatorSweptLeafClosure

namespace NearCubicWires.ValidatorRebuiltMachineClosure

open NearCubicWires
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeListRebuildProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.RecoveryLimitsFrontEndProgram
open NearCubicWires.RecoveryVerifierResourceEnvelope
open NearCubicWires.ValidatorCanonicalizerRebuildLedger
open NearCubicWires.ValidatorCircuitRebuildLedger
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorEndpointRebuildProgram
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorModeWidthClosure
open NearCubicWires.ValidatorOracleResultWidth
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorRebuiltMachineSpine
open NearCubicWires.ValidatorRebuiltSpineBudget
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

theorem hvalidatorRebuild_at_computableLimits
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier stageCoefficient parameterCoefficient : ℕ)
    (hfour : 4 ≤ frontier)
    (hpolicyFrontier : 204800 * (parameterCoefficient + 1) ^ 2 ≤ frontier)
    (hresultFrontier :
      512 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) + 2 ≤ frontier)
    (hcoefficientFuel :
      (max recoveryValidatorStructuralPrefixFuel <|
        max
          (recoveryOracleValidationRebuildFuelCoefficient frontier
            (max frontier frontier)) <|
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
        (booleanCircuitValidationRebuildFuel
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
        (recoveryOracleCallRebuildBits (WeakVerifierRequest.length request)
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
      recoveryWitnessValidatorRebuildBits (WeakVerifierRequest.length request)
          (computableLimitsOf profile copyBound oracleArity oracleSizeCap
            sumArity symmetricWireCap thresholdWireCap request.inputArity)
          (encodeBitInput request.witness) ≤
        polynomialBudget
          (recoveryValidatorRebuildSpineCoefficient stageCoefficient)
          recoveryVerifierDegree request.measure) ∧
      ∀ request : WeakVerifierRequest,
        recoveryWitnessValidatorRebuildFuel (WeakVerifierRequest.length request)
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness) ≤
          polynomialBudget
            (recoveryValidatorRebuildSpineCoefficient stageCoefficient)
            recoveryVerifierDegree request.measure := by
  have hhandoffFrontier :
      16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) ≤ frontier := by
    omega
  have hresultCoefficient :
      32 * (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2)) + 2 ≤
        frontier := by
    omega
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
  have hresult :
      ∀ request : WeakVerifierRequest,
        PolyBounded
          (natBitLength
            (recoveryOracleValidationResult
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness))))
          request.measure frontier recoveryVerifierDegree :=
    fun request =>
      (polyBounded_recoveryOracleValidationResult
        (polyBounded_structuralPrefixOutput
          (hprefix request))).coefficient_mono hresultCoefficient
  have hmode :
      ∀ request : WeakVerifierRequest,
        PolyBounded
          (natBitLength
            (recoveryValidatorLegalSumPrefixOutput
              (WeakVerifierRequest.length request)
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          request.measure frontier recoveryVerifierDegree :=
    fun request =>
      (polyBounded_legalSumPrefixOutput (hprefix request)).coefficient_mono
        hhandoffFrontier
  exact hvalidatorRebuild_of_stageFrontier
    (computableLimitsOf profile copyBound oracleArity oracleSizeCap sumArity
      symmetricWireCap thresholdWireCap)
    stageCoefficient recoveryVerifierDegree le_rfl
    (fun request =>
      (recoveryValidatorMaximumStageRebuildFuel_polyBounded (hcircuit request)
        (hresult request) (hhandoff request)
        (henvelopeFuel request)).coefficient_mono hcoefficientFuel)
    (fun request =>
      (recoveryValidatorMaximumStageRebuildBits_polyBounded
        ((polyBounded_requestLengthWidth_at
          (show (1 : ℕ) ≤ recoveryVerifierDegree by
            norm_num [recoveryVerifierDegree]) request).coefficient_mono hfour)
        ((hprefix request).coefficient_mono
          (Nat.max_le.2 ⟨hfour, hpolicyFrontier⟩))
        (polyBounded_recoveryOracleStageWidth (hresult request)
          (hhandoff request))
        (hcall request) (henvelopeBits request)
        (hmode request)).coefficient_mono hcoefficientBits)

/-- **The rebuilt validator's budget, from the two rebuilt callee widths.** -/
theorem hvalidatorRebuild_at_computableLimits_of_two_widths
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (frontier widthFrontier stageCoefficient parameterCoefficient : ℕ)
    (hfour : 4 ≤ frontier)
    (hwidthFour : 4 ≤ widthFrontier)
    (hpolicyFrontier : 204800 * (parameterCoefficient + 1) ^ 2 ≤ frontier)
    (hresultFrontier :
      512 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) + 2 ≤ frontier)
    (hwidthHandoffFrontier :
      16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) ≤ widthFrontier)
    (hwidthCircuitFrontier :
      2048 * max (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2))
          (max 4 2) ≤ widthFrontier)
    (hcallFrontier : 128 * widthFrontier + 8 ≤ frontier)
    (hcoefficientFuel :
      (max recoveryValidatorStructuralPrefixFuel <|
        max
          (recoveryOracleValidationRebuildFuelCoefficient frontier
            (max frontier frontier)) <|
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
        (booleanCircuitValidationRebuildFuel
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
    (henvelopeFuel : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeFuel (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (hnode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (booleanNodeListValidationRebuildBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitNodesCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure widthFrontier recoveryVerifierDegree)
    (hnat : ∀ request : WeakVerifierRequest,
      PolyBounded
        (canonicalNatValidationRebuildBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitOutputCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure widthFrontier recoveryVerifierDegree)
    (henvelopeBits : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeBits (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree) :
    (∀ request : WeakVerifierRequest,
      recoveryWitnessValidatorRebuildBits (WeakVerifierRequest.length request)
          (computableLimitsOf profile copyBound oracleArity oracleSizeCap
            sumArity symmetricWireCap thresholdWireCap request.inputArity)
          (encodeBitInput request.witness) ≤
        polynomialBudget
          (recoveryValidatorRebuildSpineCoefficient stageCoefficient)
          recoveryVerifierDegree request.measure) ∧
      ∀ request : WeakVerifierRequest,
        recoveryWitnessValidatorRebuildFuel (WeakVerifierRequest.length request)
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness) ≤
          polynomialBudget
            (recoveryValidatorRebuildSpineCoefficient stageCoefficient)
            recoveryVerifierDegree request.measure :=
  hvalidatorRebuild_at_computableLimits profile copyBound oracleArity
    oracleSizeCap sumArity symmetricWireCap thresholdWireCap frontier
    stageCoefficient parameterCoefficient hfour hpolicyFrontier hresultFrontier
    hcoefficientFuel hcoefficientBits hparameter hcircuit henvelopeFuel
    (fun request =>
      (hcall_rebuild_at_computableLimits profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap widthFrontier
        parameterCoefficient hwidthFour hwidthHandoffFrontier
        hwidthCircuitFrontier hparameter hnode hnat request).coefficient_mono
        hcallFrontier)
    henvelopeBits

/-! ## §3 The machine constructor at the rebuilt validator -/

/-- **The executable recovery machine at the computable limits family, over the
rebuilt recovery-witness validator.**  Its verifier runs
`recoveryWitnessValidatorRebuildProgram`, whose output is the pure validator's
own output at every input, so the witness shape, the verifier degree and the
verifier's execution are the published ones.  The validator side of the
constructor is: seven numeric side conditions, the family's own parameter
certificate, the rebuilt circuit validator's fuel, the two rebuilt callee
widths, and the legal-sum envelope's fuel and width. -/
def executableRecoveryMachineOfRebuiltValidator
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      widthFrontier parameterCoefficient : ℕ)
    (hfour : 4 ≤ frontier)
    (hwidthFour : 4 ≤ widthFrontier)
    (hpolicyFrontier : 204800 * (parameterCoefficient + 1) ^ 2 ≤ frontier)
    (hresultFrontier :
      512 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) + 2 ≤ frontier)
    (hwidthHandoffFrontier :
      16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) ≤ widthFrontier)
    (hwidthCircuitFrontier :
      2048 * max (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2))
          (max 4 2) ≤ widthFrontier)
    (hcallFrontier : 128 * widthFrontier + 8 ≤ frontier)
    (hcoefficientFuel :
      (max recoveryValidatorStructuralPrefixFuel <|
        max
          (recoveryOracleValidationRebuildFuelCoefficient frontier
            (max frontier frontier)) <|
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
        (booleanCircuitValidationRebuildFuel
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
    (henvelopeFuel : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeFuel (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput
            (computableLimitsOf profile copyBound oracleArity oracleSizeCap
              sumArity symmetricWireCap thresholdWireCap request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier recoveryVerifierDegree)
    (hnode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (booleanNodeListValidationRebuildBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitNodesCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure widthFrontier recoveryVerifierDegree)
    (hnat : ∀ request : WeakVerifierRequest,
      PolyBounded
        (canonicalNatValidationRebuildBits
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (booleanCircuitOutputCode
            (handoffOracleCode
              (recoveryValidatorStructuralPrefixOutput
                (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                  sumArity symmetricWireCap thresholdWireCap
                  request.inputArity)
                (encodeBitInput request.witness)))))
        request.measure widthFrontier recoveryVerifierDegree)
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
  executableRecoveryMachineOfRebuildComponents
    (computableLimitsOf profile copyBound oracleArity oracleSizeCap sumArity
      symmetricWireCap thresholdWireCap)
    limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel semanticBits
    semanticFuel semanticOutput frontEndCoefficient
    (recoveryValidatorRebuildSpineCoefficient stageCoefficient)
    semanticCoefficient hlimitsCode hsemanticStage hfrontEndBits
    (hvalidatorRebuild_at_computableLimits_of_two_widths profile copyBound
      oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
      frontier widthFrontier stageCoefficient parameterCoefficient hfour
      hwidthFour hpolicyFrontier hresultFrontier hwidthHandoffFrontier
      hwidthCircuitFrontier hcallFrontier hcoefficientFuel hcoefficientBits
      hparameter hcircuit henvelopeFuel hnode hnat henvelopeBits).1
    hsemanticBits hfrontEndFuel
    (hvalidatorRebuild_at_computableLimits_of_two_widths profile copyBound
      oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
      frontier widthFrontier stageCoefficient parameterCoefficient hfour
      hwidthFour hpolicyFrontier hresultFrontier hwidthHandoffFrontier
      hwidthCircuitFrontier hcallFrontier hcoefficientFuel hcoefficientBits
      hparameter hcircuit henvelopeFuel hnode hnat henvelopeBits).2
    hsemanticFuel hlimitsCodeFree hsemanticFree

/-- The rebuilt-validator machine charges at the published degree. -/
theorem executableRecoveryMachineOfRebuiltValidator_verifier_degree
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      widthFrontier parameterCoefficient : ℕ)
    (hfour hwidthFour hpolicyFrontier hresultFrontier hwidthHandoffFrontier
      hwidthCircuitFrontier hcallFrontier hcoefficientFuel hcoefficientBits
      hparameter hcircuit henvelopeFuel hnode hnat henvelopeBits hlimitsCode
      hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel hsemanticFuel
      hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfRebuiltValidator profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient frontier widthFrontier
        parameterCoefficient hfour hwidthFour hpolicyFrontier hresultFrontier
        hwidthHandoffFrontier hwidthCircuitFrontier hcallFrontier
        hcoefficientFuel hcoefficientBits hparameter hcircuit henvelopeFuel
        hnode hnat henvelopeBits hlimitsCode hsemanticStage hfrontEndBits
        hsemanticBits hfrontEndFuel hsemanticFuel hlimitsCodeFree
        hsemanticFree).verifier.degree =
      honestRecoveryDegree :=
  rfl

/-- The rebuilt-validator machine keeps the recovery witness shape. -/
theorem executableRecoveryMachineOfRebuiltValidator_witnessShape
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      widthFrontier parameterCoefficient : ℕ)
    (hfour hwidthFour hpolicyFrontier hresultFrontier hwidthHandoffFrontier
      hwidthCircuitFrontier hcallFrontier hcoefficientFuel hcoefficientBits
      hparameter hcircuit henvelopeFuel hnode hnat henvelopeBits hlimitsCode
      hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel hsemanticFuel
      hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfRebuiltValidator profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient frontier widthFrontier
        parameterCoefficient hfour hwidthFour hpolicyFrontier hresultFrontier
        hwidthHandoffFrontier hwidthCircuitFrontier hcallFrontier
        hcoefficientFuel hcoefficientBits hparameter hcircuit henvelopeFuel
        hnode hnat henvelopeBits hlimitsCode hsemanticStage hfrontEndBits
        hsemanticBits hfrontEndFuel hsemanticFuel hlimitsCodeFree
        hsemanticFree).witnessShape =
      RecoveryWitnessShape.recoveryWitnessShape :=
  rfl

/-- The rebuilt-validator machine's verifier executes the semantic stage. -/
theorem executableRecoveryMachineOfRebuiltValidator_verifier_execute
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      widthFrontier parameterCoefficient : ℕ)
    (hfour hwidthFour hpolicyFrontier hresultFrontier hwidthHandoffFrontier
      hwidthCircuitFrontier hcallFrontier hcoefficientFuel hcoefficientBits
      hparameter hcircuit henvelopeFuel hnode hnat henvelopeBits hlimitsCode
      hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel hsemanticFuel
      hlimitsCodeFree hsemanticFree)
    (request : WeakVerifierRequest) :
    (executableRecoveryMachineOfRebuiltValidator profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient frontier widthFrontier
        parameterCoefficient hfour hwidthFour hpolicyFrontier hresultFrontier
        hwidthHandoffFrontier hwidthCircuitFrontier hcallFrontier
        hcoefficientFuel hcoefficientBits hparameter hcircuit henvelopeFuel
        hnode hnat henvelopeBits hlimitsCode hsemanticStage hfrontEndBits
        hsemanticBits hfrontEndFuel hsemanticFuel hlimitsCodeFree
        hsemanticFree).verifier.execute request =
      semanticOutput request :=
  executableRecoveryMachineOfRebuildComponents_verifier_execute _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ request

/-! ## §4 What the validator side still asks for

Five request-indexed charges, none of them a validator obligation:

1. `hcircuit` — `booleanCircuitValidationRebuildFuel`.  The frozen twin is
   closed at `ValidatorThreeLeafClosure.circuitLeafFrontier`; the rebuilt
   validator's fuel is the same eight-stage `linkFuel` sum with the node-list
   and natural stages replaced, so the residue is the two rebuilt stages' own
   fuel.  Neither has a published polynomial ledger yet.

2. `hnode` — `booleanNodeListValidationRebuildBits`, reduced by
   `ValidatorRebuildWidthLedger.booleanNodeListValidationRebuildBits_le_of_prepare_le`
   to `booleanNodeListPrepareBits` and one balanced measurement.

3. `hnat` — `canonicalNatValidationRebuildBits`, reduced by
   `ValidatorRebuildWidthLedger.canonicalNatValidationRebuildBits_le_measurements`
   to five balanced measurements.

4. `henvelopeFuel`, `henvelopeBits` — the legal-sum envelope, carried unchanged
   from `ValidatorThreeLeafClosure` §4.  Its ten stages are *not* rebuilt here:
   `recoveryLegalSumQStageProgram` links `canonicalNatValidationProgram`, and
   `recoveryLegalTermCoefficientStageProgram`,
   `recoveryLegalTermCircuitStageProgram`,
   `recoveryLegalTermBitCapStageProgram`, `recoveryLegalTermMassProgram` and
   `recoveryLegalSumResourceTailProgram` link
   `balancedValidationSummaryProgram` at six call sites.  Those six stage
   programs are the remaining stage-swap sweep. -/

end NearCubicWires.ValidatorRebuiltMachineClosure
