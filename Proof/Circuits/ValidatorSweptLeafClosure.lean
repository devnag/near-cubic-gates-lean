import Proof.Circuits.ValidatorOracleResultWidth

namespace NearCubicWires.ValidatorSweptLeafClosure

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
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorModeWidthClosure
open NearCubicWires.ValidatorOracleResultWidth
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.ValidatorUnconditionalBudget
open NearCubicWires.VerifiedLinker

theorem hvalidator_at_computableLimits_of_four_leaves
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
            recoveryVerifierDegree request.measure := by
  obtain ⟨policyBudget, hpolicyBudget⟩ :
      ∃ value : ℕ, max 4 (204800 * (parameterCoefficient + 1) ^ 2) = value :=
    ⟨_, rfl⟩
  have hresultBudget : 512 * policyBudget + 2 ≤ frontier := by
    rw [hpolicyBudget] at hresultFrontier
    exact hresultFrontier
  have hhandoffFrontier :
      16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2) ≤ frontier := by
    rw [hpolicyBudget]
    omega
  have hresultCoefficient :
      32 * (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2)) + 2 ≤
        frontier := by
    rw [hpolicyBudget]
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
  exact hvalidator_at_computableLimits_swept profile copyBound oracleArity
    oracleSizeCap sumArity symmetricWireCap thresholdWireCap frontier
    stageCoefficient parameterCoefficient hfour hpolicyFrontier
    hhandoffFrontier hcoefficientFuel hcoefficientBits hparameter hcircuit
    (fun request =>
      (polyBounded_recoveryOracleValidationResult
        (polyBounded_structuralPrefixOutput (hprefix request))).coefficient_mono
          hresultCoefficient)
    henvelopeFuel hcall henvelopeBits
    (fun request =>
      (polyBounded_legalSumPrefixOutput (hprefix request)).coefficient_mono
        hhandoffFrontier)

def executableRecoveryMachineOfFourSweptLeaves
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
    (hvalidator_at_computableLimits_of_four_leaves profile copyBound oracleArity
      oracleSizeCap sumArity symmetricWireCap thresholdWireCap frontier
      stageCoefficient parameterCoefficient hfour hpolicyFrontier
      hresultFrontier hcoefficientFuel hcoefficientBits hparameter hcircuit
      henvelopeFuel hcall henvelopeBits)
    hlimitsCodeFree hsemanticFree

theorem executableRecoveryMachineOfFourSweptLeaves_verifier_degree
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      parameterCoefficient : ℕ)
    (hfour hpolicyFrontier hresultFrontier hcoefficientFuel hcoefficientBits
      hparameter hcircuit henvelopeFuel hcall henvelopeBits hlimitsCode
      hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel hsemanticFuel
      hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfFourSweptLeaves profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient frontier parameterCoefficient
        hfour hpolicyFrontier hresultFrontier hcoefficientFuel
        hcoefficientBits hparameter hcircuit henvelopeFuel hcall
        henvelopeBits hlimitsCode hsemanticStage hfrontEndBits hsemanticBits
        hfrontEndFuel hsemanticFuel hlimitsCodeFree
        hsemanticFree).verifier.degree =
      honestRecoveryDegree :=
  rfl

theorem executableRecoveryMachineOfFourSweptLeaves_witnessShape
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (limitsCodeProgram semanticStage : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
      WeakVerifierRequest → ℕ)
    (frontEndCoefficient semanticCoefficient stageCoefficient frontier
      parameterCoefficient : ℕ)
    (hfour hpolicyFrontier hresultFrontier hcoefficientFuel hcoefficientBits
      hparameter hcircuit henvelopeFuel hcall henvelopeBits hlimitsCode
      hsemanticStage hfrontEndBits hsemanticBits hfrontEndFuel hsemanticFuel
      hlimitsCodeFree hsemanticFree) :
    (executableRecoveryMachineOfFourSweptLeaves profile copyBound oracleArity
        oracleSizeCap sumArity symmetricWireCap thresholdWireCap
        limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
        semanticBits semanticFuel semanticOutput frontEndCoefficient
        semanticCoefficient stageCoefficient frontier parameterCoefficient
        hfour hpolicyFrontier hresultFrontier hcoefficientFuel
        hcoefficientBits hparameter hcircuit henvelopeFuel hcall
        henvelopeBits hlimitsCode hsemanticStage hfrontEndBits hsemanticBits
        hfrontEndFuel hsemanticFuel hlimitsCodeFree
        hsemanticFree).witnessShape =
      RecoveryWitnessShape.recoveryWitnessShape :=
  rfl

/-! ## §3 What the validator still asks for

Four request-indexed charges.  Two of them now have their deepest missing
ledger published:

1. `hcircuit` — `booleanCircuitValidationFuel`.  `ValidatorCircuitStageWidths`
   §3 reduced it to two named fuel charges.  The first,
   `booleanCircuitPreparationFuel`, is closed by
   `ValidatorNodePreparationLedger` §3 at degree `3` over the node-list code's
   own width: the tagged spine's walk, the tagged codec's counting ledger and
   the structural parse's atom-width ledger pay for the whole cone.  What is
   left of `hcircuit` is the *second* charge,
   `booleanNodeTopologyRangeFuel` — a fixed Boolean range aggregation whose
   generated half is published and whose per-descriptor lookup bottoms out in
   `nativeLtRequestFuel`, closed by `ValidatorCircuitStageWidths` §2 — plus the
   chain assembly through `booleanNodeListValidationFuel`.

2. `hcall` — `recoveryOracleCallBits`, a `nativeContextCallBits` over the
   handoff's projections, the result of `ValidatorOracleResultWidth` §2 and
   `booleanCircuitValidationBits`.  The result half is now paid; the register
   requirement is an eight-way maximum of stage widths with no published ledger.

3. `henvelopeFuel`, 4. `henvelopeBits` — `ValidatorLegalSumWalk` §1 and §2
   reduce these to ten (respectively eleven) named legal-sum sub-stages.  On the
   fuel side the walk bottoms out in `supportedGateRelationFuel`, the one charge
   in that cone with no published bound; on the width side none of the eleven
   sub-stages has a ledger yet.

Nothing on this list is a *validator* obligation: every one lives strictly below
the stage boundary. -/

end NearCubicWires.ValidatorSweptLeafClosure
