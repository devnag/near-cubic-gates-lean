import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorRebuiltSpineBudget

/-!
# The composed recovery verifier and its machine, over the rebuilt validator

`ExecutableRecoveryMachine` §2 links the limits front end to
`recoveryWitnessValidatorProgram` *definitionally*, so the published machine
constructor charges `recoveryWitnessValidatorBits`, a name
`ValidatorTraversalWidthLedger` refutes every polynomial bound on.  The repair
`ValidatorEndpointRebuildProgram.recoveryWitnessValidatorRebuildProgram` cannot
be spent through that constructor: the composed verifier has to be re-linked on
it.

This module re-links it.  Every stage between the front end and the semantic
stage — the request extractor, the validation lowering, the input-preserving
call and the zero-sentinel gate — is *already* parameterized by the validator
program (`CanonicalRecoveryRequest.recoveryWitnessRequestProgram`), so the
rebuild is one substitution and the plumbing ledgers replay verbatim.  The
rebuilt validator returns `recoveryWitnessValidatorOutput` at every input
(`run_recoveryWitnessValidatorRebuildProgram_eq_validatorOutput`), so no
semantic obligation changes: `recoveryWitnessValidatorRequestOutput` is the
same function of the same limits and request.

* §1 the length-indexed validator, rebuilt.

* §2 the composed verifier stream, rebuilt.

* §3 the plumbing width and fuel ledgers, rebuilt.

* §4 the two component budgets at the published degree.

* §5 the polynomial runner and the machine.

* §6 the machine from its components.
-/

namespace NearCubicWires.ValidatorRebuiltMachineSpine

open NearCubicWires
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwiseEstimatorAccuracy
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryLimitsFrontEndProgram
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryWitnessShape
open NearCubicWires.RecoveryVerifierResourceEnvelope
open NearCubicWires.ValidatorEndpointRebuildProgram
open NearCubicWires.VerifiedLinker

open private recoveryVerifier_initialBitsFit from
  Proof.MachineModel.ExecutableRecoveryMachine

open private natBitLength_pair_le
  natBitLength_recoveryWitnessValidatorOutput_le measure_succ_le_budget
  component_le_budget from Proof.Amplification.RecoveryVerifierResourceEnvelope

/-! ## §1 The length-indexed validator, rebuilt -/

/-- The limits front end followed by the **rebuilt** recovery-witness
validator endpoint. -/
def recoveryVerifierValidatorRebuildProgram
    (limitsFrontEnd : NPOracleProgram) : NPOracleProgram :=
  linkPrograms limitsFrontEnd recoveryWitnessValidatorRebuildProgram

theorem recoveryVerifierValidatorRebuildProgram_oracleFree
    {limitsFrontEnd : NPOracleProgram} (hfrontEnd : OracleFree limitsFrontEnd) :
    OracleFree (recoveryVerifierValidatorRebuildProgram limitsFrontEnd) :=
  oracleFree_linkPrograms hfrontEnd
    recoveryWitnessValidatorRebuildProgram_oracleFree

def recoveryVerifierValidatorRebuildBits (frontEndBits inputLength : ℕ)
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength)
    (max frontEndBits
      (recoveryWitnessValidatorRebuildBits inputLength limits raw))

def recoveryVerifierValidatorRebuildFuel (frontEndFuel inputLength : ℕ)
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  linkFuel recoveryWitnessValidatorRebuildProgram frontEndFuel
    (recoveryWitnessValidatorRebuildFuel inputLength limits raw)

theorem run_recoveryVerifierValidatorRebuildProgram
    (limitsFrontEnd : NPOracleProgram)
    (frontEndBits frontEndFuel inputLength : ℕ)
    (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hfrontEnd :
      runNPOracleProgram limitsFrontEnd frontEndBits frontEndFuel
          (initialNPOracleState inputLength raw) =
        some (recoveryWitnessValidatorInput limits raw)) :
    runNPOracleProgram (recoveryVerifierValidatorRebuildProgram limitsFrontEnd)
        (recoveryVerifierValidatorRebuildBits frontEndBits inputLength limits
          raw)
        (recoveryVerifierValidatorRebuildFuel frontEndFuel inputLength limits
          raw)
        (initialNPOracleState inputLength raw) =
      some (recoveryWitnessValidatorOutput limits raw) := by
  have hlength :
      natBitLength inputLength ≤
        recoveryVerifierValidatorRebuildBits frontEndBits inputLength limits
          raw := Nat.le_max_left _ _
  have hpositive :
      1 ≤
        recoveryVerifierValidatorRebuildBits frontEndBits inputLength limits
          raw := by
    refine le_trans ?_ hlength
    unfold natBitLength
    omega
  have hfrontEndBits :
      frontEndBits ≤
        recoveryVerifierValidatorRebuildBits frontEndBits inputLength limits
          raw := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hvalidatorBits :
      recoveryWitnessValidatorRebuildBits inputLength limits raw ≤
        recoveryVerifierValidatorRebuildBits frontEndBits inputLength limits
          raw := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact run_linkPrograms hpositive hlength
    (run_bits_mono hfrontEnd hfrontEndBits)
    (run_bits_mono
      (run_recoveryWitnessValidatorRebuildProgram_eq_validatorOutput inputLength
        limits raw)
      hvalidatorBits)

/-! ## §2 The composed verifier stream, rebuilt -/

/-- **The rebuilt recovery verifier instruction stream.** -/
def recoveryVerifierRebuildProgram
    (limitsFrontEnd semanticStage : NPOracleProgram) : NPOracleProgram :=
  linkPrograms
    (recoveryWitnessRequestProgram
      (recoveryVerifierValidatorRebuildProgram limitsFrontEnd))
    semanticStage

theorem recoveryVerifierRebuildProgram_oracleFree
    {limitsFrontEnd semanticStage : NPOracleProgram}
    (hfrontEnd : OracleFree limitsFrontEnd)
    (hsemantic : OracleFree semanticStage) :
    OracleFree (recoveryVerifierRebuildProgram limitsFrontEnd semanticStage) :=
  oracleFree_linkPrograms
    (recoveryWitnessRequestProgram_oracleFree
      (recoveryVerifierValidatorRebuildProgram_oracleFree hfrontEnd))
    hsemantic

def recoveryVerifierRequestRebuildBits (frontEndBits : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest) : ℕ :=
  recoveryWitnessRequestBits
    (recoveryVerifierValidatorRebuildBits frontEndBits request.length limits
      (encodeBitInput request.witness))
    (recoveryWitnessValidatorOutput limits (encodeBitInput request.witness))
    request

def recoveryVerifierRequestRebuildFuel (limitsFrontEnd : NPOracleProgram)
    (frontEndFuel : ℕ) (limits : RecoveryWitnessLimits)
    (request : WeakVerifierRequest) : ℕ :=
  recoveryWitnessRequestFuel
    (recoveryVerifierValidatorRebuildProgram limitsFrontEnd)
    (recoveryVerifierValidatorRebuildFuel frontEndFuel request.length limits
      (encodeBitInput request.witness))
    (recoveryWitnessValidatorOutput limits (encodeBitInput request.witness))

def recoveryVerifierRebuildBits (frontEndBits semanticBits : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest) : ℕ :=
  max (natBitLength request.length)
    (max (recoveryVerifierRequestRebuildBits frontEndBits limits request)
      semanticBits)

def recoveryVerifierRebuildFuel (limitsFrontEnd semanticStage : NPOracleProgram)
    (frontEndFuel semanticFuel : ℕ) (limits : RecoveryWitnessLimits)
    (request : WeakVerifierRequest) : ℕ :=
  linkFuel semanticStage
    (recoveryVerifierRequestRebuildFuel limitsFrontEnd frontEndFuel limits
      request)
    semanticFuel

/-- **Exact execution of the rebuilt composed verifier stream.** -/
theorem run_recoveryVerifierRebuildProgram
    (limitsFrontEnd semanticStage : NPOracleProgram)
    (frontEndBits frontEndFuel semanticBits semanticFuel : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest)
    (semanticValue : ℕ)
    (hfrontEnd :
      runNPOracleProgram limitsFrontEnd frontEndBits frontEndFuel
          (initialNPOracleState request.length
            (encodeBitInput request.witness)) =
        some
          (recoveryWitnessValidatorInput limits
            (encodeBitInput request.witness)))
    (hsemantic :
      runNPOracleProgram semanticStage semanticBits semanticFuel
          (initialNPOracleState request.length
            (recoveryWitnessValidatorRequestOutput limits request)) =
        some semanticValue) :
    runNPOracleProgram
        (recoveryVerifierRebuildProgram limitsFrontEnd semanticStage)
        (recoveryVerifierRebuildBits frontEndBits semanticBits limits request)
        (recoveryVerifierRebuildFuel limitsFrontEnd semanticStage frontEndFuel
          semanticFuel limits request)
        (initialNPOracleState request.length request.code) =
      some semanticValue := by
  have hlength :
      natBitLength request.length ≤
        recoveryVerifierRebuildBits frontEndBits semanticBits limits request :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤
        recoveryVerifierRebuildBits frontEndBits semanticBits limits request :=
    by
    refine le_trans ?_ hlength
    unfold natBitLength
    omega
  have hrequestBits :
      recoveryVerifierRequestRebuildBits frontEndBits limits request ≤
        recoveryVerifierRebuildBits frontEndBits semanticBits limits request :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsemanticBits :
      semanticBits ≤
        recoveryVerifierRebuildBits frontEndBits semanticBits limits request :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hvalidator :=
    run_recoveryVerifierValidatorRebuildProgram limitsFrontEnd frontEndBits
      frontEndFuel request.length limits (encodeBitInput request.witness)
      hfrontEnd
  have hrequest :=
    run_recoveryWitnessRequestProgram
      (recoveryVerifierValidatorRebuildProgram limitsFrontEnd) request
      (recoveryVerifierValidatorRebuildBits frontEndBits request.length limits
        (encodeBitInput request.witness))
      (recoveryVerifierValidatorRebuildFuel frontEndFuel request.length limits
        (encodeBitInput request.witness))
      (recoveryWitnessValidatorOutput limits (encodeBitInput request.witness))
      hvalidator
  exact run_linkPrograms hpositive hlength
    (run_bits_mono hrequest hrequestBits)
    (run_bits_mono hsemantic hsemanticBits)

/-! ## §3 The plumbing ledgers, rebuilt -/

/-- **Plumbing width ledger, rebuilt.**  `RecoveryVerifierResourceEnvelope` §2
verbatim, at the rebuilt validator's charge. -/
theorem recoveryVerifierRebuildBits_le
    (frontEndBits semanticBits bound : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest)
    (hfrontEnd : frontEndBits ≤ bound)
    (hsemantic : semanticBits ≤ bound)
    (hvalidator :
      recoveryWitnessValidatorRebuildBits (WeakVerifierRequest.length request)
          limits (encodeBitInput request.witness) ≤ bound)
    (hmeasure : 8 * (WeakVerifierRequest.measure request + 1) ≤ bound) :
    recoveryVerifierRebuildBits frontEndBits semanticBits limits request ≤
      bound := by
  set measure := WeakVerifierRequest.measure request with hmeasureDef
  set inputCode := encodeBitInput request.input with hinputDef
  set witnessCode := encodeBitInput request.witness with hwitnessDef
  set validatorOutput :=
    recoveryWitnessValidatorOutput limits witnessCode with hvalidatorDef
  have hlengthLe : WeakVerifierRequest.length request ≤ measure := by
    simp [hmeasureDef, WeakVerifierRequest.length, WeakVerifierRequest.measure]
  have hlength :
      natBitLength (WeakVerifierRequest.length request) ≤ measure + 1 :=
    (natBitLength_le_succ _).trans (by omega)
  have hinput : natBitLength inputCode ≤ measure + 1 := by
    refine (natBitLength_encodeBitInput_le request.input).trans ?_
    simp [hmeasureDef, WeakVerifierRequest.measure]
  have hwitness : natBitLength witnessCode ≤ measure + 1 := by
    refine (natBitLength_encodeBitInput_le request.witness).trans ?_
    simp [hmeasureDef, WeakVerifierRequest.measure]
  have hcode : natBitLength request.code ≤ 4 * (measure + 1) :=
    weakVerifierRequest_codeBits_le request
  have houtput : natBitLength validatorOutput ≤ 4 * (measure + 1) :=
    natBitLength_recoveryWitnessValidatorOutput_le limits witnessCode measure
      hwitness
  have hpairInputWitness :
      natBitLength (Nat.pair inputCode witnessCode) ≤ 2 * (measure + 1) := by
    have hpair := natBitLength_pair_le inputCode witnessCode
    have hmax :
        max (natBitLength inputCode) (natBitLength witnessCode) ≤
          measure + 1 := max_le hinput hwitness
    omega
  have hpairWitnessInput :
      natBitLength (Nat.pair witnessCode inputCode) ≤ 2 * (measure + 1) := by
    have hpair := natBitLength_pair_le witnessCode inputCode
    have hmax :
        max (natBitLength witnessCode) (natBitLength inputCode) ≤
          measure + 1 := max_le hwitness hinput
    omega
  have hpairOutputInput :
      natBitLength (Nat.pair validatorOutput inputCode) ≤
        8 * (measure + 1) := by
    have hpair := natBitLength_pair_le validatorOutput inputCode
    have hmax :
        max (natBitLength validatorOutput) (natBitLength inputCode) ≤
          4 * (measure + 1) := max_le houtput (by omega)
    omega
  have hvalidatorStage :
      recoveryVerifierValidatorRebuildBits frontEndBits
          (WeakVerifierRequest.length request) limits witnessCode ≤ bound := by
    refine max_le (le_trans hlength (by omega)) ?_
    exact max_le hfrontEnd hvalidator
  have hpreserve :
      preserveRightBits
          (recoveryVerifierValidatorRebuildBits frontEndBits
            (WeakVerifierRequest.length request) limits witnessCode)
          witnessCode inputCode validatorOutput ≤ bound := by
    refine max_le hvalidatorStage ?_
    exact max_le (le_trans hpairWitnessInput (by omega))
      (le_trans hpairOutputInput hmeasure)
  have hgate :
      recoveryWitnessValidationGateBits validatorOutput inputCode ≤ bound := by
    refine max_le (by omega) ?_
    exact le_trans hpairOutputInput hmeasure
  have hlowering :
      recoveryWitnessValidationLoweringBits request ≤ bound := by
    refine max_le ?_ ?_
    · exact le_trans hpairInputWitness (by omega)
    · exact le_trans hpairWitnessInput (by omega)
  have hrequest :
      recoveryVerifierRequestRebuildBits frontEndBits limits request ≤
        bound := by
    refine max_le (le_trans hlength (by omega)) ?_
    refine max_le (le_trans hcode (by omega)) ?_
    exact max_le hlowering (max_le hpreserve hgate)
  refine max_le (le_trans hlength (by omega)) ?_
  exact max_le hrequest hsemantic

private def recoveryVerifierRebuildGateTail
    (limitsFrontEnd : NPOracleProgram) : NPOracleProgram :=
  linkPrograms
    (preserveRightProgram
      (recoveryVerifierValidatorRebuildProgram limitsFrontEnd))
    recoveryWitnessValidationGateProgram

private def recoveryVerifierRebuildLoweringTail
    (limitsFrontEnd : NPOracleProgram) : NPOracleProgram :=
  linkPrograms recoveryWitnessValidationLoweringProgram
    (recoveryVerifierRebuildGateTail limitsFrontEnd)

/-- **The closed linker overhead of the rebuilt stream.** -/
def recoveryVerifierRebuildFuelOverhead
    (limitsFrontEnd semanticStage : NPOracleProgram) : ℕ :=
  programRegisterSpan recoveryWitnessValidatorRebuildProgram +
    programRegisterSpan recoveryWitnessValidationGateProgram +
      programRegisterSpan (recoveryVerifierRebuildGateTail limitsFrontEnd) +
        programRegisterSpan
          (recoveryVerifierRebuildLoweringTail limitsFrontEnd) +
          programRegisterSpan semanticStage + 39

/-- **Plumbing fuel ledger, rebuilt.** -/
theorem recoveryVerifierRebuildFuel_le
    (limitsFrontEnd semanticStage : NPOracleProgram)
    (frontEndFuel semanticFuel : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest) :
    recoveryVerifierRebuildFuel limitsFrontEnd semanticStage frontEndFuel
        semanticFuel limits request ≤
      frontEndFuel +
        recoveryWitnessValidatorRebuildFuel (WeakVerifierRequest.length request)
          limits (encodeBitInput request.witness) +
        semanticFuel +
        recoveryVerifierRebuildFuelOverhead limitsFrontEnd semanticStage := by
  have hgateFuel :
      recoveryWitnessValidationGateFuel
          (recoveryWitnessValidatorOutput limits
            (encodeBitInput request.witness)) ≤ 4 := by
    unfold recoveryWitnessValidationGateFuel
    split <;> omega
  simp only [recoveryVerifierRebuildFuel, recoveryVerifierRequestRebuildFuel,
    recoveryWitnessRequestFuel, recoveryVerifierValidatorRebuildFuel,
    recoveryVerifierRebuildFuelOverhead, recoveryVerifierRebuildGateTail,
    recoveryVerifierRebuildLoweringTail, linkFuel_exact, preserveRightFuel]
  omega

/-! ## §4 The two component budgets at the published degree -/

/-- **`hbits`, reduced to the three component widths, at the rebuilt
validator.** -/
theorem recoveryVerifierRebuildBits_le_polynomialBudget
    (frontEndCoefficient validatorCoefficient semanticCoefficient
      overhead frontEndBits semanticBits : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest)
    (hfrontEnd :
      frontEndBits ≤
        polynomialBudget frontEndCoefficient recoveryVerifierDegree
          (WeakVerifierRequest.measure request))
    (hsemantic :
      semanticBits ≤
        polynomialBudget semanticCoefficient recoveryVerifierDegree
          (WeakVerifierRequest.measure request))
    (hvalidator :
      recoveryWitnessValidatorRebuildBits (WeakVerifierRequest.length request)
          limits (encodeBitInput request.witness) ≤
        polynomialBudget validatorCoefficient recoveryVerifierDegree
          (WeakVerifierRequest.measure request)) :
    recoveryVerifierRebuildBits frontEndBits semanticBits limits request ≤
      polynomialBudget
        (recoveryVerifierCoefficient frontEndCoefficient validatorCoefficient
          semanticCoefficient overhead)
        recoveryVerifierDegree (WeakVerifierRequest.measure request) := by
  refine recoveryVerifierRebuildBits_le frontEndBits semanticBits _ limits
    request
    (component_le_budget _ _ _ _ (by
      simp only [recoveryVerifierCoefficient]
      omega) hfrontEnd)
    (component_le_budget _ _ _ _ (by
      simp only [recoveryVerifierCoefficient]
      omega) hsemantic)
    (component_le_budget _ _ _ _ (by
      simp only [recoveryVerifierCoefficient]
      omega) hvalidator) ?_
  exact measure_succ_le_budget _ _ (by
    simp only [recoveryVerifierCoefficient]
    omega)

/-- **`hfuel`, reduced to the three component fuels, at the rebuilt
validator.** -/
theorem recoveryVerifierRebuildFuel_le_polynomialBudget
    (limitsFrontEnd semanticStage : NPOracleProgram)
    (frontEndCoefficient validatorCoefficient semanticCoefficient
      frontEndFuel semanticFuel : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest)
    (hfrontEnd :
      frontEndFuel ≤
        polynomialBudget frontEndCoefficient recoveryVerifierDegree
          (WeakVerifierRequest.measure request))
    (hsemantic :
      semanticFuel ≤
        polynomialBudget semanticCoefficient recoveryVerifierDegree
          (WeakVerifierRequest.measure request))
    (hvalidator :
      recoveryWitnessValidatorRebuildFuel (WeakVerifierRequest.length request)
          limits (encodeBitInput request.witness) ≤
        polynomialBudget validatorCoefficient recoveryVerifierDegree
          (WeakVerifierRequest.measure request)) :
    recoveryVerifierRebuildFuel limitsFrontEnd semanticStage frontEndFuel
        semanticFuel limits request ≤
      polynomialBudget
        (recoveryVerifierCoefficient frontEndCoefficient validatorCoefficient
          semanticCoefficient
          (recoveryVerifierRebuildFuelOverhead limitsFrontEnd semanticStage))
        recoveryVerifierDegree (WeakVerifierRequest.measure request) := by
  set measure := WeakVerifierRequest.measure request with hmeasureDef
  set overhead :=
    recoveryVerifierRebuildFuelOverhead limitsFrontEnd semanticStage
    with hoverheadDef
  have hsum :=
    recoveryVerifierRebuildFuel_le limitsFrontEnd semanticStage frontEndFuel
      semanticFuel limits request
  have hpositive : 1 ≤ (measure + 1) ^ recoveryVerifierDegree :=
    Nat.one_le_pow _ _ (by omega)
  have hoverhead :
      overhead ≤ overhead * (measure + 1) ^ recoveryVerifierDegree := by
    calc
      overhead = overhead * 1 := by omega
      _ ≤ overhead * (measure + 1) ^ recoveryVerifierDegree :=
        Nat.mul_le_mul_left _ hpositive
  have hexpand :
      polynomialBudget
          (recoveryVerifierCoefficient frontEndCoefficient validatorCoefficient
            semanticCoefficient overhead)
          recoveryVerifierDegree measure =
        polynomialBudget frontEndCoefficient recoveryVerifierDegree measure +
          polynomialBudget validatorCoefficient recoveryVerifierDegree
            measure +
          polynomialBudget semanticCoefficient recoveryVerifierDegree measure +
          overhead * (measure + 1) ^ recoveryVerifierDegree +
          8 * (measure + 1) ^ recoveryVerifierDegree := by
    simp only [polynomialBudget, recoveryVerifierCoefficient, Nat.add_mul]
  omega

/-! ## §5 The polynomial runner and the machine -/

section Assembly

variable (limitsOf : ℕ → RecoveryWitnessLimits)
  (limitsFrontEnd semanticStage : NPOracleProgram)
  (frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput :
    WeakVerifierRequest → ℕ)
  (coefficient : ℕ) (hcoefficient : 4 ≤ coefficient)
  (hlimitsFrontEnd : ∀ request : WeakVerifierRequest,
    runNPOracleProgram limitsFrontEnd (frontEndBits request)
        (frontEndFuel request)
        (initialNPOracleState request.length
          (encodeBitInput request.witness)) =
      some
        (recoveryWitnessValidatorInput (limitsOf request.inputArity)
          (encodeBitInput request.witness)))
  (hsemanticStage : ∀ request : WeakVerifierRequest,
    runNPOracleProgram semanticStage (semanticBits request)
        (semanticFuel request)
        (initialNPOracleState request.length
          (recoveryWitnessValidatorRequestOutput
            (limitsOf request.inputArity) request)) =
      some (semanticOutput request))
  (hbits : ∀ request : WeakVerifierRequest,
    recoveryVerifierRebuildBits (frontEndBits request) (semanticBits request)
        (limitsOf request.inputArity) request ≤
      polynomialBudget coefficient recoveryVerifierDegree request.measure)
  (hfuel : ∀ request : WeakVerifierRequest,
    recoveryVerifierRebuildFuel limitsFrontEnd semanticStage
        (frontEndFuel request) (semanticFuel request)
        (limitsOf request.inputArity) request ≤
      polynomialBudget coefficient recoveryVerifierDegree request.measure)
  (hfrontEndFree : OracleFree limitsFrontEnd)
  (hsemanticFree : OracleFree semanticStage)

/-- The rebuilt recovery verifier as a polynomial runner, at the same closed
degree envelope `recoveryVerifierDegree`. -/
def executableRecoveryVerifierRebuild :
    PolynomialNatProgram WeakVerifierRequest WeakVerifierRequest.length
      WeakVerifierRequest.code WeakVerifierRequest.measure :=
  polynomialNatProgramOfRun
    (recoveryVerifierRebuildProgram limitsFrontEnd semanticStage) coefficient
    recoveryVerifierDegree (by omega)
    (fun request =>
      recoveryVerifierRebuildBits (frontEndBits request) (semanticBits request)
        (limitsOf request.inputArity) request)
    (fun request =>
      recoveryVerifierRebuildFuel limitsFrontEnd semanticStage
        (frontEndFuel request) (semanticFuel request)
        (limitsOf request.inputArity) request)
    semanticOutput hbits hfuel
    (recoveryVerifier_initialBitsFit coefficient hcoefficient)
    (fun request =>
      run_recoveryVerifierRebuildProgram limitsFrontEnd semanticStage
        (frontEndBits request) (frontEndFuel request) (semanticBits request)
        (semanticFuel request) (limitsOf request.inputArity) request
        (semanticOutput request) (hlimitsFrontEnd request)
        (hsemanticStage request))

theorem executableRecoveryVerifierRebuild_execute
    (request : WeakVerifierRequest) :
    (executableRecoveryVerifierRebuild limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits
        hfuel).execute request =
      semanticOutput request :=
  polynomialNatProgramOfRun_execute _ _ _ _ _ _ _ _ _ _ _ request

/-- **The executable weak nondeterministic recovery machine over the rebuilt
validator.**  Same witness shape, same verifier degree; only the validator's
instruction stream changed. -/
def executableRecoveryMachineRebuild :
    ExecutableWeakNondeterministicMachine where
  witnessShape := recoveryWitnessShape
  witnessShapeOracleFree := recoveryWitnessShapeProgram_oracleFree
  verifier :=
    (executableRecoveryVerifierRebuild limitsOf limitsFrontEnd semanticStage
      frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
      coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel).toQuotient
      honestRecoveryDegree savingExponent
      (by change recoveryVerifierDegree + 2 * savingExponent ≤
            honestRecoveryDegree
          decide)
  verifierOracleFree :=
    recoveryVerifierRebuildProgram_oracleFree hfrontEndFree hsemanticFree

theorem executableRecoveryMachineRebuild_witnessShape :
    (executableRecoveryMachineRebuild limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
        hfrontEndFree hsemanticFree).witnessShape = recoveryWitnessShape :=
  rfl

theorem executableRecoveryMachineRebuild_verifier_degree :
    (executableRecoveryMachineRebuild limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
        hfrontEndFree hsemanticFree).verifier.degree = honestRecoveryDegree :=
  rfl

theorem executableRecoveryMachineRebuild_verifier_execute
    (request : WeakVerifierRequest) :
    (executableRecoveryMachineRebuild limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
        hfrontEndFree hsemanticFree).verifier.execute request =
      semanticOutput request :=
  (PolynomialNatProgram.toQuotient_execute
    (executableRecoveryVerifierRebuild limitsOf limitsFrontEnd semanticStage frontEndBits
      frontEndFuel semanticBits semanticFuel semanticOutput coefficient hcoefficient
      hlimitsFrontEnd hsemanticStage hbits hfuel)
    honestRecoveryDegree savingExponent
    (by change recoveryVerifierDegree + 2 * savingExponent ≤
          honestRecoveryDegree
        decide) request).trans
  (executableRecoveryVerifierRebuild_execute limitsOf limitsFrontEnd semanticStage frontEndBits
      frontEndFuel semanticBits semanticFuel semanticOutput coefficient hcoefficient
      hlimitsFrontEnd hsemanticStage hbits hfuel request)

end Assembly

/-! ## §6 The machine from its components -/

section Components

variable (limitsOf : ℕ → RecoveryWitnessLimits)
  (limitsCodeProgram semanticStage : NPOracleProgram)
  (limitsCodeBits limitsCodeFuel semanticBits semanticFuel semanticOutput :
    WeakVerifierRequest → ℕ)
  (frontEndCoefficient validatorCoefficient semanticCoefficient : ℕ)
  (hlimitsCode : ∀ request : WeakVerifierRequest,
    runNPOracleProgram limitsCodeProgram (limitsCodeBits request)
        (limitsCodeFuel request)
        (initialNPOracleState (WeakVerifierRequest.length request)
          (encodeBitInput request.witness)) =
      some (encodeRecoveryWitnessLimits (limitsOf request.inputArity)))
  (hsemanticStage : ∀ request : WeakVerifierRequest,
    runNPOracleProgram semanticStage (semanticBits request)
        (semanticFuel request)
        (initialNPOracleState (WeakVerifierRequest.length request)
          (recoveryWitnessValidatorRequestOutput
            (limitsOf request.inputArity) request)) =
      some (semanticOutput request))
  (hfrontEndBits : ∀ request : WeakVerifierRequest,
    recoveryLimitsFrontEndRequestBits limitsCodeBits limitsOf request ≤
      polynomialBudget frontEndCoefficient recoveryVerifierDegree
        request.measure)
  (hvalidatorBits : ∀ request : WeakVerifierRequest,
    recoveryWitnessValidatorRebuildBits (WeakVerifierRequest.length request)
        (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
      polynomialBudget validatorCoefficient recoveryVerifierDegree
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
  (hvalidatorFuel : ∀ request : WeakVerifierRequest,
    recoveryWitnessValidatorRebuildFuel (WeakVerifierRequest.length request)
        (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
      polynomialBudget validatorCoefficient recoveryVerifierDegree
        request.measure)
  (hsemanticFuel : ∀ request : WeakVerifierRequest,
    semanticFuel request ≤
      polynomialBudget semanticCoefficient recoveryVerifierDegree
        request.measure)
  (hlimitsCodeFree : OracleFree limitsCodeProgram)
  (hsemanticFree : OracleFree semanticStage)

/-- **The executable recovery machine from its components, over the rebuilt
validator.** -/
def executableRecoveryMachineOfRebuildComponents :
    ExecutableWeakNondeterministicMachine :=
  executableRecoveryMachineRebuild limitsOf
    (recoveryLimitsFrontEndProgram limitsCodeProgram) semanticStage
    (recoveryLimitsFrontEndRequestBits limitsCodeBits limitsOf)
    (recoveryLimitsFrontEndRequestFuel limitsCodeProgram limitsCodeFuel)
    semanticBits semanticFuel semanticOutput
    (recoveryVerifierCoefficient frontEndCoefficient validatorCoefficient
      semanticCoefficient
      (recoveryVerifierRebuildFuelOverhead
        (recoveryLimitsFrontEndProgram limitsCodeProgram) semanticStage))
    (by
      simp only [recoveryVerifierCoefficient]
      omega)
    (run_recoveryLimitsFrontEndProgram_request limitsCodeProgram limitsCodeBits
      limitsCodeFuel limitsOf hlimitsCode)
    hsemanticStage
    (fun request =>
      recoveryVerifierRebuildBits_le_polynomialBudget frontEndCoefficient
        validatorCoefficient semanticCoefficient
        (recoveryVerifierRebuildFuelOverhead
          (recoveryLimitsFrontEndProgram limitsCodeProgram) semanticStage)
        (recoveryLimitsFrontEndRequestBits limitsCodeBits limitsOf request)
        (semanticBits request) (limitsOf request.inputArity) request
        (hfrontEndBits request) (hsemanticBits request)
        (hvalidatorBits request))
    (fun request =>
      recoveryVerifierRebuildFuel_le_polynomialBudget
        (recoveryLimitsFrontEndProgram limitsCodeProgram) semanticStage
        frontEndCoefficient validatorCoefficient semanticCoefficient
        (recoveryLimitsFrontEndRequestFuel limitsCodeProgram limitsCodeFuel
          request)
        (semanticFuel request) (limitsOf request.inputArity) request
        (hfrontEndFuel request) (hsemanticFuel request)
        (hvalidatorFuel request))
    (recoveryLimitsFrontEndProgram_oracleFree hlimitsCodeFree) hsemanticFree

theorem executableRecoveryMachineOfRebuildComponents_witnessShape :
    (executableRecoveryMachineOfRebuildComponents limitsOf limitsCodeProgram
        semanticStage limitsCodeBits limitsCodeFuel semanticBits semanticFuel
        semanticOutput frontEndCoefficient validatorCoefficient
        semanticCoefficient hlimitsCode hsemanticStage hfrontEndBits
        hvalidatorBits hsemanticBits hfrontEndFuel hvalidatorFuel hsemanticFuel
        hlimitsCodeFree hsemanticFree).witnessShape =
      RecoveryWitnessShape.recoveryWitnessShape :=
  rfl

theorem executableRecoveryMachineOfRebuildComponents_verifier_degree :
    (executableRecoveryMachineOfRebuildComponents limitsOf limitsCodeProgram
        semanticStage limitsCodeBits limitsCodeFuel semanticBits semanticFuel
        semanticOutput frontEndCoefficient validatorCoefficient
        semanticCoefficient hlimitsCode hsemanticStage hfrontEndBits
        hvalidatorBits hsemanticBits hfrontEndFuel hvalidatorFuel hsemanticFuel
        hlimitsCodeFree hsemanticFree).verifier.degree =
      honestRecoveryDegree :=
  rfl

theorem executableRecoveryMachineOfRebuildComponents_verifier_execute
    (request : WeakVerifierRequest) :
    (executableRecoveryMachineOfRebuildComponents limitsOf limitsCodeProgram
        semanticStage limitsCodeBits limitsCodeFuel semanticBits semanticFuel
        semanticOutput frontEndCoefficient validatorCoefficient
        semanticCoefficient hlimitsCode hsemanticStage hfrontEndBits
        hvalidatorBits hsemanticBits hfrontEndFuel hvalidatorFuel hsemanticFuel
        hlimitsCodeFree hsemanticFree).verifier.execute request =
      semanticOutput request :=
  executableRecoveryMachineRebuild_verifier_execute _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ request

end Components

end NearCubicWires.ValidatorRebuiltMachineSpine
