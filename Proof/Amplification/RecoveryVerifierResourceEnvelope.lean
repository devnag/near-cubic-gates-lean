import Proof.Supplier.ComponentwiseEstimatorAccuracy
import Proof.MachineModel.RecoveryLimitsFrontEndProgram

/-!
# The polynomial resource envelope of the composed recovery verifier

`ExecutableRecoveryMachine` charges the composed verifier at the closed degree
`recoveryVerifierDegree = 4`, and leaves the two budget facts as the named
premises `hbits` and `hfuel`.  This module reduces both of them to the three
budgets that are genuinely owned by a component:

* the limits front end (`RecoveryLimitsFrontEndProgram`),
* the recovery-witness validator endpoint
  (`recoveryWitnessValidatorBits` / `recoveryWitnessValidatorFuel`),
* the semantic stage.

Everything in between — request extraction, the input-preserving lowering, the
count-preserving validator call, the zero-sentinel gate and the two linkers —
is charged here once and for all:

* `recoveryVerifierBits_le` shows the composed width is the maximum of the
  three component widths and a plumbing term of size `8 * (measure + 1)`;
* `recoveryVerifierFuel_le` shows the composed fuel is the *sum* of the three
  component fuels and one closed program-shape overhead
  `recoveryVerifierFuelOverhead`, which mentions no request.

Consequently the degree numeral 4 is spent entirely on the three components:
the plumbing is linear in the measure and the linker overhead is constant.
-/

namespace NearCubicWires.RecoveryVerifierResourceEnvelope

open NearCubicWires
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryLimitsFrontEndProgram
open NearCubicWires.VerifiedLinker

/-! ## §1 Width arithmetic for the pairing ABI -/

private theorem natBitLength_pair_le (left right : ℕ) :
    natBitLength (Nat.pair left right) ≤
      2 * max (natBitLength left) (natBitLength right) :=
  CanonicalBinary.pairCodeBits_le left right

/-- The full validator's semantic output is either the global zero sentinel or
the mode-tagged guessed code, so its width is linear in the measure. -/
private theorem natBitLength_recoveryWitnessValidatorOutput_le
    (limits : RecoveryWitnessLimits) (raw bound : ℕ)
    (hraw : natBitLength raw ≤ bound + 1) :
    natBitLength (recoveryWitnessValidatorOutput limits raw) ≤
      4 * (bound + 1) := by
  cases hdecode : decodeRecoveryWitness limits raw with
  | none =>
      rw [show recoveryWitnessValidatorOutput limits raw = 0 by
        simp [recoveryWitnessValidatorOutput, hdecode]]
      simp only [natBitLength, Nat.log_zero_right]
      omega
  | some witness =>
      rw [recoveryWitnessValidatorOutput_of_decode hdecode]
      have htag :
          natBitLength (checkedRecoveryWitnessModeTag witness) ≤ 2 := by
        have hle : checkedRecoveryWitnessModeTag witness ≤ 2 := by
          cases witness <;>
            simp [checkedRecoveryWitnessModeTag, recoveryWitnessModeTag,
              CheckedRecoveryWitness.mode]
        refine (natBitLength_mono hle).trans ?_
        have hlog : Nat.log 2 2 = 1 :=
          Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
        unfold natBitLength
        omega
      have hpair :=
        natBitLength_pair_le (checkedRecoveryWitnessModeTag witness) raw
      have hmax :
          max (natBitLength (checkedRecoveryWitnessModeTag witness))
              (natBitLength raw) ≤ 2 * (bound + 1) := by
        rcases le_total
          (natBitLength (checkedRecoveryWitnessModeTag witness))
          (natBitLength raw) with hle | hle
        · rw [max_eq_right hle]
          omega
        · rw [max_eq_left hle]
          omega
      omega

/-! ## §2 The composed width -/

/-- **Plumbing width ledger.**  The composed verifier's register width is the
maximum of the three component widths and one term linear in the measure: no
stage between them widens a register beyond the pairing of the guessed code,
the retained public input and the mode-tagged validator output. -/
theorem recoveryVerifierBits_le
    (frontEndBits semanticBits bound : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest)
    (hfrontEnd : frontEndBits ≤ bound)
    (hsemantic : semanticBits ≤ bound)
    (hvalidator :
      recoveryWitnessValidatorBits (WeakVerifierRequest.length request) limits
          (encodeBitInput request.witness) ≤ bound)
    (hmeasure : 8 * (WeakVerifierRequest.measure request + 1) ≤ bound) :
    recoveryVerifierBits frontEndBits semanticBits limits request ≤ bound := by
  set measure := WeakVerifierRequest.measure request with hmeasureDef
  set inputCode := encodeBitInput request.input with hinputDef
  set witnessCode := encodeBitInput request.witness with hwitnessDef
  set validatorOutput :=
    recoveryWitnessValidatorOutput limits witnessCode with hvalidatorDef
  have hlengthLe : WeakVerifierRequest.length request ≤ measure := by
    simp [hmeasureDef, WeakVerifierRequest.length,
      WeakVerifierRequest.measure]
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
      recoveryVerifierValidatorBits frontEndBits
          (WeakVerifierRequest.length request) limits witnessCode ≤ bound := by
    refine max_le (le_trans hlength (by omega)) ?_
    exact max_le hfrontEnd hvalidator
  have hpreserve :
      preserveRightBits
          (recoveryVerifierValidatorBits frontEndBits
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
      recoveryVerifierRequestBits frontEndBits limits request ≤ bound := by
    refine max_le (le_trans hlength (by omega)) ?_
    refine max_le (le_trans hcode (by omega)) ?_
    exact max_le hlowering (max_le hpreserve hgate)
  refine max_le (le_trans hlength (by omega)) ?_
  exact max_le hrequest hsemantic

/-! ## §3 The composed fuel

Every linker charge is a closed function of the *programs* it links, so the
whole plumbing cost is one request-independent overhead. -/

private def recoveryVerifierGateTail
    (limitsFrontEnd : NPOracleProgram) : NPOracleProgram :=
  linkPrograms
    (preserveRightProgram (recoveryVerifierValidatorProgram limitsFrontEnd))
    recoveryWitnessValidationGateProgram

private def recoveryVerifierLoweringTail
    (limitsFrontEnd : NPOracleProgram) : NPOracleProgram :=
  linkPrograms recoveryWitnessValidationLoweringProgram
    (recoveryVerifierGateTail limitsFrontEnd)

/-- **The closed linker overhead.**  It mentions the two abstract program
arguments only through their register spans, and no request, schedule
coordinate or policy at all. -/
def recoveryVerifierFuelOverhead
    (limitsFrontEnd semanticStage : NPOracleProgram) : ℕ :=
  programRegisterSpan recoveryWitnessValidatorProgram +
    programRegisterSpan recoveryWitnessValidationGateProgram +
      programRegisterSpan (recoveryVerifierGateTail limitsFrontEnd) +
        programRegisterSpan (recoveryVerifierLoweringTail limitsFrontEnd) +
          programRegisterSpan semanticStage + 39

/-- **Plumbing fuel ledger.**  The composed fuel is the sum of the three
component fuels and the closed overhead. -/
theorem recoveryVerifierFuel_le
    (limitsFrontEnd semanticStage : NPOracleProgram)
    (frontEndFuel semanticFuel : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest) :
    recoveryVerifierFuel limitsFrontEnd semanticStage frontEndFuel
        semanticFuel limits request ≤
      frontEndFuel +
        recoveryWitnessValidatorFuel (WeakVerifierRequest.length request)
          limits (encodeBitInput request.witness) +
        semanticFuel +
        recoveryVerifierFuelOverhead limitsFrontEnd semanticStage := by
  have hgateFuel :
      recoveryWitnessValidationGateFuel
          (recoveryWitnessValidatorOutput limits
            (encodeBitInput request.witness)) ≤ 4 := by
    unfold recoveryWitnessValidationGateFuel
    split <;> omega
  simp only [recoveryVerifierFuel, recoveryVerifierRequestFuel,
    recoveryWitnessRequestFuel, recoveryVerifierValidatorFuel,
    recoveryVerifierFuelOverhead, recoveryVerifierGateTail,
    recoveryVerifierLoweringTail, linkFuel_exact, preserveRightFuel]
  omega

/-! ## §4 The limits front end at the request boundary -/

/-- The wrapper's width is the maximum of the limits-code width, twice the
limits-code magnitude width and a linear plumbing term. -/
theorem recoveryLimitsFrontEndRequestBits_le
    (limitsCodeBits : WeakVerifierRequest → ℕ)
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (request : WeakVerifierRequest) (bound : ℕ)
    (hlimitsCodeBits : limitsCodeBits request ≤ bound)
    (hlimitsCodeWidth :
      2 *
          natBitLength
            (encodeRecoveryWitnessLimits (limitsOf request.inputArity)) ≤
        bound)
    (hmeasure : 2 * (WeakVerifierRequest.measure request + 1) ≤ bound) :
    recoveryLimitsFrontEndRequestBits limitsCodeBits limitsOf request ≤
      bound := by
  set witnessCode := encodeBitInput request.witness with hwitnessDef
  set limitsCode :=
    encodeRecoveryWitnessLimits (limitsOf request.inputArity) with hlimitsDef
  have hlengthLe :
      WeakVerifierRequest.length request ≤
        WeakVerifierRequest.measure request := by
    simp [WeakVerifierRequest.length, WeakVerifierRequest.measure]
  have hlength :
      natBitLength (WeakVerifierRequest.length request) ≤
        WeakVerifierRequest.measure request + 1 :=
    (natBitLength_le_succ _).trans (by omega)
  have hwitness :
      natBitLength witnessCode ≤ WeakVerifierRequest.measure request + 1 := by
    refine (natBitLength_encodeBitInput_le request.witness).trans ?_
    simp [WeakVerifierRequest.measure]
  have hduplicate :
      recoveryLimitsDuplicateBits witnessCode ≤ bound := by
    have hpair := natBitLength_pair_le witnessCode witnessCode
    have hmax :
        max (natBitLength witnessCode) (natBitLength witnessCode) ≤
          WeakVerifierRequest.measure request + 1 := max_le hwitness hwitness
    have : natBitLength (Nat.pair witnessCode witnessCode) ≤ bound := by
      omega
    exact this
  have hpairLimits :
      natBitLength (Nat.pair limitsCode witnessCode) ≤ bound := by
    have hpair := natBitLength_pair_le limitsCode witnessCode
    rcases le_total (natBitLength limitsCode) (natBitLength witnessCode) with
      hle | hle
    · rw [max_eq_right hle] at hpair
      omega
    · rw [max_eq_left hle] at hpair
      omega
  refine max_le (le_trans hlength (by omega)) ?_
  refine max_le hduplicate ?_
  exact max_le hlimitsCodeBits (max_le hduplicate hpairLimits)

/-- The wrapper's fuel is the limits-code fuel plus a closed program-shape
constant. -/
theorem recoveryLimitsFrontEndRequestFuel_eq
    (limitsCodeProgram : NPOracleProgram)
    (limitsCodeFuel : WeakVerifierRequest → ℕ)
    (request : WeakVerifierRequest) :
    recoveryLimitsFrontEndRequestFuel limitsCodeProgram limitsCodeFuel
        request =
      limitsCodeFuel request +
        (programRegisterSpan (preserveRightProgram limitsCodeProgram) + 11) := by
  simp only [recoveryLimitsFrontEndRequestFuel, recoveryLimitsFrontEndFuel,
    recoveryLimitsDuplicateFuel, linkFuel_exact, preserveRightFuel]
  omega

/-! ## §5 The polynomial budget

Every component budget is charged with its own coefficient at the closed
degree `recoveryVerifierDegree = 4`; the composed coefficient is their sum
plus the linker overhead.  This is exactly the "schedule-dependent growth is
charged to the coefficient" discipline of `ExecutableRecoveryMachine`. -/

/-- The composed coefficient.  Each summand is the coefficient of one
component; the `8` covers the linear plumbing width. -/
def recoveryVerifierCoefficient
    (frontEndCoefficient validatorCoefficient semanticCoefficient
      overhead : ℕ) : ℕ :=
  frontEndCoefficient + validatorCoefficient + semanticCoefficient +
    overhead + 8

private theorem measure_succ_le_budget (coefficient measure : ℕ)
    (hcoefficient : 8 ≤ coefficient) :
    8 * (measure + 1) ≤
      polynomialBudget coefficient recoveryVerifierDegree measure := by
  have hpow : measure + 1 ≤ (measure + 1) ^ recoveryVerifierDegree :=
    Nat.le_self_pow (by simp [recoveryVerifierDegree]) _
  exact le_trans (Nat.mul_le_mul hcoefficient hpow) (le_refl _)

private theorem component_le_budget
    (component coefficient total measure : ℕ)
    (hcoefficient : coefficient ≤ total)
    (hcomponent :
      component ≤
        polynomialBudget coefficient recoveryVerifierDegree measure) :
    component ≤ polynomialBudget total recoveryVerifierDegree measure := by
  refine hcomponent.trans ?_
  exact Nat.mul_le_mul_right _ hcoefficient

/-- **`hbits`, reduced to the three component widths.** -/
theorem recoveryVerifierBits_le_polynomialBudget
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
      recoveryWitnessValidatorBits (WeakVerifierRequest.length request) limits
          (encodeBitInput request.witness) ≤
        polynomialBudget validatorCoefficient recoveryVerifierDegree
          (WeakVerifierRequest.measure request)) :
    recoveryVerifierBits frontEndBits semanticBits limits request ≤
      polynomialBudget
        (recoveryVerifierCoefficient frontEndCoefficient validatorCoefficient
          semanticCoefficient overhead)
        recoveryVerifierDegree (WeakVerifierRequest.measure request) := by
  refine recoveryVerifierBits_le frontEndBits semanticBits _ limits request
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

/-- **`hfuel`, reduced to the three component fuels.** -/
theorem recoveryVerifierFuel_le_polynomialBudget
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
      recoveryWitnessValidatorFuel (WeakVerifierRequest.length request) limits
          (encodeBitInput request.witness) ≤
        polynomialBudget validatorCoefficient recoveryVerifierDegree
          (WeakVerifierRequest.measure request)) :
    recoveryVerifierFuel limitsFrontEnd semanticStage frontEndFuel semanticFuel
        limits request ≤
      polynomialBudget
        (recoveryVerifierCoefficient frontEndCoefficient validatorCoefficient
          semanticCoefficient
          (recoveryVerifierFuelOverhead limitsFrontEnd semanticStage))
        recoveryVerifierDegree (WeakVerifierRequest.measure request) := by
  set measure := WeakVerifierRequest.measure request with hmeasureDef
  set overhead := recoveryVerifierFuelOverhead limitsFrontEnd semanticStage
    with hoverheadDef
  have hsum :=
    recoveryVerifierFuel_le limitsFrontEnd semanticStage frontEndFuel
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

section Assembly

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
    recoveryWitnessValidatorBits (WeakVerifierRequest.length request)
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
    recoveryWitnessValidatorFuel (WeakVerifierRequest.length request)
        (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
      polynomialBudget validatorCoefficient recoveryVerifierDegree
        request.measure)
  (hsemanticFuel : ∀ request : WeakVerifierRequest,
    semanticFuel request ≤
      polynomialBudget semanticCoefficient recoveryVerifierDegree
        request.measure)
  (hlimitsCodeFree : OracleFree limitsCodeProgram)
  (hsemanticFree : OracleFree semanticStage)

/-- **The executable recovery machine from its components.**  The limits front
end and its oracle-freedom are supplied by
`RecoveryLimitsFrontEndProgram`; the two budget premises are the component
envelopes of §5. -/
def executableRecoveryMachineOfComponents :
    ExecutableWeakNondeterministicMachine :=
  executableRecoveryMachine limitsOf
    (recoveryLimitsFrontEndProgram limitsCodeProgram) semanticStage
    (recoveryLimitsFrontEndRequestBits limitsCodeBits limitsOf)
    (recoveryLimitsFrontEndRequestFuel limitsCodeProgram limitsCodeFuel)
    semanticBits semanticFuel semanticOutput
    (recoveryVerifierCoefficient frontEndCoefficient validatorCoefficient
      semanticCoefficient
      (recoveryVerifierFuelOverhead
        (recoveryLimitsFrontEndProgram limitsCodeProgram) semanticStage))
    (by
      simp only [recoveryVerifierCoefficient]
      omega)
    (run_recoveryLimitsFrontEndProgram_request limitsCodeProgram limitsCodeBits
      limitsCodeFuel limitsOf hlimitsCode)
    hsemanticStage
    (fun request =>
      recoveryVerifierBits_le_polynomialBudget frontEndCoefficient
        validatorCoefficient semanticCoefficient
        (recoveryVerifierFuelOverhead
          (recoveryLimitsFrontEndProgram limitsCodeProgram) semanticStage)
        (recoveryLimitsFrontEndRequestBits limitsCodeBits limitsOf request)
        (semanticBits request) (limitsOf request.inputArity) request
        (hfrontEndBits request) (hsemanticBits request)
        (hvalidatorBits request))
    (fun request =>
      recoveryVerifierFuel_le_polynomialBudget
        (recoveryLimitsFrontEndProgram limitsCodeProgram) semanticStage
        frontEndCoefficient validatorCoefficient semanticCoefficient
        (recoveryLimitsFrontEndRequestFuel limitsCodeProgram limitsCodeFuel
          request)
        (semanticFuel request) (limitsOf request.inputArity) request
        (hfrontEndFuel request) (hsemanticFuel request)
        (hvalidatorFuel request))
    (recoveryLimitsFrontEndProgram_oracleFree hlimitsCodeFree) hsemanticFree

theorem executableRecoveryMachineOfComponents_witnessShape :
    (executableRecoveryMachineOfComponents limitsOf limitsCodeProgram
        semanticStage limitsCodeBits limitsCodeFuel semanticBits semanticFuel
        semanticOutput frontEndCoefficient validatorCoefficient
        semanticCoefficient hlimitsCode hsemanticStage hfrontEndBits
        hvalidatorBits hsemanticBits hfrontEndFuel hvalidatorFuel hsemanticFuel
        hlimitsCodeFree hsemanticFree).witnessShape =
      RecoveryWitnessShape.recoveryWitnessShape :=
  rfl

theorem executableRecoveryMachineOfComponents_verifier_degree :
    (executableRecoveryMachineOfComponents limitsOf limitsCodeProgram
        semanticStage limitsCodeBits limitsCodeFuel semanticBits semanticFuel
        semanticOutput frontEndCoefficient validatorCoefficient
        semanticCoefficient hlimitsCode hsemanticStage hfrontEndBits
        hvalidatorBits hsemanticBits hfrontEndFuel hvalidatorFuel hsemanticFuel
        hlimitsCodeFree hsemanticFree).verifier.degree =
      honestRecoveryDegree :=
  rfl

theorem executableRecoveryMachineOfComponents_verifier_execute
    (request : WeakVerifierRequest) :
    (executableRecoveryMachineOfComponents limitsOf limitsCodeProgram
        semanticStage limitsCodeBits limitsCodeFuel semanticBits semanticFuel
        semanticOutput frontEndCoefficient validatorCoefficient
        semanticCoefficient hlimitsCode hsemanticStage hfrontEndBits
        hvalidatorBits hsemanticBits hfrontEndFuel hvalidatorFuel hsemanticFuel
        hlimitsCodeFree hsemanticFree).verifier.execute request =
      semanticOutput request :=
  executableRecoveryMachine_verifier_execute _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    request

/-- **`honeSided` for the assembled machine through the estimator-free
route.**  The composed verifier's execution is `semanticOutput` by
`executableRecoveryMachineOfComponents_verifier_execute`, so
`ComponentwiseEstimatorAccuracy.eventuallyOneSided_of_exactRationalStage`
applies verbatim: the only surviving premise is that an accepting semantic
stage exposes a decoded rational proof with its two range checks, the rational
validity charge and the exact rational threshold comparison. -/
theorem executableRecoveryMachineOfComponents_eventuallyOneSided
    {hierarchy : Language} (source : UniformPointwisePCPPSource) (onset : ℕ)
    (hstageChecks :
      ∀ n, onset ≤ n → ∀ input : BitInput n,
        hierarchy n input = false →
        ∀ witness : BitInput
          ((executableRecoveryMachineOfComponents limitsOf limitsCodeProgram
            semanticStage limitsCodeBits limitsCodeFuel semanticBits
            semanticFuel semanticOutput frontEndCoefficient
            validatorCoefficient semanticCoefficient hlimitsCode
            hsemanticStage hfrontEndBits hvalidatorBits hsemanticBits
            hfrontEndFuel hvalidatorFuel hsemanticFuel hlimitsCodeFree
            hsemanticFree).witnessBits n),
          semanticOutput
              ((executableRecoveryMachineOfComponents limitsOf
                limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
                semanticBits semanticFuel semanticOutput frontEndCoefficient
                validatorCoefficient semanticCoefficient hlimitsCode
                hsemanticStage hfrontEndBits hvalidatorBits hsemanticBits
                hfrontEndFuel hvalidatorFuel hsemanticFuel hlimitsCodeFree
                hsemanticFree).verifierRequest input witness) ≠ 0 →
            ∃ (arity : ℕ) (branchCircuit : BooleanCircuit arity)
              (_ : arity ≤ branchCircuit.size) (branchInput : BitInput arity)
              (_ : ¬branchCircuit.eval branchInput)
              (supportBound :
                ∀ i,
                  ((source.factory.forCircuit
                    branchCircuit).systematicSupport i).card ≤ arity / 2)
              (proofValue :
                Fin
                  (((source.factory.forCircuit branchCircuit).toSemantic
                      supportBound).systematicBits +
                    ((source.factory.forCircuit branchCircuit).toSemantic
                      supportBound).auxiliaryBits) → ℚ),
              (∀ j, 0 ≤ proofValue j) ∧ (∀ j, proofValue j ≤ 1) ∧
                rationalTotalClausePenaltyCharge
                    ((source.factory.forCircuit branchCircuit).toSemantic
                      supportBound) branchInput proofValue ≤
                  6 * (executableParametersOfSource source).zeta ∧
                (executableParametersOfSource source).threshold ≤
                  ComponentwiseEstimatorAccuracy.rationalClauseMean
                    ((source.factory.forCircuit branchCircuit).toSemantic
                      supportBound) proofValue) :
    EventuallyOneSided hierarchy
      (executableRecoveryMachineOfComponents limitsOf limitsCodeProgram
        semanticStage limitsCodeBits limitsCodeFuel semanticBits semanticFuel
        semanticOutput frontEndCoefficient validatorCoefficient
        semanticCoefficient hlimitsCode hsemanticStage hfrontEndBits
        hvalidatorBits hsemanticBits hfrontEndFuel hvalidatorFuel hsemanticFuel
        hlimitsCodeFree hsemanticFree) :=
  ComponentwiseEstimatorAccuracy.eventuallyOneSided_of_exactRationalStage
    source _ semanticOutput
    (executableRecoveryMachineOfComponents_verifier_execute limitsOf
      limitsCodeProgram semanticStage limitsCodeBits limitsCodeFuel
      semanticBits semanticFuel semanticOutput frontEndCoefficient
      validatorCoefficient semanticCoefficient hlimitsCode hsemanticStage
      hfrontEndBits hvalidatorBits hsemanticBits hfrontEndFuel hvalidatorFuel
      hsemanticFuel hlimitsCodeFree hsemanticFree)
    onset hstageChecks

end Assembly

end NearCubicWires.RecoveryVerifierResourceEnvelope
