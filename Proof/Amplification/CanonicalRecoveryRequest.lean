import Proof.MachineModel.CanonicalRecoveryProgram
import Proof.Foundations.PolynomialClock
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.VerifiedLinker

/-!
# Raw weak-request extraction for recovery validation

The verifier receives only `WeakVerifierRequest.code` in register zero.  This
module proves the fixed extraction/linking path that recovers both public input
and witness bits, validates the witness, and preserves the same public input
for the downstream verifier.  No shallow request-level specialization is
retained.
-/

namespace NearCubicWires.CanonicalRecoveryRequest

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker
open scoped BigOperators

/-- The ordinary binary encoding of an `n`-bit function never sets a bit at
index `n` or above.  This is the width fact used at the raw request boundary;
it does not inspect or trust a decoded recovery object. -/
theorem encodeBitInput_lt_pow {n : ℕ} (input : BitInput n) :
    encodeBitInput input < 2 ^ n := by
  induction n with
  | zero =>
      simp [encodeBitInput]
  | succ n ih =>
      rw [encodeBitInput, Fin.sum_univ_succ]
      have htail := ih (fun i : Fin n => input i.succ)
      unfold encodeBitInput at htail
      have htail' :
          (∑ i : Fin n,
              if input i.succ then 2 ^ i.val else 0) < 2 ^ n := by
        simpa using htail
      have hshift :
          (∑ i : Fin n,
              if input i.succ then 2 ^ i.succ.val else 0) =
            2 * ∑ i : Fin n,
              if input i.succ then 2 ^ i.val else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Fin.val_succ]
        split <;> simp_all [pow_succ, Nat.mul_comm]
      rw [hshift]
      simp only [Fin.val_zero, pow_zero]
      rw [pow_succ]
      split <;> omega

theorem natBitLength_encodeBitInput_le {n : ℕ} (input : BitInput n) :
    natBitLength (encodeBitInput input) ≤ n + 1 := by
  by_cases hzero : encodeBitInput input = 0
  · simp [hzero, natBitLength]
  · unfold natBitLength
    have hlog :
        Nat.log 2 (encodeBitInput input) < n :=
      Nat.log_lt_of_lt_pow hzero (encodeBitInput_lt_pow input)
    omega

/-- The complete raw request code has width linear in the declared arities.
This closes the easy-to-miss gap between a clock over a nested natural and the
actual `WeakVerifierRequest.measure` required by the public machine ABI. -/
theorem weakVerifierRequest_code_lt_pow
    (request : WeakVerifierRequest) :
    request.code < 2 ^ (4 * (request.measure + 1)) := by
  let measure := request.measure
  let inputCode := encodeBitInput request.input
  let witnessCode := encodeBitInput request.witness
  let payload := Nat.pair inputCode witnessCode
  have hinput :
      inputCode < 2 ^ (measure + 1) := by
    apply (encodeBitInput_lt_pow request.input).trans_le
    exact Nat.pow_le_pow_right (by omega) (by
      dsimp [measure, WeakVerifierRequest.measure]
      omega)
  have hwitness :
      witnessCode < 2 ^ (measure + 1) := by
    apply (encodeBitInput_lt_pow request.witness).trans_le
    exact Nat.pow_le_pow_right (by omega) (by
      dsimp [measure, WeakVerifierRequest.measure]
      omega)
  have hinnerMax :
      max inputCode witnessCode + 1 ≤ 2 ^ (measure + 1) := by
    omega
  have hpayload :
      payload < 2 ^ (2 * (measure + 1)) := by
    calc
      payload < (max inputCode witnessCode + 1) ^ 2 :=
        Nat.pair_lt_max_add_one_sq inputCode witnessCode
      _ ≤ (2 ^ (measure + 1)) ^ 2 :=
        Nat.pow_le_pow_left hinnerMax 2
      _ = 2 ^ (2 * (measure + 1)) := by
        rw [← pow_mul]
        congr 1
        omega
  have harity :
      request.inputArity < 2 ^ (2 * (measure + 1)) := by
    apply request.inputArity.lt_two_pow_self.trans_le
    exact Nat.pow_le_pow_right (by omega) (by
      dsimp [measure, WeakVerifierRequest.measure]
      omega)
  have houterMax :
      max request.inputArity payload + 1 ≤
        2 ^ (2 * (measure + 1)) := by
    omega
  calc
    request.code =
        Nat.pair request.inputArity payload := by
      rfl
    _ < (max request.inputArity payload + 1) ^ 2 :=
      Nat.pair_lt_max_add_one_sq request.inputArity payload
    _ ≤ (2 ^ (2 * (measure + 1))) ^ 2 :=
      Nat.pow_le_pow_left houterMax 2
    _ = 2 ^ (4 * (measure + 1)) := by
      rw [← pow_mul]
      congr 1
      omega

theorem weakVerifierRequest_codeBits_le
    (request : WeakVerifierRequest) :
    natBitLength request.code ≤ 4 * (request.measure + 1) := by
  by_cases hcode : request.code = 0
  · simp [hcode, natBitLength]
    omega
  · unfold natBitLength
    have hlog :
        Nat.log 2 request.code < 4 * (request.measure + 1) :=
      Nat.log_lt_of_lt_pow hcode
        (weakVerifierRequest_code_lt_pow request)
    omega

/-- Canonical payload retained across validation.  The public input remains on
the left exactly as serialized by `WeakVerifierRequest.code`. -/
def recoveryWitnessRequestPayload (request : WeakVerifierRequest) : ℕ :=
  Nat.pair (encodeBitInput request.input)
    (encodeBitInput request.witness)

/-- Extract the complete `(input, witness)` payload from the sole public
request code.  Validation must not erase the input needed by later checks. -/
def recoveryWitnessCodeExtractorProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .halt 0
  ]

@[simp] theorem recoveryWitnessCodeExtractorProgram_oracleFree :
    OracleFree recoveryWitnessCodeExtractorProgram := by
  rfl

theorem run_recoveryWitnessCodeExtractorProgram
    (request : WeakVerifierRequest) (maximumBits : ℕ)
    (hbits :
      natBitLength (WeakVerifierRequest.code request) ≤ maximumBits) :
    runNPOracleProgram recoveryWitnessCodeExtractorProgram maximumBits 2
        (initialNPOracleState request.length request.code) =
      some (recoveryWitnessRequestPayload request) := by
  let payload := recoveryWitnessRequestPayload request
  have hpayload :
      (Nat.unpair request.code).2 = payload := by
    simp [WeakVerifierRequest.code, recoveryWitnessRequestPayload, payload]
  have hpayloadBits :
      natBitLength payload ≤ maximumBits := by
    rw [← hpayload]
    exact (natBitLength_mono
      (Nat.unpair_right_le request.code)).trans hbits
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [initialNPOracleState, hpayload]) hpayloadBits]
  rw [show recoveryWitnessRequestPayload request = payload by rfl]
  exact run_halt_instruction (fuel := 0) (value := payload)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpayloadBits

/-! ## Input-preserving validator ABI -/

/-- Reorder the public payload to `(witness, input)`, the standard
`preserveRightProgram` calling convention. -/
def recoveryWitnessValidationLoweringOutput
    (request : WeakVerifierRequest) : ℕ :=
  Nat.pair (encodeBitInput request.witness)
    (encodeBitInput request.input)

def recoveryWitnessValidationLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 3 2 0 3
  , .halt 0
  ]

@[simp] theorem recoveryWitnessValidationLoweringProgram_oracleFree :
    OracleFree recoveryWitnessValidationLoweringProgram := by
  rfl

def recoveryWitnessValidationLoweringBits
    (request : WeakVerifierRequest) : ℕ :=
  max (natBitLength (recoveryWitnessRequestPayload request))
    (natBitLength (recoveryWitnessValidationLoweringOutput request))

theorem run_recoveryWitnessValidationLoweringProgram
    (request : WeakVerifierRequest) :
    runNPOracleProgram recoveryWitnessValidationLoweringProgram
        (recoveryWitnessValidationLoweringBits request) 4
        (initialNPOracleState request.length
          (recoveryWitnessRequestPayload request)) =
      some (recoveryWitnessValidationLoweringOutput request) := by
  let inputCode := encodeBitInput request.input
  let witnessCode := encodeBitInput request.witness
  let payload := Nat.pair inputCode witnessCode
  let output := Nat.pair witnessCode inputCode
  let maximumBits := recoveryWitnessValidationLoweringBits request
  have hpayloadBits : natBitLength payload ≤ maximumBits := by
    exact Nat.le_max_left _ _
  have houtputBits : natBitLength output ≤ maximumBits := by
    exact Nat.le_max_right _ _
  have hinputBits : natBitLength inputCode ≤ maximumBits := by
    exact (natBitLength_mono (Nat.left_le_pair inputCode witnessCode)).trans
      hpayloadBits
  have hwitnessBits : natBitLength witnessCode ≤ maximumBits := by
    exact (natBitLength_mono (Nat.right_le_pair inputCode witnessCode)).trans
      hpayloadBits
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := recoveryWitnessValidationLoweringProgram)
    (maximumBits := maximumBits) (fuel := 3) (pc := 0)
    (source := 0) (destination := 2) (next := 1)
    (value := inputCode) (by rfl) (by rfl)
    (by simp [initialNPOracleState, recoveryWitnessRequestPayload,
      inputCode])
    hinputBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := recoveryWitnessValidationLoweringProgram)
    (maximumBits := maximumBits) (fuel := 2) (pc := 1)
    (source := 0) (destination := 3) (next := 2)
    (value := witnessCode) (by rfl) (by rfl)
    (by simp [initialNPOracleState, recoveryWitnessRequestPayload,
      inputCode, witnessCode, NPOracleState.write,
      NPOracleState.jump])
    hwitnessBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := recoveryWitnessValidationLoweringProgram)
    (maximumBits := maximumBits) (fuel := 1) (pc := 2)
    (left := 3) (right := 2) (destination := 0) (next := 3)
    (value := output) (by rfl) (by rfl)
    (by simp [initialNPOracleState, recoveryWitnessRequestPayload,
      inputCode, witnessCode, output, NPOracleState.write,
      NPOracleState.jump])
    houtputBits]
  rw [show recoveryWitnessValidationLoweringOutput request = output by rfl]
  exact run_halt_instruction
    (program := recoveryWitnessValidationLoweringProgram)
    (maximumBits := maximumBits) (fuel := 0) (pc := 3)
    (outputRegister := 0) (value := output)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- A rejected witness must erase the retained public input as well. -/
def recoveryWitnessValidationGateOutput
    (validatorOutput inputCode : ℕ) : ℕ :=
  if validatorOutput = 0 then 0 else Nat.pair validatorOutput inputCode

@[simp] theorem recoveryWitnessValidationGateOutput_ne_zero_iff
    (validatorOutput inputCode : ℕ) :
    recoveryWitnessValidationGateOutput validatorOutput inputCode ≠ 0 ↔
      validatorOutput ≠ 0 := by
  by_cases hzero : validatorOutput = 0
  · simp [recoveryWitnessValidationGateOutput, hzero]
  · simp [recoveryWitnessValidationGateOutput, hzero]
    have hpositive := Nat.left_le_pair validatorOutput inputCode
    omega

theorem recoveryWitnessValidationGateOutput_input
    {validatorOutput inputCode : ℕ} (houtput : validatorOutput ≠ 0) :
    (Nat.unpair
      (recoveryWitnessValidationGateOutput validatorOutput inputCode)).2 =
        inputCode := by
  simp [recoveryWitnessValidationGateOutput, houtput]

def recoveryWitnessValidationGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 3 2
  , .halt 0
  , .set 0 0 4
  , .halt 0
  ]

@[simp] theorem recoveryWitnessValidationGateProgram_oracleFree :
    OracleFree recoveryWitnessValidationGateProgram := by
  rfl

def recoveryWitnessValidationGateFuel (validatorOutput : ℕ) : ℕ :=
  if validatorOutput = 0 then 4 else 3

def recoveryWitnessValidationGateBits
    (validatorOutput inputCode : ℕ) : ℕ :=
  max 1 (natBitLength (Nat.pair validatorOutput inputCode))

theorem run_recoveryWitnessValidationGateProgram
    (inputLength validatorOutput inputCode : ℕ) :
    runNPOracleProgram recoveryWitnessValidationGateProgram
        (recoveryWitnessValidationGateBits validatorOutput inputCode)
        (recoveryWitnessValidationGateFuel validatorOutput)
        (initialNPOracleState inputLength
          (Nat.pair validatorOutput inputCode)) =
      some (recoveryWitnessValidationGateOutput
        validatorOutput inputCode) := by
  let maximumBits :=
    recoveryWitnessValidationGateBits validatorOutput inputCode
  have hinput :
      natBitLength (Nat.pair validatorOutput inputCode) ≤ maximumBits :=
    Nat.le_max_right _ _
  have hvalidator : natBitLength validatorOutput ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair validatorOutput inputCode)).trans hinput
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  rw [show recoveryWitnessValidationGateFuel validatorOutput =
      (if validatorOutput = 0 then 3 else 2) + 1 by
    by_cases hzero : validatorOutput = 0 <;>
      simp [recoveryWitnessValidationGateFuel, hzero]]
  rw [run_unpairLeft_instruction
    (program := recoveryWitnessValidationGateProgram)
    (maximumBits := maximumBits)
    (fuel := if validatorOutput = 0 then 3 else 2)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := validatorOutput) (by rfl) (by rfl)
    (by simp [initialNPOracleState]) hvalidator]
  let state₁ :=
    ((initialNPOracleState inputLength
      (Nat.pair validatorOutput inputCode)).write
        2 validatorOutput).jump 1
  by_cases hzero : validatorOutput = 0
  · rw [if_pos hzero]
    rw [show (3 : ℕ) = 2 + 1 by omega]
    rw [run_branchZero_instruction
      (program := recoveryWitnessValidationGateProgram)
      (maximumBits := maximumBits) (fuel := 2) (pc := 1)
      (register := 2) (zeroTarget := 3) (nonzeroTarget := 2)
      (by rfl) (by rfl)]
    rw [if_pos (by simpa [state₁] using hzero)]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_set_instruction
      (program := recoveryWitnessValidationGateProgram)
      (maximumBits := maximumBits) (fuel := 1) (pc := 3)
      (register := 0) (value := 0) (next := 4)
      (by rfl) (by rfl)
      (by simpa [natBitLength] using hpositive)]
    rw [show recoveryWitnessValidationGateOutput
        validatorOutput inputCode = 0 by
      simp [recoveryWitnessValidationGateOutput, hzero]]
    exact run_halt_instruction
      (program := recoveryWitnessValidationGateProgram)
      (maximumBits := maximumBits) (fuel := 0) (pc := 4)
      (outputRegister := 0) (value := 0)
      (by rfl) (by rfl) (by simp) hpositive
  · rw [if_neg hzero]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_branchZero_instruction
      (program := recoveryWitnessValidationGateProgram)
      (maximumBits := maximumBits) (fuel := 1) (pc := 1)
      (register := 2) (zeroTarget := 3) (nonzeroTarget := 2)
      (by rfl) (by rfl)]
    rw [if_neg (by simpa [state₁] using hzero)]
    rw [show recoveryWitnessValidationGateOutput
        validatorOutput inputCode =
          Nat.pair validatorOutput inputCode by
      simp [recoveryWitnessValidationGateOutput, hzero]]
    exact run_halt_instruction
      (program := recoveryWitnessValidationGateProgram)
      (maximumBits := maximumBits) (fuel := 0) (pc := 2)
      (outputRegister := 0)
      (value := Nat.pair validatorOutput inputCode)
      (by rfl) (by rfl)
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump])
      hinput

/-- The sole public recovery-validation path.  It validates the witness on the
left of an internal pair, retains the actual public input on the right, and
then restores the global zero failure sentinel. -/
def recoveryWitnessRequestProgram
    (validator : NPOracleProgram) : NPOracleProgram :=
  linkPrograms recoveryWitnessCodeExtractorProgram <|
    linkPrograms recoveryWitnessValidationLoweringProgram <|
      linkPrograms (preserveRightProgram validator)
        recoveryWitnessValidationGateProgram

@[simp] theorem recoveryWitnessRequestProgram_oracleFree
    {validator : NPOracleProgram} (hvalidator : OracleFree validator) :
    OracleFree (recoveryWitnessRequestProgram validator) := by
  exact oracleFree_linkPrograms
    recoveryWitnessCodeExtractorProgram_oracleFree <|
      oracleFree_linkPrograms
        recoveryWitnessValidationLoweringProgram_oracleFree <|
          oracleFree_linkPrograms
            (preserveRightProgram_oracleFree validator hvalidator)
            recoveryWitnessValidationGateProgram_oracleFree

def recoveryWitnessRequestOutput
    (request : WeakVerifierRequest) (validatorOutput : ℕ) : ℕ :=
  recoveryWitnessValidationGateOutput validatorOutput
    (encodeBitInput request.input)

def recoveryWitnessRequestFuel
    (validator : NPOracleProgram) (validatorFuel validatorOutput : ℕ) : ℕ :=
  linkFuel
    (linkPrograms recoveryWitnessValidationLoweringProgram <|
      linkPrograms (preserveRightProgram validator)
        recoveryWitnessValidationGateProgram)
    2 <|
      linkFuel
        (linkPrograms (preserveRightProgram validator)
          recoveryWitnessValidationGateProgram)
        4 <|
          linkFuel recoveryWitnessValidationGateProgram
            (preserveRightFuel validatorFuel)
            (recoveryWitnessValidationGateFuel validatorOutput)

def recoveryWitnessRequestBits
    (validatorBits validatorOutput : ℕ)
    (request : WeakVerifierRequest) : ℕ :=
  max (natBitLength request.length) <|
    max (natBitLength request.code) <|
      max (recoveryWitnessValidationLoweringBits request) <|
        max
          (preserveRightBits validatorBits
            (encodeBitInput request.witness)
            (encodeBitInput request.input) validatorOutput)
          (recoveryWitnessValidationGateBits validatorOutput
            (encodeBitInput request.input))

theorem run_recoveryWitnessRequestProgram
    (validator : NPOracleProgram)
    (request : WeakVerifierRequest)
    (validatorBits validatorFuel output : ℕ)
    (hvalidator :
      runNPOracleProgram validator validatorBits validatorFuel
          (initialNPOracleState request.length
            (encodeBitInput request.witness)) =
        some output) :
    runNPOracleProgram
        (recoveryWitnessRequestProgram validator)
        (recoveryWitnessRequestBits validatorBits output request)
        (recoveryWitnessRequestFuel validator validatorFuel output)
        (initialNPOracleState request.length request.code) =
      some (recoveryWitnessRequestOutput request output) := by
  let maximumBits :=
    recoveryWitnessRequestBits validatorBits output request
  have hlength : natBitLength request.length ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength request.length by
      unfold natBitLength
      omega).trans hlength
  have hrequest :
      natBitLength request.code ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hloweringBits :
      recoveryWitnessValidationLoweringBits request ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hvalidatorBits :
      preserveRightBits validatorBits
          (encodeBitInput request.witness)
          (encodeBitInput request.input) output ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hgateBits :
      recoveryWitnessValidationGateBits output
          (encodeBitInput request.input) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hextractor :=
    run_recoveryWitnessCodeExtractorProgram request maximumBits hrequest
  have hlowering :=
    run_bits_mono
      (run_recoveryWitnessValidationLoweringProgram request)
      hloweringBits
  have hvalidation :=
    run_bits_mono
      (run_preserveRightProgram validator request.length validatorBits
        validatorFuel
        (encodeBitInput request.witness)
        (encodeBitInput request.input) output hvalidator)
      hvalidatorBits
  have hgate :=
    run_bits_mono
      (run_recoveryWitnessValidationGateProgram request.length output
        (encodeBitInput request.input))
      hgateBits
  have hvalidationTail :=
    run_linkPrograms hpositive hlength hvalidation hgate
  have hloweringTail :=
    run_linkPrograms hpositive hlength hlowering hvalidationTail
  have hrun :=
    run_linkPrograms hpositive hlength hextractor hloweringTail
  simpa only [maximumBits, recoveryWitnessRequestProgram,
    recoveryWitnessRequestFuel, recoveryWitnessRequestOutput] using hrun

/-- Exact full-validator target at the public weak-request ABI. -/
def recoveryWitnessValidatorRequestOutput
    (limits : RecoveryWitnessLimits)
    (request : WeakVerifierRequest) : ℕ :=
  recoveryWitnessRequestOutput request <|
    recoveryWitnessValidatorOutput limits
      (encodeBitInput request.witness)

theorem recoveryWitnessValidatorRequest_accepts_with_resources_iff
    {limits : RecoveryWitnessLimits}
    {request : WeakVerifierRequest} :
    recoveryWitnessValidatorRequestOutput limits request ≠ 0 ↔
      ∃ witness : CheckedRecoveryWitness limits,
        decodeRecoveryWitness limits
            (encodeBitInput request.witness) =
          some witness ∧
        RecoveryWitnessResourceChecks witness := by
  unfold recoveryWitnessValidatorRequestOutput recoveryWitnessRequestOutput
  rw [recoveryWitnessValidationGateOutput_ne_zero_iff]
  exact recoveryWitnessValidator_accepts_with_resources_iff

theorem recoveryWitnessValidatorRequestOutput_input
    {limits : RecoveryWitnessLimits} {request : WeakVerifierRequest}
    (haccepts : recoveryWitnessValidatorRequestOutput limits request ≠ 0) :
    (Nat.unpair
      (recoveryWitnessValidatorRequestOutput limits request)).2 =
        encodeBitInput request.input := by
  apply recoveryWitnessValidationGateOutput_input
  exact (recoveryWitnessValidationGateOutput_ne_zero_iff _ _).1 haccepts

/-- The only permitted handoff from a raw full validator to the public
request.  The premise deliberately requires equality to the complete decoder
target; an envelope-only or syntax-only runner cannot instantiate it. -/
theorem run_recoveryWitnessRequestProgram_of_fullValidator
    (limits : RecoveryWitnessLimits)
    (rawValidator : NPOracleProgram)
    (request : WeakVerifierRequest)
    (validatorBits validatorFuel : ℕ)
    (hvalidator :
      runNPOracleProgram rawValidator validatorBits validatorFuel
          (initialNPOracleState request.length
            (encodeBitInput request.witness)) =
        some
          (recoveryWitnessValidatorOutput limits
            (encodeBitInput request.witness))) :
    runNPOracleProgram
        (recoveryWitnessRequestProgram rawValidator)
        (recoveryWitnessRequestBits validatorBits
          (recoveryWitnessValidatorOutput limits
            (encodeBitInput request.witness)) request)
        (recoveryWitnessRequestFuel rawValidator validatorFuel
          (recoveryWitnessValidatorOutput limits
            (encodeBitInput request.witness)))
        (initialNPOracleState request.length request.code) =
      some (recoveryWitnessValidatorRequestOutput limits request) := by
  exact run_recoveryWitnessRequestProgram rawValidator request
    validatorBits validatorFuel
    (recoveryWitnessValidatorOutput limits
      (encodeBitInput request.witness))
    hvalidator

end NearCubicWires.CanonicalRecoveryRequest
