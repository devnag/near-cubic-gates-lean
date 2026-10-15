import Proof.Foundations.CanonicalBinaryProgram
import Proof.Circuits.CanonicalWitnessCodec

/-!
# Fixed-machine recovery-witness validation

This module starts the executable refinement of `decodeRecoveryWitness`.  The
outer envelope is deliberately validated by the register machine itself:
register `0` contains the untrusted code, no decoded value or acceptance bit is
supplied in another register, and malformed constructor tags or mode encodings
reach the unique zero-returning reject block.
-/

namespace NearCubicWires.CanonicalRecoveryProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline

@[simp] private theorem encodeNat_zero : encodeNat 0 = 0 := by
  simp [encodeNat, encodeBits, encodeBoolList, encodeBalancedList]

private theorem encodeNat_injective :
    Function.Injective encodeNat := by
  intro left right hequal
  have hdecoded := congrArg decodeNat hequal
  simpa using hdecoded

@[simp] private theorem decodeNat_zero : decodeNat 0 = some 0 := by
  simpa using decodeNat_encode 0

@[simp] private theorem encodeNat_one_ne_zero : encodeNat 1 ≠ 0 := by
  rw [← encodeNat_zero]
  intro hequal
  have := encodeNat_injective hequal
  omega

private theorem pair_one_ne_zero (value : ℕ) :
    Nat.pair 1 value ≠ 0 := by
  have hleft := Nat.left_le_pair 1 value
  omega

inductive RecoveryEnvelopeMode
  | symmetric
  | threshold
  deriving DecidableEq, Repr

structure RecoveryEnvelope where
  mode : RecoveryEnvelopeMode
  oracleCode : ℕ
  sumCode : ℕ
  deriving DecidableEq, Repr

/-- Exact outer syntax shared by the pure decoder and the machine proof. -/
def decodeRecoveryEnvelope (raw : ℕ) : Option RecoveryEnvelope := do
  let fields ← decodeTaggedList raw
  match fields with
  | [modeCode, oracleCode, sumCode] =>
      match decodeNat modeCode with
      | some 0 => some ⟨.symmetric, oracleCode, sumCode⟩
      | some 1 => some ⟨.threshold, oracleCode, sumCode⟩
      | _ => none
  | _ => none

def RecoveryEnvelope.outputTag : RecoveryEnvelopeMode → ℕ
  | .symmetric => 1
  | .threshold => 2

def recoveryEnvelopeOutput (raw : ℕ) : ℕ :=
  match decodeRecoveryEnvelope raw with
  | some envelope => Nat.pair (RecoveryEnvelope.outputTag envelope.mode) raw
  | none => 0

def recoveryEnvelopeOfChecked
    {limits : RecoveryWitnessLimits} :
    CheckedRecoveryWitness limits → RecoveryEnvelope
  | .symmetric oracle _ sum =>
      ⟨.symmetric, encodeBooleanCircuit oracle,
        sum.code symmetricCircuitCodec⟩
  | .threshold oracle _ sum =>
      ⟨.threshold, encodeBooleanCircuit oracle,
        sum.code thresholdCircuitCodec⟩

/-- The outer executable ABI is definitionally the envelope of the complete
canonical witness decoder; no second mode or payload convention is introduced. -/
theorem decodeRecoveryEnvelope_of_decodeRecoveryWitness
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    {witness : CheckedRecoveryWitness limits}
    (hdecode : decodeRecoveryWitness limits raw = some witness) :
    decodeRecoveryEnvelope raw = some (recoveryEnvelopeOfChecked witness) := by
  have hcode := CheckedRecoveryWitness.code_of_decode hdecode
  cases witness with
  | symmetric oracle horacle sum =>
      rw [← hcode]
      simp [CheckedRecoveryWitness.code, recoveryEnvelopeOfChecked,
        decodeRecoveryEnvelope]
  | threshold oracle horacle sum =>
      rw [← hcode]
      simp [CheckedRecoveryWitness.code, recoveryEnvelopeOfChecked,
        decodeRecoveryEnvelope]

theorem recoveryEnvelopeOutput_of_decodeRecoveryWitness
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    {witness : CheckedRecoveryWitness limits}
    (hdecode : decodeRecoveryWitness limits raw = some witness) :
    recoveryEnvelopeOutput raw =
      Nat.pair
        (RecoveryEnvelope.outputTag (recoveryEnvelopeOfChecked witness).mode)
        raw := by
  unfold recoveryEnvelopeOutput
  rw [decodeRecoveryEnvelope_of_decodeRecoveryWitness hdecode]

/-! ## Unique full-validator specification -/

def recoveryWitnessModeTag : RecoveryWitnessMode → ℕ
  | .symmetric => 1
  | .threshold => 2

def checkedRecoveryWitnessModeTag
    {limits : RecoveryWitnessLimits}
    (witness : CheckedRecoveryWitness limits) : ℕ :=
  recoveryWitnessModeTag witness.mode

theorem checkedRecoveryWitnessModeTag_positive
    {limits : RecoveryWitnessLimits}
    (witness : CheckedRecoveryWitness limits) :
    0 < checkedRecoveryWitnessModeTag witness := by
  cases witness <;>
    simp [checkedRecoveryWitnessModeTag, recoveryWitnessModeTag,
      CheckedRecoveryWitness.mode]

/-- The sole semantic target for the final full validator.  In contrast to
`recoveryEnvelopeOutput`, this accepts exactly when the complete canonical
decoder has checked the Boolean DAG, selected circuit family, rational
coefficients, and every configured resource limit. -/
def recoveryWitnessValidatorOutput
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  match decodeRecoveryWitness limits raw with
  | some witness =>
      Nat.pair (checkedRecoveryWitnessModeTag witness) raw
  | none => 0

theorem recoveryWitnessValidatorOutput_of_decode
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    {witness : CheckedRecoveryWitness limits}
    (hdecode : decodeRecoveryWitness limits raw = some witness) :
    recoveryWitnessValidatorOutput limits raw =
      Nat.pair (checkedRecoveryWitnessModeTag witness) raw := by
  simp [recoveryWitnessValidatorOutput, hdecode]

@[simp] theorem recoveryWitnessValidatorOutput_code
    {limits : RecoveryWitnessLimits}
    (witness : CheckedRecoveryWitness limits) :
    recoveryWitnessValidatorOutput limits witness.code =
      Nat.pair (checkedRecoveryWitnessModeTag witness) witness.code := by
  exact recoveryWitnessValidatorOutput_of_decode
    (decodeRecoveryWitness_encode witness)

/-- Explicit resource ledger carried by a successful full decode.  Naming the
conjunction prevents a future executable layer from proving only canonical
syntax while silently omitting term count, coefficient, mass, wire, or
description checks. -/
def RecoveryWitnessResourceChecks
    {limits : RecoveryWitnessLimits}
    (witness : CheckedRecoveryWitness limits) : Prop :=
  match witness with
  | .symmetric oracle _ sum =>
      oracle.output.val < oracle.nodes.length ∧
      (∀ index : Fin oracle.nodes.length,
        (oracle.nodes.get index).WellFormedAt index.val) ∧
      oracle.size ≤ limits.oracleSizeCap ∧
      sum.value.q = limits.symmetric.expectedArity ∧
      sum.value.q = limits.sumArity ∧
      sum.value.terms.length ≤ limits.symmetric.termCap ∧
      (∀ term ∈ sum.value.terms,
        natBitLength term.coefficient.num.natAbs ≤
            limits.symmetric.coefficientBitCap ∧
          natBitLength term.coefficient.den ≤
            limits.symmetric.coefficientBitCap) ∧
      sum.value.coefficientMass ≤
        limits.symmetric.coefficientMassCap ∧
      (∀ term ∈ sum.value.terms,
        NormalizedSymmetricThresholdCircuit.wireCount term.circuit ≤
          limits.symmetric.wireCap) ∧
      (∀ term ∈ sum.value.terms,
        NormalizedSymmetricThresholdCircuit.descriptionBits term.circuit ≤
          limits.symmetric.descriptionCap)
  | .threshold oracle _ sum =>
      oracle.output.val < oracle.nodes.length ∧
      (∀ index : Fin oracle.nodes.length,
        (oracle.nodes.get index).WellFormedAt index.val) ∧
      oracle.size ≤ limits.oracleSizeCap ∧
      sum.value.q = limits.threshold.expectedArity ∧
      sum.value.q = limits.sumArity ∧
      sum.value.terms.length ≤ limits.threshold.termCap ∧
      (∀ term ∈ sum.value.terms,
        natBitLength term.coefficient.num.natAbs ≤
            limits.threshold.coefficientBitCap ∧
          natBitLength term.coefficient.den ≤
            limits.threshold.coefficientBitCap) ∧
      sum.value.coefficientMass ≤
        limits.threshold.coefficientMassCap ∧
      (∀ term ∈ sum.value.terms,
        NormalizedThresholdThresholdCircuit.wireCount term.circuit ≤
          limits.threshold.wireCap) ∧
      (∀ term ∈ sum.value.terms,
        NormalizedThresholdThresholdCircuit.descriptionBits term.circuit ≤
          limits.threshold.descriptionCap)

theorem checkedRecoveryWitness_resourceChecks
    {limits : RecoveryWitnessLimits}
    (witness : CheckedRecoveryWitness limits) :
    RecoveryWitnessResourceChecks witness := by
  cases witness with
  | symmetric oracle horacle sum =>
      exact ⟨oracle.output.isLt, oracle.wellFormed, horacle, sum.arity_eq,
        sum.arity_eq.trans limits.symmetricArity, sum.terms_le,
        sum.coefficient_bits_le, sum.mass_le, sum.wires_le,
        sum.description_le⟩
  | threshold oracle horacle sum =>
      exact ⟨oracle.output.isLt, oracle.wellFormed, horacle, sum.arity_eq,
        sum.arity_eq.trans limits.thresholdArity, sum.terms_le,
        sum.coefficient_bits_le, sum.mass_le, sum.wires_le,
        sum.description_le⟩

theorem recoveryWitnessValidatorOutput_ne_zero_iff
    {limits : RecoveryWitnessLimits} {raw : ℕ} :
    recoveryWitnessValidatorOutput limits raw ≠ 0 ↔
      ∃ witness : CheckedRecoveryWitness limits,
        decodeRecoveryWitness limits raw = some witness := by
  unfold recoveryWitnessValidatorOutput
  cases hdecode : decodeRecoveryWitness limits raw with
  | none => simp
  | some witness =>
      constructor
      · intro _
        exact ⟨witness, rfl⟩
      · intro _
        have htag := checkedRecoveryWitnessModeTag_positive witness
        have hleft :=
          Nat.left_le_pair (checkedRecoveryWitnessModeTag witness) raw
        exact (htag.trans_le hleft).ne'

theorem recoveryWitnessValidatorOutput_eq_zero_iff
    {limits : RecoveryWitnessLimits} {raw : ℕ} :
    recoveryWitnessValidatorOutput limits raw = 0 ↔
      decodeRecoveryWitness limits raw = none := by
  cases hdecode : decodeRecoveryWitness limits raw with
  | none =>
      simp [recoveryWitnessValidatorOutput, hdecode]
  | some witness =>
      have hnonzero :
          Nat.pair (checkedRecoveryWitnessModeTag witness) raw ≠ 0 := by
        have htag := checkedRecoveryWitnessModeTag_positive witness
        have hleft :=
          Nat.left_le_pair (checkedRecoveryWitnessModeTag witness) raw
        exact (htag.trans_le hleft).ne'
      simp [recoveryWitnessValidatorOutput, hdecode, hnonzero]

theorem recoveryWitnessValidator_accepts_with_resources_iff
    {limits : RecoveryWitnessLimits} {raw : ℕ} :
    recoveryWitnessValidatorOutput limits raw ≠ 0 ↔
      ∃ witness : CheckedRecoveryWitness limits,
        decodeRecoveryWitness limits raw = some witness ∧
          RecoveryWitnessResourceChecks witness := by
  rw [recoveryWitnessValidatorOutput_ne_zero_iff]
  constructor
  · rintro ⟨witness, hdecode⟩
    exact ⟨witness, hdecode, checkedRecoveryWitness_resourceChecks witness⟩
  · rintro ⟨witness, hdecode, _⟩
    exact ⟨witness, hdecode⟩

/-! The following closed counterexample is a regression guard against wiring
the executable envelope parser into a theorem that requires full validation.
The outer three-field syntax and mode are valid, but the empty Boolean-oracle
code is not a circuit under any limits. -/

def malformedNestedRecoveryCode : ℕ :=
  encodeTaggedList [encodeNat 0, 0, 0]

theorem recoveryEnvelope_accepts_malformedNestedRecoveryCode :
    recoveryEnvelopeOutput malformedNestedRecoveryCode =
      Nat.pair 1 malformedNestedRecoveryCode := by
  simp [recoveryEnvelopeOutput, malformedNestedRecoveryCode,
    decodeRecoveryEnvelope, RecoveryEnvelope.outputTag]

theorem recoveryWitnessValidator_rejects_malformedNestedRecoveryCode
    (limits : RecoveryWitnessLimits) :
    recoveryWitnessValidatorOutput limits malformedNestedRecoveryCode = 0 := by
  unfold recoveryWitnessValidatorOutput malformedNestedRecoveryCode
  rw [decodeRecoveryWitness_zeroOracle_symmetric]

theorem recoveryEnvelope_is_not_fullRecoveryValidator
    (limits : RecoveryWitnessLimits) :
    recoveryEnvelopeOutput malformedNestedRecoveryCode ≠
      recoveryWitnessValidatorOutput limits malformedNestedRecoveryCode := by
  rw [recoveryEnvelope_accepts_malformedNestedRecoveryCode,
    recoveryWitnessValidator_rejects_malformedNestedRecoveryCode]
  have hleft := Nat.left_le_pair 1 malformedNestedRecoveryCode
  omega

theorem recoveryEnvelope_not_extensionally_fullRecoveryValidator
    (limits : RecoveryWitnessLimits) :
    ¬∀ raw,
      recoveryEnvelopeOutput raw =
        recoveryWitnessValidatorOutput limits raw := by
  intro hequal
  exact recoveryEnvelope_is_not_fullRecoveryValidator limits
    (hequal malformedNestedRecoveryCode)

/-!
The program is intentionally unrolled at this fixed three-field boundary.  A
loop counter would itself need subtraction, while unrolling keeps every
control-flow edge finite and makes “exactly three fields” part of the code.

Register ABI:
* `r2`: current outer-list cursor;
* `r3`: original raw code;
* `r4`, `r5`, `r6`: mode, oracle, and legal-sum payload codes;
* `r12`--`r15`: structural scratch;
* `r11`: nonzero accepted-mode tag.
-/
def recoveryEnvelopeProgram : NPOracleProgram :=
  [ .copy 0 2 1
  , .copy 0 3 2
  -- First tagged cell, payload to r4.
  , .branchZero 2 65 3
  , .unpairLeft 2 12 4
  , .branchZero 12 65 5
  , .unpairLeft 12 13 6
  , .branchZero 13 7 65
  , .copy 12 14 8
  , .increment 14 9
  , .unpairRight 14 13 10
  , .branchZero 13 11 65
  , .unpairRight 2 15 12
  , .unpairLeft 15 4 13
  , .unpairRight 15 2 14
  -- Second tagged cell, payload to r5.
  , .branchZero 2 65 15
  , .unpairLeft 2 12 16
  , .branchZero 12 65 17
  , .unpairLeft 12 13 18
  , .branchZero 13 19 65
  , .copy 12 14 20
  , .increment 14 21
  , .unpairRight 14 13 22
  , .branchZero 13 23 65
  , .unpairRight 2 15 24
  , .unpairLeft 15 5 25
  , .unpairRight 15 2 26
  -- Third tagged cell, payload to r6.
  , .branchZero 2 65 27
  , .unpairLeft 2 12 28
  , .branchZero 12 65 29
  , .unpairLeft 12 13 30
  , .branchZero 13 31 65
  , .copy 12 14 32
  , .increment 14 33
  , .unpairRight 14 13 34
  , .branchZero 13 35 65
  , .unpairRight 2 15 36
  , .unpairLeft 15 6 37
  , .unpairRight 15 2 38
  , .branchZero 2 39 65
  -- Canonical mode 0 is raw code 0; canonical mode 1 is
  -- pair 1 1.  The two exact-one checks use the finite signature
  -- proved by `CanonicalBinary.isOneCode_iff`.
  , .branchZero 4 60 40
  , .unpairLeft 4 12 41
  , .branchZero 12 65 42
  , .unpairLeft 12 13 43
  , .branchZero 13 44 65
  , .copy 12 14 45
  , .increment 14 46
  , .unpairRight 14 13 47
  , .branchZero 13 48 65
  , .unpairRight 4 15 49
  , .branchZero 15 65 50
  -- Validate that the right child is the raw numeral one.  The successor
  -- signature makes the check exact without trusting a decoded side channel.
  , .unpairLeft 15 12 51
  , .branchZero 12 52 65
  , .copy 15 14 53
  , .increment 14 54
  , .unpairRight 14 13 55
  , .branchZero 13 56 65
  , .unpairLeft 14 12 57
  , .branchZero 12 65 58
  , .unpairRight 15 13 59
  , .branchZero 13 65 62
  -- The output tag distinguishes the two accepted branches without trusting
  -- a side-channel register supplied by the caller.
  , .set 11 1 61
  , .pair 11 3 0 64
  , .set 11 2 63
  , .pair 11 3 0 64
  , .halt 0
  , .set 0 0 66
  , .halt 0
  ]

@[simp] theorem recoveryEnvelopeProgram_length :
    recoveryEnvelopeProgram.length = 67 := by
  rfl

@[simp] theorem recoveryEnvelopeProgram_oracleFree :
    OracleFree recoveryEnvelopeProgram := by
  rfl

def recoveryEnvelopeFuel : ℕ := 67

/-- A deliberately simple dominating register bound.  Every unpaired
component is at most `raw`; the only larger scratch value is a constructor tag
plus one, and the only paired value is one of the two public outputs. -/
def recoveryEnvelopeRegisterBound (raw : ℕ) : ℕ :=
  max (Nat.pair 1 raw)
    (max (Nat.pair 2 raw) (raw + 2))

def recoveryEnvelopeBits (raw : ℕ) : ℕ :=
  natBitLength (recoveryEnvelopeRegisterBound raw)

private theorem envelopeValueBits
    (raw value maximumBits : ℕ)
    (hvalue : value ≤ recoveryEnvelopeRegisterBound raw)
    (hbits : recoveryEnvelopeBits raw ≤ maximumBits) :
    natBitLength value ≤ maximumBits := by
  exact (natBitLength_mono hvalue).trans hbits

private theorem raw_le_envelopeBound (raw : ℕ) :
    raw ≤ recoveryEnvelopeRegisterBound raw := by
  exact (Nat.right_le_pair 1 raw).trans
    (le_max_left _ _)

private theorem raw_add_one_le_envelopeBound (raw : ℕ) :
    raw + 1 ≤ recoveryEnvelopeRegisterBound raw := by
  exact (by omega : raw + 1 ≤ raw + 2) |>.trans
    (le_trans (le_max_right _ _) (le_max_right _ _))

private theorem small_le_envelopeBound (raw : ℕ) :
    2 ≤ recoveryEnvelopeRegisterBound raw := by
  exact (by omega : 2 ≤ raw + 2) |>.trans
    (le_trans (le_max_right _ _) (le_max_right _ _))

private theorem outputOne_le_envelopeBound (raw : ℕ) :
    Nat.pair 1 raw ≤ recoveryEnvelopeRegisterBound raw :=
  le_max_left _ _

private theorem outputTwo_le_envelopeBound (raw : ℕ) :
    Nat.pair 2 raw ≤ recoveryEnvelopeRegisterBound raw :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- Pairing increases bit length by at most a constant factor.  This bound,
not the numeric register value, is the width charged by the polynomial
runner. -/
theorem recoveryEnvelopeBits_le_linear (raw : ℕ) :
    recoveryEnvelopeBits raw ≤ 2 * natBitLength raw + 4 := by
  let length := natBitLength raw
  have hlengthPositive : 0 < length := by
    unfold length natBitLength
    omega
  have hrawPow : raw < 2 ^ length := by
    dsimp [length, natBitLength]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two raw
  have hpowPositive : 0 < 2 ^ length := pow_pos (by omega) _
  have hrawThree : raw + 3 ≤ 4 * 2 ^ length := by
    omega
  have hmaxOne : max 1 raw + 1 ≤ raw + 3 := by
    apply Nat.add_le_add_right
    exact max_le (by omega) (by omega)
  have hmaxTwo : max 2 raw + 1 ≤ raw + 3 := by
    apply Nat.add_le_add_right
    exact max_le (by omega) (by omega)
  have hscale :
      (4 * 2 ^ length) ^ 2 = 2 ^ (2 * length + 4) := by
    calc
      (4 * 2 ^ length) ^ 2 =
          (2 ^ (length + 2)) ^ 2 := by
        congr 1
        simp [pow_add, Nat.mul_comm]
      _ = 2 ^ ((length + 2) * 2) := by
        rw [pow_mul]
      _ = 2 ^ (2 * length + 4) := by
        congr 1
        omega
  have hpairOne :
      Nat.pair 1 raw < 2 ^ (2 * length + 4) := by
    calc
      Nat.pair 1 raw < (max 1 raw + 1) ^ 2 :=
        Nat.pair_lt_max_add_one_sq 1 raw
      _ ≤ (4 * 2 ^ length) ^ 2 :=
        Nat.pow_le_pow_left (hmaxOne.trans hrawThree) 2
      _ = 2 ^ (2 * length + 4) := hscale
  have hpairTwo :
      Nat.pair 2 raw < 2 ^ (2 * length + 4) := by
    calc
      Nat.pair 2 raw < (max 2 raw + 1) ^ 2 :=
        Nat.pair_lt_max_add_one_sq 2 raw
      _ ≤ (4 * 2 ^ length) ^ 2 :=
        Nat.pow_le_pow_left (hmaxTwo.trans hrawThree) 2
      _ = 2 ^ (2 * length + 4) := hscale
  have hrawTwo :
      raw + 2 < 2 ^ (2 * length + 4) := by
    have hbase : 4 * 2 ^ length < (4 * 2 ^ length) ^ 2 := by
      nlinarith
    exact (by omega : raw + 2 ≤ 4 * 2 ^ length) |>.trans_lt
      (hbase.trans_eq hscale)
  have hbound :
      recoveryEnvelopeRegisterBound raw <
        2 ^ (2 * length + 4) := by
    unfold recoveryEnvelopeRegisterBound
    exact max_lt hpairOne (max_lt hpairTwo hrawTwo)
  have hboundNe : recoveryEnvelopeRegisterBound raw ≠ 0 := by
    have := (by omega : 0 < raw + 2)
    have hle :
        raw + 2 ≤ recoveryEnvelopeRegisterBound raw :=
      (le_max_right _ _).trans (le_max_right _ _)
    omega
  have hlog :
      Nat.log 2 (recoveryEnvelopeRegisterBound raw) <
        2 * length + 4 :=
    Nat.log_lt_of_lt_pow hboundNe hbound
  unfold recoveryEnvelopeBits natBitLength
  change
    Nat.log 2 (recoveryEnvelopeRegisterBound raw) + 1 ≤
      2 * length + 4
  omega

/-!
`recoveryEnvelopeMachineOutput` is the direct structural trace mirrored by the
program.  Keeping this tiny proof model separate from the public decoder lets
the interpreter proof normalize instruction by instruction; the equivalence
to `decodeRecoveryEnvelope` is proved below.
-/
def recoveryEnvelopeMachineOutput (raw : ℕ) : ℕ :=
  let outer₀ := Nat.unpair raw
  let payload₀ := Nat.unpair outer₀.2
  let outer₁ := Nat.unpair payload₀.2
  let payload₁ := Nat.unpair outer₁.2
  let outer₂ := Nat.unpair payload₁.2
  let payload₂ := Nat.unpair outer₂.2
  if outer₀.1 = 1 ∧ outer₁.1 = 1 ∧ outer₂.1 = 1 ∧ payload₂.2 = 0 then
    if payload₀.1 = 0 then
      Nat.pair 1 raw
    else if payload₀.1 = encodeNat 1 then
      Nat.pair 2 raw
    else
      0
  else
    0

private theorem recoveryEnvelope_structural_raw
    (raw : ℕ)
    (outer₀ payload₀ outer₁ payload₁ outer₂ payload₂ : ℕ × ℕ)
    (houter₀ : Nat.unpair raw = outer₀)
    (hpayload₀ : Nat.unpair outer₀.2 = payload₀)
    (houter₁ : Nat.unpair payload₀.2 = outer₁)
    (hpayload₁ : Nat.unpair outer₁.2 = payload₁)
    (houter₂ : Nat.unpair payload₁.2 = outer₂)
    (hpayload₂ : Nat.unpair outer₂.2 = payload₂)
    (htag₀ : outer₀.1 = 1)
    (htag₁ : outer₁.1 = 1)
    (htag₂ : outer₂.1 = 1)
    (htail : payload₂.2 = 0) :
    raw = encodeTaggedList [payload₀.1, payload₁.1, payload₂.1] := by
  have hrawPair := Nat.pair_unpair raw
  rw [houter₀] at hrawPair
  have hpayload₀Pair := Nat.pair_unpair outer₀.2
  rw [hpayload₀] at hpayload₀Pair
  have houter₁Pair := Nat.pair_unpair payload₀.2
  rw [houter₁] at houter₁Pair
  have hpayload₁Pair := Nat.pair_unpair outer₁.2
  rw [hpayload₁] at hpayload₁Pair
  have houter₂Pair := Nat.pair_unpair payload₁.2
  rw [houter₂] at houter₂Pair
  have hpayload₂Pair := Nat.pair_unpair outer₂.2
  rw [hpayload₂] at hpayload₂Pair
  have hpayload₀ :
      outer₀.2 = Nat.pair payload₀.1 payload₀.2 :=
    hpayload₀Pair.symm
  have houter₁Code :
      payload₀.2 = Nat.pair outer₁.1 outer₁.2 :=
    houter₁Pair.symm
  have hpayload₁Code :
      outer₁.2 = Nat.pair payload₁.1 payload₁.2 :=
    hpayload₁Pair.symm
  have houter₂Code :
      payload₁.2 = Nat.pair outer₂.1 outer₂.2 :=
    houter₂Pair.symm
  have hpayload₂Code :
      outer₂.2 = Nat.pair payload₂.1 payload₂.2 :=
    hpayload₂Pair.symm
  calc
    raw = Nat.pair outer₀.1 outer₀.2 := hrawPair.symm
    _ = Nat.pair 1 outer₀.2 := by rw [htag₀]
    _ = Nat.pair 1 (Nat.pair payload₀.1 payload₀.2) := by
      rw [hpayload₀]
    _ = Nat.pair 1
          (Nat.pair payload₀.1 (Nat.pair outer₁.1 outer₁.2)) := by
      rw [houter₁Code]
    _ = Nat.pair 1
          (Nat.pair payload₀.1
            (Nat.pair 1 outer₁.2)) := by
      rw [htag₁]
    _ = Nat.pair 1
          (Nat.pair payload₀.1
            (Nat.pair 1 (Nat.pair payload₁.1 payload₁.2))) := by
      rw [hpayload₁Code]
    _ = Nat.pair 1
          (Nat.pair payload₀.1
            (Nat.pair 1
              (Nat.pair payload₁.1 (Nat.pair outer₂.1 outer₂.2)))) := by
      rw [houter₂Code]
    _ = Nat.pair 1
          (Nat.pair payload₀.1
            (Nat.pair 1
              (Nat.pair payload₁.1
                (Nat.pair 1 outer₂.2)))) := by
      rw [htag₂]
    _ = Nat.pair 1
          (Nat.pair payload₀.1
            (Nat.pair 1
              (Nat.pair payload₁.1
                (Nat.pair 1 (Nat.pair payload₂.1 payload₂.2))))) := by
      rw [hpayload₂Code]
    _ = Nat.pair 1
          (Nat.pair payload₀.1
            (Nat.pair 1
              (Nat.pair payload₁.1
                (Nat.pair 1 (Nat.pair payload₂.1 0))))) := by
      rw [htail]
    _ = encodeTaggedList [payload₀.1, payload₁.1, payload₂.1] := by
      rfl

set_option maxHeartbeats 2000000 in
-- Dependent canonical decoding makes this structural normalization expensive.
theorem recoveryEnvelopeMachineOutput_eq
    (raw : ℕ) :
    recoveryEnvelopeMachineOutput raw = recoveryEnvelopeOutput raw := by
  generalize hdecode : decodeTaggedList raw = decoded
  cases decoded with
  | none =>
      unfold recoveryEnvelopeMachineOutput recoveryEnvelopeOutput
        decodeRecoveryEnvelope
      rw [hdecode]
      by_cases hstructure :
          let outer₀ := Nat.unpair raw
          let payload₀ := Nat.unpair outer₀.2
          let outer₁ := Nat.unpair payload₀.2
          let payload₁ := Nat.unpair outer₁.2
          let outer₂ := Nat.unpair payload₁.2
          let payload₂ := Nat.unpair outer₂.2
          outer₀.1 = 1 ∧ outer₁.1 = 1 ∧ outer₂.1 = 1 ∧
            payload₂.2 = 0
      · let outer₀ := Nat.unpair raw
        let payload₀ := Nat.unpair outer₀.2
        let outer₁ := Nat.unpair payload₀.2
        let payload₁ := Nat.unpair outer₁.2
        let outer₂ := Nat.unpair payload₁.2
        let payload₂ := Nat.unpair outer₂.2
        change
          outer₀.1 = 1 ∧ outer₁.1 = 1 ∧ outer₂.1 = 1 ∧
            payload₂.2 = 0 at hstructure
        rcases hstructure with ⟨htag₀, htag₁, htag₂, htail⟩
        have hraw :=
          recoveryEnvelope_structural_raw raw
            outer₀ payload₀ outer₁ payload₁ outer₂ payload₂
            (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
            htag₀ htag₁ htag₂ htail
        have hdecoded :
            decodeTaggedList raw =
              some [payload₀.1, payload₁.1, payload₂.1] := by
          rw [hraw]
          exact decodeTaggedList_encode _
        rw [hdecode] at hdecoded
        simp at hdecoded
      · simp [hstructure]
  | some fields =>
      have hraw : encodeTaggedList fields = raw :=
        encodeTaggedList_of_decode hdecode
      rw [← hraw]
      unfold recoveryEnvelopeOutput decodeRecoveryEnvelope
      rw [decodeTaggedList_encode fields]
      cases fields with
      | nil =>
          simp [recoveryEnvelopeMachineOutput, encodeTaggedList]
      | cons first rest =>
          cases rest with
          | nil =>
              simp [recoveryEnvelopeMachineOutput, encodeTaggedList,
                Nat.unpair_pair]
          | cons second rest =>
              cases rest with
              | nil =>
                  simp [recoveryEnvelopeMachineOutput, encodeTaggedList,
                    Nat.unpair_pair]
              | cons third rest =>
                  cases rest with
                  | nil =>
                      generalize hmode : decodeNat first = mode
                      cases mode with
                      | none =>
                          have hzero : first ≠ 0 := by
                            intro hfirst
                            subst first
                            simp at hmode
                          have hone : first ≠ encodeNat 1 := by
                            intro hfirst
                            subst first
                            simp at hmode
                          simp [recoveryEnvelopeMachineOutput,
                            encodeTaggedList, Nat.unpair_pair, hmode,
                            hzero, hone]
                      | some value =>
                          have hcode : encodeNat value = first :=
                            encodeNat_of_decode hmode
                          subst first
                          cases value with
                          | zero =>
                              simp [recoveryEnvelopeMachineOutput,
                                encodeTaggedList,
                                Nat.unpair_pair,
                                RecoveryEnvelope.outputTag]
                          | succ value =>
                              cases value with
                              | zero =>
                                  simp [recoveryEnvelopeMachineOutput,
                                    encodeTaggedList,
                                    Nat.unpair_pair,
                                    RecoveryEnvelope.outputTag]
                              | succ value =>
                                  have hzero :
                                      encodeNat (value + 1 + 1) ≠ 0 := by
                                    rw [← encodeNat_zero]
                                    intro hequal
                                    have := encodeNat_injective hequal
                                    omega
                                  have hone :
                                      encodeNat (value + 1 + 1) ≠
                                        encodeNat 1 := by
                                    intro hequal
                                    have := encodeNat_injective hequal
                                    omega
                                  simp [recoveryEnvelopeMachineOutput,
                                    encodeTaggedList, Nat.unpair_pair,
                                    hmode, hzero, hone]
                  | cons fourth rest =>
                      have htail :
                          Nat.pair 1
                              (Nat.pair fourth (encodeTaggedList rest)) ≠
                            0 :=
                        pair_one_ne_zero _
                      simp [recoveryEnvelopeMachineOutput,
                        encodeTaggedList, Nat.unpair_pair, htail]

end CanonicalRecoveryProgram
end NearCubicWires
