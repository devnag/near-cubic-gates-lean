import Proof.MachineModel.CanonicalBalancedLengthProgram
import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalFourfoldRowTailProgram
import Proof.MachineModel.FixedAccuracyDenominatorProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# The symmetric list denominator, executed from the typed envelope

Every symmetric row of a fourfold request is indexed by a
`NormalizedOccurrenceListSeed` at the *list denominator*

```text
symmetricListDenominator request (fixedTargetDenominator accuracyExponent q)
  = request.circuits.length * (q ^ accuracyExponent + 1)
```

Both the row evaluator and the row counter need that number as a machine value
computed from the typed envelope alone: the evaluator uses it to select the
seed family, the counter uses it to select the canonical walk length.  This
module supplies the fixed program.

The three arithmetic stages already exist — `fixedTargetDenominatorProgram`
for `q ^ accuracyExponent`, `balancedLengthProgram` for the circuit count, and
`bitSerialMulProgram` for the product — so only the two structural repacks
between them are new.  The accuracy exponent is a link-time constant; the
request ABI still carries no denominator field.
-/

namespace NearCubicWires.CanonicalFourfoldListDenominatorProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 The two structural repacks -/

/-- Drop the encoded family tag; the arity/circuit-list payload remains.  The
tag has already been validated by the front end, so no decoding happens
here. -/
def fourfoldEnvelopePayloadProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .halt 0
  ]

@[simp] theorem fourfoldEnvelopePayloadProgram_oracleFree :
    OracleFree fourfoldEnvelopePayloadProgram := by
  rfl

def fourfoldEnvelopePayloadBits (q listCode : ℕ) : ℕ :=
  natBitLength (Nat.pair q listCode)

theorem run_fourfoldEnvelopePayloadProgram
    (inputLength tagCode q listCode : ℕ) :
    runNPOracleProgram fourfoldEnvelopePayloadProgram
        (fourfoldEnvelopePayloadBits q listCode) 2
        (initialNPOracleState inputLength
          (Nat.pair tagCode (Nat.pair q listCode))) =
      some (Nat.pair q listCode) := by
  have hpayload :
      natBitLength (Nat.pair q listCode) ≤
        fourfoldEnvelopePayloadBits q listCode :=
    Nat.le_refl _
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair q listCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hpayload]
  exact run_halt_instruction (fuel := 0) (value := Nat.pair q listCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpayload

/-- Multiplier ABI of the list denominator: the circuit-list code on the left
and the *positive* target denominator on the right. -/
def fourfoldDenominatorSwapOutput (power listCode : ℕ) : ℕ :=
  Nat.pair listCode (power + 1)

/-- Move the computed power past the retained circuit-list code and add the
canonical successor.  No value is decoded. -/
def fourfoldDenominatorSwapProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .increment 2 3
  , .pair 3 2 0 4
  , .halt 0
  ]

@[simp] theorem fourfoldDenominatorSwapProgram_oracleFree :
    OracleFree fourfoldDenominatorSwapProgram := by
  rfl

def fourfoldDenominatorSwapBits (power listCode : ℕ) : ℕ :=
  natBitLength <|
    max (Nat.pair power listCode)
      (fourfoldDenominatorSwapOutput power listCode) + 1

theorem run_fourfoldDenominatorSwapProgram
    (inputLength power listCode : ℕ) :
    runNPOracleProgram fourfoldDenominatorSwapProgram
        (fourfoldDenominatorSwapBits power listCode) 5
        (initialNPOracleState inputLength (Nat.pair power listCode)) =
      some (fourfoldDenominatorSwapOutput power listCode) := by
  let input := Nat.pair power listCode
  let output := fourfoldDenominatorSwapOutput power listCode
  let bound := max input output + 1
  let maximumBits := fourfoldDenominatorSwapBits power listCode
  have hmaximumBits : natBitLength bound = maximumBits := rfl
  have bits_of_le {value : ℕ} (hvalue : value ≤ bound) :
      natBitLength value ≤ maximumBits := by
    rw [← hmaximumBits]
    exact natBitLength_mono hvalue
  have hinput : natBitLength input ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_left _ _).trans (Nat.le_add_right _ _)
  have houtput : natBitLength output ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)
  have hpower : natBitLength power ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair power listCode)).trans hinput
  have hlistCode : natBitLength listCode ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair power listCode)).trans hinput
  have hsuccessor : natBitLength (power + 1) ≤ maximumBits := by
    apply bits_of_le
    have hle : power ≤ input := Nat.left_le_pair power listCode
    have hbound : input ≤ max input output := Nat.le_max_left _ _
    omega
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := power)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hpower]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := listCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hlistCode]
  rw [show 3 = 2 + 1 by omega]
  rw [run_increment_instruction (value := power + 1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsuccessor]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        fourfoldDenominatorSwapOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-! ## §2 The composed list denominator -/

/-- **The list denominator.**  Payload projection, the fixed accuracy power,
the retained circuit-list length, and one bit-serial product. -/
def fourfoldListDenominatorProgram (accuracyExponent : ℕ) : NPOracleProgram :=
  linkPrograms fourfoldEnvelopePayloadProgram
    (linkPrograms
      (preserveRightProgram (fixedTargetDenominatorProgram accuracyExponent))
      (linkPrograms fourfoldDenominatorSwapProgram
        (linkPrograms (preserveRightProgram balancedLengthProgram)
          bitSerialMulProgram)))

theorem fourfoldListDenominatorProgram_oracleFree (accuracyExponent : ℕ) :
    OracleFree (fourfoldListDenominatorProgram accuracyExponent) :=
  oracleFree_linkPrograms fourfoldEnvelopePayloadProgram_oracleFree <|
    oracleFree_linkPrograms
      (preserveRightProgram_oracleFree _
        (fixedTargetDenominatorProgram_oracleFree accuracyExponent)) <|
      oracleFree_linkPrograms fourfoldDenominatorSwapProgram_oracleFree <|
        oracleFree_linkPrograms
          (preserveRightProgram_oracleFree _ balancedLengthProgram_oracleFree)
          bitSerialMulProgram_oracleFree

def fourfoldListDenominatorStageBits
    (accuracyExponent q : ℕ) (values : List ℕ) : List ℕ :=
  let listCode := encodeBalancedList values
  let power := q ^ accuracyExponent
  [ 1
  , natBitLength q
  , fourfoldEnvelopePayloadBits q listCode
  , preserveRightBits (fixedTargetDenominatorBits accuracyExponent q) q
      listCode power
  , fourfoldDenominatorSwapBits power listCode
  , preserveRightBits (balancedLengthBits q values) listCode (power + 1)
      values.length
  , bitSerialMulBits q values.length (power + 1)
  ]

def fourfoldListDenominatorBits
    (accuracyExponent q : ℕ) (values : List ℕ) : ℕ :=
  (fourfoldListDenominatorStageBits accuracyExponent q values).foldr max 1

def fourfoldListDenominatorFuel
    (accuracyExponent q : ℕ) (values : List ℕ) : ℕ :=
  linkFuel
      (linkPrograms
        (preserveRightProgram (fixedTargetDenominatorProgram accuracyExponent))
        (linkPrograms fourfoldDenominatorSwapProgram
          (linkPrograms (preserveRightProgram balancedLengthProgram)
            bitSerialMulProgram))) 2 <|
    linkFuel
        (linkPrograms fourfoldDenominatorSwapProgram
          (linkPrograms (preserveRightProgram balancedLengthProgram)
            bitSerialMulProgram))
        (preserveRightFuel (fixedTargetDenominatorFuel accuracyExponent q)) <|
      linkFuel
          (linkPrograms (preserveRightProgram balancedLengthProgram)
            bitSerialMulProgram) 5 <|
        linkFuel bitSerialMulProgram
          (preserveRightFuel (balancedLengthFuel values))
          (bitSerialMulFuel (q ^ accuracyExponent + 1))

private theorem denominator_le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ}
    (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

/-- **The list denominator, executed.**  From the typed envelope alone the
fixed program returns `circuitCount * (q ^ accuracyExponent + 1)`. -/
theorem run_fourfoldListDenominatorProgram
    (accuracyExponent q tagCode maximumBits : ℕ) (values : List ℕ)
    (hbits :
      fourfoldListDenominatorBits accuracyExponent q values ≤ maximumBits) :
    runNPOracleProgram (fourfoldListDenominatorProgram accuracyExponent)
        maximumBits (fourfoldListDenominatorFuel accuracyExponent q values)
        (initialNPOracleState q
          (Nat.pair tagCode (Nat.pair q (encodeBalancedList values)))) =
      some (values.length * (q ^ accuracyExponent + 1)) := by
  let listCode := encodeBalancedList values
  let power := q ^ accuracyExponent
  let maximumStages := fourfoldListDenominatorBits accuracyExponent q values
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ fourfoldListDenominatorStageBits accuracyExponent q values) :
      value ≤ maximumBits := by
    refine le_trans ?_ hbits
    dsimp only [maximumStages, fourfoldListDenominatorBits]
    exact denominator_le_foldr_max_of_mem hvalue
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldListDenominatorStageBits]
  have hlength : natBitLength q ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldListDenominatorStageBits]
  have hpayloadBits :
      fourfoldEnvelopePayloadBits q listCode ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldListDenominatorStageBits, listCode]
  have hpowerBits :
      preserveRightBits (fixedTargetDenominatorBits accuracyExponent q) q
          listCode power ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldListDenominatorStageBits, listCode, power]
  have hswapBits :
      fourfoldDenominatorSwapBits power listCode ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldListDenominatorStageBits, listCode, power]
  have hcountBits :
      preserveRightBits (balancedLengthBits q values) listCode (power + 1)
          values.length ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldListDenominatorStageBits, listCode, power]
  have hmulBits :
      bitSerialMulBits q values.length (power + 1) ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldListDenominatorStageBits, power]
  have hpayload :
      runNPOracleProgram fourfoldEnvelopePayloadProgram maximumBits 2
          (initialNPOracleState q
            (Nat.pair tagCode (Nat.pair q listCode))) =
        some (Nat.pair q listCode) :=
    run_bits_mono
      (run_fourfoldEnvelopePayloadProgram q tagCode q listCode)
      hpayloadBits
  have hpower :
      runNPOracleProgram
          (preserveRightProgram
            (fixedTargetDenominatorProgram accuracyExponent))
          maximumBits
          (preserveRightFuel (fixedTargetDenominatorFuel accuracyExponent q))
          (initialNPOracleState q (Nat.pair q listCode)) =
        some (Nat.pair power listCode) :=
    run_bits_mono
      (run_preserveRightProgram
        (fixedTargetDenominatorProgram accuracyExponent) q
        (fixedTargetDenominatorBits accuracyExponent q)
        (fixedTargetDenominatorFuel accuracyExponent q) q listCode power
        (run_fixedTargetDenominatorProgram accuracyExponent q
          (fixedTargetDenominatorBits accuracyExponent q) (le_refl _)))
      hpowerBits
  have hswap :
      runNPOracleProgram fourfoldDenominatorSwapProgram maximumBits 5
          (initialNPOracleState q (Nat.pair power listCode)) =
        some (Nat.pair listCode (power + 1)) :=
    run_bits_mono
      (run_fourfoldDenominatorSwapProgram q power listCode)
      hswapBits
  have hcount :
      runNPOracleProgram (preserveRightProgram balancedLengthProgram)
          maximumBits (preserveRightFuel (balancedLengthFuel values))
          (initialNPOracleState q (Nat.pair listCode (power + 1))) =
        some (Nat.pair values.length (power + 1)) :=
    run_bits_mono
      (run_preserveRightProgram balancedLengthProgram q
        (balancedLengthBits q values) (balancedLengthFuel values) listCode
        (power + 1) values.length (run_balancedLengthProgram q values))
      hcountBits
  have hmul :
      runNPOracleProgram bitSerialMulProgram maximumBits
          (bitSerialMulFuel (power + 1))
          (initialNPOracleState q (Nat.pair values.length (power + 1))) =
        some (values.length * (power + 1)) :=
    run_bits_mono
      (run_bitSerialMulProgram q values.length (power + 1))
      hmulBits
  exact run_linkPrograms hpositive hlength hpayload
    (run_linkPrograms hpositive hlength hpower
      (run_linkPrograms hpositive hlength hswap
        (run_linkPrograms hpositive hlength hcount hmul)))

/-! ## §3 The published symmetric specialization -/

def symmetricListDenominatorBits
    (accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  fourfoldListDenominatorBits accuracyExponent request.q
    (request.circuits.map encodeNormalizedSymmetricThresholdCircuit)

def symmetricListDenominatorFuel
    (accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  fourfoldListDenominatorFuel accuracyExponent request.q
    (request.circuits.map encodeNormalizedSymmetricThresholdCircuit)

/-- **The symmetric list denominator, executed from the typed envelope.**
This is exactly the denominator at which every published symmetric row seed is
indexed. -/
theorem run_symmetricListDenominatorProgram
    (accuracyExponent maximumBits : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (hbits : symmetricListDenominatorBits accuracyExponent request ≤ maximumBits) :
    runNPOracleProgram (fourfoldListDenominatorProgram accuracyExponent)
        maximumBits (symmetricListDenominatorFuel accuracyExponent request)
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)) =
      some
        (symmetricListDenominator request
          (fixedTargetDenominator accuracyExponent request.q)) := by
  have hrun :=
    run_fourfoldListDenominatorProgram accuracyExponent request.q
      (encodeNat symmetricCircuitFamilyTag) maximumBits
      (request.circuits.map encodeNormalizedSymmetricThresholdCircuit) hbits
  rw [show
      symmetricListDenominator request
          (fixedTargetDenominator accuracyExponent request.q) =
        (request.circuits.map
          encodeNormalizedSymmetricThresholdCircuit).length *
          (request.q ^ accuracyExponent + 1) by
      rw [List.length_map]
      rfl]
  exact hrun

end NearCubicWires.CanonicalFourfoldListDenominatorProgram
