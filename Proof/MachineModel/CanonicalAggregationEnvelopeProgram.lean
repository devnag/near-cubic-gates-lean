import Proof.MachineModel.FourfoldRequestEnvelopeProgram

/-!
# Canonical aggregation-envelope lowering

The public envelope stores its published family tag as a canonical natural.
This fixed adapter lowers the two typed public variants to the internal
right-associated context

`pair(mode, pair(q, balancedCircuitTree))`.

At this boundary the input has already been typed by `PublishedContracts`.
Consequently zero selects the symmetric family and nonzero selects threshold;
the public theorems below prove the exact canonical encodings of tags zero and
one take those paths.  Keeping validation at the typed boundary avoids a second
wire decoder and a shadow notion of envelope validity.
-/

namespace NearCubicWires.CanonicalAggregationEnvelopeProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline

def aggregationEnvelopeContext
    (familyTag q circuitTreeCode : ℕ) : ℕ :=
  Nat.pair familyTag (Nat.pair q circuitTreeCode)

/-- Register ABI:

* `r0`: public envelope, then lowered context;
* `r2`: canonical family code, then internal mode;
* `r3`: arity/tree payload;
* `r4`, `r5`: arity and balanced circuit tree;
* `r6`: right-associated context tail.
-/
def aggregationEnvelopeLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .branchZero 2 3 4
  , .set 2 0 5
  , .set 2 1 5
  , .unpairLeft 3 4 6
  , .unpairRight 3 5 7
  , .pair 4 5 6 8
  , .pair 2 6 0 9
  , .halt 0
  ]

@[simp] theorem aggregationEnvelopeLoweringProgram_oracleFree :
    OracleFree aggregationEnvelopeLoweringProgram := by
  rfl

/-- Exact width charge for the fixed adapter, parameterized by the external
family code and the internal mode it selects. -/
private def aggregationEnvelopeLoweringBitsFromCode
    (familyCode familyTag q circuitTreeCode : ℕ) : ℕ :=
  natBitLength <|
    max
      (Nat.pair familyCode (Nat.pair q circuitTreeCode))
      (aggregationEnvelopeContext familyTag q circuitTreeCode) + 1

def aggregationEnvelopeLoweringBits
    (familyTag q circuitTreeCode : ℕ) : ℕ :=
  aggregationEnvelopeLoweringBitsFromCode
    (encodeNat familyTag) familyTag q circuitTreeCode

private theorem loweringValueBits
    {familyCode familyTag q circuitTreeCode value : ℕ}
    (hvalue :
      value ≤
        max
          (Nat.pair familyCode (Nat.pair q circuitTreeCode))
          (aggregationEnvelopeContext familyTag q circuitTreeCode) + 1) :
    natBitLength value ≤
      aggregationEnvelopeLoweringBitsFromCode
        familyCode familyTag q circuitTreeCode := by
  exact natBitLength_mono hvalue

private theorem run_aggregationEnvelopeLoweringProgram_zero
    (q circuitTreeCode : ℕ) :
    runNPOracleProgram aggregationEnvelopeLoweringProgram
        (aggregationEnvelopeLoweringBitsFromCode 0 0 q circuitTreeCode)
        9
        (initialNPOracleState q
          (Nat.pair 0 (Nat.pair q circuitTreeCode))) =
      some (aggregationEnvelopeContext 0 q circuitTreeCode) := by
  have hraw :
      natBitLength (Nat.pair 0 (Nat.pair q circuitTreeCode)) ≤
        aggregationEnvelopeLoweringBitsFromCode 0 0 q circuitTreeCode := by
    apply loweringValueBits
    omega
  have hfamilyCode :
      natBitLength 0 ≤
        aggregationEnvelopeLoweringBitsFromCode 0 0 q circuitTreeCode := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair 0 (Nat.pair q circuitTreeCode))).trans hraw
  have hpayload :
      natBitLength (Nat.pair q circuitTreeCode) ≤
        aggregationEnvelopeLoweringBitsFromCode 0 0 q circuitTreeCode := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair 0 (Nat.pair q circuitTreeCode))).trans hraw
  have hq :
      natBitLength q ≤
        aggregationEnvelopeLoweringBitsFromCode 0 0 q circuitTreeCode :=
    (natBitLength_mono (Nat.left_le_pair q circuitTreeCode)).trans
      hpayload
  have htree :
      natBitLength circuitTreeCode ≤
        aggregationEnvelopeLoweringBitsFromCode 0 0 q circuitTreeCode :=
    (natBitLength_mono (Nat.right_le_pair q circuitTreeCode)).trans
      hpayload
  have houtput :
      natBitLength (aggregationEnvelopeContext 0 q circuitTreeCode) ≤
        aggregationEnvelopeLoweringBitsFromCode 0 0 q circuitTreeCode := by
    apply loweringValueBits
    omega
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [initialNPOracleState]) hfamilyCode]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]) hpayload]
  rw [show 7 = 6 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  rw [show 6 = 5 + 1 by omega]
  rw [run_set_instruction (by rfl) rfl hfamilyCode]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hq]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htree]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpayload]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      aggregationEnvelopeContext]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      aggregationEnvelopeContext]) houtput

private theorem run_aggregationEnvelopeLoweringProgram_nonzero
    (familyCode q circuitTreeCode : ℕ)
    (hfamilyCodeNonzero : familyCode ≠ 0) :
    runNPOracleProgram aggregationEnvelopeLoweringProgram
        (aggregationEnvelopeLoweringBitsFromCode
          familyCode 1 q circuitTreeCode)
        9
        (initialNPOracleState q
          (Nat.pair familyCode (Nat.pair q circuitTreeCode))) =
      some (aggregationEnvelopeContext 1 q circuitTreeCode) := by
  have hraw :
      natBitLength
          (Nat.pair familyCode (Nat.pair q circuitTreeCode)) ≤
        aggregationEnvelopeLoweringBitsFromCode
          familyCode 1 q circuitTreeCode := by
    apply loweringValueBits
    omega
  have hfamilyCode :
      natBitLength familyCode ≤
        aggregationEnvelopeLoweringBitsFromCode
          familyCode 1 q circuitTreeCode := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair familyCode
          (Nat.pair q circuitTreeCode))).trans hraw
  have hpayload :
      natBitLength (Nat.pair q circuitTreeCode) ≤
        aggregationEnvelopeLoweringBitsFromCode
          familyCode 1 q circuitTreeCode := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair familyCode
          (Nat.pair q circuitTreeCode))).trans hraw
  have hone :
      natBitLength 1 ≤
        aggregationEnvelopeLoweringBitsFromCode
          familyCode 1 q circuitTreeCode := by
    apply loweringValueBits
    have hleft :
        1 ≤ aggregationEnvelopeContext 1 q circuitTreeCode :=
      Nat.left_le_pair 1 (Nat.pair q circuitTreeCode)
    omega
  have hq :
      natBitLength q ≤
        aggregationEnvelopeLoweringBitsFromCode
          familyCode 1 q circuitTreeCode :=
    (natBitLength_mono (Nat.left_le_pair q circuitTreeCode)).trans
      hpayload
  have htree :
      natBitLength circuitTreeCode ≤
        aggregationEnvelopeLoweringBitsFromCode
          familyCode 1 q circuitTreeCode :=
    (natBitLength_mono (Nat.right_le_pair q circuitTreeCode)).trans
      hpayload
  have houtput :
      natBitLength (aggregationEnvelopeContext 1 q circuitTreeCode) ≤
        aggregationEnvelopeLoweringBitsFromCode
          familyCode 1 q circuitTreeCode := by
    apply loweringValueBits
    omega
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [initialNPOracleState]) hfamilyCode]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]) hpayload]
  rw [show 7 = 6 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  rw [show 6 = 5 + 1 by omega]
  rw [run_set_instruction (pc := 4) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump,
      hfamilyCodeNonzero]) hone]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hq]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htree]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpayload]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      aggregationEnvelopeContext]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      aggregationEnvelopeContext]) houtput

theorem run_aggregationEnvelopeLoweringProgram_symmetric
    (q circuitTreeCode : ℕ) :
    runNPOracleProgram aggregationEnvelopeLoweringProgram
        (aggregationEnvelopeLoweringBits
          symmetricCircuitFamilyTag q circuitTreeCode)
        9
        (initialNPOracleState q
          (Nat.pair (encodeNat symmetricCircuitFamilyTag)
            (Nat.pair q circuitTreeCode))) =
      some
        (aggregationEnvelopeContext
          symmetricCircuitFamilyTag q circuitTreeCode) := by
  simpa [aggregationEnvelopeLoweringBits,
    symmetricCircuitFamilyTag, encodeNat, encodeBits, encodeBoolList,
    encodeBalancedList] using
    run_aggregationEnvelopeLoweringProgram_zero q circuitTreeCode

theorem run_aggregationEnvelopeLoweringProgram_threshold
    (q circuitTreeCode : ℕ) :
    runNPOracleProgram aggregationEnvelopeLoweringProgram
        (aggregationEnvelopeLoweringBits
          thresholdCircuitFamilyTag q circuitTreeCode)
        9
        (initialNPOracleState q
          (Nat.pair (encodeNat thresholdCircuitFamilyTag)
            (Nat.pair q circuitTreeCode))) =
      some
        (aggregationEnvelopeContext
          thresholdCircuitFamilyTag q circuitTreeCode) := by
  have hencodedThreshold :
      encodeNat thresholdCircuitFamilyTag ≠ 0 := by
    have hpair : Nat.pair 1 1 ≠ 0 := by
      have hleft := Nat.left_le_pair 1 1
      omega
    simpa [thresholdCircuitFamilyTag, encodeNat, encodeBits,
      encodeBoolList, encodeBalancedList, boolCode] using hpair
  simpa [aggregationEnvelopeLoweringBits, thresholdCircuitFamilyTag] using
    run_aggregationEnvelopeLoweringProgram_nonzero
      (encodeNat thresholdCircuitFamilyTag) q circuitTreeCode
      hencodedThreshold

end NearCubicWires.CanonicalAggregationEnvelopeProgram
