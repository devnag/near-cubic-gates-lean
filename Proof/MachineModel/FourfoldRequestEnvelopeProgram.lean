import Proof.Foundations.CanonicalBinaryProgram
import Proof.Foundations.SupplierPipeline

/-!
# Executable Fourfold request envelope

The supplier VM receives a canonical `FourfoldRequest.code` in register zero
and the request arity in register one.  This fixed oracle-free stage strips the
three structural list cells and emits a compact handoff containing the encoded
family tag, numeric arity, and raw circuit-list code.  Circuit decoding and row
construction remain later linked stages; this module proves only the exact raw
ABI boundary and does not introduce a semantic parser callback.
-/

namespace NearCubicWires.FourfoldRequestEnvelopeProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline

/-- Handoff ABI: `pair encodedFamilyTag (pair arity circuitListCode)`. -/
def fourfoldRequestEnvelopeOutput
    {Circuit : CircuitFamily}
    (familyTag : ℕ)
    (encodeCircuit : {q : ℕ} → Circuit q → ℕ)
    (request : FourfoldRequest Circuit) : ℕ :=
  Nat.pair (encodeNat familyTag)
    (Nat.pair request.q
      (encodeBalancedList (request.circuits.map encodeCircuit)))

/-- The program deliberately relies only on canonical typed requests, exactly
the input domain quantified by `ExecutableFourfoldEstimator.computes`.
Registers `r2`–`r5` are structural scratch and `r6` holds the inner handoff. -/
def fourfoldRequestEnvelopeProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 3 2
  , .unpairRight 2 2 3
  , .unpairRight 2 2 4
  , .unpairRight 2 2 5
  , .unpairRight 2 2 6
  , .unpairLeft 2 5 7
  , .pair 1 5 6 8
  , .pair 3 6 0 9
  , .halt 0
  ]

@[simp] theorem fourfoldRequestEnvelopeProgram_oracleFree :
    OracleFree fourfoldRequestEnvelopeProgram := by
  rfl

def fourfoldRequestEnvelopeRegisterBound
    {Circuit : CircuitFamily}
    (familyTag : ℕ)
    (encodeCircuit : {q : ℕ} → Circuit q → ℕ)
    (request : FourfoldRequest Circuit) : ℕ :=
  max (FourfoldRequest.code familyTag encodeCircuit request)
    (fourfoldRequestEnvelopeOutput familyTag encodeCircuit request) + 1

def fourfoldRequestEnvelopeBits
    {Circuit : CircuitFamily}
    (familyTag : ℕ)
    (encodeCircuit : {q : ℕ} → Circuit q → ℕ)
    (request : FourfoldRequest Circuit) : ℕ :=
  natBitLength
    (fourfoldRequestEnvelopeRegisterBound familyTag encodeCircuit request)

private theorem boundedValueBits
    {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound)
    (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

theorem run_fourfoldRequestEnvelopeProgram
    {Circuit : CircuitFamily}
    (familyTag : ℕ)
    (encodeCircuit : {q : ℕ} → Circuit q → ℕ)
    (request : FourfoldRequest Circuit)
    (maximumBits : ℕ)
    (hbits :
      fourfoldRequestEnvelopeBits familyTag encodeCircuit request ≤
        maximumBits) :
    runNPOracleProgram fourfoldRequestEnvelopeProgram maximumBits 10
        (initialNPOracleState request.q
          (FourfoldRequest.code familyTag encodeCircuit request)) =
      some
        (fourfoldRequestEnvelopeOutput familyTag encodeCircuit request) := by
  let circuitsCode :=
    encodeBalancedList (request.circuits.map encodeCircuit)
  let tagCode := encodeNat familyTag
  let raw :=
    FourfoldRequest.code familyTag encodeCircuit request
  let innerOutput := Nat.pair request.q circuitsCode
  let output := Nat.pair tagCode innerOutput
  let bound :=
    fourfoldRequestEnvelopeRegisterBound familyTag encodeCircuit request
  have hbound : natBitLength bound ≤ maximumBits := hbits
  have hrawLe : raw ≤ bound := by
    dsimp [bound, fourfoldRequestEnvelopeRegisterBound]
    exact (le_max_left _ _).trans (Nat.le_add_right _ _)
  have houtputLe : output ≤ bound := by
    dsimp [bound, output, fourfoldRequestEnvelopeOutput]
    exact (le_max_right _ _).trans (Nat.le_add_right _ _)
  have hraw : natBitLength raw ≤ maximumBits :=
    boundedValueBits hrawLe hbound
  have houtput : natBitLength output ≤ maximumBits :=
    boundedValueBits houtputLe hbound
  have hinnerOutputLe : innerOutput ≤ output := by
    dsimp [output]
    exact Nat.right_le_pair _ _
  have hinnerOutput : natBitLength innerOutput ≤ maximumBits :=
    boundedValueBits (hinnerOutputLe.trans houtputLe) hbound
  have hq : natBitLength request.q ≤ maximumBits := by
    apply boundedValueBits
      ((Nat.left_le_pair request.q circuitsCode).trans
        (hinnerOutputLe.trans houtputLe)) hbound
  have hcircuits : natBitLength circuitsCode ≤ maximumBits := by
    apply boundedValueBits
      ((Nat.right_le_pair request.q circuitsCode).trans
        (hinnerOutputLe.trans houtputLe)) hbound
  have htag : natBitLength tagCode ≤ maximumBits := by
    apply boundedValueBits
      ((Nat.left_le_pair tagCode innerOutput).trans houtputLe) hbound
  let tail₁ :=
    encodeTaggedList [encodeNat request.q, circuitsCode]
  let payload₀ := Nat.pair tagCode tail₁
  let payload₁ := Nat.pair (encodeNat request.q)
    (encodeTaggedList [circuitsCode])
  let tail₂ := encodeTaggedList [circuitsCode]
  let payload₂ := Nat.pair circuitsCode 0
  have componentBits :
      ∀ value, value ≤ raw → natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact boundedValueBits (hvalue.trans hrawLe) hbound
  have hpayload₀Le : payload₀ ≤ raw := by
    simpa [raw, payload₀, tail₁, FourfoldRequest.code,
      encodeTaggedList] using
      (Nat.right_le_pair 1 payload₀)
  have htail₁Le : tail₁ ≤ payload₀ :=
    Nat.right_le_pair tagCode tail₁
  have hpayload₁Le : payload₁ ≤ tail₁ := by
    simpa [tail₁, payload₁, tail₂, encodeTaggedList] using
      (Nat.right_le_pair 1 payload₁)
  have htail₂Le : tail₂ ≤ payload₁ :=
    Nat.right_le_pair (encodeNat request.q) tail₂
  have hpayload₂Le : payload₂ ≤ tail₂ := by
    simpa [tail₂, payload₂, encodeTaggedList] using
      (Nat.right_le_pair 1 payload₂)
  have hpayload₀ : natBitLength payload₀ ≤ maximumBits := by
    exact componentBits payload₀ hpayload₀Le
  have htail₁ : natBitLength tail₁ ≤ maximumBits := by
    exact componentBits tail₁ (htail₁Le.trans hpayload₀Le)
  have hpayload₁ : natBitLength payload₁ ≤ maximumBits := by
    exact componentBits payload₁
      (hpayload₁Le.trans (htail₁Le.trans hpayload₀Le))
  have htail₂ : natBitLength tail₂ ≤ maximumBits := by
    exact componentBits tail₂
      (htail₂Le.trans
        (hpayload₁Le.trans (htail₁Le.trans hpayload₀Le)))
  have hpayload₂ : natBitLength payload₂ ≤ maximumBits := by
    exact componentBits payload₂
      (hpayload₂Le.trans
        (htail₂Le.trans
          (hpayload₁Le.trans (htail₁Le.trans hpayload₀Le))))
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by
      simp [initialNPOracleState, payload₀, tail₁,
        FourfoldRequest.code, encodeTaggedList, tagCode,
        circuitsCode]) hpayload₀]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₀]) htag]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₀]) htail₁]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, tail₁, payload₁,
        encodeTaggedList]) hpayload₁]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, payload₁, tail₂])
    htail₂]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, tail₂, payload₂,
        encodeTaggedList])
    hpayload₂]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₂]) hcircuits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, initialNPOracleState,
        innerOutput, circuitsCode]) hinnerOutput]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output, tagCode,
        innerOutput]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        fourfoldRequestEnvelopeOutput, tagCode, innerOutput,
        circuitsCode]) houtput

end NearCubicWires.FourfoldRequestEnvelopeProgram
