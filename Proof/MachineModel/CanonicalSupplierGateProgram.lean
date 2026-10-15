import Proof.Foundations.CanonicalBinaryProgram
import Proof.MachineModel.CanonicalIntPredecessorProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.SupplierPipeline
import Proof.Foundations.VerifiedLinker

/-!
# Canonical supplier gate-field lowering

Supported normalized gates have one public canonical representation:
`[weights, threshold, support]`.  This fixed parser exposes those three wire
codes without decoding a semantic gate or accepting a host-built request.

The threshold is placed on the left of the output.  The next linked stage can
therefore transform it with `preserveRightProgram` while retaining the
weights/support context exactly once.
-/

namespace NearCubicWires.CanonicalSupplierGateProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalIntPredecessorProgram
open NearCubicWires.CompilerSemantics
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

def supplierGateFieldInput
    (weightsCode thresholdCode supportCode : ℕ) : ℕ :=
  encodeTaggedList [weightsCode, thresholdCode, supportCode]

def supplierGateFieldContext
    (weightsCode supportCode : ℕ) : ℕ :=
  Nat.pair weightsCode supportCode

def supplierGateFieldOutput
    (weightsCode thresholdCode supportCode : ℕ) : ℕ :=
  Nat.pair thresholdCode
    (supplierGateFieldContext weightsCode supportCode)

/-- Register ABI:

* `r0`: raw gate code, then `pair(threshold, pair(weights, support))`;
* `r2`–`r9`: the unique right-associated tagged-list parsing path;
* `r10`: weights/support context.
-/
def supplierGateFieldProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 3 2
  , .unpairRight 2 4 3
  , .unpairRight 4 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairRight 7 8 7
  , .unpairLeft 8 9 8
  , .pair 3 9 10 9
  , .pair 6 10 0 10
  , .halt 0
  ]

@[simp] theorem supplierGateFieldProgram_oracleFree :
    OracleFree supplierGateFieldProgram := by
  rfl

def supplierGateFieldFuel : ℕ := 11

private def supplierGateFieldWorkingValues
    (weightsCode thresholdCode supportCode : ℕ) : List ℕ :=
  let rest₂ := encodeTaggedList [supportCode]
  let payload₂ := Nat.pair supportCode 0
  let rest₁ := encodeTaggedList [thresholdCode, supportCode]
  let payload₁ := Nat.pair thresholdCode rest₂
  let raw := supplierGateFieldInput weightsCode thresholdCode supportCode
  let payload₀ := Nat.pair weightsCode rest₁
  let context := supplierGateFieldContext weightsCode supportCode
  let output :=
    supplierGateFieldOutput weightsCode thresholdCode supportCode
  [ 0, 1, weightsCode, thresholdCode, supportCode, rest₂, payload₂,
    rest₁, payload₁, raw, payload₀, context, output ]

private def supplierGateFieldWorkBound
    (weightsCode thresholdCode supportCode : ℕ) : ℕ :=
  (supplierGateFieldWorkingValues weightsCode thresholdCode supportCode).foldr
    max 1

def supplierGateFieldBits
    (weightsCode thresholdCode supportCode : ℕ) : ℕ :=
  natBitLength <|
    supplierGateFieldWorkBound weightsCode thresholdCode supportCode

private theorem gate_le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 1 := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (ih hmem).trans (Nat.le_max_right _ _)

private theorem supplierGateField_value_bits
    (weightsCode thresholdCode supportCode value : ℕ)
    (hmem :
      value ∈
        supplierGateFieldWorkingValues weightsCode thresholdCode
          supportCode) :
    natBitLength value ≤
      supplierGateFieldBits weightsCode thresholdCode supportCode := by
  unfold supplierGateFieldBits supplierGateFieldWorkBound
  exact natBitLength_mono (gate_le_foldr_max_of_mem hmem)

/-- Exact execution on arbitrary field codes.  Canonical typed callers are
specialized below; malformed codes have deterministic but unspecified output.
-/
theorem run_supplierGateFieldProgram
    (inputLength weightsCode thresholdCode supportCode : ℕ) :
    runNPOracleProgram supplierGateFieldProgram
        (supplierGateFieldBits weightsCode thresholdCode supportCode)
        supplierGateFieldFuel
        (initialNPOracleState inputLength
          (supplierGateFieldInput weightsCode thresholdCode supportCode)) =
      some
        (supplierGateFieldOutput weightsCode thresholdCode supportCode) := by
  let rest₂ := encodeTaggedList [supportCode]
  let payload₂ := Nat.pair supportCode 0
  let rest₁ := encodeTaggedList [thresholdCode, supportCode]
  let payload₁ := Nat.pair thresholdCode rest₂
  let raw := supplierGateFieldInput weightsCode thresholdCode supportCode
  let payload₀ := Nat.pair weightsCode rest₁
  let context := supplierGateFieldContext weightsCode supportCode
  let output :=
    supplierGateFieldOutput weightsCode thresholdCode supportCode
  let maximumBits :=
    supplierGateFieldBits weightsCode thresholdCode supportCode
  have hbits :
      ∀ value,
        value ∈
            supplierGateFieldWorkingValues weightsCode thresholdCode
              supportCode →
          natBitLength value ≤ maximumBits :=
    supplierGateField_value_bits weightsCode thresholdCode supportCode
  have hpayload₀ := hbits payload₀ (by
    simp [supplierGateFieldWorkingValues, payload₀, rest₁])
  have hweights := hbits weightsCode (by
    simp [supplierGateFieldWorkingValues])
  have hrest₁ := hbits rest₁ (by
    simp [supplierGateFieldWorkingValues, rest₁])
  have hpayload₁ := hbits payload₁ (by
    simp [supplierGateFieldWorkingValues, payload₁, rest₂])
  have hthreshold := hbits thresholdCode (by
    simp [supplierGateFieldWorkingValues])
  have hrest₂ := hbits rest₂ (by
    simp [supplierGateFieldWorkingValues, rest₂])
  have hpayload₂ := hbits payload₂ (by
    simp [supplierGateFieldWorkingValues, payload₂])
  have hsupport := hbits supportCode (by
    simp [supplierGateFieldWorkingValues])
  have hcontext := hbits context (by
    simp [supplierGateFieldWorkingValues, context])
  have houtput := hbits output (by
    simp [supplierGateFieldWorkingValues, output])
  rw [show supplierGateFieldFuel = 10 + 1 by rfl]
  rw [run_unpairRight_instruction (value := payload₀)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, supplierGateFieldInput, payload₀,
        rest₁, encodeTaggedList])
    hpayload₀]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := weightsCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₀])
    hweights]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := rest₁)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₀])
    hrest₁]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := payload₁)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rest₁, payload₁,
        rest₂, encodeTaggedList])
    hpayload₁]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := thresholdCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₁])
    hthreshold]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := rest₂)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₁])
    hrest₂]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := payload₂)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rest₂, payload₂,
        encodeTaggedList])
    hpayload₂]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := supportCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₂])
    hsupport]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := context)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, context,
        supplierGateFieldContext])
    hcontext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (fuel := 1) (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        supplierGateFieldOutput, context])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

/-! ## Exact-decomposition request packing -/

def supplierGateRequestPackerInput
    (weightsCode strictThresholdCode supportCode : ℕ) : ℕ :=
  Nat.pair strictThresholdCode
    (supplierGateFieldContext weightsCode supportCode)

def supplierGateExactRequestCode
    (weightsCode strictThresholdCode : ℕ) : ℕ :=
  encodeTaggedList [weightsCode, strictThresholdCode]

def supplierGateRequestPackerOutput
    (weightsCode strictThresholdCode supportCode : ℕ) : ℕ :=
  Nat.pair
    (supplierGateExactRequestCode weightsCode strictThresholdCode)
    supportCode

/-- Rebuild the imported exact-decomposition request from independently
addressable canonical fields, retaining support beside (not inside) it. -/
def supplierGateRequestPackerProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .set 6 1 5
  , .pair 2 7 8 6
  , .pair 6 8 9 7
  , .pair 4 9 10 8
  , .pair 6 10 11 9
  , .pair 11 5 0 10
  , .halt 0
  ]

@[simp] theorem supplierGateRequestPackerProgram_oracleFree :
    OracleFree supplierGateRequestPackerProgram := by
  rfl

def supplierGateRequestPackerFuel : ℕ := 11

private def supplierGateRequestPackerWorkingValues
    (weightsCode strictThresholdCode supportCode : ℕ) : List ℕ :=
  let context := supplierGateFieldContext weightsCode supportCode
  let input :=
    supplierGateRequestPackerInput weightsCode strictThresholdCode
      supportCode
  let thresholdPayload := Nat.pair strictThresholdCode 0
  let thresholdTail := Nat.pair 1 thresholdPayload
  let requestPayload := Nat.pair weightsCode thresholdTail
  let requestCode :=
    supplierGateExactRequestCode weightsCode strictThresholdCode
  let output :=
    supplierGateRequestPackerOutput weightsCode strictThresholdCode
      supportCode
  [ 0, 1, weightsCode, strictThresholdCode, supportCode, context, input,
    thresholdPayload, thresholdTail, requestPayload, requestCode, output ]

private def supplierGateRequestPackerWorkBound
    (weightsCode strictThresholdCode supportCode : ℕ) : ℕ :=
  (supplierGateRequestPackerWorkingValues weightsCode strictThresholdCode
    supportCode).foldr max 1

def supplierGateRequestPackerBits
    (weightsCode strictThresholdCode supportCode : ℕ) : ℕ :=
  natBitLength <|
    supplierGateRequestPackerWorkBound weightsCode strictThresholdCode
      supportCode

private theorem supplierGateRequestPacker_value_bits
    (weightsCode strictThresholdCode supportCode value : ℕ)
    (hmem :
      value ∈
        supplierGateRequestPackerWorkingValues weightsCode
          strictThresholdCode supportCode) :
    natBitLength value ≤
      supplierGateRequestPackerBits weightsCode strictThresholdCode
        supportCode := by
  unfold supplierGateRequestPackerBits
    supplierGateRequestPackerWorkBound
  exact natBitLength_mono (gate_le_foldr_max_of_mem hmem)

theorem run_supplierGateRequestPackerProgram
    (inputLength weightsCode strictThresholdCode supportCode : ℕ) :
    runNPOracleProgram supplierGateRequestPackerProgram
        (supplierGateRequestPackerBits weightsCode strictThresholdCode
          supportCode)
        supplierGateRequestPackerFuel
        (initialNPOracleState inputLength
          (supplierGateRequestPackerInput weightsCode
            strictThresholdCode supportCode)) =
      some
        (supplierGateRequestPackerOutput weightsCode
          strictThresholdCode supportCode) := by
  let context := supplierGateFieldContext weightsCode supportCode
  let input :=
    supplierGateRequestPackerInput weightsCode strictThresholdCode
      supportCode
  let thresholdPayload := Nat.pair strictThresholdCode 0
  let thresholdTail := Nat.pair 1 thresholdPayload
  let requestPayload := Nat.pair weightsCode thresholdTail
  let requestCode :=
    supplierGateExactRequestCode weightsCode strictThresholdCode
  let output :=
    supplierGateRequestPackerOutput weightsCode strictThresholdCode
      supportCode
  let maximumBits :=
    supplierGateRequestPackerBits weightsCode strictThresholdCode
      supportCode
  have hbits :
      ∀ value,
        value ∈
            supplierGateRequestPackerWorkingValues weightsCode
              strictThresholdCode supportCode →
          natBitLength value ≤ maximumBits :=
    supplierGateRequestPacker_value_bits weightsCode strictThresholdCode
      supportCode
  have hthreshold := hbits strictThresholdCode (by
    simp [supplierGateRequestPackerWorkingValues])
  have hcontext := hbits context (by
    simp [supplierGateRequestPackerWorkingValues, context])
  have hweights := hbits weightsCode (by
    simp [supplierGateRequestPackerWorkingValues])
  have hsupport := hbits supportCode (by
    simp [supplierGateRequestPackerWorkingValues])
  have hone := hbits 1 (by
    simp [supplierGateRequestPackerWorkingValues])
  have hthresholdPayload := hbits thresholdPayload (by
    simp [supplierGateRequestPackerWorkingValues, thresholdPayload])
  have hthresholdTail := hbits thresholdTail (by
    simp [supplierGateRequestPackerWorkingValues, thresholdTail,
      thresholdPayload])
  have hrequestPayload := hbits requestPayload (by
    simp [supplierGateRequestPackerWorkingValues, requestPayload,
      thresholdTail, thresholdPayload])
  have hrequestCode := hbits requestCode (by
    simp [supplierGateRequestPackerWorkingValues, requestCode])
  have houtput := hbits output (by
    simp [supplierGateRequestPackerWorkingValues, output])
  rw [show supplierGateRequestPackerFuel = 10 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := strictThresholdCode)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, supplierGateRequestPackerInput,
        supplierGateFieldContext])
    hthreshold]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, supplierGateRequestPackerInput, context])
    hcontext]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := weightsCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, context,
        supplierGateFieldContext])
    hweights]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := supportCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, context,
        supplierGateFieldContext])
    hsupport]
  rw [show 7 = 6 + 1 by omega]
  rw [run_set_instruction (value := 1)
    (by rfl) rfl hone]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := thresholdPayload)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, thresholdPayload])
    hthresholdPayload]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := thresholdTail)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, thresholdTail])
    hthresholdTail]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := requestPayload)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, requestPayload])
    hrequestPayload]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := requestCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, requestCode,
        supplierGateExactRequestCode, encodeTaggedList,
        requestPayload, thresholdTail, thresholdPayload])
    hrequestCode]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        supplierGateRequestPackerOutput, requestCode])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

def supplierGateWeightsCode {n : ℕ}
    (gate : SupportedNormalizedGate n) : ℕ :=
  encodeIntList (List.ofFn gate.gate.weight)

def supplierGateThresholdCode {n : ℕ}
    (gate : SupportedNormalizedGate n) : ℕ :=
  encodeInt gate.gate.threshold

def supplierGateSupportCode {n : ℕ}
    (gate : SupportedNormalizedGate n) : ℕ :=
  encodeBoolList
    (List.ofFn fun index => decide (index ∈ gate.support))

@[simp] theorem supplierGateFieldInput_supported
    {n : ℕ} (gate : SupportedNormalizedGate n) :
    supplierGateFieldInput (supplierGateWeightsCode gate)
        (supplierGateThresholdCode gate) (supplierGateSupportCode gate) =
      encodeSupportedNormalizedGate gate := by
  rfl

theorem run_supplierGateFieldProgram_supported
    (inputLength : ℕ) {n : ℕ}
    (gate : SupportedNormalizedGate n) :
    runNPOracleProgram supplierGateFieldProgram
        (supplierGateFieldBits (supplierGateWeightsCode gate)
          (supplierGateThresholdCode gate) (supplierGateSupportCode gate))
        supplierGateFieldFuel
        (initialNPOracleState inputLength
          (encodeSupportedNormalizedGate gate)) =
      some
        (supplierGateFieldOutput (supplierGateWeightsCode gate)
          (supplierGateThresholdCode gate)
          (supplierGateSupportCode gate)) := by
  simpa only [supplierGateFieldInput_supported] using
    run_supplierGateFieldProgram inputLength
      (supplierGateWeightsCode gate)
      (supplierGateThresholdCode gate)
      (supplierGateSupportCode gate)

/-! ## Shared compressed-gate primitives -/

def supplierGateStrictThresholdCode {n : ℕ}
    (gate : SupportedNormalizedGate n) : ℕ :=
  encodeInt (gate.gate.threshold - 1)

/-- The compressed production path preserves its validated payload while
normalizing the threshold before packing the exact decomposition request. -/
def supplierGateThresholdPredecessorProgram : NPOracleProgram :=
  preserveRightProgram canonicalIntPredecessorProgram

def supplierGateThresholdPredecessorFuel {n : ℕ}
    (gate : SupportedNormalizedGate n) : ℕ :=
  preserveRightFuel <|
    canonicalIntPredecessorFuel gate.gate.threshold

end NearCubicWires.CanonicalSupplierGateProgram
