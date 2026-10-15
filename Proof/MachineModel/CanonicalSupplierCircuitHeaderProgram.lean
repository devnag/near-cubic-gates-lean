import Proof.MachineModel.CanonicalNatDecodeProgram
import Proof.MachineModel.PreserveRightProgram

namespace NearCubicWires.CanonicalSupplierCircuitHeaderProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-- Typed inputs use canonical tags zero and one.  Keeping the dispatch total
makes malformed raw calls deterministic without defining another validity
language. -/
def supplierCircuitMode (familyCode : ℕ) : ℕ :=
  if familyCode = 0 then 0 else 1

def supplierCircuitHeaderContext
    (mode bottomTree topCode : ℕ) : ℕ :=
  Nat.pair mode (Nat.pair bottomTree topCode)

def supplierCircuitHeaderParserInput
    (familyCode countCode bottomTree topCode : ℕ) : ℕ :=
  encodeTaggedList [familyCode, countCode, bottomTree, topCode]

def supplierCircuitHeaderParserOutput
    (familyCode countCode bottomTree topCode : ℕ) : ℕ :=
  Nat.pair countCode <|
    supplierCircuitHeaderContext
      (supplierCircuitMode familyCode) bottomTree topCode

/-- Register ABI:

* `r0`: raw circuit code, then `pair(encodedCount, headerContext)`;
* `r2`–`r13`: the unique right-associated parsing path;
* `r5`: native mode selected from the embedded family tag;
* `r14`: bottom/top and output-packing scratch.
-/
def supplierCircuitHeaderParserProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 3 2
  , .unpairRight 2 4 3
  , .branchZero 3 4 5
  , .set 5 0 6
  , .set 5 1 6
  , .unpairRight 4 6 7
  , .unpairLeft 6 7 8
  , .unpairRight 6 8 9
  , .unpairRight 8 9 10
  , .unpairLeft 9 10 11
  , .unpairRight 9 11 12
  , .unpairRight 11 12 13
  , .unpairLeft 12 13 14
  , .pair 10 13 14 15
  , .pair 5 14 14 16
  , .pair 7 14 0 17
  , .halt 0
  ]

@[simp] theorem supplierCircuitHeaderParserProgram_oracleFree :
    OracleFree supplierCircuitHeaderParserProgram := by
  rfl

def supplierCircuitHeaderParserFuel : ℕ := 17

private def supplierCircuitHeaderWorkingValues
    (familyCode countCode bottomTree topCode : ℕ) : List ℕ :=
  let rest₃ := encodeTaggedList [topCode]
  let payload₃ := Nat.pair topCode 0
  let rest₂ := encodeTaggedList [bottomTree, topCode]
  let payload₂ := Nat.pair bottomTree rest₃
  let rest₁ := encodeTaggedList [countCode, bottomTree, topCode]
  let payload₁ := Nat.pair countCode rest₂
  let circuitCode :=
    encodeTaggedList [familyCode, countCode, bottomTree, topCode]
  let payload₀ := Nat.pair familyCode rest₁
  let mode := supplierCircuitMode familyCode
  let bottomTop := Nat.pair bottomTree topCode
  let context :=
    supplierCircuitHeaderContext mode bottomTree topCode
  let output :=
    supplierCircuitHeaderParserOutput familyCode countCode
      bottomTree topCode
  [ 0, 1, familyCode, countCode, bottomTree, topCode,
    rest₃, payload₃, rest₂, payload₂, rest₁, payload₁,
    circuitCode, payload₀, mode, bottomTop, context, output ]

private def supplierCircuitHeaderWorkBound
    (familyCode countCode bottomTree topCode : ℕ) : ℕ :=
  (supplierCircuitHeaderWorkingValues familyCode countCode
    bottomTree topCode).foldr max 1

def supplierCircuitHeaderParserBits
    (familyCode countCode bottomTree topCode : ℕ) : ℕ :=
  natBitLength <|
    supplierCircuitHeaderWorkBound familyCode countCode
      bottomTree topCode

private theorem header_le_foldr_max_of_mem
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

private theorem supplierCircuitHeader_value_bits
    (familyCode countCode bottomTree topCode value : ℕ)
    (hmem :
      value ∈ supplierCircuitHeaderWorkingValues familyCode
        countCode bottomTree topCode) :
    natBitLength value ≤
      supplierCircuitHeaderParserBits familyCode countCode
        bottomTree topCode := by
  unfold supplierCircuitHeaderParserBits
    supplierCircuitHeaderWorkBound
  exact natBitLength_mono (header_le_foldr_max_of_mem hmem)

theorem run_supplierCircuitHeaderParserProgram
    (inputLength familyCode countCode bottomTree topCode : ℕ) :
    runNPOracleProgram supplierCircuitHeaderParserProgram
        (supplierCircuitHeaderParserBits familyCode countCode
          bottomTree topCode)
        supplierCircuitHeaderParserFuel
        (initialNPOracleState inputLength
          (supplierCircuitHeaderParserInput familyCode countCode
            bottomTree topCode)) =
      some
        (supplierCircuitHeaderParserOutput familyCode countCode
          bottomTree topCode) := by
  let rest₃ := encodeTaggedList [topCode]
  let payload₃ := Nat.pair topCode 0
  let rest₂ := encodeTaggedList [bottomTree, topCode]
  let payload₂ := Nat.pair bottomTree rest₃
  let rest₁ := encodeTaggedList [countCode, bottomTree, topCode]
  let payload₁ := Nat.pair countCode rest₂
  let circuitCode :=
    encodeTaggedList [familyCode, countCode, bottomTree, topCode]
  let payload₀ := Nat.pair familyCode rest₁
  let mode := supplierCircuitMode familyCode
  let bottomTop := Nat.pair bottomTree topCode
  let context :=
    supplierCircuitHeaderContext mode bottomTree topCode
  let output :=
    supplierCircuitHeaderParserOutput familyCode countCode
      bottomTree topCode
  let maximumBits :=
    supplierCircuitHeaderParserBits familyCode countCode
      bottomTree topCode
  have hbits :
      ∀ value,
        value ∈
            supplierCircuitHeaderWorkingValues familyCode countCode
              bottomTree topCode →
          natBitLength value ≤ maximumBits :=
    supplierCircuitHeader_value_bits familyCode countCode
      bottomTree topCode
  have hcircuit := hbits circuitCode (by
    simp [supplierCircuitHeaderWorkingValues, circuitCode])
  have hpayload₀ := hbits payload₀ (by
    simp [supplierCircuitHeaderWorkingValues, payload₀, rest₁])
  have hfamily := hbits familyCode (by
    simp [supplierCircuitHeaderWorkingValues])
  have hrest₁ := hbits rest₁ (by
    simp [supplierCircuitHeaderWorkingValues, rest₁])
  have hzero := hbits 0 (by
    simp [supplierCircuitHeaderWorkingValues])
  have hone := hbits 1 (by
    simp [supplierCircuitHeaderWorkingValues])
  have hmode := hbits mode (by
    simp [supplierCircuitHeaderWorkingValues, mode])
  have hpayload₁ := hbits payload₁ (by
    simp [supplierCircuitHeaderWorkingValues, payload₁, rest₂])
  have hcount := hbits countCode (by
    simp [supplierCircuitHeaderWorkingValues])
  have hrest₂ := hbits rest₂ (by
    simp [supplierCircuitHeaderWorkingValues, rest₂])
  have hpayload₂ := hbits payload₂ (by
    simp [supplierCircuitHeaderWorkingValues, payload₂, rest₃])
  have hbottom := hbits bottomTree (by
    simp [supplierCircuitHeaderWorkingValues])
  have hrest₃ := hbits rest₃ (by
    simp [supplierCircuitHeaderWorkingValues, rest₃])
  have hpayload₃ := hbits payload₃ (by
    simp [supplierCircuitHeaderWorkingValues, payload₃])
  have htop := hbits topCode (by
    simp [supplierCircuitHeaderWorkingValues])
  have hbottomTop := hbits bottomTop (by
    simp [supplierCircuitHeaderWorkingValues, bottomTop])
  have hcontext := hbits context (by
    simp [supplierCircuitHeaderWorkingValues, context, mode])
  have houtput := hbits output (by
    simp [supplierCircuitHeaderWorkingValues, output])
  let initial :=
    initialNPOracleState inputLength
      (supplierCircuitHeaderParserInput familyCode countCode
        bottomTree topCode)
  let state1 := (initial.write 2 payload₀).jump 1
  let state2 := (state1.write 3 familyCode).jump 2
  let state3 := (state2.write 4 rest₁).jump 3
  let branchPc := if familyCode = 0 then 4 else 5
  let state4 := ((state3.jump branchPc).write 5 mode).jump 6
  have hdispatch :
      runNPOracleProgram supplierCircuitHeaderParserProgram maximumBits
          14 state3 =
        runNPOracleProgram supplierCircuitHeaderParserProgram maximumBits
          12 state4 := by
    rw [show 14 = 13 + 1 by omega]
    rw [run_branchZero_instruction (fuel := 13)
      (pc := 3) (register := 3) (zeroTarget := 4)
      (nonzeroTarget := 5) (by rfl) (by rfl)]
    rw [show state3.registers 3 = familyCode by
      simp [state3, state2]]
    by_cases hfamilyZero : familyCode = 0
    · rw [hfamilyZero, if_pos rfl]
      rw [show 13 = 12 + 1 by omega]
      rw [run_set_instruction (pc := 4) (value := 0)
        (by rfl) rfl hzero]
      simp [state4, branchPc, mode, supplierCircuitMode,
        hfamilyZero]
    · rw [if_neg hfamilyZero]
      rw [show 13 = 12 + 1 by omega]
      rw [run_set_instruction (pc := 5) (value := 1)
        (by rfl) rfl hone]
      simp [state4, branchPc, mode, supplierCircuitMode,
        hfamilyZero]
  rw [show supplierCircuitHeaderParserFuel = 16 + 1 by rfl]
  rw [run_unpairRight_instruction (value := payload₀)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, supplierCircuitHeaderParserInput,
        payload₀, rest₁, encodeTaggedList])
    hpayload₀]
  change
    runNPOracleProgram supplierCircuitHeaderParserProgram maximumBits
        16 state1 =
      some output
  rw [show 16 = 15 + 1 by omega]
  rw [run_unpairLeft_instruction (value := familyCode)
    (by rfl) rfl
    (by simp [state1, payload₀])
    hfamily]
  change
    runNPOracleProgram supplierCircuitHeaderParserProgram maximumBits
        15 state2 =
      some output
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairRight_instruction (value := rest₁)
    (by rfl) rfl
    (by simp [state2, state1, payload₀])
    hrest₁]
  change
    runNPOracleProgram supplierCircuitHeaderParserProgram maximumBits
        14 state3 =
      some output
  rw [hdispatch]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := payload₁)
    (by rfl) rfl
    (by
      simp [state4, state3, state2, state1, rest₁, payload₁,
        rest₂, encodeTaggedList])
    hpayload₁]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := countCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₁])
    hcount]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := rest₂)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₁])
    hrest₂]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := payload₂)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rest₂,
        payload₂, rest₃, encodeTaggedList])
    hpayload₂]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := bottomTree)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₂])
    hbottom]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := rest₃)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₂])
    hrest₃]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := payload₃)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rest₃,
        payload₃, encodeTaggedList])
    hpayload₃]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := topCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₃])
    htop]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := bottomTop)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, bottomTop])
    hbottomTop]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := context)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, state4]
      rfl)
    hcontext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        supplierCircuitHeaderParserOutput, context,
        supplierCircuitHeaderContext, mode])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

/-! ## Linked native-count header -/

def supplierCircuitHeaderProgram : NPOracleProgram :=
  linkPrograms supplierCircuitHeaderParserProgram <|
    preserveRightProgram canonicalNatDecodeProgram

def supplierCircuitHeaderOutput
    (familyCode bottomCount bottomTree topCode : ℕ) : ℕ :=
  Nat.pair bottomCount <|
    supplierCircuitHeaderContext
      (supplierCircuitMode familyCode) bottomTree topCode

def supplierCircuitHeaderFuel (bottomCount : ℕ) : ℕ :=
  linkFuel (preserveRightProgram canonicalNatDecodeProgram)
    supplierCircuitHeaderParserFuel
    (preserveRightFuel (canonicalNatDecodeFuel bottomCount))

def supplierCircuitHeaderBits
    (inputLength familyCode bottomCount bottomTree topCode : ℕ) : ℕ :=
  let context :=
    supplierCircuitHeaderContext
      (supplierCircuitMode familyCode) bottomTree topCode
  max
    (supplierCircuitHeaderParserBits familyCode
      (encodeNat bottomCount) bottomTree topCode)
    (preserveRightBits
      (canonicalNatDecodeBits inputLength bottomCount)
      (encodeNat bottomCount) context bottomCount)

@[simp] theorem supplierCircuitHeaderProgram_oracleFree :
    OracleFree supplierCircuitHeaderProgram := by
  apply oracleFree_linkPrograms
  · exact supplierCircuitHeaderParserProgram_oracleFree
  · exact preserveRightProgram_oracleFree _
      canonicalNatDecodeProgram_oracleFree

/-- Exact VM execution from a raw canonical circuit code to a native header. -/
theorem run_supplierCircuitHeaderProgram
    (inputLength familyCode bottomCount bottomTree topCode : ℕ) :
    runNPOracleProgram supplierCircuitHeaderProgram
        (supplierCircuitHeaderBits inputLength familyCode bottomCount
          bottomTree topCode)
        (supplierCircuitHeaderFuel bottomCount)
        (initialNPOracleState inputLength
          (supplierCircuitHeaderParserInput familyCode
            (encodeNat bottomCount) bottomTree topCode)) =
      some
        (supplierCircuitHeaderOutput familyCode bottomCount
          bottomTree topCode) := by
  let mode := supplierCircuitMode familyCode
  let context :=
    supplierCircuitHeaderContext mode bottomTree topCode
  let maximumBits :=
    supplierCircuitHeaderBits inputLength familyCode bottomCount
      bottomTree topCode
  have hparserBits :
      supplierCircuitHeaderParserBits familyCode
          (encodeNat bottomCount) bottomTree topCode ≤
        maximumBits :=
    Nat.le_max_left _ _
  have hdecoderBits :
      preserveRightBits
          (canonicalNatDecodeBits inputLength bottomCount)
          (encodeNat bottomCount) context bottomCount ≤
        maximumBits := by
    exact Nat.le_max_right _ _
  have hinputLengthBits :
      natBitLength inputLength ≤ maximumBits := by
    have hsourceBits :
        canonicalNatDecodeBits inputLength bottomCount ≤ maximumBits :=
      (Nat.le_max_left _ _).trans hdecoderBits
    exact
      (canonicalNatDecode_inputLength_bits inputLength bottomCount).trans
        hsourceBits
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hinputLengthBits
  have hparser :
      runNPOracleProgram supplierCircuitHeaderParserProgram maximumBits
          supplierCircuitHeaderParserFuel
          (initialNPOracleState inputLength
            (supplierCircuitHeaderParserInput familyCode
              (encodeNat bottomCount) bottomTree topCode)) =
        some (Nat.pair (encodeNat bottomCount) context) := by
    have hrun :=
      run_bits_mono
        (run_supplierCircuitHeaderParserProgram inputLength familyCode
          (encodeNat bottomCount) bottomTree topCode)
        hparserBits
    simpa only [supplierCircuitHeaderParserOutput, context, mode] using
      hrun
  have hdecoder :
      runNPOracleProgram
          (preserveRightProgram canonicalNatDecodeProgram)
          maximumBits
          (preserveRightFuel (canonicalNatDecodeFuel bottomCount))
          (initialNPOracleState inputLength
            (Nat.pair (encodeNat bottomCount) context)) =
        some (Nat.pair bottomCount context) := by
    have hrun :=
      run_preserveRightProgram canonicalNatDecodeProgram inputLength
        (canonicalNatDecodeBits inputLength bottomCount)
        (canonicalNatDecodeFuel bottomCount)
        (encodeNat bottomCount) context bottomCount
        (run_canonicalNatDecodeProgram inputLength bottomCount)
    exact run_bits_mono hrun hdecoderBits
  exact run_linkPrograms hpositive hinputLengthBits hparser hdecoder

end NearCubicWires.CanonicalSupplierCircuitHeaderProgram
