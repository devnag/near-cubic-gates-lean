import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalNormalizedCircuitValidationProgram
import Proof.MachineModel.CanonicalSupplierCompressedGateProgram
import Proof.MachineModel.CanonicalSupplierSupportCompressionProgram

/-!
# Exact wire resources from validated normalized-circuit summaries

The normalized-circuit validator already emits everything needed for the
physical wire metric: each bottom-gate summary contains its support count, and
the threshold-family top summary contains the exact membership vector.  This
module consumes only that validated summary ABI.  It does not decode circuit
syntax again.
-/

namespace NearCubicWires.CanonicalNormalizedCircuitResourceProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNormalizedCircuitValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalSupplierCompressedGateProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalSupportedGateRelationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## One bottom-gate wire contribution -/

/-- The validated gate summary is
`pair 1 (pair threshold (pair selectedWeights (pair supportCount membership)))`.
Only the already-computed support count is charged here. -/
def normalizedGateWireMetric (summary : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair
      (Nat.unpair (Nat.unpair summary).2).2).2).1 + 1

def normalizedGateWireMetricRequestOutput (request : ℕ) : ℕ :=
  normalizedGateWireMetric (Nat.unpair request).2

def normalizedGateWireMetricProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairRight 2 3 2
  , .unpairRight 3 4 3
  , .unpairLeft 4 0 4
  , .increment 0 5
  , .halt 0
  ]

@[simp] theorem normalizedGateWireMetricProgram_oracleFree :
    OracleFree normalizedGateWireMetricProgram := by
  rfl

private def normalizedGateWireMetricValues
    (inputLength summary : ℕ) : List ℕ :=
  [ inputLength
  , summary
  , (Nat.unpair summary).2
  , (Nat.unpair (Nat.unpair summary).2).2
  , (Nat.unpair
      (Nat.unpair (Nat.unpair summary).2).2).2
  , (Nat.unpair
      (Nat.unpair
        (Nat.unpair (Nat.unpair summary).2).2).2).1
  , normalizedGateWireMetric summary
  ]

def normalizedGateWireMetricBits (request : ℕ) : ℕ :=
  let inputLength := (Nat.unpair request).1
  let summary := (Nat.unpair request).2
  ((normalizedGateWireMetricValues inputLength summary).map natBitLength)
    |>.foldr max 1

def normalizedGateWireMetricFuel (_request : ℕ) : ℕ := 6

private theorem bitLength_le_foldrMax
    {values : List ℕ} {value : ℕ} (hvalue : value ∈ values) :
    natBitLength value ≤
      (values.map natBitLength).foldr max 1 := by
  induction values with
  | nil =>
      simp at hvalue
  | cons head tail ih =>
      simp only [List.mem_cons] at hvalue
      simp only [List.map_cons, List.foldr_cons]
      rcases hvalue with rfl | htail
      · exact le_max_left _ _
      · exact (ih htail).trans (le_max_right _ _)

theorem run_normalizedGateWireMetricProgram
    (inputLength summary : ℕ) :
    let request := nativeInputRequest inputLength summary
    runNPOracleProgram normalizedGateWireMetricProgram
        (normalizedGateWireMetricBits request)
        (normalizedGateWireMetricFuel request)
        (initialNPOracleState inputLength summary) =
      some (normalizedGateWireMetric summary) := by
  dsimp only
  have hbits :
      ∀ value ∈ normalizedGateWireMetricValues inputLength summary,
        natBitLength value ≤
          normalizedGateWireMetricBits
            (nativeInputRequest inputLength summary) := by
    intro value hvalue
    simpa [normalizedGateWireMetricBits, nativeInputRequest] using
      (bitLength_le_foldrMax hvalue)
  have hpayload :=
    hbits (Nat.unpair summary).2 (by
      simp [normalizedGateWireMetricValues])
  have htail :=
    hbits (Nat.unpair (Nat.unpair summary).2).2 (by
      simp [normalizedGateWireMetricValues])
  have hcountMembership :=
    hbits
      (Nat.unpair (Nat.unpair (Nat.unpair summary).2).2).2
      (by simp [normalizedGateWireMetricValues])
  have hcount :=
    hbits
      (Nat.unpair
        (Nat.unpair (Nat.unpair (Nat.unpair summary).2).2).2).1
      (by simp [normalizedGateWireMetricValues])
  have hmetric :=
    hbits (normalizedGateWireMetric summary) (by
      simp [normalizedGateWireMetricValues])
  rw [show normalizedGateWireMetricFuel
      (nativeInputRequest inputLength summary) = 5 + 1 by rfl]
  rw [run_unpairRight_instruction
    (program := normalizedGateWireMetricProgram)
    (maximumBits :=
      normalizedGateWireMetricBits
        (nativeInputRequest inputLength summary))
    (fuel := 5) (pc := 0) (source := 0) (destination := 2)
    (next := 1) (value := (Nat.unpair summary).2)
    (by rfl) rfl (by simp [initialNPOracleState]) hpayload]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedGateWireMetricProgram)
    (maximumBits :=
      normalizedGateWireMetricBits
        (nativeInputRequest inputLength summary))
    (fuel := 4) (pc := 1) (source := 2) (destination := 3)
    (next := 2)
    (value := (Nat.unpair (Nat.unpair summary).2).2)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedGateWireMetricProgram)
    (maximumBits :=
      normalizedGateWireMetricBits
        (nativeInputRequest inputLength summary))
    (fuel := 3) (pc := 2) (source := 3) (destination := 4)
    (next := 3)
    (value :=
      (Nat.unpair (Nat.unpair (Nat.unpair summary).2).2).2)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcountMembership]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := normalizedGateWireMetricProgram)
    (maximumBits :=
      normalizedGateWireMetricBits
        (nativeInputRequest inputLength summary))
    (fuel := 2) (pc := 3) (source := 4) (destination := 0)
    (next := 4)
    (value :=
      (Nat.unpair
        (Nat.unpair (Nat.unpair (Nat.unpair summary).2).2).2).1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcount]
  rw [show 2 = 1 + 1 by omega]
  rw [run_increment_instruction
    (program := normalizedGateWireMetricProgram)
    (maximumBits :=
      normalizedGateWireMetricBits
        (nativeInputRequest inputLength summary))
    (fuel := 1) (pc := 4) (register := 0) (next := 5)
    (value := normalizedGateWireMetric summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedGateWireMetric])
    hmetric]
  exact run_halt_instruction
    (program := normalizedGateWireMetricProgram)
    (maximumBits :=
      normalizedGateWireMetricBits
        (nativeInputRequest inputLength summary))
    (fuel := 0) (pc := 5) (outputRegister := 0)
    (value := normalizedGateWireMetric summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hmetric

/-- A canonical gate summary charges exactly its retained inputs plus the
single wire from the gate output to its parent. -/
theorem normalizedGateWireMetric_supportedGateRelationOutput
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    normalizedGateWireMetric
        (supportedGateRelationOutput inputLength
          (encodeSupportedNormalizedGate gate)) =
      gate.wireCount + 1 := by
  let weights := List.ofFn gate.gate.weight
  let membership :=
    List.ofFn fun index => decide (index ∈ gate.support)
  let weightsCode := encodeIntList weights
  let thresholdCode := encodeInt gate.gate.threshold
  let membershipCode := encodeBoolList membership
  have hzeroOutside :
      List.Forall₂
        (fun weight bit => bit = false → weight = 0)
        weights membership := by
    apply List.forall₂_of_length_eq_of_get
    · simp [weights, membership]
    · intro index _hweights _hmembership
      simp only [weights, membership, List.get_ofFn]
      intro hfalse
      apply gate.zeroOutside
      simpa using hfalse
  have hsummary :=
    supportedGateRelationOutput_eq_of_fields inputLength
      (encodeSupportedNormalizedGate gate) weightsCode thresholdCode
      membershipCode weights gate.gate.threshold membership
      (by
        simp [encodeSupportedNormalizedGate, weightsCode, thresholdCode,
          membershipCode, weights, membership])
      (by simp [weightsCode])
      (by simp [thresholdCode])
      (by simp [membershipCode])
      (by simp [weights])
      (by simp [membership])
      hzeroOutside
  have hcount :
      nonzeroSupportCount membership = gate.support.card := by
    simpa only [membership] using nonzeroSupportCount_eq_supportCard gate
  rw [hsummary]
  simp [normalizedGateWireMetric, supportedGateCompressedPayload,
    hcount, SupportedNormalizedGate.wireCount]

/-! ## Shared summary map and sum -/

def normalizedGateWireMetricRequests
    (inputLength : ℕ) (summaries : List ℕ) : List ℕ :=
  summaries.map (nativeInputRequest inputLength)

def normalizedGateWireMetrics
    (summaries : List ℕ) : List ℕ :=
  summaries.map normalizedGateWireMetric

def normalizedGateWireMetricMapRawOutput
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  balancedValidationMapOutput inputLength
    (encodeBalancedList summaries)
    normalizedGateWireMetricRequestOutput

@[simp] theorem normalizedGateWireMetricMapRawOutput_left
    (inputLength : ℕ) (summaries : List ℕ) :
    (Nat.unpair
      (normalizedGateWireMetricMapRawOutput inputLength summaries)).1 =
      encodeBalancedList (normalizedGateWireMetrics summaries) := by
  simp [normalizedGateWireMetricMapRawOutput,
    balancedValidationMapOutput, balancedValidationMapOutputs,
    balancedValidationMapRequests, balancedValidationMapCodes,
    normalizedGateWireMetricRequestOutput,
    normalizedGateWireMetrics, nativeInputRequest, Function.comp_def]

def normalizedGateWireMetricMapProjectionProgram : NPOracleProgram :=
  [.unpairLeft 0 0 1, .halt 0]

@[simp] theorem normalizedGateWireMetricMapProjectionProgram_oracleFree :
    OracleFree normalizedGateWireMetricMapProjectionProgram := by
  rfl

def normalizedGateWireMetricMapProjectionBits
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  max
    (natBitLength
      (normalizedGateWireMetricMapRawOutput inputLength summaries))
    (natBitLength
      (encodeBalancedList (normalizedGateWireMetrics summaries)))

def normalizedGateWireMetricMapProjectionFuel : ℕ := 2

theorem run_normalizedGateWireMetricMapProjectionProgram
    (inputLength : ℕ) (summaries : List ℕ) :
    runNPOracleProgram normalizedGateWireMetricMapProjectionProgram
        (normalizedGateWireMetricMapProjectionBits inputLength summaries)
        normalizedGateWireMetricMapProjectionFuel
        (initialNPOracleState inputLength
          (normalizedGateWireMetricMapRawOutput inputLength summaries)) =
      some (encodeBalancedList (normalizedGateWireMetrics summaries)) := by
  have houtput :
      natBitLength
          (encodeBalancedList (normalizedGateWireMetrics summaries)) ≤
        normalizedGateWireMetricMapProjectionBits inputLength summaries :=
    Nat.le_max_right _ _
  rw [show normalizedGateWireMetricMapProjectionFuel = 1 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (program := normalizedGateWireMetricMapProjectionProgram)
    (maximumBits :=
      normalizedGateWireMetricMapProjectionBits inputLength summaries)
    (fuel := 1) (pc := 0) (source := 0) (destination := 0)
    (next := 1)
    (value := encodeBalancedList (normalizedGateWireMetrics summaries))
    (by rfl) rfl
    (by simp [initialNPOracleState]) houtput]
  exact run_halt_instruction
    (program := normalizedGateWireMetricMapProjectionProgram)
    (maximumBits :=
      normalizedGateWireMetricMapProjectionBits inputLength summaries)
    (fuel := 0) (pc := 1) (outputRegister := 0)
    (value := encodeBalancedList (normalizedGateWireMetrics summaries))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def normalizedGateWireMetricMapProgram : NPOracleProgram :=
  linkPrograms
    (balancedValidationMapProgram normalizedGateWireMetricProgram)
    normalizedGateWireMetricMapProjectionProgram

@[simp] theorem normalizedGateWireMetricMapProgram_oracleFree :
    OracleFree normalizedGateWireMetricMapProgram := by
  exact oracleFree_linkPrograms
    (balancedValidationMapProgram_oracleFree
      normalizedGateWireMetricProgram
      normalizedGateWireMetricProgram_oracleFree)
    normalizedGateWireMetricMapProjectionProgram_oracleFree

def normalizedGateWireMetricMapBits
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  balancedValidationMapBits normalizedGateWireMetricBits
    normalizedGateWireMetricRequestOutput inputLength
    (encodeBalancedList summaries)

def normalizedGateWireMetricMapFuel
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  linkFuel normalizedGateWireMetricMapProjectionProgram
    (balancedValidationMapFuel normalizedGateWireMetricProgram
      normalizedGateWireMetricFuel inputLength
      (encodeBalancedList summaries))
    normalizedGateWireMetricMapProjectionFuel

private theorem member_le_foldr_max
    {value : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil =>
      simp at hvalue
  | cons head tail ih =>
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact le_max_left _ _
      · exact (ih htail).trans (le_max_right _ _)

theorem run_normalizedGateWireMetricValidationMapProgram
    (inputLength : ℕ) (summaries : List ℕ) :
    runNPOracleProgram
        (balancedValidationMapProgram normalizedGateWireMetricProgram)
        (balancedValidationMapBits normalizedGateWireMetricBits
          normalizedGateWireMetricRequestOutput inputLength
          (encodeBalancedList summaries))
        (balancedValidationMapFuel normalizedGateWireMetricProgram
          normalizedGateWireMetricFuel inputLength
          (encodeBalancedList summaries))
        (initialNPOracleState inputLength
          (encodeBalancedList summaries)) =
      some
        (normalizedGateWireMetricMapRawOutput inputLength summaries) := by
  apply run_balancedValidationMapProgram
  intro request _hrequest
  have hrun :=
    run_normalizedGateWireMetricProgram
      (Nat.unpair request).1 (Nat.unpair request).2
  simpa only [normalizedGateWireMetricRequestOutput,
    nativeInputRequest, Nat.pair_unpair] using hrun

theorem run_normalizedGateWireMetricMapProgram
    (inputLength : ℕ) (summaries : List ℕ) :
    runNPOracleProgram normalizedGateWireMetricMapProgram
        (normalizedGateWireMetricMapBits inputLength summaries)
        (normalizedGateWireMetricMapFuel inputLength summaries)
        (initialNPOracleState inputLength
          (encodeBalancedList summaries)) =
      some (encodeBalancedList (normalizedGateWireMetrics summaries)) := by
  have hpositive :
      1 ≤ normalizedGateWireMetricMapBits inputLength summaries :=
    Nat.le_max_left _ _
  have hlength :
      natBitLength inputLength ≤
        normalizedGateWireMetricMapBits inputLength summaries :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hrawBits :
      natBitLength
          (normalizedGateWireMetricMapRawOutput inputLength summaries) ≤
        normalizedGateWireMetricMapBits inputLength summaries := by
    exact balancedValidationMapOutput_bits_le
      normalizedGateWireMetricProgram normalizedGateWireMetricBits
      normalizedGateWireMetricFuel normalizedGateWireMetricRequestOutput
      inputLength (encodeBalancedList summaries) (by
        intro request _hrequest
        have hrun :=
          run_normalizedGateWireMetricProgram
            (Nat.unpair request).1 (Nat.unpair request).2
        simpa only [normalizedGateWireMetricRequestOutput,
          nativeInputRequest, Nat.pair_unpair] using hrun)
  have hmappedBits :
      natBitLength
          (encodeBalancedList (normalizedGateWireMetrics summaries)) ≤
        normalizedGateWireMetricMapBits inputLength summaries := by
    rw [← normalizedGateWireMetricMapRawOutput_left]
    exact
      (natBitLength_mono
        (Nat.unpair_left_le
          (normalizedGateWireMetricMapRawOutput inputLength summaries))).trans
        hrawBits
  have hprojectionBits :
      normalizedGateWireMetricMapProjectionBits inputLength summaries ≤
        normalizedGateWireMetricMapBits inputLength summaries :=
    max_le hrawBits hmappedBits
  have hmap :=
    run_normalizedGateWireMetricValidationMapProgram inputLength summaries
  have hprojection :=
    run_bits_mono
      (run_normalizedGateWireMetricMapProjectionProgram
        inputLength summaries)
      hprojectionBits
  simpa only [normalizedGateWireMetricMapProgram,
    normalizedGateWireMetricMapFuel] using
      (run_linkPrograms hpositive hlength hmap hprojection)

-- Treat the verified map as an atomic linker stage downstream.  Its expanded
-- controller is large and no later proof may rely on its instruction layout.
attribute [irreducible] normalizedGateWireMetricMapProgram

def normalizedCircuitSymmetricWireProgram : NPOracleProgram :=
  balancedNatSumAfterProgram normalizedGateWireMetricMapProgram

theorem normalizedCircuitSymmetricWireProgram_eq :
    normalizedCircuitSymmetricWireProgram =
      balancedNatSumAfterProgram normalizedGateWireMetricMapProgram := by
  rfl

@[simp] theorem normalizedCircuitSymmetricWireProgram_oracleFree :
    OracleFree normalizedCircuitSymmetricWireProgram := by
  exact oracleFree_linkPrograms
    normalizedGateWireMetricMapProgram_oracleFree
    balancedNatSumProgram_oracleFree

def normalizedCircuitSymmetricWireBits
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  balancedNatSumAfterBits inputLength
    (normalizedGateWireMetricMapBits inputLength summaries)
    (normalizedGateWireMetrics summaries)

def normalizedCircuitSymmetricWireFuel
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  balancedNatSumAfterFuel
    (normalizedGateWireMetricMapFuel inputLength summaries)
    (normalizedGateWireMetrics summaries)

theorem normalizedCircuitSymmetricWireFuel_eq
    (inputLength : ℕ) (summaries : List ℕ) :
    normalizedCircuitSymmetricWireFuel inputLength summaries =
      balancedNatSumAfterFuel
        (normalizedGateWireMetricMapFuel inputLength summaries)
        (normalizedGateWireMetrics summaries) := by
  rfl

attribute [irreducible] normalizedCircuitSymmetricWireProgram

theorem run_normalizedCircuitSymmetricWireProgram
    (inputLength : ℕ) (summaries : List ℕ) :
    runNPOracleProgram normalizedCircuitSymmetricWireProgram
        (normalizedCircuitSymmetricWireBits inputLength summaries)
        (normalizedCircuitSymmetricWireFuel inputLength summaries)
        (initialNPOracleState inputLength
          (encodeBalancedList summaries)) =
      some (normalizedGateWireMetrics summaries).sum := by
  simpa only [normalizedCircuitSymmetricWireProgram,
    normalizedCircuitSymmetricWireBits,
    normalizedCircuitSymmetricWireFuel] using
      (run_balancedNatSumAfterProgram
        normalizedGateWireMetricMapProgram inputLength
        (encodeBalancedList summaries)
        (normalizedGateWireMetricMapBits inputLength summaries)
        (normalizedGateWireMetricMapFuel inputLength summaries)
        (normalizedGateWireMetrics summaries)
        (run_normalizedGateWireMetricMapProgram inputLength summaries))

/-! ## Threshold-family support selection -/

def normalizedCircuitThresholdWireInput
    (summaries : List ℕ) (membership : List Bool) : ℕ :=
  Nat.pair (encodeBalancedList summaries)
    (Nat.pair summaries.length (encodeBoolList membership))

def normalizedCircuitThresholdMapOutput
    (_inputLength : ℕ) (summaries : List ℕ) (membership : List Bool) : ℕ :=
  Nat.pair
    (encodeBalancedList (normalizedGateWireMetrics summaries))
    (Nat.pair summaries.length (encodeBoolList membership))

def normalizedCircuitThresholdMapProgram : NPOracleProgram :=
  preserveRightProgram normalizedGateWireMetricMapProgram

@[simp] theorem normalizedCircuitThresholdMapProgram_oracleFree :
    OracleFree normalizedCircuitThresholdMapProgram :=
  preserveRightProgram_oracleFree
    normalizedGateWireMetricMapProgram
    normalizedGateWireMetricMapProgram_oracleFree

def normalizedCircuitThresholdMapBits
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool) : ℕ :=
  preserveRightBits
    (normalizedGateWireMetricMapBits inputLength summaries)
    (encodeBalancedList summaries)
    (Nat.pair summaries.length (encodeBoolList membership))
    (encodeBalancedList (normalizedGateWireMetrics summaries))

def normalizedCircuitThresholdMapFuel
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  preserveRightFuel
    (normalizedGateWireMetricMapFuel inputLength summaries)

theorem run_normalizedCircuitThresholdMapProgram
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool) :
    runNPOracleProgram normalizedCircuitThresholdMapProgram
        (normalizedCircuitThresholdMapBits inputLength summaries membership)
        (normalizedCircuitThresholdMapFuel inputLength summaries)
        (initialNPOracleState inputLength
          (normalizedCircuitThresholdWireInput summaries membership)) =
      some
        (normalizedCircuitThresholdMapOutput
          inputLength summaries membership) := by
  exact run_preserveRightProgram normalizedGateWireMetricMapProgram
    inputLength
    (normalizedGateWireMetricMapBits inputLength summaries)
    (normalizedGateWireMetricMapFuel inputLength summaries)
    (encodeBalancedList summaries)
    (Nat.pair summaries.length (encodeBoolList membership))
    (encodeBalancedList (normalizedGateWireMetrics summaries))
    (run_normalizedGateWireMetricMapProgram inputLength summaries)

/-- Reframe the mapped metrics and membership as the sole native request of
the existing support-compression program. -/
def normalizedCircuitThresholdCompressionInput
    (summaries : List ℕ) (membership : List Bool) : ℕ :=
  nativeInputRequest summaries.length <|
    Nat.pair (encodeBalancedList (normalizedGateWireMetrics summaries))
      (encodeBoolList membership)

def normalizedCircuitThresholdCompressionPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 4 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 5 3
  , .unpairRight 3 6 4
  , .pair 4 6 7 5
  , .pair 5 7 0 6
  , .halt 0
  ]

@[simp] theorem
    normalizedCircuitThresholdCompressionPrepareProgram_oracleFree :
    OracleFree normalizedCircuitThresholdCompressionPrepareProgram := by
  rfl

private def normalizedCircuitThresholdCompressionPrepareValues
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool) : List ℕ :=
  let mappedCode :=
    encodeBalancedList (normalizedGateWireMetrics summaries)
  let context := Nat.pair summaries.length (encodeBoolList membership)
  [ inputLength
  , Nat.pair mappedCode context
  , mappedCode
  , context
  , summaries.length
  , encodeBoolList membership
  , Nat.pair mappedCode (encodeBoolList membership)
  , normalizedCircuitThresholdCompressionInput summaries membership
  ]

def normalizedCircuitThresholdCompressionPrepareBits
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool) : ℕ :=
  (normalizedCircuitThresholdCompressionPrepareValues
      inputLength summaries membership).map natBitLength
    |>.foldr max 1

def normalizedCircuitThresholdCompressionPrepareFuel : ℕ := 7

theorem run_normalizedCircuitThresholdCompressionPrepareProgram
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool) :
    runNPOracleProgram
        normalizedCircuitThresholdCompressionPrepareProgram
        (normalizedCircuitThresholdCompressionPrepareBits
          inputLength summaries membership)
        normalizedCircuitThresholdCompressionPrepareFuel
        (initialNPOracleState inputLength
          (normalizedCircuitThresholdMapOutput
            inputLength summaries membership)) =
      some
        (normalizedCircuitThresholdCompressionInput summaries membership) := by
  have hbits :
      ∀ value ∈
          normalizedCircuitThresholdCompressionPrepareValues
            inputLength summaries membership,
        natBitLength value ≤
          normalizedCircuitThresholdCompressionPrepareBits
            inputLength summaries membership := by
    intro value hvalue
    exact bitLength_le_foldrMax hvalue
  have hmapped :=
    hbits
      (encodeBalancedList (normalizedGateWireMetrics summaries))
      (by simp [normalizedCircuitThresholdCompressionPrepareValues])
  have hcontext :=
    hbits (Nat.pair summaries.length (encodeBoolList membership))
      (by simp [normalizedCircuitThresholdCompressionPrepareValues])
  have hlength :=
    hbits summaries.length
      (by simp [normalizedCircuitThresholdCompressionPrepareValues])
  have hmembership :=
    hbits (encodeBoolList membership)
      (by simp [normalizedCircuitThresholdCompressionPrepareValues])
  have hcompression :=
    hbits
      (Nat.pair (encodeBalancedList (normalizedGateWireMetrics summaries))
        (encodeBoolList membership))
      (by simp [normalizedCircuitThresholdCompressionPrepareValues])
  have houtput :=
    hbits (normalizedCircuitThresholdCompressionInput summaries membership)
      (by simp [normalizedCircuitThresholdCompressionPrepareValues])
  have houtput' :
      natBitLength
          (Nat.pair summaries.length
            (Nat.pair
              (encodeBalancedList (normalizedGateWireMetrics summaries))
              (encodeBoolList membership))) ≤
        normalizedCircuitThresholdCompressionPrepareBits
          inputLength summaries membership := by
    simpa [normalizedCircuitThresholdCompressionInput,
      nativeInputRequest] using houtput
  simp [normalizedCircuitThresholdCompressionPrepareProgram,
    normalizedCircuitThresholdCompressionPrepareFuel,
    runNPOracleProgram, initialNPOracleState, NPOracleState.boundedWrite,
    normalizedCircuitThresholdMapOutput,
    normalizedCircuitThresholdCompressionInput, nativeInputRequest,
    hmapped, hcontext, hlength, hmembership, hcompression, houtput']

def normalizedCircuitThresholdCompressionOutput
    (summaries : List ℕ) (membership : List Bool) : ℕ :=
  supplierSupportCompressionOutput
    (normalizedGateWireMetrics summaries) membership

def normalizedCircuitThresholdCompressionProgram : NPOracleProgram :=
  nativeCallProgram supplierSupportCompressionProgram

@[simp] theorem normalizedCircuitThresholdCompressionProgram_oracleFree :
    OracleFree normalizedCircuitThresholdCompressionProgram :=
  nativeCallProgram_oracleFree
    supplierSupportCompressionProgram_oracleFree

def normalizedCircuitThresholdCompressionBits
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool) : ℕ :=
  nativeCallBits inputLength summaries.length
    (Nat.pair (encodeBalancedList (normalizedGateWireMetrics summaries))
      (encodeBoolList membership))
    (supplierSupportCompressionOutput
      (normalizedGateWireMetrics summaries) membership)
    (supplierSupportCompressionBits summaries.length
      (normalizedGateWireMetrics summaries) membership)

def normalizedCircuitThresholdCompressionFuel
    (summaries : List ℕ) (membership : List Bool) : ℕ :=
  nativeCallFuel supplierSupportCompressionProgram
    (supplierSupportCompressionFuel
      (normalizedGateWireMetrics summaries) membership)
    summaries.length
    (Nat.pair (encodeBalancedList (normalizedGateWireMetrics summaries))
      (encodeBoolList membership))

theorem run_normalizedCircuitThresholdCompressionProgram
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool)
    (hlength : summaries.length = membership.length) :
    runNPOracleProgram normalizedCircuitThresholdCompressionProgram
        (normalizedCircuitThresholdCompressionBits
          inputLength summaries membership)
        (normalizedCircuitThresholdCompressionFuel summaries membership)
        (initialNPOracleState inputLength
          (normalizedCircuitThresholdCompressionInput
            summaries membership)) =
      some
        (normalizedCircuitThresholdCompressionOutput
          summaries membership) := by
  apply run_nativeCallProgram supplierSupportCompressionProgram
    inputLength summaries.length
    (Nat.pair (encodeBalancedList (normalizedGateWireMetrics summaries))
      (encodeBoolList membership))
    (supplierSupportCompressionOutput
      (normalizedGateWireMetrics summaries) membership)
    (supplierSupportCompressionBits summaries.length
      (normalizedGateWireMetrics summaries) membership)
    (supplierSupportCompressionFuel
      (normalizedGateWireMetrics summaries) membership)
  apply run_supplierSupportCompressionProgram
  · simp [normalizedGateWireMetrics]
  · simpa [normalizedGateWireMetrics] using hlength

def normalizedCircuitThresholdSelectedCode
    (summaries : List ℕ) (membership : List Bool) : ℕ :=
  encodeBalancedList
    (supportedWeights (normalizedGateWireMetrics summaries) membership)

def normalizedCircuitThresholdProjectionProgram : NPOracleProgram :=
  [.unpairLeft 0 0 1, .halt 0]

@[simp] theorem normalizedCircuitThresholdProjectionProgram_oracleFree :
    OracleFree normalizedCircuitThresholdProjectionProgram := by
  rfl

def normalizedCircuitThresholdProjectionBits
    (summaries : List ℕ) (membership : List Bool) : ℕ :=
  max
    (natBitLength
      (normalizedCircuitThresholdCompressionOutput summaries membership))
    (natBitLength
      (normalizedCircuitThresholdSelectedCode summaries membership))

def normalizedCircuitThresholdProjectionFuel : ℕ := 2

theorem run_normalizedCircuitThresholdProjectionProgram
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool) :
    runNPOracleProgram normalizedCircuitThresholdProjectionProgram
        (normalizedCircuitThresholdProjectionBits summaries membership)
        normalizedCircuitThresholdProjectionFuel
        (initialNPOracleState inputLength
          (normalizedCircuitThresholdCompressionOutput
            summaries membership)) =
      some
        (normalizedCircuitThresholdSelectedCode summaries membership) := by
  have houtput :
      natBitLength
          (normalizedCircuitThresholdSelectedCode summaries membership) ≤
        normalizedCircuitThresholdProjectionBits summaries membership :=
    Nat.le_max_right _ _
  have hinput :
      natBitLength
          (normalizedCircuitThresholdCompressionOutput summaries membership) ≤
        normalizedCircuitThresholdProjectionBits summaries membership :=
    Nat.le_max_left _ _
  have houtput' :
      natBitLength
          (encodeBalancedList
            (supportedWeights
              (normalizedGateWireMetrics summaries) membership)) ≤
        normalizedCircuitThresholdProjectionBits summaries membership := by
    simpa [normalizedCircuitThresholdSelectedCode] using houtput
  simp [normalizedCircuitThresholdProjectionProgram,
    normalizedCircuitThresholdProjectionFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    normalizedCircuitThresholdCompressionOutput,
    normalizedCircuitThresholdSelectedCode,
    supplierSupportCompressionOutput, houtput']

def normalizedCircuitThresholdWireProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms
      (linkPrograms
        (linkPrograms normalizedCircuitThresholdMapProgram
          normalizedCircuitThresholdCompressionPrepareProgram)
        normalizedCircuitThresholdCompressionProgram)
      normalizedCircuitThresholdProjectionProgram)
    balancedNatSumProgram

@[simp] theorem normalizedCircuitThresholdWireProgram_oracleFree :
    OracleFree normalizedCircuitThresholdWireProgram := by
  exact oracleFree_linkPrograms
    (oracleFree_linkPrograms
      (oracleFree_linkPrograms
        (oracleFree_linkPrograms
          normalizedCircuitThresholdMapProgram_oracleFree
          normalizedCircuitThresholdCompressionPrepareProgram_oracleFree)
        normalizedCircuitThresholdCompressionProgram_oracleFree)
      normalizedCircuitThresholdProjectionProgram_oracleFree)
    balancedNatSumProgram_oracleFree

private def normalizedCircuitThresholdWireStageBits
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , normalizedCircuitThresholdMapBits inputLength summaries membership
  , normalizedCircuitThresholdCompressionPrepareBits
      inputLength summaries membership
  , normalizedCircuitThresholdCompressionBits
      inputLength summaries membership
  , normalizedCircuitThresholdProjectionBits summaries membership
  , balancedNatSumBits inputLength
      (supportedWeights (normalizedGateWireMetrics summaries) membership)
  ]

def normalizedCircuitThresholdWireBits
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool) : ℕ :=
  max 1 <|
    (normalizedCircuitThresholdWireStageBits
      inputLength summaries membership).foldr max 0

def normalizedCircuitThresholdWireFuel
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool) : ℕ :=
  linkFuel balancedNatSumProgram
    (linkFuel normalizedCircuitThresholdProjectionProgram
      (linkFuel normalizedCircuitThresholdCompressionProgram
        (linkFuel normalizedCircuitThresholdCompressionPrepareProgram
          (normalizedCircuitThresholdMapFuel inputLength summaries)
          normalizedCircuitThresholdCompressionPrepareFuel)
        (normalizedCircuitThresholdCompressionFuel summaries membership))
      normalizedCircuitThresholdProjectionFuel)
    (balancedNatSumFuel
      (supportedWeights (normalizedGateWireMetrics summaries) membership))

private theorem normalizedCircuitThresholdWire_stage_le
    {inputLength : ℕ} {summaries : List ℕ}
    {membership : List Bool} {value : ℕ}
    (hvalue :
      value ∈ normalizedCircuitThresholdWireStageBits
        inputLength summaries membership) :
    value ≤ normalizedCircuitThresholdWireBits
      inputLength summaries membership := by
  exact (member_le_foldr_max hvalue).trans (Nat.le_max_right _ _)

theorem run_normalizedCircuitThresholdWireProgram
    (inputLength : ℕ) (summaries : List ℕ)
    (membership : List Bool)
    (hlength : summaries.length = membership.length) :
    runNPOracleProgram normalizedCircuitThresholdWireProgram
        (normalizedCircuitThresholdWireBits inputLength summaries membership)
        (normalizedCircuitThresholdWireFuel inputLength summaries membership)
        (initialNPOracleState inputLength
          (normalizedCircuitThresholdWireInput summaries membership)) =
      some
        (supportedWeights
          (normalizedGateWireMetrics summaries) membership).sum := by
  let maximumBits :=
    normalizedCircuitThresholdWireBits inputLength summaries membership
  have hpositive : 1 ≤ maximumBits :=
    normalizedCircuitThresholdWire_stage_le (by
      simp [normalizedCircuitThresholdWireStageBits])
  have hinputLength :
      natBitLength inputLength ≤ maximumBits :=
    normalizedCircuitThresholdWire_stage_le (by
      simp [normalizedCircuitThresholdWireStageBits])
  have hmapBits :
      normalizedCircuitThresholdMapBits
          inputLength summaries membership ≤ maximumBits :=
    normalizedCircuitThresholdWire_stage_le (by
      simp [normalizedCircuitThresholdWireStageBits])
  have hprepareBits :
      normalizedCircuitThresholdCompressionPrepareBits
          inputLength summaries membership ≤ maximumBits :=
    normalizedCircuitThresholdWire_stage_le (by
      simp [normalizedCircuitThresholdWireStageBits])
  have hcompressionBits :
      normalizedCircuitThresholdCompressionBits
          inputLength summaries membership ≤ maximumBits :=
    normalizedCircuitThresholdWire_stage_le (by
      simp [normalizedCircuitThresholdWireStageBits])
  have hprojectionBits :
      normalizedCircuitThresholdProjectionBits
          summaries membership ≤ maximumBits :=
    normalizedCircuitThresholdWire_stage_le (by
      simp [normalizedCircuitThresholdWireStageBits])
  have hsumBits :
      balancedNatSumBits inputLength
          (supportedWeights
            (normalizedGateWireMetrics summaries) membership) ≤
        maximumBits :=
    normalizedCircuitThresholdWire_stage_le (by
      simp [normalizedCircuitThresholdWireStageBits])
  have hmap :=
    run_bits_mono
      (run_normalizedCircuitThresholdMapProgram
        inputLength summaries membership)
      hmapBits
  have hprepare :=
    run_bits_mono
      (run_normalizedCircuitThresholdCompressionPrepareProgram
        inputLength summaries membership)
      hprepareBits
  have hcompression :=
    run_bits_mono
      (run_normalizedCircuitThresholdCompressionProgram
        inputLength summaries membership hlength)
      hcompressionBits
  have hprojection :=
    run_bits_mono
      (run_normalizedCircuitThresholdProjectionProgram
        inputLength summaries membership)
      hprojectionBits
  have hsum :=
    run_bits_mono
      (run_balancedNatSumProgram inputLength
        (supportedWeights
          (normalizedGateWireMetrics summaries) membership))
      hsumBits
  have hmapPrepare :=
    run_linkPrograms hpositive hinputLength hmap hprepare
  have hcompressionPrefix :=
    run_linkPrograms hpositive hinputLength hmapPrepare hcompression
  have hprojectionPrefix :=
    run_linkPrograms hpositive hinputLength hcompressionPrefix hprojection
  exact
    run_linkPrograms hpositive hinputLength hprojectionPrefix hsum

private theorem supportedWeights_map_filter
    {ι : Type} (indices : List ι) (value : ι → ℕ)
    (selected : ι → Bool) :
    supportedWeights (indices.map value) (indices.map selected) =
      (indices.filter selected).map value := by
  induction indices with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      cases hselected : selected index <;>
        simp [supportedWeights, hselected, inductionHypothesis]

private theorem filter_finRange_membership_eq_sort
    {n : ℕ} (support : Finset (Fin n)) :
    (List.finRange n).filter
        (fun index => decide (index ∈ support)) =
      support.sort (· ≤ ·) := by
  apply List.Subset.antisymm_of_sortedLT
  · intro index hindex
    simpa using hindex
  · intro index hindex
    simpa using hindex
  · exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT
  · exact Finset.sortedLT_sort support

/-- Selecting a type-indexed list by a finite membership bitmap is the same
sum as ranging over that finite support. -/
private theorem sum_supportedWeights_ofFn_membership
    {n : ℕ} (values : Fin n → ℕ) (support : Finset (Fin n)) :
    (supportedWeights (List.ofFn values)
      (List.ofFn fun index => decide (index ∈ support))).sum =
        ∑ index ∈ support, values index := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  rw [supportedWeights_map_filter]
  rw [filter_finRange_membership_eq_sort]
  rw [← List.sum_toFinset values (Finset.sortedLT_sort support).nodup]
  rw [Finset.sort_toFinset]

/-! ## Validated-summary dispatcher

The validator's public result is
`pair familyTag (pair topSummary (pair bottomSummaryData rawCircuit))`.
This final adapter only projects that ABI.  It never parses the normalized
circuit syntax or revalidates a gate.
-/

def normalizedCircuitResourceFamilyTag (summary : ℕ) : ℕ :=
  (Nat.unpair summary).1

def normalizedCircuitResourcePayload (summary : ℕ) : ℕ :=
  (Nat.unpair summary).2

def normalizedCircuitResourceTopSummary (summary : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitResourcePayload summary)).1

def normalizedCircuitResourceBottomAndRaw (summary : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitResourcePayload summary)).2

def normalizedCircuitResourceBottomSummaryData (summary : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitResourceBottomAndRaw summary)).1

def normalizedCircuitResourceBottomSummariesCode (summary : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitResourceBottomSummaryData summary)).1

def normalizedCircuitResourceBottomMetadata (summary : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitResourceBottomSummaryData summary)).2

def normalizedCircuitResourceBottomLength (summary : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitResourceBottomMetadata summary)).1

def normalizedCircuitResourceTopPayload (summary : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitResourceTopSummary summary)).2

def normalizedCircuitResourceThresholdSelectedTail (summary : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitResourceTopPayload summary)).2

def normalizedCircuitResourceThresholdCountMembership (summary : ℕ) : ℕ :=
  (Nat.unpair
    (normalizedCircuitResourceThresholdSelectedTail summary)).2

def normalizedCircuitResourceThresholdMembershipCode (summary : ℕ) : ℕ :=
  (Nat.unpair
    (normalizedCircuitResourceThresholdCountMembership summary)).2

def normalizedCircuitResourceSummaries (summary : ℕ) : List ℕ :=
  (decodeBalancedList
    (normalizedCircuitResourceBottomSummariesCode summary)).getD []

def normalizedCircuitResourceMembership (summary : ℕ) : List Bool :=
  (decodeBoolList
    (normalizedCircuitResourceThresholdMembershipCode summary)).getD []

def normalizedCircuitResourceBranchTag (summary : ℕ) : ℕ :=
  (normalizedCircuitResourceFamilyTag summary).pred

def normalizedCircuitResourceThresholdInput (summary : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitResourceBottomSummariesCode summary) <|
    Nat.pair (normalizedCircuitResourceBottomLength summary)
      (normalizedCircuitResourceThresholdMembershipCode summary)

def normalizedCircuitResourceBranchPayload (summary : ℕ) : ℕ :=
  if normalizedCircuitResourceBranchTag summary = 0 then
    normalizedCircuitResourceBottomSummariesCode summary
  else
    normalizedCircuitResourceThresholdInput summary

def normalizedCircuitResourcePrepareOutput (summary : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitResourceBranchTag summary)
    (normalizedCircuitResourceBranchPayload summary)

def normalizedCircuitResourcePrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairLeft 6 7 6
  , .unpairRight 6 8 7
  , .unpairLeft 8 9 8
  , .unpairRight 4 10 9
  , .unpairRight 10 11 10
  , .unpairRight 11 12 11
  , .unpairRight 12 13 12
  , .decrement 2 13
  , .pair 9 13 14 14
  , .pair 7 14 15 15
  , .branchZero 2 17 16
  , .pair 2 15 0 18
  , .pair 2 7 0 18
  , .halt 0
  ]

@[simp] theorem normalizedCircuitResourcePrepareProgram_oracleFree :
    OracleFree normalizedCircuitResourcePrepareProgram := by
  rfl

private def normalizedCircuitResourcePrepareValues
    (inputLength summary : ℕ) : List ℕ :=
  [ inputLength
  , summary
  , normalizedCircuitResourceFamilyTag summary
  , normalizedCircuitResourcePayload summary
  , normalizedCircuitResourceTopSummary summary
  , normalizedCircuitResourceBottomAndRaw summary
  , normalizedCircuitResourceBottomSummaryData summary
  , normalizedCircuitResourceBottomSummariesCode summary
  , normalizedCircuitResourceBottomMetadata summary
  , normalizedCircuitResourceBottomLength summary
  , normalizedCircuitResourceTopPayload summary
  , normalizedCircuitResourceThresholdSelectedTail summary
  , normalizedCircuitResourceThresholdCountMembership summary
  , normalizedCircuitResourceThresholdMembershipCode summary
  , normalizedCircuitResourceBranchTag summary
  , Nat.pair (normalizedCircuitResourceBottomLength summary)
      (normalizedCircuitResourceThresholdMembershipCode summary)
  , normalizedCircuitResourceThresholdInput summary
  , normalizedCircuitResourcePrepareOutput summary
  ]

def normalizedCircuitResourcePrepareBits
    (inputLength summary : ℕ) : ℕ :=
  (normalizedCircuitResourcePrepareValues inputLength summary).map
      natBitLength |>.foldr max 1

def normalizedCircuitResourcePrepareFuel : ℕ := 18

theorem run_normalizedCircuitResourcePrepareProgram
    (inputLength summary : ℕ) :
    runNPOracleProgram normalizedCircuitResourcePrepareProgram
        (normalizedCircuitResourcePrepareBits inputLength summary)
        normalizedCircuitResourcePrepareFuel
        (initialNPOracleState inputLength summary) =
      some (normalizedCircuitResourcePrepareOutput summary) := by
  have hbits :
      ∀ value ∈ normalizedCircuitResourcePrepareValues inputLength summary,
        natBitLength value ≤
          normalizedCircuitResourcePrepareBits inputLength summary := by
    intro value hvalue
    exact bitLength_le_foldrMax hvalue
  have hfamily :=
    hbits (normalizedCircuitResourceFamilyTag summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have hpayload :=
    hbits (normalizedCircuitResourcePayload summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have htop :=
    hbits (normalizedCircuitResourceTopSummary summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have hbottomAndRaw :=
    hbits (normalizedCircuitResourceBottomAndRaw summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have hbottomData :=
    hbits (normalizedCircuitResourceBottomSummaryData summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have hsummaries :=
    hbits (normalizedCircuitResourceBottomSummariesCode summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have hmetadata :=
    hbits (normalizedCircuitResourceBottomMetadata summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have hlength :=
    hbits (normalizedCircuitResourceBottomLength summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have htopPayload :=
    hbits (normalizedCircuitResourceTopPayload summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have hselectedTail :=
    hbits (normalizedCircuitResourceThresholdSelectedTail summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have hcountMembership :=
    hbits (normalizedCircuitResourceThresholdCountMembership summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have hmembership :=
    hbits (normalizedCircuitResourceThresholdMembershipCode summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have htag :=
    hbits (normalizedCircuitResourceBranchTag summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have hlengthMembership :=
    hbits
      (Nat.pair (normalizedCircuitResourceBottomLength summary)
        (normalizedCircuitResourceThresholdMembershipCode summary))
      (by simp [normalizedCircuitResourcePrepareValues])
  have hthresholdInput :=
    hbits (normalizedCircuitResourceThresholdInput summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  have houtput :=
    hbits (normalizedCircuitResourcePrepareOutput summary)
      (by simp [normalizedCircuitResourcePrepareValues])
  rw [show normalizedCircuitResourcePrepareFuel = 17 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 17) (pc := 0) (source := 0) (destination := 2)
    (next := 1) (value := normalizedCircuitResourceFamilyTag summary)
    (by rfl) rfl
    (by simp [initialNPOracleState,
      normalizedCircuitResourceFamilyTag]) hfamily]
  rw [show 17 = 16 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 16) (pc := 1) (source := 0) (destination := 3)
    (next := 2) (value := normalizedCircuitResourcePayload summary)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, normalizedCircuitResourcePayload]) hpayload]
  rw [show 16 = 15 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 15) (pc := 2) (source := 3) (destination := 4)
    (next := 3) (value := normalizedCircuitResourceTopSummary summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceTopSummary,
      normalizedCircuitResourcePayload]) htop]
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 14) (pc := 3) (source := 3) (destination := 5)
    (next := 4) (value := normalizedCircuitResourceBottomAndRaw summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceBottomAndRaw,
      normalizedCircuitResourcePayload]) hbottomAndRaw]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 13) (pc := 4) (source := 5) (destination := 6)
    (next := 5)
    (value := normalizedCircuitResourceBottomSummaryData summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceBottomSummaryData,
      normalizedCircuitResourceBottomAndRaw]) hbottomData]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 12) (pc := 5) (source := 6) (destination := 7)
    (next := 6)
    (value := normalizedCircuitResourceBottomSummariesCode summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceBottomSummariesCode,
      normalizedCircuitResourceBottomSummaryData]) hsummaries]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 11) (pc := 6) (source := 6) (destination := 8)
    (next := 7)
    (value := normalizedCircuitResourceBottomMetadata summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceBottomMetadata,
      normalizedCircuitResourceBottomSummaryData]) hmetadata]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 10) (pc := 7) (source := 8) (destination := 9)
    (next := 8)
    (value := normalizedCircuitResourceBottomLength summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceBottomLength,
      normalizedCircuitResourceBottomMetadata]) hlength]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 9) (pc := 8) (source := 4) (destination := 10)
    (next := 9)
    (value := normalizedCircuitResourceTopPayload summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceTopPayload,
      normalizedCircuitResourceTopSummary]) htopPayload]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 8) (pc := 9) (source := 10) (destination := 11)
    (next := 10)
    (value := normalizedCircuitResourceThresholdSelectedTail summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceThresholdSelectedTail,
      normalizedCircuitResourceTopPayload]) hselectedTail]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 7) (pc := 10) (source := 11) (destination := 12)
    (next := 11)
    (value := normalizedCircuitResourceThresholdCountMembership summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceThresholdCountMembership,
      normalizedCircuitResourceThresholdSelectedTail]) hcountMembership]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 6) (pc := 11) (source := 12) (destination := 13)
    (next := 12)
    (value := normalizedCircuitResourceThresholdMembershipCode summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceThresholdMembershipCode,
      normalizedCircuitResourceThresholdCountMembership]) hmembership]
  rw [show 6 = 5 + 1 by omega]
  rw [run_decrement_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 5) (pc := 12) (register := 2) (next := 13)
    (value := normalizedCircuitResourceBranchTag summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceBranchTag,
      normalizedCircuitResourceFamilyTag]) htag]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 4) (pc := 13) (left := 9) (right := 13)
    (destination := 14) (next := 14)
    (value :=
      Nat.pair (normalizedCircuitResourceBottomLength summary)
        (normalizedCircuitResourceThresholdMembershipCode summary))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hlengthMembership]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 3) (pc := 14) (left := 7) (right := 14)
    (destination := 15) (next := 15)
    (value := normalizedCircuitResourceThresholdInput summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceThresholdInput]) hthresholdInput]
  rw [show 3 = 2 + 1 by omega]
  rw [run_branchZero_instruction
    (program := normalizedCircuitResourcePrepareProgram)
    (fuel := 2) (pc := 15) (register := 2)
    (zeroTarget := 17) (nonzeroTarget := 16) (by rfl) rfl]
  by_cases htagZero : normalizedCircuitResourceBranchTag summary = 0
  · rw [if_pos (by
      simp [NPOracleState.write, NPOracleState.jump, htagZero])]
    rw [show 2 = 1 + 1 by omega]
    rw [run_pair_instruction
      (program := normalizedCircuitResourcePrepareProgram)
      (fuel := 1) (pc := 17) (left := 2) (right := 7)
      (destination := 0) (next := 18)
      (value := normalizedCircuitResourcePrepareOutput summary)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump,
        normalizedCircuitResourcePrepareOutput,
        normalizedCircuitResourceBranchPayload, htagZero])
      houtput]
    exact run_halt_instruction
      (program := normalizedCircuitResourcePrepareProgram)
      (fuel := 0) (pc := 18) (outputRegister := 0)
      (value := normalizedCircuitResourcePrepareOutput summary)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      houtput
  · rw [if_neg (by
      simp [NPOracleState.write, NPOracleState.jump, htagZero])]
    rw [show 2 = 1 + 1 by omega]
    rw [run_pair_instruction
      (program := normalizedCircuitResourcePrepareProgram)
      (fuel := 1) (pc := 16) (left := 2) (right := 15)
      (destination := 0) (next := 18)
      (value := normalizedCircuitResourcePrepareOutput summary)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump,
        normalizedCircuitResourcePrepareOutput,
        normalizedCircuitResourceBranchPayload, htagZero])
      houtput]
    exact run_halt_instruction
      (program := normalizedCircuitResourcePrepareProgram)
      (fuel := 0) (pc := 18) (outputRegister := 0)
      (value := normalizedCircuitResourcePrepareOutput summary)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      houtput

def normalizedCircuitResourceMetric (summary : ℕ) : ℕ :=
  let metrics :=
    normalizedGateWireMetrics
      (normalizedCircuitResourceSummaries summary)
  if normalizedCircuitResourceBranchTag summary = 0 then
    metrics.sum
  else
    (supportedWeights metrics
      (normalizedCircuitResourceMembership summary)).sum

/-- The symmetric summary ABI refines to the semantic circuit's exact physical
wire count.  The hypothesis is precisely the bottom-summary decode already
required by the executable resource stage. -/
theorem normalizedCircuitResourceMetric_eq_symmetricWireCount
    {inputLength : ℕ} (summary : ℕ)
    (circuit : NormalizedSymmetricThresholdCircuit inputLength)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 1)
    (hsummaries :
      decodeBalancedList
          (normalizedCircuitResourceBottomSummariesCode summary) =
        some (List.ofFn fun index =>
          supportedGateRelationOutput inputLength
            (encodeSupportedNormalizedGate (circuit.bottom index)))) :
    normalizedCircuitResourceMetric summary = circuit.wireCount := by
  have htag : normalizedCircuitResourceBranchTag summary = 0 := by
    simp [normalizedCircuitResourceBranchTag, hfamily]
  have hsummariesView :
      normalizedCircuitResourceSummaries summary =
        List.ofFn fun index =>
          supportedGateRelationOutput inputLength
            (encodeSupportedNormalizedGate (circuit.bottom index)) := by
    simp [normalizedCircuitResourceSummaries, hsummaries]
  have hmetrics :
      normalizedGateWireMetrics
          (List.ofFn fun index =>
            supportedGateRelationOutput inputLength
              (encodeSupportedNormalizedGate (circuit.bottom index))) =
        List.ofFn fun index => (circuit.bottom index).wireCount + 1 := by
    rw [normalizedGateWireMetrics, List.map_ofFn]
    exact congrArg List.ofFn <| funext fun index =>
      normalizedGateWireMetric_supportedGateRelationOutput
        (circuit.bottom index)
  rw [normalizedCircuitResourceMetric, if_pos htag, hsummariesView,
    hmetrics]
  exact List.sum_ofFn

/-- The threshold summary ABI refines to the exact support-selected bottom
wire count.  In particular, the top membership bitmap is the sole selector;
raw circuit syntax is never reparsed. -/
theorem normalizedCircuitResourceMetric_eq_thresholdWireCount
    {inputLength : ℕ} (summary : ℕ)
    (circuit : NormalizedThresholdThresholdCircuit inputLength)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 2)
    (hsummaries :
      decodeBalancedList
          (normalizedCircuitResourceBottomSummariesCode summary) =
        some (List.ofFn fun index =>
          supportedGateRelationOutput inputLength
            (encodeSupportedNormalizedGate (circuit.bottom index))))
    (hmembership :
      decodeBoolList
          (normalizedCircuitResourceThresholdMembershipCode summary) =
        some (List.ofFn fun index =>
          decide (index ∈ circuit.top.support))) :
    normalizedCircuitResourceMetric summary = circuit.wireCount := by
  have htag : normalizedCircuitResourceBranchTag summary ≠ 0 := by
    simp [normalizedCircuitResourceBranchTag, hfamily]
  have hsummariesView :
      normalizedCircuitResourceSummaries summary =
        List.ofFn fun index =>
          supportedGateRelationOutput inputLength
            (encodeSupportedNormalizedGate (circuit.bottom index)) := by
    simp [normalizedCircuitResourceSummaries, hsummaries]
  have hmembershipView :
      normalizedCircuitResourceMembership summary =
        List.ofFn fun index => decide (index ∈ circuit.top.support) := by
    simp [normalizedCircuitResourceMembership, hmembership]
  have hmetrics :
      normalizedGateWireMetrics
          (List.ofFn fun index =>
            supportedGateRelationOutput inputLength
              (encodeSupportedNormalizedGate (circuit.bottom index))) =
        List.ofFn fun index => (circuit.bottom index).wireCount + 1 := by
    rw [normalizedGateWireMetrics, List.map_ofFn]
    exact congrArg List.ofFn <| funext fun index =>
      normalizedGateWireMetric_supportedGateRelationOutput
        (circuit.bottom index)
  rw [normalizedCircuitResourceMetric, if_neg htag, hsummariesView,
    hmembershipView, hmetrics]
  simpa [NormalizedThresholdThresholdCircuit.wireCount] using
    (sum_supportedWeights_ofFn_membership
      (fun index => (circuit.bottom index).wireCount + 1)
      circuit.top.support)

def normalizedCircuitResourceFamilyProgram : NPOracleProgram :=
  taggedProgramChoice normalizedCircuitSymmetricWireProgram
    normalizedCircuitThresholdWireProgram

@[simp] theorem normalizedCircuitResourceFamilyProgram_oracleFree :
    OracleFree normalizedCircuitResourceFamilyProgram := by
  exact taggedProgramChoice_oracleFree
    normalizedCircuitSymmetricWireProgram
    normalizedCircuitThresholdWireProgram
    normalizedCircuitSymmetricWireProgram_oracleFree
    normalizedCircuitThresholdWireProgram_oracleFree

def normalizedCircuitResourceFamilySourceBits
    (inputLength summary : ℕ) : ℕ :=
  if normalizedCircuitResourceBranchTag summary = 0 then
    normalizedCircuitSymmetricWireBits inputLength
      (normalizedCircuitResourceSummaries summary)
  else
    normalizedCircuitThresholdWireBits inputLength
      (normalizedCircuitResourceSummaries summary)
      (normalizedCircuitResourceMembership summary)

def normalizedCircuitResourceFamilyBits
    (inputLength summary : ℕ) : ℕ :=
  max
    (natBitLength
      (Nat.pair inputLength
        (normalizedCircuitResourcePrepareOutput summary)))
    (normalizedCircuitResourceFamilySourceBits inputLength summary)

def normalizedCircuitResourceFamilyFuel
    (inputLength summary : ℕ) : ℕ :=
  if normalizedCircuitResourceBranchTag summary = 0 then
    taggedProgramChoiceFuel <|
      normalizedCircuitSymmetricWireFuel inputLength
        (normalizedCircuitResourceSummaries summary)
  else
    taggedProgramChoiceFuel <|
      normalizedCircuitThresholdWireFuel inputLength
        (normalizedCircuitResourceSummaries summary)
        (normalizedCircuitResourceMembership summary)

theorem run_normalizedCircuitResourceFamilyProgram_symmetric
    (inputLength summary : ℕ) (summaries : List ℕ)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 1)
    (hsummaries :
      decodeBalancedList
        (normalizedCircuitResourceBottomSummariesCode summary) =
          some summaries) :
    runNPOracleProgram normalizedCircuitResourceFamilyProgram
        (normalizedCircuitResourceFamilyBits inputLength summary)
        (normalizedCircuitResourceFamilyFuel inputLength summary)
        (initialNPOracleState inputLength
          (normalizedCircuitResourcePrepareOutput summary)) =
      some (normalizedCircuitResourceMetric summary) := by
  have htag : normalizedCircuitResourceBranchTag summary = 0 := by
    simp [normalizedCircuitResourceBranchTag, hfamily]
  have hsummariesView :
      normalizedCircuitResourceSummaries summary = summaries := by
    simp [normalizedCircuitResourceSummaries, hsummaries]
  have hcode :
      normalizedCircuitResourceBottomSummariesCode summary =
        encodeBalancedList summaries :=
    (encodeBalancedList_of_decode hsummaries).symm
  have hprepare :
      normalizedCircuitResourcePrepareOutput summary =
        Nat.pair 0 (encodeBalancedList summaries) := by
    simp [normalizedCircuitResourcePrepareOutput,
      normalizedCircuitResourceBranchPayload, htag, hcode]
  have hsourceBits :
      normalizedCircuitSymmetricWireBits inputLength summaries ≤
        normalizedCircuitResourceFamilyBits inputLength summary := by
    rw [normalizedCircuitResourceFamilyBits,
      normalizedCircuitResourceFamilySourceBits, if_pos htag,
      hsummariesView]
    exact Nat.le_max_right _ _
  have hsource :=
    run_bits_mono
      (run_normalizedCircuitSymmetricWireProgram inputLength summaries)
      hsourceBits
  have hinput :
      natBitLength
          (Nat.pair inputLength (Nat.pair 0 (encodeBalancedList summaries))) ≤
        normalizedCircuitResourceFamilyBits inputLength summary := by
    rw [← hprepare]
    exact Nat.le_max_left _ _
  have houtput := run_output_bounded hsource
  have hrun :=
    run_taggedProgramChoice_zero normalizedCircuitSymmetricWireProgram
      normalizedCircuitThresholdWireProgram inputLength
      (encodeBalancedList summaries)
      (normalizedCircuitResourceFamilyBits inputLength summary)
      (normalizedCircuitSymmetricWireFuel inputLength summaries)
      (normalizedGateWireMetrics summaries).sum
      hinput hsource houtput
  simpa [normalizedCircuitResourceFamilyProgram,
    normalizedCircuitResourceFamilyFuel, htag, hsummariesView,
    normalizedCircuitResourceMetric, hprepare] using hrun

theorem run_normalizedCircuitResourceFamilyProgram_threshold
    (inputLength summary : ℕ) (summaries : List ℕ)
    (membership : List Bool)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 2)
    (hsummaries :
      decodeBalancedList
        (normalizedCircuitResourceBottomSummariesCode summary) =
          some summaries)
    (hmembership :
      decodeBoolList
        (normalizedCircuitResourceThresholdMembershipCode summary) =
          some membership)
    (hstoredLength :
      normalizedCircuitResourceBottomLength summary = summaries.length)
    (hlength : summaries.length = membership.length) :
    runNPOracleProgram normalizedCircuitResourceFamilyProgram
        (normalizedCircuitResourceFamilyBits inputLength summary)
        (normalizedCircuitResourceFamilyFuel inputLength summary)
        (initialNPOracleState inputLength
          (normalizedCircuitResourcePrepareOutput summary)) =
      some (normalizedCircuitResourceMetric summary) := by
  have htag : normalizedCircuitResourceBranchTag summary = 1 := by
    simp [normalizedCircuitResourceBranchTag, hfamily]
  have htagNonzero : normalizedCircuitResourceBranchTag summary ≠ 0 := by
    omega
  have hsummariesView :
      normalizedCircuitResourceSummaries summary = summaries := by
    simp [normalizedCircuitResourceSummaries, hsummaries]
  have hmembershipView :
      normalizedCircuitResourceMembership summary = membership := by
    simp [normalizedCircuitResourceMembership, hmembership]
  have hcode :
      normalizedCircuitResourceBottomSummariesCode summary =
        encodeBalancedList summaries :=
    (encodeBalancedList_of_decode hsummaries).symm
  have hmembershipCode :
      normalizedCircuitResourceThresholdMembershipCode summary =
        encodeBoolList membership :=
    (encodeBoolList_of_decode hmembership).symm
  have hprepare :
      normalizedCircuitResourcePrepareOutput summary =
        Nat.pair 1
          (normalizedCircuitThresholdWireInput summaries membership) := by
    simp [normalizedCircuitResourcePrepareOutput,
      normalizedCircuitResourceBranchPayload,
      normalizedCircuitResourceThresholdInput,
      normalizedCircuitThresholdWireInput, htag, hcode,
      hmembershipCode, hstoredLength]
  have hsourceBits :
      normalizedCircuitThresholdWireBits inputLength summaries membership ≤
        normalizedCircuitResourceFamilyBits inputLength summary := by
    rw [normalizedCircuitResourceFamilyBits,
      normalizedCircuitResourceFamilySourceBits,
      if_neg htagNonzero, hsummariesView, hmembershipView]
    exact Nat.le_max_right _ _
  have hsource :=
    run_bits_mono
      (run_normalizedCircuitThresholdWireProgram
        inputLength summaries membership hlength)
      hsourceBits
  have hinput :
      natBitLength
          (Nat.pair inputLength
            (Nat.pair 1
              (normalizedCircuitThresholdWireInput summaries membership))) ≤
        normalizedCircuitResourceFamilyBits inputLength summary := by
    rw [← hprepare]
    exact Nat.le_max_left _ _
  have houtput := run_output_bounded hsource
  have hrun :=
    run_taggedProgramChoice_nonzero normalizedCircuitSymmetricWireProgram
      normalizedCircuitThresholdWireProgram inputLength 1
      (normalizedCircuitThresholdWireInput summaries membership)
      (normalizedCircuitResourceFamilyBits inputLength summary)
      (normalizedCircuitThresholdWireFuel inputLength summaries membership)
      (supportedWeights
        (normalizedGateWireMetrics summaries) membership).sum
      (by omega) hinput hsource houtput
  simpa [normalizedCircuitResourceFamilyProgram,
    normalizedCircuitResourceFamilyFuel, htag, hsummariesView,
    hmembershipView, normalizedCircuitResourceMetric, hprepare] using hrun

-- The family dispatcher is a verified stage boundary.  Downstream composition
-- depends on its contract, never on either expanded branch controller.
attribute [irreducible] normalizedCircuitResourceFamilyProgram

/-- The unique fixed program from a validated normalized-circuit summary to its
exact physical wire count. -/
def normalizedCircuitResourceProgram : NPOracleProgram :=
  linkPrograms normalizedCircuitResourcePrepareProgram
    normalizedCircuitResourceFamilyProgram

@[simp] theorem normalizedCircuitResourceProgram_oracleFree :
    OracleFree normalizedCircuitResourceProgram := by
  exact oracleFree_linkPrograms
    normalizedCircuitResourcePrepareProgram_oracleFree
    normalizedCircuitResourceFamilyProgram_oracleFree

def normalizedCircuitResourceBits
    (inputLength summary : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (normalizedCircuitResourcePrepareBits inputLength summary)
      (normalizedCircuitResourceFamilyBits inputLength summary)

def normalizedCircuitResourceFuel
    (inputLength summary : ℕ) : ℕ :=
  linkFuel normalizedCircuitResourceFamilyProgram
    normalizedCircuitResourcePrepareFuel
    (normalizedCircuitResourceFamilyFuel inputLength summary)

private theorem normalizedCircuitResource_prepareBits_le
    (inputLength summary : ℕ) :
    normalizedCircuitResourcePrepareBits inputLength summary ≤
      normalizedCircuitResourceBits inputLength summary :=
  (Nat.le_max_left _ _).trans <|
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

private theorem normalizedCircuitResource_familyBits_le
    (inputLength summary : ℕ) :
    normalizedCircuitResourceFamilyBits inputLength summary ≤
      normalizedCircuitResourceBits inputLength summary :=
  (Nat.le_max_right _ _).trans <|
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

theorem run_normalizedCircuitResourceProgram_symmetric
    (inputLength summary : ℕ) (summaries : List ℕ)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 1)
    (hsummaries :
      decodeBalancedList
        (normalizedCircuitResourceBottomSummariesCode summary) =
          some summaries) :
    runNPOracleProgram normalizedCircuitResourceProgram
        (normalizedCircuitResourceBits inputLength summary)
        (normalizedCircuitResourceFuel inputLength summary)
        (initialNPOracleState inputLength summary) =
      some (normalizedCircuitResourceMetric summary) := by
  have hpositive :
      1 ≤ normalizedCircuitResourceBits inputLength summary :=
    Nat.le_max_left _ _
  have hlength :
      natBitLength inputLength ≤
        normalizedCircuitResourceBits inputLength summary :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hprepare :=
    run_bits_mono
      (run_normalizedCircuitResourcePrepareProgram inputLength summary)
      (normalizedCircuitResource_prepareBits_le inputLength summary)
  have hfamilyRun :=
    run_bits_mono
      (run_normalizedCircuitResourceFamilyProgram_symmetric
        inputLength summary summaries hfamily hsummaries)
      (normalizedCircuitResource_familyBits_le inputLength summary)
  simpa only [normalizedCircuitResourceProgram,
    normalizedCircuitResourceFuel] using
      (run_linkPrograms hpositive hlength hprepare hfamilyRun)

theorem run_normalizedCircuitResourceProgram_threshold
    (inputLength summary : ℕ) (summaries : List ℕ)
    (membership : List Bool)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 2)
    (hsummaries :
      decodeBalancedList
        (normalizedCircuitResourceBottomSummariesCode summary) =
          some summaries)
    (hmembership :
      decodeBoolList
        (normalizedCircuitResourceThresholdMembershipCode summary) =
          some membership)
    (hstoredLength :
      normalizedCircuitResourceBottomLength summary = summaries.length)
    (hlength : summaries.length = membership.length) :
    runNPOracleProgram normalizedCircuitResourceProgram
        (normalizedCircuitResourceBits inputLength summary)
        (normalizedCircuitResourceFuel inputLength summary)
        (initialNPOracleState inputLength summary) =
      some (normalizedCircuitResourceMetric summary) := by
  have hpositive :
      1 ≤ normalizedCircuitResourceBits inputLength summary :=
    Nat.le_max_left _ _
  have hinputLength :
      natBitLength inputLength ≤
        normalizedCircuitResourceBits inputLength summary :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hprepare :=
    run_bits_mono
      (run_normalizedCircuitResourcePrepareProgram inputLength summary)
      (normalizedCircuitResource_prepareBits_le inputLength summary)
  have hfamilyRun :=
    run_bits_mono
      (run_normalizedCircuitResourceFamilyProgram_threshold
        inputLength summary summaries membership hfamily hsummaries
        hmembership hstoredLength hlength)
      (normalizedCircuitResource_familyBits_le inputLength summary)
  simpa only [normalizedCircuitResourceProgram,
    normalizedCircuitResourceFuel] using
      (run_linkPrograms hpositive hinputLength hprepare hfamilyRun)

end NearCubicWires.CanonicalNormalizedCircuitResourceProgram
