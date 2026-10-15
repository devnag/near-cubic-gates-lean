import Proof.MachineModel.CanonicalBalancedLengthProgram
import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalNormalizedCircuitValidationProgram
import Proof.MachineModel.CanonicalNormalizedCircuitResourceProgram
import Proof.MachineModel.CanonicalSupplierCompressedGateProgram

/-!
# Exact description size from validated normalized-circuit summaries

The normalized-circuit validator is the sole syntax boundary.  Its gate summary
retains the threshold, the weights selected by the support mask, and the exact
support count.  Validation also proves every omitted weight is zero, so this
module restores their one-bit charge without parsing the circuit again.
-/

namespace NearCubicWires.CanonicalNormalizedCircuitDescriptionProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNormalizedCircuitValidationProgram
open NearCubicWires.CanonicalNormalizedCircuitResourceProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalSupportedGateRelationProgram
open NearCubicWires.CanonicalSupplierCompressedGateProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

private theorem descriptionValueBits
    {values : List ℕ} {value : ℕ} (hvalue : value ∈ values) :
    natBitLength value ≤
      (values.map natBitLength).foldr max 1 := by
  induction values with
  | nil => simp at hvalue
  | cons head tail ih =>
      simp only [List.mem_cons] at hvalue
      simp only [List.map_cons, List.foldr_cons]
      rcases hvalue with rfl | htail
      · exact le_max_left _ _
      · exact (ih htail).trans (le_max_right _ _)

private theorem descriptionMemberLeFoldrMax
    {values : List ℕ} {value : ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max 1 := by
  induction values with
  | nil => simp at hvalue
  | cons head tail ih =>
      simp only [List.mem_cons] at hvalue
      simp only [List.foldr_cons]
      rcases hvalue with rfl | htail
      · exact le_max_left _ _
      · exact (ih htail).trans (le_max_right _ _)

/-! ## Canonical signed-integer bit charge -/

def canonicalIntMagnitudeCode (code : ℕ) : ℕ :=
  (Nat.unpair code).2

def canonicalIntMagnitudeBits (code : ℕ) : List ℕ :=
  (decodeBalancedList (canonicalIntMagnitudeCode code)).getD []

def canonicalIntDescriptionMetric (code : ℕ) : ℕ :=
  max 1 (canonicalIntMagnitudeBits code).length

def canonicalIntMagnitudeProjectionProgram : NPOracleProgram :=
  [.unpairRight 0 0 1, .halt 0]

private def canonicalIntMagnitudeProjectionBits (code : ℕ) : ℕ :=
  max (natBitLength code) (natBitLength (canonicalIntMagnitudeCode code))

private theorem canonicalIntMagnitudeProjectionProgram_oracleFree :
    OracleFree canonicalIntMagnitudeProjectionProgram := by
  rfl

private theorem run_canonicalIntMagnitudeProjectionProgram
    (inputLength code : ℕ) :
    runNPOracleProgram canonicalIntMagnitudeProjectionProgram
        (canonicalIntMagnitudeProjectionBits code) 2
        (initialNPOracleState inputLength code) =
      some (canonicalIntMagnitudeCode code) := by
  have houtput :
      natBitLength (canonicalIntMagnitudeCode code) ≤
        canonicalIntMagnitudeProjectionBits code :=
    Nat.le_max_right _ _
  rw [show 2 = 1 + 1 by rfl]
  rw [run_unpairRight_instruction (value := canonicalIntMagnitudeCode code)
    (by rfl) rfl (by simp [initialNPOracleState,
      canonicalIntMagnitudeCode]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def canonicalPositiveLengthProgram : NPOracleProgram :=
  [ .branchZero 0 2 1
  , .halt 0
  , .set 0 1 3
  , .halt 0
  ]

def canonicalPositiveLengthFuel (length : ℕ) : ℕ :=
  if length = 0 then 3 else 2

private def canonicalPositiveLengthBits (length : ℕ) : ℕ :=
  max (natBitLength length) (natBitLength (max 1 length))

private theorem canonicalPositiveLengthProgram_oracleFree :
    OracleFree canonicalPositiveLengthProgram := by
  rfl

private theorem run_canonicalPositiveLengthProgram
    (inputLength length : ℕ) :
    runNPOracleProgram canonicalPositiveLengthProgram
        (canonicalPositiveLengthBits length)
        (canonicalPositiveLengthFuel length)
        (initialNPOracleState inputLength length) =
      some (max 1 length) := by
  have hlength :
      natBitLength length ≤ canonicalPositiveLengthBits length :=
    Nat.le_max_left _ _
  have houtput :
      natBitLength (max 1 length) ≤ canonicalPositiveLengthBits length :=
    Nat.le_max_right _ _
  by_cases hzero : length = 0
  · subst length
    simp [canonicalPositiveLengthProgram, canonicalPositiveLengthFuel,
      runNPOracleProgram, initialNPOracleState, NPOracleState.boundedWrite,
      canonicalPositiveLengthBits]
  · simp [canonicalPositiveLengthProgram, canonicalPositiveLengthFuel,
      runNPOracleProgram, initialNPOracleState,
      hzero, hlength, Nat.one_le_iff_ne_zero.mpr hzero]

def canonicalIntDescriptionProgram : NPOracleProgram :=
  linkPrograms canonicalIntMagnitudeProjectionProgram <|
    linkPrograms balancedLengthProgram canonicalPositiveLengthProgram

@[simp] theorem canonicalIntDescriptionProgram_oracleFree :
    OracleFree canonicalIntDescriptionProgram := by
  exact oracleFree_linkPrograms canonicalIntMagnitudeProjectionProgram_oracleFree <|
    oracleFree_linkPrograms balancedLengthProgram_oracleFree
      canonicalPositiveLengthProgram_oracleFree

def canonicalIntDescriptionBits (inputLength code : ℕ) : ℕ :=
  let magnitudeBits := canonicalIntMagnitudeBits code
  max 1 <| max (natBitLength inputLength) <|
    max (canonicalIntMagnitudeProjectionBits code) <|
      max (balancedLengthBits inputLength magnitudeBits)
        (canonicalPositiveLengthBits magnitudeBits.length)

def canonicalIntDescriptionFuel (code : ℕ) : ℕ :=
  let magnitudeBits := canonicalIntMagnitudeBits code
  linkFuel
    (linkPrograms balancedLengthProgram canonicalPositiveLengthProgram) 2 <|
      linkFuel canonicalPositiveLengthProgram
        (balancedLengthFuel magnitudeBits)
        (canonicalPositiveLengthFuel magnitudeBits.length)

set_option maxRecDepth 4000 in
theorem run_canonicalIntDescriptionProgram
    (inputLength : ℕ) (value : ℤ) :
    runNPOracleProgram canonicalIntDescriptionProgram
        (canonicalIntDescriptionBits inputLength (encodeInt value))
        (canonicalIntDescriptionFuel (encodeInt value))
        (initialNPOracleState inputLength (encodeInt value)) =
      some (canonicalIntDescriptionMetric (encodeInt value)) := by
  let code := encodeInt value
  let bits := value.natAbs.bits.map boolCode
  have hmagnitude : canonicalIntMagnitudeCode code = encodeBalancedList bits := by
    simp [code, bits, canonicalIntMagnitudeCode, encodeInt, encodeNat,
      encodeBits, encodeBoolList]
  have hdecoded : canonicalIntMagnitudeBits code = bits := by
    simp [canonicalIntMagnitudeBits, hmagnitude]
  let maximumBits := canonicalIntDescriptionBits inputLength code
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hprojectionBits :
      canonicalIntMagnitudeProjectionBits code ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlengthBits :
      balancedLengthBits inputLength bits ≤ maximumBits := by
    simp only [maximumBits, canonicalIntDescriptionBits, hdecoded]
    exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hfinalBits :
      canonicalPositiveLengthBits bits.length ≤ maximumBits := by
    simp only [maximumBits, canonicalIntDescriptionBits, hdecoded]
    exact (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprojection := run_bits_mono
    (run_canonicalIntMagnitudeProjectionProgram inputLength code)
    hprojectionBits
  have hlength := run_bits_mono
    (run_balancedLengthProgram inputLength bits) hlengthBits
  have hfinal := run_bits_mono
    (run_canonicalPositiveLengthProgram inputLength bits.length) hfinalBits
  have htail := run_linkPrograms hpositive hinputLength hlength hfinal
  rw [hmagnitude] at hprojection
  have hrun := run_linkPrograms hpositive hinputLength hprojection htail
  have hmetric :
      canonicalIntDescriptionMetric code = max 1 bits.length := by
    simp only [canonicalIntDescriptionMetric, hdecoded]
  simpa only [canonicalIntDescriptionProgram, canonicalIntDescriptionFuel,
    hdecoded, hmagnitude, code, bits, hmetric] using hrun

theorem canonicalIntDescriptionMetric_encode (value : ℤ) :
    canonicalIntDescriptionMetric (encodeInt value) = intBitLength value := by
  simp only [canonicalIntDescriptionMetric, canonicalIntMagnitudeBits,
    canonicalIntMagnitudeCode, encodeInt, encodeNat, encodeBits,
    encodeBoolList, Nat.unpair_pair, decodeBalancedList_encode,
    Option.getD_some, List.length_map, intBitLength]
  rw [Nat.size_eq_bits_len]
  by_cases hzero : value.natAbs = 0
  · simp [hzero]
  · have hpositive : 0 < value.natAbs := Nat.zero_lt_of_ne_zero hzero
    have hsize :
        value.natAbs.size = Nat.log 2 value.natAbs + 1 := by
      apply Nat.le_antisymm
      · apply Nat.size_le.mpr
        exact Nat.lt_pow_succ_log_self (b := 2) (by omega) value.natAbs
      · have hlog : Nat.log 2 value.natAbs < value.natAbs.size :=
          Nat.log_lt_of_lt_pow hzero (Nat.lt_size_self value.natAbs)
        omega
    rw [hsize]
    exact max_eq_right (by omega)

/-! ## Exact sum over a validated integer-code tree -/

def canonicalIntDescriptionRequestOutput (request : ℕ) : ℕ :=
  canonicalIntDescriptionMetric (Nat.unpair request).2

def canonicalIntDescriptionMetrics (values : List ℤ) : List ℕ :=
  values.map fun value => canonicalIntDescriptionMetric (encodeInt value)

private def canonicalIntDescriptionMapRawOutput
    (inputLength : ℕ) (values : List ℤ) : ℕ :=
  balancedValidationMapOutput inputLength
    (encodeBalancedList (values.map encodeInt))
    canonicalIntDescriptionRequestOutput

private theorem canonicalIntDescriptionMapRawOutput_left
    (inputLength : ℕ) (values : List ℤ) :
    (Nat.unpair
      (canonicalIntDescriptionMapRawOutput inputLength values)).1 =
        encodeBalancedList (canonicalIntDescriptionMetrics values) := by
  simp [canonicalIntDescriptionMapRawOutput, balancedValidationMapOutput,
    balancedValidationMapOutputs, balancedValidationMapRequests,
    balancedValidationMapCodes, canonicalIntDescriptionRequestOutput,
    canonicalIntDescriptionMetrics, nativeInputRequest,
    Function.comp_def]

def canonicalIntDescriptionMapProjectionProgram : NPOracleProgram :=
  [.unpairLeft 0 0 1, .halt 0]

private theorem canonicalIntDescriptionMapProjectionProgram_oracleFree :
    OracleFree canonicalIntDescriptionMapProjectionProgram := by
  rfl

private def canonicalIntDescriptionMapProjectionBits
    (inputLength : ℕ) (values : List ℤ) : ℕ :=
  max
    (natBitLength (canonicalIntDescriptionMapRawOutput inputLength values))
    (natBitLength (encodeBalancedList
      (canonicalIntDescriptionMetrics values)))

private theorem run_canonicalIntDescriptionMapProjectionProgram
    (inputLength : ℕ) (values : List ℤ) :
    runNPOracleProgram canonicalIntDescriptionMapProjectionProgram
        (canonicalIntDescriptionMapProjectionBits inputLength values) 2
        (initialNPOracleState inputLength
          (canonicalIntDescriptionMapRawOutput inputLength values)) =
      some (encodeBalancedList (canonicalIntDescriptionMetrics values)) := by
  have houtput :
      natBitLength (encodeBalancedList (canonicalIntDescriptionMetrics values)) ≤
        canonicalIntDescriptionMapProjectionBits inputLength values :=
    Nat.le_max_right _ _
  rw [show 2 = 1 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := encodeBalancedList (canonicalIntDescriptionMetrics values))
    (by rfl) rfl
    (by simp [initialNPOracleState,
      canonicalIntDescriptionMapRawOutput_left]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def canonicalIntDescriptionMapProgram : NPOracleProgram :=
  linkPrograms
    (balancedValidationMapProgram canonicalIntDescriptionProgram)
    canonicalIntDescriptionMapProjectionProgram

@[simp] theorem canonicalIntDescriptionMapProgram_oracleFree :
    OracleFree canonicalIntDescriptionMapProgram := by
  exact oracleFree_linkPrograms
    (balancedValidationMapProgram_oracleFree canonicalIntDescriptionProgram
      canonicalIntDescriptionProgram_oracleFree)
    canonicalIntDescriptionMapProjectionProgram_oracleFree

def canonicalIntDescriptionMapBits
    (inputLength : ℕ) (values : List ℤ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max
      (balancedValidationMapBits
        (fun request => canonicalIntDescriptionBits
          (Nat.unpair request).1 (Nat.unpair request).2)
        canonicalIntDescriptionRequestOutput inputLength
        (encodeBalancedList (values.map encodeInt)))
      (canonicalIntDescriptionMapProjectionBits inputLength values)

def canonicalIntDescriptionMapFuel
    (inputLength : ℕ) (values : List ℤ) : ℕ :=
  linkFuel canonicalIntDescriptionMapProjectionProgram
    (balancedValidationMapFuel canonicalIntDescriptionProgram
      (fun request => canonicalIntDescriptionFuel (Nat.unpair request).2)
      inputLength (encodeBalancedList (values.map encodeInt))) 2

private theorem run_canonicalIntDescriptionValidationMapProgram
    (inputLength : ℕ) (values : List ℤ) :
    runNPOracleProgram
        (balancedValidationMapProgram canonicalIntDescriptionProgram)
        (balancedValidationMapBits
          (fun request => canonicalIntDescriptionBits
            (Nat.unpair request).1 (Nat.unpair request).2)
          canonicalIntDescriptionRequestOutput inputLength
          (encodeBalancedList (values.map encodeInt)))
        (balancedValidationMapFuel canonicalIntDescriptionProgram
          (fun request => canonicalIntDescriptionFuel (Nat.unpair request).2)
          inputLength (encodeBalancedList (values.map encodeInt)))
        (initialNPOracleState inputLength
          (encodeBalancedList (values.map encodeInt))) =
      some (canonicalIntDescriptionMapRawOutput inputLength values) := by
  apply run_balancedValidationMapProgram
  intro request hrequest
  simp only [balancedValidationMapRequests, balancedValidationMapCodes,
    decodeBalancedList_encode, Option.getD_some, List.map_map, List.mem_map,
    Function.comp_apply, nativeInputRequest] at hrequest
  obtain ⟨value, hvalue, rfl⟩ := hrequest
  simpa only [canonicalIntDescriptionRequestOutput, Nat.unpair_pair] using
    (run_canonicalIntDescriptionProgram inputLength value)

theorem run_canonicalIntDescriptionMapProgram
    (inputLength : ℕ) (values : List ℤ) :
    runNPOracleProgram canonicalIntDescriptionMapProgram
        (canonicalIntDescriptionMapBits inputLength values)
        (canonicalIntDescriptionMapFuel inputLength values)
        (initialNPOracleState inputLength
          (encodeBalancedList (values.map encodeInt))) =
      some (encodeBalancedList (canonicalIntDescriptionMetrics values)) := by
  let maximumBits := canonicalIntDescriptionMapBits inputLength values
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hmapBits :
      balancedValidationMapBits
          (fun request => canonicalIntDescriptionBits
            (Nat.unpair request).1 (Nat.unpair request).2)
          canonicalIntDescriptionRequestOutput inputLength
          (encodeBalancedList (values.map encodeInt)) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprojectionBits :
      canonicalIntDescriptionMapProjectionBits inputLength values ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hmap := run_bits_mono
    (run_canonicalIntDescriptionValidationMapProgram inputLength values)
    hmapBits
  have hprojection := run_bits_mono
    (run_canonicalIntDescriptionMapProjectionProgram inputLength values)
    hprojectionBits
  simpa only [maximumBits, canonicalIntDescriptionMapProgram,
    canonicalIntDescriptionMapFuel] using
      (run_linkPrograms hpositive hinputLength hmap hprojection)

attribute [irreducible] canonicalIntDescriptionMapProgram

def canonicalIntDescriptionSumProgram : NPOracleProgram :=
  balancedNatSumAfterProgram canonicalIntDescriptionMapProgram

@[simp] theorem canonicalIntDescriptionSumProgram_oracleFree :
    OracleFree canonicalIntDescriptionSumProgram := by
  exact balancedNatSumAfterProgram_oracleFree _
    canonicalIntDescriptionMapProgram_oracleFree

def canonicalIntDescriptionSumBits
    (inputLength : ℕ) (values : List ℤ) : ℕ :=
  balancedNatSumAfterBits inputLength
    (canonicalIntDescriptionMapBits inputLength values)
    (canonicalIntDescriptionMetrics values)

def canonicalIntDescriptionSumFuel
    (inputLength : ℕ) (values : List ℤ) : ℕ :=
  balancedNatSumAfterFuel
    (canonicalIntDescriptionMapFuel inputLength values)
    (canonicalIntDescriptionMetrics values)

theorem run_canonicalIntDescriptionSumProgram
    (inputLength : ℕ) (values : List ℤ) :
    runNPOracleProgram canonicalIntDescriptionSumProgram
        (canonicalIntDescriptionSumBits inputLength values)
        (canonicalIntDescriptionSumFuel inputLength values)
        (initialNPOracleState inputLength
          (encodeBalancedList (values.map encodeInt))) =
      some (values.map intBitLength).sum := by
  have hrun := run_balancedNatSumAfterProgram
    canonicalIntDescriptionMapProgram inputLength
    (encodeBalancedList (values.map encodeInt))
    (canonicalIntDescriptionMapBits inputLength values)
    (canonicalIntDescriptionMapFuel inputLength values)
    (canonicalIntDescriptionMetrics values)
    (run_canonicalIntDescriptionMapProgram inputLength values)
  simpa [canonicalIntDescriptionSumProgram,
    canonicalIntDescriptionSumBits, canonicalIntDescriptionSumFuel,
    canonicalIntDescriptionMetrics, canonicalIntDescriptionMetric_encode]
    using hrun

-- Downstream links use these verified contracts, never their expanded bodies.
attribute [irreducible] canonicalIntDescriptionProgram
  canonicalIntDescriptionSumProgram

/-! ## One validated normalized gate -/

def normalizedGateDescriptionThresholdCode (summary : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair summary).2).1

def normalizedGateDescriptionSelectedWeightsCode (summary : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair summary).2).2).1

def normalizedGateDescriptionSupportCount (summary : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair (Nat.unpair (Nat.unpair summary).2).2).2).1

def normalizedGateDescriptionThreshold (summary : ℕ) : ℤ :=
  (decodeInt (normalizedGateDescriptionThresholdCode summary)).getD 0

def normalizedGateDescriptionSelectedWeights (summary : ℕ) : List ℤ :=
  (decodeIntList
    (normalizedGateDescriptionSelectedWeightsCode summary)).getD []

def normalizedGateDescriptionMetric (inputLength summary : ℕ) : ℕ :=
  intBitLength (normalizedGateDescriptionThreshold summary) +
    ((normalizedGateDescriptionSelectedWeights summary).map intBitLength).sum +
    (inputLength - normalizedGateDescriptionSupportCount summary) +
    inputLength

private def normalizedGateDescriptionPrepareContext (summary : ℕ) : ℕ :=
  Nat.pair (normalizedGateDescriptionSelectedWeightsCode summary)
    (normalizedGateDescriptionSupportCount summary)

private def normalizedGateDescriptionPrepareOutput (summary : ℕ) : ℕ :=
  Nat.pair (normalizedGateDescriptionThresholdCode summary)
    (normalizedGateDescriptionPrepareContext summary)

def normalizedGateDescriptionPrepareProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 3 2
  , .unpairRight 2 4 3
  , .unpairLeft 4 5 4
  , .unpairRight 4 6 5
  , .unpairLeft 6 7 6
  , .pair 5 7 8 7
  , .pair 3 8 0 8
  , .halt 0
  ]

private theorem normalizedGateDescriptionPrepareProgram_oracleFree :
    OracleFree normalizedGateDescriptionPrepareProgram := by
  rfl

private def normalizedGateDescriptionPrepareValues
    (inputLength summary : ℕ) : List ℕ :=
  [ inputLength, summary, (Nat.unpair summary).2,
    normalizedGateDescriptionThresholdCode summary,
    (Nat.unpair (Nat.unpair summary).2).2,
    normalizedGateDescriptionSelectedWeightsCode summary,
    (Nat.unpair (Nat.unpair (Nat.unpair summary).2).2).2,
    normalizedGateDescriptionSupportCount summary,
    normalizedGateDescriptionPrepareContext summary,
    normalizedGateDescriptionPrepareOutput summary ]

private def normalizedGateDescriptionPrepareBits
    (inputLength summary : ℕ) : ℕ :=
  (normalizedGateDescriptionPrepareValues inputLength summary).map natBitLength
    |>.foldr max 1

private theorem run_normalizedGateDescriptionPrepareProgram
    (inputLength summary : ℕ) :
    runNPOracleProgram normalizedGateDescriptionPrepareProgram
        (normalizedGateDescriptionPrepareBits inputLength summary) 9
        (initialNPOracleState inputLength summary) =
      some (normalizedGateDescriptionPrepareOutput summary) := by
  have hbits :
      ∀ value ∈ normalizedGateDescriptionPrepareValues inputLength summary,
        natBitLength value ≤
          normalizedGateDescriptionPrepareBits inputLength summary := by
    intro value hvalue
    exact descriptionValueBits hvalue
  simp [normalizedGateDescriptionPrepareProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    normalizedGateDescriptionPrepareValues, hbits,
    normalizedGateDescriptionPrepareOutput,
    normalizedGateDescriptionPrepareContext,
    normalizedGateDescriptionThresholdCode,
    normalizedGateDescriptionSelectedWeightsCode,
    normalizedGateDescriptionSupportCount]

private def normalizedGateDescriptionSecondPrepareOutput
    (thresholdBits : ℕ) (summary : ℕ) : ℕ :=
  Nat.pair (normalizedGateDescriptionSelectedWeightsCode summary)
    (Nat.pair thresholdBits
      (normalizedGateDescriptionSupportCount summary))

def normalizedGateDescriptionSecondPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 5 6 5
  , .pair 4 6 0 6
  , .halt 0
  ]

private theorem normalizedGateDescriptionSecondPrepareProgram_oracleFree :
    OracleFree normalizedGateDescriptionSecondPrepareProgram := by
  rfl

private def normalizedGateDescriptionSecondPrepareValues
    (inputLength thresholdBits summary : ℕ) : List ℕ :=
  [ inputLength,
    Nat.pair thresholdBits (normalizedGateDescriptionPrepareContext summary),
    thresholdBits, normalizedGateDescriptionPrepareContext summary,
    normalizedGateDescriptionSelectedWeightsCode summary,
    normalizedGateDescriptionSupportCount summary,
    Nat.pair thresholdBits (normalizedGateDescriptionSupportCount summary),
    normalizedGateDescriptionSecondPrepareOutput thresholdBits summary ]

private def normalizedGateDescriptionSecondPrepareBits
    (inputLength thresholdBits summary : ℕ) : ℕ :=
  (normalizedGateDescriptionSecondPrepareValues inputLength thresholdBits summary).map
      natBitLength |>.foldr max 1

private theorem run_normalizedGateDescriptionSecondPrepareProgram
    (inputLength thresholdBits summary : ℕ) :
    runNPOracleProgram normalizedGateDescriptionSecondPrepareProgram
        (normalizedGateDescriptionSecondPrepareBits
          inputLength thresholdBits summary) 7
        (initialNPOracleState inputLength
          (Nat.pair thresholdBits
            (normalizedGateDescriptionPrepareContext summary))) =
      some (normalizedGateDescriptionSecondPrepareOutput thresholdBits summary) := by
  have hbits :
      ∀ value ∈ normalizedGateDescriptionSecondPrepareValues
          inputLength thresholdBits summary,
        natBitLength value ≤
          normalizedGateDescriptionSecondPrepareBits
            inputLength thresholdBits summary := by
    intro value hvalue
    exact descriptionValueBits hvalue
  simp [normalizedGateDescriptionSecondPrepareProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    normalizedGateDescriptionSecondPrepareValues, hbits,
    normalizedGateDescriptionSecondPrepareOutput,
    normalizedGateDescriptionPrepareContext]

private def normalizedGateDescriptionFinalOutput
    (inputLength weightBits thresholdBits supportCount : ℕ) : ℕ :=
  thresholdBits + weightBits + (inputLength - supportCount) + inputLength

def normalizedGateDescriptionFinalProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .subtract 1 5 6 5
  , .add 4 2 7 6
  , .add 7 6 8 7
  , .add 8 1 0 8
  , .halt 0
  ]

private theorem normalizedGateDescriptionFinalProgram_oracleFree :
    OracleFree normalizedGateDescriptionFinalProgram := by
  rfl

private def normalizedGateDescriptionFinalValues
    (inputLength weightBits thresholdBits supportCount : ℕ) : List ℕ :=
  [ inputLength, Nat.pair weightBits (Nat.pair thresholdBits supportCount),
    weightBits, Nat.pair thresholdBits supportCount, thresholdBits,
    supportCount, inputLength - supportCount,
    thresholdBits + weightBits,
    thresholdBits + weightBits + (inputLength - supportCount),
    normalizedGateDescriptionFinalOutput inputLength weightBits thresholdBits
      supportCount ]

private def normalizedGateDescriptionFinalBits
    (inputLength weightBits thresholdBits supportCount : ℕ) : ℕ :=
  (normalizedGateDescriptionFinalValues inputLength weightBits thresholdBits
    supportCount).map natBitLength |>.foldr max 1

private theorem run_normalizedGateDescriptionFinalProgram
    (inputLength weightBits thresholdBits supportCount : ℕ) :
    runNPOracleProgram normalizedGateDescriptionFinalProgram
        (normalizedGateDescriptionFinalBits inputLength weightBits thresholdBits
          supportCount) 9
        (initialNPOracleState inputLength
          (Nat.pair weightBits (Nat.pair thresholdBits supportCount))) =
      some (normalizedGateDescriptionFinalOutput inputLength weightBits
        thresholdBits supportCount) := by
  have hbits :
      ∀ value ∈ normalizedGateDescriptionFinalValues inputLength weightBits
          thresholdBits supportCount,
        natBitLength value ≤ normalizedGateDescriptionFinalBits inputLength
          weightBits thresholdBits supportCount := by
    intro value hvalue
    exact descriptionValueBits hvalue
  simp [normalizedGateDescriptionFinalProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    normalizedGateDescriptionFinalValues, hbits,
    normalizedGateDescriptionFinalOutput, Nat.add_assoc]

def normalizedGateDescriptionThresholdStageProgram : NPOracleProgram :=
  linkPrograms normalizedGateDescriptionPrepareProgram
    (preserveRightProgram canonicalIntDescriptionProgram)

private theorem normalizedGateDescriptionThresholdStageProgram_oracleFree :
    OracleFree normalizedGateDescriptionThresholdStageProgram := by
  exact oracleFree_linkPrograms normalizedGateDescriptionPrepareProgram_oracleFree
    (preserveRightProgram_oracleFree canonicalIntDescriptionProgram
      canonicalIntDescriptionProgram_oracleFree)

private def normalizedGateDescriptionThresholdStageBitValues
    (inputLength summary : ℕ) : List ℕ :=
  let threshold := normalizedGateDescriptionThreshold summary
  [ 1, natBitLength inputLength,
    normalizedGateDescriptionPrepareBits inputLength summary,
    preserveRightBits
        (canonicalIntDescriptionBits inputLength (encodeInt threshold))
        (normalizedGateDescriptionThresholdCode summary)
        (normalizedGateDescriptionPrepareContext summary)
        (intBitLength threshold) ]

private def normalizedGateDescriptionThresholdStageBits
    (inputLength summary : ℕ) : ℕ :=
  (normalizedGateDescriptionThresholdStageBitValues inputLength summary).foldr
    max 1

def normalizedGateDescriptionThresholdStageFuel
    (summary : ℕ) : ℕ :=
  let threshold := normalizedGateDescriptionThreshold summary
  linkFuel (preserveRightProgram canonicalIntDescriptionProgram) 9 <|
    preserveRightFuel (canonicalIntDescriptionFuel (encodeInt threshold))

set_option maxHeartbeats 1000000 in
-- This proof treats the verified integer reducer opaquely across one link.
private theorem run_normalizedGateDescriptionThresholdStageProgram
    (inputLength summary : ℕ) (threshold : ℤ)
    (hthreshold : normalizedGateDescriptionThresholdCode summary =
      encodeInt threshold) :
    runNPOracleProgram normalizedGateDescriptionThresholdStageProgram
        (normalizedGateDescriptionThresholdStageBits inputLength summary)
        (normalizedGateDescriptionThresholdStageFuel summary)
        (initialNPOracleState inputLength summary) =
      some (Nat.pair (intBitLength threshold)
        (normalizedGateDescriptionPrepareContext summary)) := by
  have hthresholdView : normalizedGateDescriptionThreshold summary = threshold := by
    simp [normalizedGateDescriptionThreshold, hthreshold]
  let maximumBits :=
    normalizedGateDescriptionThresholdStageBits inputLength summary
  have hbound :
      ∀ value ∈ normalizedGateDescriptionThresholdStageBitValues
          inputLength summary,
        value ≤ maximumBits := by
    intro value hvalue
    exact descriptionMemberLeFoldrMax hvalue
  have hpositive : 1 ≤ maximumBits :=
    hbound 1 (by simp [normalizedGateDescriptionThresholdStageBitValues])
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    hbound _ (by simp [normalizedGateDescriptionThresholdStageBitValues])
  have hprepareBits :
      normalizedGateDescriptionPrepareBits inputLength summary ≤ maximumBits :=
    hbound _ (by simp [normalizedGateDescriptionThresholdStageBitValues])
  have hcallBits :
      preserveRightBits
          (canonicalIntDescriptionBits inputLength (encodeInt threshold))
          (normalizedGateDescriptionThresholdCode summary)
          (normalizedGateDescriptionPrepareContext summary)
          (intBitLength threshold) ≤ maximumBits := by
    apply hbound
    simp [normalizedGateDescriptionThresholdStageBitValues, hthresholdView]
  have hprepare := run_bits_mono
    (run_normalizedGateDescriptionPrepareProgram inputLength summary)
    hprepareBits
  simp only [normalizedGateDescriptionPrepareOutput, hthreshold] at hprepare
  have hthresholdRun := run_canonicalIntDescriptionProgram inputLength threshold
  rw [canonicalIntDescriptionMetric_encode] at hthresholdRun
  have hpreservedBase :=
    run_preserveRightProgram canonicalIntDescriptionProgram inputLength
      (canonicalIntDescriptionBits inputLength (encodeInt threshold))
      (canonicalIntDescriptionFuel (encodeInt threshold))
      (encodeInt threshold) (normalizedGateDescriptionPrepareContext summary)
      (intBitLength threshold) hthresholdRun
  have hpreserved := @run_bits_mono
    (preserveRightProgram canonicalIntDescriptionProgram)
    (preserveRightBits
      (canonicalIntDescriptionBits inputLength (encodeInt threshold))
      (encodeInt threshold)
      (normalizedGateDescriptionPrepareContext summary)
      (intBitLength threshold)) maximumBits
    (preserveRightFuel
      (canonicalIntDescriptionFuel (encodeInt threshold)))
    (initialNPOracleState inputLength
      (Nat.pair (encodeInt threshold)
        (normalizedGateDescriptionPrepareContext summary)))
    (Nat.pair (intBitLength threshold)
      (normalizedGateDescriptionPrepareContext summary))
    hpreservedBase (by simpa only [hthreshold] using hcallBits)
  have hfuel :
      normalizedGateDescriptionThresholdStageFuel summary =
        linkFuel (preserveRightProgram canonicalIntDescriptionProgram) 9
          (preserveRightFuel
            (canonicalIntDescriptionFuel (encodeInt threshold))) := by
    simp only [normalizedGateDescriptionThresholdStageFuel, hthresholdView]
  rw [normalizedGateDescriptionThresholdStageProgram, hfuel]
  exact @run_linkPrograms normalizedGateDescriptionPrepareProgram
    (preserveRightProgram canonicalIntDescriptionProgram) maximumBits
    inputLength summary 9
    (Nat.pair (encodeInt threshold)
      (normalizedGateDescriptionPrepareContext summary))
    (preserveRightFuel
      (canonicalIntDescriptionFuel (encodeInt threshold)))
    (Nat.pair (intBitLength threshold)
      (normalizedGateDescriptionPrepareContext summary))
    hpositive hinputLength hprepare hpreserved

attribute [irreducible] normalizedGateDescriptionThresholdStageProgram

def normalizedGateDescriptionWeightStageProgram : NPOracleProgram :=
  linkPrograms normalizedGateDescriptionSecondPrepareProgram
    (preserveRightProgram canonicalIntDescriptionSumProgram)

private theorem normalizedGateDescriptionWeightStageProgram_oracleFree :
    OracleFree normalizedGateDescriptionWeightStageProgram := by
  exact oracleFree_linkPrograms
    normalizedGateDescriptionSecondPrepareProgram_oracleFree
    (preserveRightProgram_oracleFree canonicalIntDescriptionSumProgram
      canonicalIntDescriptionSumProgram_oracleFree)

private def normalizedGateDescriptionWeightStageBitValues
    (inputLength thresholdBits : ℕ) (summary : ℕ) : List ℕ :=
  let weights := normalizedGateDescriptionSelectedWeights summary
  let supportCount := normalizedGateDescriptionSupportCount summary
  [ 1, natBitLength inputLength,
    normalizedGateDescriptionSecondPrepareBits inputLength thresholdBits summary,
    preserveRightBits (canonicalIntDescriptionSumBits inputLength weights)
        (normalizedGateDescriptionSelectedWeightsCode summary)
        (Nat.pair thresholdBits supportCount)
        (weights.map intBitLength).sum ]

private def normalizedGateDescriptionWeightStageBits
    (inputLength thresholdBits : ℕ) (summary : ℕ) : ℕ :=
  (normalizedGateDescriptionWeightStageBitValues inputLength thresholdBits
    summary).foldr max 1

def normalizedGateDescriptionWeightStageFuel
    (inputLength summary : ℕ) : ℕ :=
  let weights := normalizedGateDescriptionSelectedWeights summary
  linkFuel (preserveRightProgram canonicalIntDescriptionSumProgram) 7 <|
    preserveRightFuel (canonicalIntDescriptionSumFuel inputLength weights)

set_option maxHeartbeats 1000000 in
-- This proof treats the verified integer-tree reducer opaquely across one link.
private theorem run_normalizedGateDescriptionWeightStageProgram
    (inputLength thresholdBits summary : ℕ) (weights : List ℤ)
    (hweights : normalizedGateDescriptionSelectedWeightsCode summary =
      encodeIntList weights) :
    runNPOracleProgram normalizedGateDescriptionWeightStageProgram
        (normalizedGateDescriptionWeightStageBits inputLength thresholdBits
          summary)
        (normalizedGateDescriptionWeightStageFuel inputLength summary)
        (initialNPOracleState inputLength
          (Nat.pair thresholdBits
            (normalizedGateDescriptionPrepareContext summary))) =
      some (Nat.pair (weights.map intBitLength).sum
        (Nat.pair thresholdBits
          (normalizedGateDescriptionSupportCount summary))) := by
  have hweightsView :
      normalizedGateDescriptionSelectedWeights summary = weights := by
    simp [normalizedGateDescriptionSelectedWeights, hweights]
  let maximumBits :=
    normalizedGateDescriptionWeightStageBits inputLength thresholdBits summary
  have hbound :
      ∀ value ∈ normalizedGateDescriptionWeightStageBitValues
          inputLength thresholdBits summary,
        value ≤ maximumBits := by
    intro value hvalue
    exact descriptionMemberLeFoldrMax hvalue
  have hpositive : 1 ≤ maximumBits :=
    hbound 1 (by simp [normalizedGateDescriptionWeightStageBitValues])
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    hbound _ (by simp [normalizedGateDescriptionWeightStageBitValues])
  have hprepareBits :
      normalizedGateDescriptionSecondPrepareBits inputLength thresholdBits
          summary ≤ maximumBits :=
    hbound _ (by simp [normalizedGateDescriptionWeightStageBitValues])
  have hcallBits :
      preserveRightBits (canonicalIntDescriptionSumBits inputLength weights)
          (normalizedGateDescriptionSelectedWeightsCode summary)
          (Nat.pair thresholdBits
            (normalizedGateDescriptionSupportCount summary))
          (weights.map intBitLength).sum ≤ maximumBits := by
    apply hbound
    simp [normalizedGateDescriptionWeightStageBitValues, hweightsView]
  have hprepare := run_bits_mono
    (run_normalizedGateDescriptionSecondPrepareProgram inputLength thresholdBits
      summary) hprepareBits
  simp only [normalizedGateDescriptionSecondPrepareOutput, hweights] at hprepare
  have hpreservedBase :=
    run_preserveRightProgram canonicalIntDescriptionSumProgram inputLength
      (canonicalIntDescriptionSumBits inputLength weights)
      (canonicalIntDescriptionSumFuel inputLength weights)
      (encodeIntList weights)
      (Nat.pair thresholdBits
      (normalizedGateDescriptionSupportCount summary))
      (weights.map intBitLength).sum
      (run_canonicalIntDescriptionSumProgram inputLength weights)
  have hpreserved := @run_bits_mono
    (preserveRightProgram canonicalIntDescriptionSumProgram)
    (preserveRightBits (canonicalIntDescriptionSumBits inputLength weights)
      (encodeIntList weights)
      (Nat.pair thresholdBits
        (normalizedGateDescriptionSupportCount summary))
      (weights.map intBitLength).sum) maximumBits
    (preserveRightFuel
      (canonicalIntDescriptionSumFuel inputLength weights))
    (initialNPOracleState inputLength
      (Nat.pair (encodeIntList weights)
        (Nat.pair thresholdBits
          (normalizedGateDescriptionSupportCount summary))))
    (Nat.pair (weights.map intBitLength).sum
      (Nat.pair thresholdBits
        (normalizedGateDescriptionSupportCount summary)))
    hpreservedBase (by simpa only [hweights] using hcallBits)
  have hfuel :
      normalizedGateDescriptionWeightStageFuel inputLength summary =
        linkFuel (preserveRightProgram canonicalIntDescriptionSumProgram) 7
          (preserveRightFuel
            (canonicalIntDescriptionSumFuel inputLength weights)) := by
    simp only [normalizedGateDescriptionWeightStageFuel, hweightsView]
  rw [normalizedGateDescriptionWeightStageProgram, hfuel]
  exact @run_linkPrograms normalizedGateDescriptionSecondPrepareProgram
    (preserveRightProgram canonicalIntDescriptionSumProgram) maximumBits
    inputLength
    (Nat.pair thresholdBits
      (normalizedGateDescriptionPrepareContext summary)) 7
    (Nat.pair (encodeIntList weights)
      (Nat.pair thresholdBits
        (normalizedGateDescriptionSupportCount summary)))
    (preserveRightFuel
      (canonicalIntDescriptionSumFuel inputLength weights))
    (Nat.pair (weights.map intBitLength).sum
      (Nat.pair thresholdBits
        (normalizedGateDescriptionSupportCount summary)))
    hpositive hinputLength hprepare hpreserved

attribute [irreducible] normalizedGateDescriptionWeightStageProgram

def normalizedGateDescriptionProgram : NPOracleProgram :=
  linkPrograms normalizedGateDescriptionThresholdStageProgram <|
    linkPrograms normalizedGateDescriptionWeightStageProgram
      normalizedGateDescriptionFinalProgram

@[simp] theorem normalizedGateDescriptionProgram_oracleFree :
    OracleFree normalizedGateDescriptionProgram := by
  exact oracleFree_linkPrograms
    normalizedGateDescriptionThresholdStageProgram_oracleFree <|
      oracleFree_linkPrograms normalizedGateDescriptionWeightStageProgram_oracleFree
        normalizedGateDescriptionFinalProgram_oracleFree

private def normalizedGateDescriptionStageBits
    (inputLength summary : ℕ) : List ℕ :=
  let threshold := normalizedGateDescriptionThreshold summary
  let weights := normalizedGateDescriptionSelectedWeights summary
  let thresholdBits := intBitLength threshold
  let weightBits := (weights.map intBitLength).sum
  let supportCount := normalizedGateDescriptionSupportCount summary
  [ 1, natBitLength inputLength,
    normalizedGateDescriptionThresholdStageBits inputLength summary,
    normalizedGateDescriptionWeightStageBits inputLength thresholdBits summary,
    normalizedGateDescriptionFinalBits inputLength weightBits thresholdBits
      supportCount ]

def normalizedGateDescriptionBits (inputLength summary : ℕ) : ℕ :=
  (normalizedGateDescriptionStageBits inputLength summary).foldr max 1

def normalizedGateDescriptionFuel (inputLength summary : ℕ) : ℕ :=
  linkFuel
    (linkPrograms normalizedGateDescriptionWeightStageProgram
      normalizedGateDescriptionFinalProgram)
    (normalizedGateDescriptionThresholdStageFuel summary) <|
      linkFuel normalizedGateDescriptionFinalProgram
        (normalizedGateDescriptionWeightStageFuel inputLength summary) 9

theorem run_normalizedGateDescriptionProgram
    (inputLength summary : ℕ)
    (threshold : ℤ) (weights : List ℤ)
    (hthreshold : normalizedGateDescriptionThresholdCode summary =
      encodeInt threshold)
    (hweights : normalizedGateDescriptionSelectedWeightsCode summary =
      encodeIntList weights) :
    runNPOracleProgram normalizedGateDescriptionProgram
        (normalizedGateDescriptionBits inputLength summary)
        (normalizedGateDescriptionFuel inputLength summary)
        (initialNPOracleState inputLength summary) =
      some (normalizedGateDescriptionMetric inputLength summary) := by
  have hthresholdView : normalizedGateDescriptionThreshold summary = threshold := by
    simp [normalizedGateDescriptionThreshold, hthreshold]
  have hweightsView :
      normalizedGateDescriptionSelectedWeights summary = weights := by
    simp [normalizedGateDescriptionSelectedWeights, hweights]
  let thresholdBits := intBitLength threshold
  let weightBits := (weights.map intBitLength).sum
  let supportCount := normalizedGateDescriptionSupportCount summary
  let maximumBits := normalizedGateDescriptionBits inputLength summary
  have hbound :
      ∀ value ∈ normalizedGateDescriptionStageBits inputLength summary,
        value ≤ maximumBits := by
    intro value hvalue
    exact descriptionMemberLeFoldrMax hvalue
  have hpositive : 1 ≤ maximumBits :=
    hbound 1 (by simp [normalizedGateDescriptionStageBits])
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    hbound (natBitLength inputLength)
      (by simp [normalizedGateDescriptionStageBits])
  have hthresholdStage := run_bits_mono
    (run_normalizedGateDescriptionThresholdStageProgram inputLength summary
      threshold hthreshold)
    (hbound (normalizedGateDescriptionThresholdStageBits inputLength summary)
      (by simp [normalizedGateDescriptionStageBits]))
  have hweightStage := run_bits_mono
    (run_normalizedGateDescriptionWeightStageProgram inputLength thresholdBits
      summary weights hweights)
    (hbound
      (normalizedGateDescriptionWeightStageBits inputLength thresholdBits summary)
      (by simp [normalizedGateDescriptionStageBits, thresholdBits,
        hthresholdView]))
  have hfinal := run_bits_mono
    (run_normalizedGateDescriptionFinalProgram inputLength weightBits
      thresholdBits supportCount)
    (hbound
      (normalizedGateDescriptionFinalBits inputLength weightBits thresholdBits
        supportCount)
      (by simp [normalizedGateDescriptionStageBits, thresholdBits, weightBits,
        supportCount, hthresholdView, hweightsView]))
  have htail := run_linkPrograms hpositive hinputLength hweightStage hfinal
  have hrun := run_linkPrograms hpositive hinputLength hthresholdStage htail
  simpa only [normalizedGateDescriptionProgram,
    normalizedGateDescriptionFuel, hthresholdView, hweightsView,
    thresholdBits, weightBits, supportCount,
    normalizedGateDescriptionMetric,
    normalizedGateDescriptionFinalOutput, hthreshold, hweights] using hrun

attribute [irreducible] normalizedGateDescriptionProgram

/-! ## Bottom-gate map and sum -/

def normalizedGateDescriptionMetrics
    (inputLength : ℕ) (summaries : List ℕ) : List ℕ :=
  summaries.map (normalizedGateDescriptionMetric inputLength)

def normalizedGateDescriptionRequestOutput (request : ℕ) : ℕ :=
  normalizedGateDescriptionMetric (Nat.unpair request).1
    (Nat.unpair request).2

private def normalizedGateDescriptionMapRawOutput
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  balancedValidationMapOutput inputLength (encodeBalancedList summaries)
    normalizedGateDescriptionRequestOutput

private theorem normalizedGateDescriptionMapRawOutput_left
    (inputLength : ℕ) (summaries : List ℕ) :
    (Nat.unpair
      (normalizedGateDescriptionMapRawOutput inputLength summaries)).1 =
        encodeBalancedList
          (normalizedGateDescriptionMetrics inputLength summaries) := by
  simp [normalizedGateDescriptionMapRawOutput, balancedValidationMapOutput,
    balancedValidationMapOutputs, balancedValidationMapRequests,
    balancedValidationMapCodes, normalizedGateDescriptionRequestOutput,
    normalizedGateDescriptionMetrics, nativeInputRequest,
    Function.comp_def]

def normalizedGateDescriptionMapProjectionProgram : NPOracleProgram :=
  [.unpairLeft 0 0 1, .halt 0]

private theorem normalizedGateDescriptionMapProjectionProgram_oracleFree :
    OracleFree normalizedGateDescriptionMapProjectionProgram := by
  rfl

private def normalizedGateDescriptionMapProjectionBits
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  max (natBitLength
      (normalizedGateDescriptionMapRawOutput inputLength summaries))
    (natBitLength (encodeBalancedList
      (normalizedGateDescriptionMetrics inputLength summaries)))

private theorem run_normalizedGateDescriptionMapProjectionProgram
    (inputLength : ℕ) (summaries : List ℕ) :
    runNPOracleProgram normalizedGateDescriptionMapProjectionProgram
        (normalizedGateDescriptionMapProjectionBits inputLength summaries) 2
        (initialNPOracleState inputLength
          (normalizedGateDescriptionMapRawOutput inputLength summaries)) =
      some (encodeBalancedList
        (normalizedGateDescriptionMetrics inputLength summaries)) := by
  have houtput :
      natBitLength (encodeBalancedList
          (normalizedGateDescriptionMetrics inputLength summaries)) ≤
        normalizedGateDescriptionMapProjectionBits inputLength summaries :=
    Nat.le_max_right _ _
  rw [show 2 = 1 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := encodeBalancedList
      (normalizedGateDescriptionMetrics inputLength summaries))
    (by rfl) rfl
    (by simp [initialNPOracleState,
      normalizedGateDescriptionMapRawOutput_left]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def normalizedGateDescriptionMapProgram : NPOracleProgram :=
  linkPrograms
    (balancedValidationMapProgram normalizedGateDescriptionProgram)
    normalizedGateDescriptionMapProjectionProgram

@[simp] theorem normalizedGateDescriptionMapProgram_oracleFree :
    OracleFree normalizedGateDescriptionMapProgram := by
  exact oracleFree_linkPrograms
    (balancedValidationMapProgram_oracleFree normalizedGateDescriptionProgram
      normalizedGateDescriptionProgram_oracleFree)
    normalizedGateDescriptionMapProjectionProgram_oracleFree

def normalizedGateDescriptionMapBits
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max
      (balancedValidationMapBits
        (fun request => normalizedGateDescriptionBits
          (Nat.unpair request).1 (Nat.unpair request).2)
        normalizedGateDescriptionRequestOutput inputLength
        (encodeBalancedList summaries))
      (normalizedGateDescriptionMapProjectionBits inputLength summaries)

def normalizedGateDescriptionMapFuel
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  linkFuel normalizedGateDescriptionMapProjectionProgram
    (balancedValidationMapFuel normalizedGateDescriptionProgram
      (fun request => normalizedGateDescriptionFuel
        (Nat.unpair request).1 (Nat.unpair request).2)
      inputLength (encodeBalancedList summaries)) 2

def NormalizedGateDescriptionSummariesCanonical
    (summaries : List ℕ) : Prop :=
  ∀ summary ∈ summaries,
    normalizedGateDescriptionThresholdCode summary =
        encodeInt (normalizedGateDescriptionThreshold summary) ∧
      normalizedGateDescriptionSelectedWeightsCode summary =
        encodeIntList (normalizedGateDescriptionSelectedWeights summary)

private theorem run_normalizedGateDescriptionValidationMapProgram
    (inputLength : ℕ) (summaries : List ℕ)
    (hcanonical : NormalizedGateDescriptionSummariesCanonical summaries) :
    runNPOracleProgram
        (balancedValidationMapProgram normalizedGateDescriptionProgram)
        (balancedValidationMapBits
          (fun request => normalizedGateDescriptionBits
            (Nat.unpair request).1 (Nat.unpair request).2)
          normalizedGateDescriptionRequestOutput inputLength
          (encodeBalancedList summaries))
        (balancedValidationMapFuel normalizedGateDescriptionProgram
          (fun request => normalizedGateDescriptionFuel
            (Nat.unpair request).1 (Nat.unpair request).2)
          inputLength (encodeBalancedList summaries))
        (initialNPOracleState inputLength (encodeBalancedList summaries)) =
      some (normalizedGateDescriptionMapRawOutput inputLength summaries) := by
  apply run_balancedValidationMapProgram
  intro request hrequest
  simp only [balancedValidationMapRequests, balancedValidationMapCodes,
    decodeBalancedList_encode, Option.getD_some, List.mem_map,
    nativeInputRequest] at hrequest
  obtain ⟨summary, hsummary, rfl⟩ := hrequest
  obtain ⟨hthreshold, hweights⟩ := hcanonical summary hsummary
  simpa only [normalizedGateDescriptionRequestOutput, Nat.unpair_pair] using
    (run_normalizedGateDescriptionProgram inputLength summary
      (normalizedGateDescriptionThreshold summary)
      (normalizedGateDescriptionSelectedWeights summary)
      hthreshold hweights)

set_option maxHeartbeats 1000000 in
-- The mapped gate program is a stable call boundary for the final sum.
theorem run_normalizedGateDescriptionMapProgram
    (inputLength : ℕ) (summaries : List ℕ)
    (hcanonical : NormalizedGateDescriptionSummariesCanonical summaries) :
    runNPOracleProgram normalizedGateDescriptionMapProgram
        (normalizedGateDescriptionMapBits inputLength summaries)
        (normalizedGateDescriptionMapFuel inputLength summaries)
        (initialNPOracleState inputLength (encodeBalancedList summaries)) =
      some (encodeBalancedList
        (normalizedGateDescriptionMetrics inputLength summaries)) := by
  let maximumBits := normalizedGateDescriptionMapBits inputLength summaries
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, normalizedGateDescriptionMapBits]
  have hinputLength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, normalizedGateDescriptionMapBits]
  have hmapBits :
      balancedValidationMapBits
          (fun request => normalizedGateDescriptionBits
            (Nat.unpair request).1 (Nat.unpair request).2)
          normalizedGateDescriptionRequestOutput inputLength
          (encodeBalancedList summaries) ≤ maximumBits := by
    simp [maximumBits, normalizedGateDescriptionMapBits]
  have hprojectionBits :
      normalizedGateDescriptionMapProjectionBits inputLength summaries ≤
        maximumBits := by
    simp [maximumBits, normalizedGateDescriptionMapBits]
  have hmap := run_bits_mono
    (run_normalizedGateDescriptionValidationMapProgram inputLength summaries
      hcanonical) hmapBits
  have hprojection := run_bits_mono
    (run_normalizedGateDescriptionMapProjectionProgram inputLength summaries)
    hprojectionBits
  rw [normalizedGateDescriptionMapProgram,
    normalizedGateDescriptionMapFuel]
  exact run_linkPrograms hpositive hinputLength hmap hprojection

attribute [irreducible] normalizedGateDescriptionMapProgram

def normalizedGateDescriptionSumProgram : NPOracleProgram :=
  balancedNatSumAfterProgram normalizedGateDescriptionMapProgram

@[simp] theorem normalizedGateDescriptionSumProgram_oracleFree :
    OracleFree normalizedGateDescriptionSumProgram := by
  exact balancedNatSumAfterProgram_oracleFree _
    normalizedGateDescriptionMapProgram_oracleFree

def normalizedGateDescriptionSumBits
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  balancedNatSumAfterBits inputLength
    (normalizedGateDescriptionMapBits inputLength summaries)
    (normalizedGateDescriptionMetrics inputLength summaries)

def normalizedGateDescriptionSumFuel
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  balancedNatSumAfterFuel
    (normalizedGateDescriptionMapFuel inputLength summaries)
    (normalizedGateDescriptionMetrics inputLength summaries)

theorem run_normalizedGateDescriptionSumProgram
    (inputLength : ℕ) (summaries : List ℕ)
    (hcanonical : NormalizedGateDescriptionSummariesCanonical summaries) :
    runNPOracleProgram normalizedGateDescriptionSumProgram
        (normalizedGateDescriptionSumBits inputLength summaries)
        (normalizedGateDescriptionSumFuel inputLength summaries)
        (initialNPOracleState inputLength (encodeBalancedList summaries)) =
      some (normalizedGateDescriptionMetrics inputLength summaries).sum := by
  exact run_balancedNatSumAfterProgram normalizedGateDescriptionMapProgram
    inputLength (encodeBalancedList summaries)
    (normalizedGateDescriptionMapBits inputLength summaries)
    (normalizedGateDescriptionMapFuel inputLength summaries)
    (normalizedGateDescriptionMetrics inputLength summaries)
    (run_normalizedGateDescriptionMapProgram inputLength summaries hcanonical)

attribute [irreducible] normalizedGateDescriptionSumProgram

/-! ## Family branches -/

private def normalizedCircuitSymmetricDescriptionFinalOutput
    (bottomMetric bottomCount : ℕ) : ℕ :=
  bottomMetric + bottomCount + 1

def normalizedCircuitSymmetricDescriptionFinalProgram :
    NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .add 2 3 0 3
  , .increment 0 4
  , .halt 0
  ]

private theorem normalizedCircuitSymmetricDescriptionFinalProgram_oracleFree :
    OracleFree normalizedCircuitSymmetricDescriptionFinalProgram := by
  rfl

private def normalizedCircuitSymmetricDescriptionFinalValues
    (inputLength bottomMetric bottomCount : ℕ) : List ℕ :=
  [ inputLength, Nat.pair bottomMetric bottomCount, bottomMetric, bottomCount,
    bottomMetric + bottomCount,
    normalizedCircuitSymmetricDescriptionFinalOutput bottomMetric bottomCount ]

private def normalizedCircuitSymmetricDescriptionFinalBits
    (inputLength bottomMetric bottomCount : ℕ) : ℕ :=
  (normalizedCircuitSymmetricDescriptionFinalValues inputLength bottomMetric
    bottomCount).map natBitLength |>.foldr max 1

private theorem run_normalizedCircuitSymmetricDescriptionFinalProgram
    (inputLength bottomMetric bottomCount : ℕ) :
    runNPOracleProgram normalizedCircuitSymmetricDescriptionFinalProgram
        (normalizedCircuitSymmetricDescriptionFinalBits inputLength bottomMetric
          bottomCount) 5
        (initialNPOracleState inputLength
          (Nat.pair bottomMetric bottomCount)) =
      some (normalizedCircuitSymmetricDescriptionFinalOutput bottomMetric
        bottomCount) := by
  have hbits :
      ∀ value ∈ normalizedCircuitSymmetricDescriptionFinalValues inputLength
          bottomMetric bottomCount,
        natBitLength value ≤
          normalizedCircuitSymmetricDescriptionFinalBits inputLength
            bottomMetric bottomCount := by
    intro value hvalue
    exact descriptionValueBits hvalue
  simp [normalizedCircuitSymmetricDescriptionFinalProgram,
    runNPOracleProgram, initialNPOracleState, NPOracleState.boundedWrite,
    normalizedCircuitSymmetricDescriptionFinalValues, hbits,
    normalizedCircuitSymmetricDescriptionFinalOutput, Nat.add_assoc]

def normalizedCircuitSymmetricDescriptionProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram normalizedGateDescriptionSumProgram)
    normalizedCircuitSymmetricDescriptionFinalProgram

@[simp] theorem normalizedCircuitSymmetricDescriptionProgram_oracleFree :
    OracleFree normalizedCircuitSymmetricDescriptionProgram := by
  exact oracleFree_linkPrograms
    (preserveRightProgram_oracleFree normalizedGateDescriptionSumProgram
      normalizedGateDescriptionSumProgram_oracleFree)
    normalizedCircuitSymmetricDescriptionFinalProgram_oracleFree

def normalizedCircuitSymmetricDescriptionMetric
    (inputLength bottomCount : ℕ) (summaries : List ℕ) : ℕ :=
  (normalizedGateDescriptionMetrics inputLength summaries).sum + bottomCount + 1

private def normalizedCircuitSymmetricDescriptionStageBits
    (inputLength bottomCount : ℕ) (summaries : List ℕ) : List ℕ :=
  let bottomMetric :=
    (normalizedGateDescriptionMetrics inputLength summaries).sum
  [ 1, natBitLength inputLength,
    preserveRightBits
      (normalizedGateDescriptionSumBits inputLength summaries)
      (encodeBalancedList summaries) bottomCount bottomMetric,
    normalizedCircuitSymmetricDescriptionFinalBits inputLength bottomMetric
      bottomCount ]

def normalizedCircuitSymmetricDescriptionBits
    (inputLength bottomCount : ℕ) (summaries : List ℕ) : ℕ :=
  (normalizedCircuitSymmetricDescriptionStageBits inputLength bottomCount
    summaries).foldr max 1

def normalizedCircuitSymmetricDescriptionFuel
    (inputLength _bottomCount : ℕ) (summaries : List ℕ) : ℕ :=
  linkFuel normalizedCircuitSymmetricDescriptionFinalProgram
    (preserveRightFuel
      (normalizedGateDescriptionSumFuel inputLength summaries)) 5

theorem run_normalizedCircuitSymmetricDescriptionProgram
    (inputLength bottomCount : ℕ) (summaries : List ℕ)
    (hcanonical : NormalizedGateDescriptionSummariesCanonical summaries) :
    runNPOracleProgram normalizedCircuitSymmetricDescriptionProgram
        (normalizedCircuitSymmetricDescriptionBits inputLength bottomCount
          summaries)
        (normalizedCircuitSymmetricDescriptionFuel inputLength bottomCount
          summaries)
        (initialNPOracleState inputLength
          (Nat.pair (encodeBalancedList summaries) bottomCount)) =
      some (normalizedCircuitSymmetricDescriptionMetric inputLength bottomCount
        summaries) := by
  let bottomMetric :=
    (normalizedGateDescriptionMetrics inputLength summaries).sum
  let maximumBits :=
    normalizedCircuitSymmetricDescriptionBits inputLength bottomCount summaries
  have hbound :
      ∀ value ∈ normalizedCircuitSymmetricDescriptionStageBits inputLength
          bottomCount summaries,
        value ≤ maximumBits := by
    intro value hvalue
    exact descriptionMemberLeFoldrMax hvalue
  have hpositive : 1 ≤ maximumBits :=
    hbound 1 (by simp [normalizedCircuitSymmetricDescriptionStageBits])
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    hbound _ (by simp [normalizedCircuitSymmetricDescriptionStageBits])
  have hsumBase := run_preserveRightProgram normalizedGateDescriptionSumProgram
    inputLength (normalizedGateDescriptionSumBits inputLength summaries)
    (normalizedGateDescriptionSumFuel inputLength summaries)
    (encodeBalancedList summaries) bottomCount bottomMetric
    (run_normalizedGateDescriptionSumProgram inputLength summaries hcanonical)
  have hsum := run_bits_mono hsumBase <|
    hbound _ (by simp [normalizedCircuitSymmetricDescriptionStageBits,
      bottomMetric])
  have hfinal := run_bits_mono
    (run_normalizedCircuitSymmetricDescriptionFinalProgram inputLength
      bottomMetric bottomCount) <|
    hbound _ (by simp [normalizedCircuitSymmetricDescriptionStageBits,
      bottomMetric])
  rw [normalizedCircuitSymmetricDescriptionProgram,
    normalizedCircuitSymmetricDescriptionFuel]
  exact run_linkPrograms hpositive hinputLength hsum hfinal

attribute [irreducible] normalizedCircuitSymmetricDescriptionProgram

private def normalizedCircuitThresholdTopCallInput
    (bottomMetric topSummary bottomCount : ℕ) : ℕ :=
  Nat.pair topSummary (Nat.pair bottomCount bottomMetric)

def normalizedCircuitThresholdTopCallAdapterProgram :
    NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 5 2 6 5
  , .pair 4 6 0 6
  , .halt 0
  ]

private theorem normalizedCircuitThresholdTopCallAdapterProgram_oracleFree :
    OracleFree normalizedCircuitThresholdTopCallAdapterProgram := by
  rfl

private def normalizedCircuitThresholdTopCallAdapterValues
    (inputLength bottomMetric topSummary bottomCount : ℕ) : List ℕ :=
  [ inputLength, Nat.pair bottomMetric (Nat.pair topSummary bottomCount),
    bottomMetric, Nat.pair topSummary bottomCount, topSummary, bottomCount,
    Nat.pair bottomCount bottomMetric,
    normalizedCircuitThresholdTopCallInput bottomMetric topSummary bottomCount ]

private def normalizedCircuitThresholdTopCallAdapterBits
    (inputLength bottomMetric topSummary bottomCount : ℕ) : ℕ :=
  (normalizedCircuitThresholdTopCallAdapterValues inputLength bottomMetric
    topSummary bottomCount).map natBitLength |>.foldr max 1

private theorem run_normalizedCircuitThresholdTopCallAdapterProgram
    (inputLength bottomMetric topSummary bottomCount : ℕ) :
    runNPOracleProgram normalizedCircuitThresholdTopCallAdapterProgram
        (normalizedCircuitThresholdTopCallAdapterBits inputLength bottomMetric
          topSummary bottomCount) 7
        (initialNPOracleState inputLength
          (Nat.pair bottomMetric (Nat.pair topSummary bottomCount))) =
      some (normalizedCircuitThresholdTopCallInput bottomMetric topSummary
        bottomCount) := by
  have hbits :
      ∀ value ∈ normalizedCircuitThresholdTopCallAdapterValues inputLength
          bottomMetric topSummary bottomCount,
        natBitLength value ≤
          normalizedCircuitThresholdTopCallAdapterBits inputLength bottomMetric
            topSummary bottomCount := by
    intro value hvalue
    exact descriptionValueBits hvalue
  simp [normalizedCircuitThresholdTopCallAdapterProgram,
    runNPOracleProgram, initialNPOracleState, NPOracleState.boundedWrite,
    normalizedCircuitThresholdTopCallAdapterValues, hbits,
    normalizedCircuitThresholdTopCallInput]

def normalizedCircuitThresholdTopCallProgram : NPOracleProgram :=
  linkPrograms normalizedCircuitThresholdTopCallAdapterProgram
    (nativeContextCallProgram normalizedGateDescriptionProgram)

private theorem normalizedCircuitThresholdTopCallProgram_oracleFree :
    OracleFree normalizedCircuitThresholdTopCallProgram := by
  exact oracleFree_linkPrograms
    normalizedCircuitThresholdTopCallAdapterProgram_oracleFree
    (nativeContextCallProgram_oracleFree
      normalizedGateDescriptionProgram_oracleFree)

private def normalizedCircuitThresholdTopCallBitValues
    (inputLength bottomMetric topSummary bottomCount : ℕ) : List ℕ :=
  let topMetric := normalizedGateDescriptionMetric bottomCount topSummary
  [ 1, natBitLength inputLength,
    normalizedCircuitThresholdTopCallAdapterBits inputLength bottomMetric
      topSummary bottomCount,
    nativeContextCallBits inputLength bottomCount topSummary bottomMetric
      topMetric (normalizedGateDescriptionBits bottomCount topSummary) ]

private def normalizedCircuitThresholdTopCallBits
    (inputLength bottomMetric topSummary bottomCount : ℕ) : ℕ :=
  (normalizedCircuitThresholdTopCallBitValues inputLength bottomMetric topSummary
    bottomCount).foldr max 1

def normalizedCircuitThresholdTopCallFuel
    (_bottomMetric topSummary bottomCount : ℕ) : ℕ :=
  linkFuel (nativeContextCallProgram normalizedGateDescriptionProgram) 7 <|
    nativeContextCallFuel normalizedGateDescriptionProgram
      (normalizedGateDescriptionFuel bottomCount topSummary)
      bottomCount topSummary

set_option maxHeartbeats 1000000 in
-- The explicit native call changes only the top gate's semantic arity.
private theorem run_normalizedCircuitThresholdTopCallProgram
    (inputLength bottomMetric topSummary bottomCount : ℕ)
    (threshold : ℤ) (weights : List ℤ)
    (hthreshold : normalizedGateDescriptionThresholdCode topSummary =
      encodeInt threshold)
    (hweights : normalizedGateDescriptionSelectedWeightsCode topSummary =
      encodeIntList weights) :
    runNPOracleProgram normalizedCircuitThresholdTopCallProgram
        (normalizedCircuitThresholdTopCallBits inputLength bottomMetric topSummary
          bottomCount)
        (normalizedCircuitThresholdTopCallFuel bottomMetric topSummary bottomCount)
        (initialNPOracleState inputLength
          (Nat.pair bottomMetric (Nat.pair topSummary bottomCount))) =
      some (Nat.pair
        (normalizedGateDescriptionMetric bottomCount topSummary)
        (Nat.pair bottomCount bottomMetric)) := by
  let topMetric := normalizedGateDescriptionMetric bottomCount topSummary
  let maximumBits := normalizedCircuitThresholdTopCallBits inputLength
    bottomMetric topSummary bottomCount
  have hbound :
      ∀ value ∈ normalizedCircuitThresholdTopCallBitValues inputLength
          bottomMetric topSummary bottomCount,
        value ≤ maximumBits := by
    intro value hvalue
    exact descriptionMemberLeFoldrMax hvalue
  have hpositive : 1 ≤ maximumBits :=
    hbound 1 (by simp [normalizedCircuitThresholdTopCallBitValues])
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    hbound _ (by simp [normalizedCircuitThresholdTopCallBitValues])
  have hadapter := run_bits_mono
    (run_normalizedCircuitThresholdTopCallAdapterProgram inputLength bottomMetric
      topSummary bottomCount) <|
    hbound _ (by simp [normalizedCircuitThresholdTopCallBitValues])
  have hgate := run_normalizedGateDescriptionProgram bottomCount topSummary
    threshold weights hthreshold hweights
  have hcall := run_bits_mono
    (run_nativeContextCallProgram normalizedGateDescriptionProgram inputLength
      bottomCount topSummary bottomMetric topMetric
      (normalizedGateDescriptionBits bottomCount topSummary)
      (normalizedGateDescriptionFuel bottomCount topSummary) hgate) <|
    hbound _ (by simp [normalizedCircuitThresholdTopCallBitValues, topMetric])
  rw [normalizedCircuitThresholdTopCallProgram,
    normalizedCircuitThresholdTopCallFuel]
  exact run_linkPrograms hpositive hinputLength hadapter hcall

attribute [irreducible] normalizedCircuitThresholdTopCallProgram

private def normalizedCircuitThresholdDescriptionFinalOutput
    (topMetric bottomMetric : ℕ) : ℕ :=
  topMetric + bottomMetric

def normalizedCircuitThresholdDescriptionFinalProgram :
    NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .add 2 4 0 4
  , .halt 0
  ]

private theorem normalizedCircuitThresholdDescriptionFinalProgram_oracleFree :
    OracleFree normalizedCircuitThresholdDescriptionFinalProgram := by
  rfl

private def normalizedCircuitThresholdDescriptionFinalValues
    (inputLength topMetric bottomCount bottomMetric : ℕ) : List ℕ :=
  [ inputLength, Nat.pair topMetric (Nat.pair bottomCount bottomMetric),
    topMetric, Nat.pair bottomCount bottomMetric, bottomMetric,
    normalizedCircuitThresholdDescriptionFinalOutput topMetric bottomMetric ]

private def normalizedCircuitThresholdDescriptionFinalBits
    (inputLength topMetric bottomCount bottomMetric : ℕ) : ℕ :=
  (normalizedCircuitThresholdDescriptionFinalValues inputLength topMetric
    bottomCount bottomMetric).map natBitLength |>.foldr max 1

private theorem run_normalizedCircuitThresholdDescriptionFinalProgram
    (inputLength topMetric bottomCount bottomMetric : ℕ) :
    runNPOracleProgram normalizedCircuitThresholdDescriptionFinalProgram
        (normalizedCircuitThresholdDescriptionFinalBits inputLength topMetric
          bottomCount bottomMetric) 5
        (initialNPOracleState inputLength
          (Nat.pair topMetric (Nat.pair bottomCount bottomMetric))) =
      some (normalizedCircuitThresholdDescriptionFinalOutput topMetric
        bottomMetric) := by
  have hbits :
      ∀ value ∈ normalizedCircuitThresholdDescriptionFinalValues inputLength
          topMetric bottomCount bottomMetric,
        natBitLength value ≤ normalizedCircuitThresholdDescriptionFinalBits
          inputLength topMetric bottomCount bottomMetric := by
    intro value hvalue
    exact descriptionValueBits hvalue
  simp [normalizedCircuitThresholdDescriptionFinalProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    normalizedCircuitThresholdDescriptionFinalValues, hbits,
    normalizedCircuitThresholdDescriptionFinalOutput]

def normalizedCircuitThresholdDescriptionProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram normalizedGateDescriptionSumProgram) <|
    linkPrograms normalizedCircuitThresholdTopCallProgram
      normalizedCircuitThresholdDescriptionFinalProgram

@[simp] theorem normalizedCircuitThresholdDescriptionProgram_oracleFree :
    OracleFree normalizedCircuitThresholdDescriptionProgram := by
  exact oracleFree_linkPrograms
    (preserveRightProgram_oracleFree normalizedGateDescriptionSumProgram
      normalizedGateDescriptionSumProgram_oracleFree) <|
    oracleFree_linkPrograms normalizedCircuitThresholdTopCallProgram_oracleFree
      normalizedCircuitThresholdDescriptionFinalProgram_oracleFree

def normalizedCircuitThresholdDescriptionMetric
    (inputLength topSummary : ℕ) (summaries : List ℕ) : ℕ :=
  normalizedGateDescriptionMetric summaries.length topSummary +
    (normalizedGateDescriptionMetrics inputLength summaries).sum

private def normalizedCircuitThresholdDescriptionStageBits
    (inputLength topSummary : ℕ) (summaries : List ℕ) : List ℕ :=
  let bottomCount := summaries.length
  let bottomMetric :=
    (normalizedGateDescriptionMetrics inputLength summaries).sum
  let topMetric := normalizedGateDescriptionMetric bottomCount topSummary
  [ 1, natBitLength inputLength,
    preserveRightBits
      (normalizedGateDescriptionSumBits inputLength summaries)
      (encodeBalancedList summaries) (Nat.pair topSummary bottomCount)
      bottomMetric,
    normalizedCircuitThresholdTopCallBits inputLength bottomMetric topSummary
      bottomCount,
    normalizedCircuitThresholdDescriptionFinalBits inputLength topMetric
      bottomCount bottomMetric ]

def normalizedCircuitThresholdDescriptionBits
    (inputLength topSummary : ℕ) (summaries : List ℕ) : ℕ :=
  (normalizedCircuitThresholdDescriptionStageBits inputLength topSummary
    summaries).foldr max 1

def normalizedCircuitThresholdDescriptionFuel
    (inputLength topSummary : ℕ) (summaries : List ℕ) : ℕ :=
  let bottomCount := summaries.length
  let bottomMetric :=
    (normalizedGateDescriptionMetrics inputLength summaries).sum
  linkFuel
    (linkPrograms normalizedCircuitThresholdTopCallProgram
      normalizedCircuitThresholdDescriptionFinalProgram)
    (preserveRightFuel
      (normalizedGateDescriptionSumFuel inputLength summaries)) <|
    linkFuel normalizedCircuitThresholdDescriptionFinalProgram
      (normalizedCircuitThresholdTopCallFuel bottomMetric topSummary bottomCount) 5

theorem run_normalizedCircuitThresholdDescriptionProgram
    (inputLength topSummary : ℕ) (summaries : List ℕ)
    (threshold : ℤ) (weights : List ℤ)
    (hcanonical : NormalizedGateDescriptionSummariesCanonical summaries)
    (hthreshold : normalizedGateDescriptionThresholdCode topSummary =
      encodeInt threshold)
    (hweights : normalizedGateDescriptionSelectedWeightsCode topSummary =
      encodeIntList weights) :
    runNPOracleProgram normalizedCircuitThresholdDescriptionProgram
        (normalizedCircuitThresholdDescriptionBits inputLength topSummary
          summaries)
        (normalizedCircuitThresholdDescriptionFuel inputLength topSummary
          summaries)
        (initialNPOracleState inputLength
          (Nat.pair (encodeBalancedList summaries)
            (Nat.pair topSummary summaries.length))) =
      some (normalizedCircuitThresholdDescriptionMetric inputLength topSummary
        summaries) := by
  let bottomCount := summaries.length
  let bottomMetric :=
    (normalizedGateDescriptionMetrics inputLength summaries).sum
  let topMetric := normalizedGateDescriptionMetric bottomCount topSummary
  let maximumBits :=
    normalizedCircuitThresholdDescriptionBits inputLength topSummary summaries
  have hbound :
      ∀ value ∈ normalizedCircuitThresholdDescriptionStageBits inputLength
          topSummary summaries,
        value ≤ maximumBits := by
    intro value hvalue
    exact descriptionMemberLeFoldrMax hvalue
  have hpositive : 1 ≤ maximumBits :=
    hbound 1 (by simp [normalizedCircuitThresholdDescriptionStageBits])
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    hbound _ (by simp [normalizedCircuitThresholdDescriptionStageBits])
  have hbottomBase :=
    run_preserveRightProgram normalizedGateDescriptionSumProgram inputLength
      (normalizedGateDescriptionSumBits inputLength summaries)
      (normalizedGateDescriptionSumFuel inputLength summaries)
      (encodeBalancedList summaries) (Nat.pair topSummary bottomCount)
      bottomMetric
      (run_normalizedGateDescriptionSumProgram inputLength summaries hcanonical)
  have hbottom := run_bits_mono hbottomBase <|
    hbound _ (by simp [normalizedCircuitThresholdDescriptionStageBits,
      bottomCount, bottomMetric])
  have htop := run_bits_mono
    (run_normalizedCircuitThresholdTopCallProgram inputLength bottomMetric
      topSummary bottomCount threshold weights hthreshold hweights) <|
    hbound _ (by simp [normalizedCircuitThresholdDescriptionStageBits,
      bottomCount, bottomMetric])
  have hfinal := run_bits_mono
    (run_normalizedCircuitThresholdDescriptionFinalProgram inputLength topMetric
      bottomCount bottomMetric) <|
    hbound _ (by simp [normalizedCircuitThresholdDescriptionStageBits,
      bottomCount, bottomMetric, topMetric])
  have htail := run_linkPrograms hpositive hinputLength htop hfinal
  rw [normalizedCircuitThresholdDescriptionProgram,
    normalizedCircuitThresholdDescriptionFuel]
  exact run_linkPrograms hpositive hinputLength hbottom htail

attribute [irreducible] normalizedCircuitThresholdDescriptionProgram

/-! ## One validated-summary dispatcher -/

def normalizedCircuitDescriptionBranchTag (summary : ℕ) : ℕ :=
  (normalizedCircuitResourceFamilyTag summary).pred

def normalizedCircuitDescriptionSymmetricInput (summary : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitResourceBottomSummariesCode summary)
    (normalizedCircuitResourceBottomLength summary)

def normalizedCircuitDescriptionThresholdInput (summary : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitResourceBottomSummariesCode summary) <|
    Nat.pair (normalizedCircuitResourceTopSummary summary)
      (normalizedCircuitResourceBottomLength summary)

def normalizedCircuitDescriptionBranchInput (summary : ℕ) : ℕ :=
  if normalizedCircuitDescriptionBranchTag summary = 0 then
    normalizedCircuitDescriptionSymmetricInput summary
  else
    normalizedCircuitDescriptionThresholdInput summary

def normalizedCircuitDescriptionPrepareOutput (summary : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitDescriptionBranchTag summary)
    (normalizedCircuitDescriptionBranchInput summary)

def normalizedCircuitDescriptionPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairLeft 6 7 6
  , .unpairRight 6 8 7
  , .unpairLeft 8 9 8
  , .decrement 2 9
  , .pair 4 9 11 10
  , .pair 7 11 12 11
  , .pair 7 9 13 12
  , .branchZero 2 14 13
  , .pair 2 12 0 15
  , .pair 2 13 0 15
  , .halt 0
  ]

@[simp] theorem normalizedCircuitDescriptionPrepareProgram_oracleFree :
    OracleFree normalizedCircuitDescriptionPrepareProgram := by
  rfl

private def normalizedCircuitDescriptionPrepareValues
    (inputLength summary : ℕ) : List ℕ :=
  [ inputLength, summary, normalizedCircuitResourceFamilyTag summary,
    normalizedCircuitResourcePayload summary,
    normalizedCircuitResourceTopSummary summary,
    normalizedCircuitResourceBottomAndRaw summary,
    normalizedCircuitResourceBottomSummaryData summary,
    normalizedCircuitResourceBottomSummariesCode summary,
    normalizedCircuitResourceBottomMetadata summary,
    normalizedCircuitResourceBottomLength summary,
    normalizedCircuitDescriptionBranchTag summary,
    Nat.pair (normalizedCircuitResourceTopSummary summary)
      (normalizedCircuitResourceBottomLength summary),
    normalizedCircuitDescriptionThresholdInput summary,
    normalizedCircuitDescriptionSymmetricInput summary,
    normalizedCircuitDescriptionPrepareOutput summary ]

def normalizedCircuitDescriptionPrepareBits
    (inputLength summary : ℕ) : ℕ :=
  (normalizedCircuitDescriptionPrepareValues inputLength summary).map natBitLength
    |>.foldr max 1

def normalizedCircuitDescriptionPrepareFuel (_summary : ℕ) : ℕ := 15

set_option maxHeartbeats 1000000 in
-- The projection is shallow but its paired ABI is intentionally explicit.
theorem run_normalizedCircuitDescriptionPrepareProgram
    (inputLength summary : ℕ) :
    runNPOracleProgram normalizedCircuitDescriptionPrepareProgram
        (normalizedCircuitDescriptionPrepareBits inputLength summary)
        (normalizedCircuitDescriptionPrepareFuel summary)
        (initialNPOracleState inputLength summary) =
      some (normalizedCircuitDescriptionPrepareOutput summary) := by
  have hbits :
      ∀ value ∈ normalizedCircuitDescriptionPrepareValues inputLength summary,
        natBitLength value ≤
          normalizedCircuitDescriptionPrepareBits inputLength summary := by
    intro value hvalue
    exact descriptionValueBits hvalue
  have hfamily := hbits (normalizedCircuitResourceFamilyTag summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have hpayload := hbits (normalizedCircuitResourcePayload summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have htop := hbits (normalizedCircuitResourceTopSummary summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have hbottomAndRaw := hbits
    (normalizedCircuitResourceBottomAndRaw summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have hbottomData := hbits
    (normalizedCircuitResourceBottomSummaryData summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have hsummaries := hbits
    (normalizedCircuitResourceBottomSummariesCode summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have hmetadata := hbits
    (normalizedCircuitResourceBottomMetadata summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have hlength := hbits (normalizedCircuitResourceBottomLength summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have htagBits := hbits (normalizedCircuitDescriptionBranchTag summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have htopLength := hbits
    (Nat.pair (normalizedCircuitResourceTopSummary summary)
      (normalizedCircuitResourceBottomLength summary))
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have hthresholdInput := hbits
    (normalizedCircuitDescriptionThresholdInput summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have hsymmetricInput := hbits
    (normalizedCircuitDescriptionSymmetricInput summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  have houtput := hbits (normalizedCircuitDescriptionPrepareOutput summary)
    (by simp [normalizedCircuitDescriptionPrepareValues])
  rw [show normalizedCircuitDescriptionPrepareFuel summary = 14 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 14) (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := normalizedCircuitResourceFamilyTag summary)
    (by rfl) rfl
    (by simp [initialNPOracleState,
      normalizedCircuitResourceFamilyTag]) hfamily]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 13) (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := normalizedCircuitResourcePayload summary)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, normalizedCircuitResourcePayload]) hpayload]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 12) (pc := 2) (source := 3) (destination := 4) (next := 3)
    (value := normalizedCircuitResourceTopSummary summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceTopSummary,
      normalizedCircuitResourcePayload]) htop]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 11) (pc := 3) (source := 3) (destination := 5) (next := 4)
    (value := normalizedCircuitResourceBottomAndRaw summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceBottomAndRaw,
      normalizedCircuitResourcePayload]) hbottomAndRaw]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 10) (pc := 4) (source := 5) (destination := 6) (next := 5)
    (value := normalizedCircuitResourceBottomSummaryData summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceBottomSummaryData,
      normalizedCircuitResourceBottomAndRaw]) hbottomData]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 9) (pc := 5) (source := 6) (destination := 7) (next := 6)
    (value := normalizedCircuitResourceBottomSummariesCode summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceBottomSummariesCode,
      normalizedCircuitResourceBottomSummaryData]) hsummaries]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 8) (pc := 6) (source := 6) (destination := 8) (next := 7)
    (value := normalizedCircuitResourceBottomMetadata summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceBottomMetadata,
      normalizedCircuitResourceBottomSummaryData]) hmetadata]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 7) (pc := 7) (source := 8) (destination := 9) (next := 8)
    (value := normalizedCircuitResourceBottomLength summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitResourceBottomLength,
      normalizedCircuitResourceBottomMetadata]) hlength]
  rw [show 7 = 6 + 1 by omega]
  rw [run_decrement_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 6) (pc := 8) (register := 2) (next := 9)
    (value := normalizedCircuitDescriptionBranchTag summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitDescriptionBranchTag,
      normalizedCircuitResourceFamilyTag]) htagBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 5) (pc := 9) (left := 4) (right := 9) (destination := 11)
    (next := 10)
    (value := Nat.pair (normalizedCircuitResourceTopSummary summary)
      (normalizedCircuitResourceBottomLength summary))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    htopLength]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 4) (pc := 10) (left := 7) (right := 11) (destination := 12)
    (next := 11)
    (value := normalizedCircuitDescriptionThresholdInput summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitDescriptionThresholdInput]) hthresholdInput]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 3) (pc := 11) (left := 7) (right := 9) (destination := 13)
    (next := 12)
    (value := normalizedCircuitDescriptionSymmetricInput summary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      normalizedCircuitDescriptionSymmetricInput]) hsymmetricInput]
  rw [show 3 = 2 + 1 by omega]
  rw [run_branchZero_instruction
    (program := normalizedCircuitDescriptionPrepareProgram)
    (fuel := 2) (pc := 12) (register := 2)
    (zeroTarget := 14) (nonzeroTarget := 13) (by rfl) rfl]
  by_cases htag : normalizedCircuitDescriptionBranchTag summary = 0
  · rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump, htag])]
    rw [show 2 = 1 + 1 by omega]
    rw [run_pair_instruction
      (program := normalizedCircuitDescriptionPrepareProgram)
      (fuel := 1) (pc := 14) (left := 2) (right := 13)
      (destination := 0) (next := 15)
      (value := normalizedCircuitDescriptionPrepareOutput summary)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump,
        normalizedCircuitDescriptionPrepareOutput,
        normalizedCircuitDescriptionBranchInput, htag]) houtput]
    exact run_halt_instruction (fuel := 0) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) houtput
  · rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump, htag])]
    rw [show 2 = 1 + 1 by omega]
    rw [run_pair_instruction
      (program := normalizedCircuitDescriptionPrepareProgram)
      (fuel := 1) (pc := 13) (left := 2) (right := 12)
      (destination := 0) (next := 15)
      (value := normalizedCircuitDescriptionPrepareOutput summary)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump,
        normalizedCircuitDescriptionPrepareOutput,
        normalizedCircuitDescriptionBranchInput, htag]) houtput]
    exact run_halt_instruction (fuel := 0) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def normalizedCircuitDescriptionMetric (inputLength summary : ℕ) : ℕ :=
  let summaries := normalizedCircuitResourceSummaries summary
  if normalizedCircuitDescriptionBranchTag summary = 0 then
    normalizedCircuitSymmetricDescriptionMetric inputLength
      (normalizedCircuitResourceBottomLength summary) summaries
  else
    normalizedCircuitThresholdDescriptionMetric inputLength
      (normalizedCircuitResourceTopSummary summary) summaries

def normalizedCircuitDescriptionFamilyProgram : NPOracleProgram :=
  taggedProgramChoice normalizedCircuitSymmetricDescriptionProgram
    normalizedCircuitThresholdDescriptionProgram

@[simp] theorem normalizedCircuitDescriptionFamilyProgram_oracleFree :
    OracleFree normalizedCircuitDescriptionFamilyProgram := by
  exact taggedProgramChoice_oracleFree
    normalizedCircuitSymmetricDescriptionProgram
    normalizedCircuitThresholdDescriptionProgram
    normalizedCircuitSymmetricDescriptionProgram_oracleFree
    normalizedCircuitThresholdDescriptionProgram_oracleFree

private def normalizedCircuitDescriptionFamilySourceBits
    (inputLength summary : ℕ) : ℕ :=
  let summaries := normalizedCircuitResourceSummaries summary
  if normalizedCircuitDescriptionBranchTag summary = 0 then
    normalizedCircuitSymmetricDescriptionBits inputLength
      (normalizedCircuitResourceBottomLength summary) summaries
  else
    normalizedCircuitThresholdDescriptionBits inputLength
      (normalizedCircuitResourceTopSummary summary) summaries

def normalizedCircuitDescriptionFamilyBits
    (inputLength summary : ℕ) : ℕ :=
  max (natBitLength
      (Nat.pair inputLength (normalizedCircuitDescriptionPrepareOutput summary)))
    (normalizedCircuitDescriptionFamilySourceBits inputLength summary)

def normalizedCircuitDescriptionFamilyFuel
    (inputLength summary : ℕ) : ℕ :=
  let summaries := normalizedCircuitResourceSummaries summary
  if normalizedCircuitDescriptionBranchTag summary = 0 then
    taggedProgramChoiceFuel <|
      normalizedCircuitSymmetricDescriptionFuel inputLength
        (normalizedCircuitResourceBottomLength summary) summaries
  else
    taggedProgramChoiceFuel <|
      normalizedCircuitThresholdDescriptionFuel inputLength
        (normalizedCircuitResourceTopSummary summary) summaries

set_option maxHeartbeats 1000000 in
-- Family-choice normalization sees the two opaque verified branch programs.
theorem run_normalizedCircuitDescriptionFamilyProgram_symmetric
    (inputLength summary : ℕ) (summaries : List ℕ)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 1)
    (hsummaries : decodeBalancedList
      (normalizedCircuitResourceBottomSummariesCode summary) = some summaries)
    (hcanonical : NormalizedGateDescriptionSummariesCanonical summaries) :
    runNPOracleProgram normalizedCircuitDescriptionFamilyProgram
        (normalizedCircuitDescriptionFamilyBits inputLength summary)
        (normalizedCircuitDescriptionFamilyFuel inputLength summary)
        (initialNPOracleState inputLength
          (normalizedCircuitDescriptionPrepareOutput summary)) =
      some (normalizedCircuitDescriptionMetric inputLength summary) := by
  have htag : normalizedCircuitDescriptionBranchTag summary = 0 := by
    simp [normalizedCircuitDescriptionBranchTag, hfamily]
  have hsummariesView :
      normalizedCircuitResourceSummaries summary = summaries := by
    simp [normalizedCircuitResourceSummaries, hsummaries]
  have hcode : normalizedCircuitResourceBottomSummariesCode summary =
      encodeBalancedList summaries :=
    (encodeBalancedList_of_decode hsummaries).symm
  have hprepare : normalizedCircuitDescriptionPrepareOutput summary =
      Nat.pair 0 (Nat.pair (encodeBalancedList summaries)
        (normalizedCircuitResourceBottomLength summary)) := by
    simp [normalizedCircuitDescriptionPrepareOutput,
      normalizedCircuitDescriptionBranchInput,
      normalizedCircuitDescriptionSymmetricInput, htag, hcode]
  have hsource := run_normalizedCircuitSymmetricDescriptionProgram inputLength
    (normalizedCircuitResourceBottomLength summary) summaries hcanonical
  have hsourceBits :
      normalizedCircuitSymmetricDescriptionBits inputLength
          (normalizedCircuitResourceBottomLength summary) summaries ≤
        normalizedCircuitDescriptionFamilyBits inputLength summary := by
    rw [normalizedCircuitDescriptionFamilyBits,
      normalizedCircuitDescriptionFamilySourceBits, if_pos htag,
      hsummariesView]
    exact Nat.le_max_right _ _
  have hsourceWide :
      runNPOracleProgram normalizedCircuitSymmetricDescriptionProgram
          (normalizedCircuitDescriptionFamilyBits inputLength summary)
          (normalizedCircuitSymmetricDescriptionFuel inputLength
            (normalizedCircuitResourceBottomLength summary) summaries)
          (initialNPOracleState inputLength
            (Nat.pair (encodeBalancedList summaries)
              (normalizedCircuitResourceBottomLength summary))) =
        some (normalizedCircuitSymmetricDescriptionMetric inputLength
          (normalizedCircuitResourceBottomLength summary) summaries) :=
    run_bits_mono hsource hsourceBits
  have hsourceOutput := run_output_bounded hsourceWide
  have hinput :
      natBitLength (Nat.pair inputLength
          (Nat.pair 0 (Nat.pair (encodeBalancedList summaries)
            (normalizedCircuitResourceBottomLength summary)))) ≤
        normalizedCircuitDescriptionFamilyBits inputLength summary := by
    rw [← hprepare]
    exact Nat.le_max_left _ _
  have hrun := run_taggedProgramChoice_zero
    normalizedCircuitSymmetricDescriptionProgram
    normalizedCircuitThresholdDescriptionProgram inputLength
    (Nat.pair (encodeBalancedList summaries)
      (normalizedCircuitResourceBottomLength summary))
    (normalizedCircuitDescriptionFamilyBits inputLength summary)
    (normalizedCircuitSymmetricDescriptionFuel inputLength
      (normalizedCircuitResourceBottomLength summary) summaries)
    (normalizedCircuitSymmetricDescriptionMetric inputLength
      (normalizedCircuitResourceBottomLength summary) summaries)
    hinput hsourceWide hsourceOutput
  rw [normalizedCircuitDescriptionFamilyProgram,
    normalizedCircuitDescriptionFamilyFuel,
    normalizedCircuitDescriptionMetric, htag, hsummariesView, hprepare]
  exact hrun

set_option maxHeartbeats 1000000 in
-- Family-choice normalization sees the two opaque verified branch programs.
theorem run_normalizedCircuitDescriptionFamilyProgram_threshold
    (inputLength summary : ℕ) (summaries : List ℕ)
    (threshold : ℤ) (weights : List ℤ)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 2)
    (hsummaries : decodeBalancedList
      (normalizedCircuitResourceBottomSummariesCode summary) = some summaries)
    (hstoredLength : normalizedCircuitResourceBottomLength summary =
      summaries.length)
    (hcanonical : NormalizedGateDescriptionSummariesCanonical summaries)
    (hthreshold : normalizedGateDescriptionThresholdCode
      (normalizedCircuitResourceTopSummary summary) = encodeInt threshold)
    (hweights : normalizedGateDescriptionSelectedWeightsCode
      (normalizedCircuitResourceTopSummary summary) = encodeIntList weights) :
    runNPOracleProgram normalizedCircuitDescriptionFamilyProgram
        (normalizedCircuitDescriptionFamilyBits inputLength summary)
        (normalizedCircuitDescriptionFamilyFuel inputLength summary)
        (initialNPOracleState inputLength
          (normalizedCircuitDescriptionPrepareOutput summary)) =
      some (normalizedCircuitDescriptionMetric inputLength summary) := by
  have htag : normalizedCircuitDescriptionBranchTag summary = 1 := by
    simp [normalizedCircuitDescriptionBranchTag, hfamily]
  have htagNonzero : normalizedCircuitDescriptionBranchTag summary ≠ 0 := by
    omega
  have hsummariesView :
      normalizedCircuitResourceSummaries summary = summaries := by
    simp [normalizedCircuitResourceSummaries, hsummaries]
  have hcode : normalizedCircuitResourceBottomSummariesCode summary =
      encodeBalancedList summaries :=
    (encodeBalancedList_of_decode hsummaries).symm
  have hprepare : normalizedCircuitDescriptionPrepareOutput summary =
      Nat.pair 1 (Nat.pair (encodeBalancedList summaries)
        (Nat.pair (normalizedCircuitResourceTopSummary summary)
          summaries.length)) := by
    simp [normalizedCircuitDescriptionPrepareOutput,
      normalizedCircuitDescriptionBranchInput,
      normalizedCircuitDescriptionThresholdInput, htag,
      hcode, hstoredLength]
  have hsource := run_normalizedCircuitThresholdDescriptionProgram inputLength
    (normalizedCircuitResourceTopSummary summary) summaries threshold weights
    hcanonical hthreshold hweights
  have hsourceBits :
      normalizedCircuitThresholdDescriptionBits inputLength
          (normalizedCircuitResourceTopSummary summary) summaries ≤
        normalizedCircuitDescriptionFamilyBits inputLength summary := by
    rw [normalizedCircuitDescriptionFamilyBits,
      normalizedCircuitDescriptionFamilySourceBits, if_neg htagNonzero,
      hsummariesView]
    exact Nat.le_max_right _ _
  have hsourceWide :
      runNPOracleProgram normalizedCircuitThresholdDescriptionProgram
          (normalizedCircuitDescriptionFamilyBits inputLength summary)
          (normalizedCircuitThresholdDescriptionFuel inputLength
            (normalizedCircuitResourceTopSummary summary) summaries)
          (initialNPOracleState inputLength
            (Nat.pair (encodeBalancedList summaries)
              (Nat.pair (normalizedCircuitResourceTopSummary summary)
                summaries.length))) =
        some (normalizedCircuitThresholdDescriptionMetric inputLength
          (normalizedCircuitResourceTopSummary summary) summaries) :=
    run_bits_mono hsource hsourceBits
  have hsourceOutput := run_output_bounded hsourceWide
  have hinput :
      natBitLength (Nat.pair inputLength
          (Nat.pair 1 (Nat.pair (encodeBalancedList summaries)
            (Nat.pair (normalizedCircuitResourceTopSummary summary)
              summaries.length)))) ≤
        normalizedCircuitDescriptionFamilyBits inputLength summary := by
    rw [← hprepare]
    exact Nat.le_max_left _ _
  have hrun := run_taggedProgramChoice_nonzero
    normalizedCircuitSymmetricDescriptionProgram
    normalizedCircuitThresholdDescriptionProgram inputLength 1
    (Nat.pair (encodeBalancedList summaries)
      (Nat.pair (normalizedCircuitResourceTopSummary summary)
        summaries.length))
    (normalizedCircuitDescriptionFamilyBits inputLength summary)
    (normalizedCircuitThresholdDescriptionFuel inputLength
      (normalizedCircuitResourceTopSummary summary) summaries)
    (normalizedCircuitThresholdDescriptionMetric inputLength
      (normalizedCircuitResourceTopSummary summary) summaries)
    (by omega) hinput hsourceWide hsourceOutput
  rw [normalizedCircuitDescriptionFamilyProgram,
    normalizedCircuitDescriptionFamilyFuel,
    normalizedCircuitDescriptionMetric, if_neg htagNonzero,
    hsummariesView, hprepare]
  simp only [if_neg htagNonzero]
  exact hrun

attribute [irreducible] normalizedCircuitDescriptionFamilyProgram

/-- The single fixed, oracle-free program from a validated normalized-circuit
summary to its exact semantic description size. -/
def normalizedCircuitDescriptionProgram : NPOracleProgram :=
  linkPrograms normalizedCircuitDescriptionPrepareProgram
    normalizedCircuitDescriptionFamilyProgram

@[simp] theorem normalizedCircuitDescriptionProgram_oracleFree :
    OracleFree normalizedCircuitDescriptionProgram := by
  exact oracleFree_linkPrograms normalizedCircuitDescriptionPrepareProgram_oracleFree
    normalizedCircuitDescriptionFamilyProgram_oracleFree

def normalizedCircuitDescriptionBits (inputLength summary : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (normalizedCircuitDescriptionPrepareBits inputLength summary)
      (normalizedCircuitDescriptionFamilyBits inputLength summary)

def normalizedCircuitDescriptionFuel (inputLength summary : ℕ) : ℕ :=
  linkFuel normalizedCircuitDescriptionFamilyProgram
    (normalizedCircuitDescriptionPrepareFuel summary)
    (normalizedCircuitDescriptionFamilyFuel inputLength summary)

private theorem normalizedCircuitDescriptionPrepareBits_le
    (inputLength summary : ℕ) :
    normalizedCircuitDescriptionPrepareBits inputLength summary ≤
      normalizedCircuitDescriptionBits inputLength summary := by
  let tail := max
    (normalizedCircuitDescriptionPrepareBits inputLength summary)
    (normalizedCircuitDescriptionFamilyBits inputLength summary)
  have hone :
      normalizedCircuitDescriptionPrepareBits inputLength summary ≤ tail :=
    Nat.le_max_left _ _
  have htwo : tail ≤ max (natBitLength inputLength) tail :=
    Nat.le_max_right _ _
  have hthree : max (natBitLength inputLength) tail ≤
      max 1 (max (natBitLength inputLength) tail) :=
    Nat.le_max_right _ _
  exact hone.trans (htwo.trans hthree)

private theorem normalizedCircuitDescriptionFamilyBits_le
    (inputLength summary : ℕ) :
    normalizedCircuitDescriptionFamilyBits inputLength summary ≤
      normalizedCircuitDescriptionBits inputLength summary := by
  let tail := max
    (normalizedCircuitDescriptionPrepareBits inputLength summary)
    (normalizedCircuitDescriptionFamilyBits inputLength summary)
  have hone :
      normalizedCircuitDescriptionFamilyBits inputLength summary ≤ tail :=
    Nat.le_max_right _ _
  have htwo : tail ≤ max (natBitLength inputLength) tail :=
    Nat.le_max_right _ _
  have hthree : max (natBitLength inputLength) tail ≤
      max 1 (max (natBitLength inputLength) tail) :=
    Nat.le_max_right _ _
  exact hone.trans (htwo.trans hthree)

theorem run_normalizedCircuitDescriptionProgram_symmetric
    (inputLength summary : ℕ) (summaries : List ℕ)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 1)
    (hsummaries : decodeBalancedList
      (normalizedCircuitResourceBottomSummariesCode summary) = some summaries)
    (hcanonical : NormalizedGateDescriptionSummariesCanonical summaries) :
    runNPOracleProgram normalizedCircuitDescriptionProgram
        (normalizedCircuitDescriptionBits inputLength summary)
        (normalizedCircuitDescriptionFuel inputLength summary)
        (initialNPOracleState inputLength summary) =
      some (normalizedCircuitDescriptionMetric inputLength summary) := by
  have hpositive : 1 ≤ normalizedCircuitDescriptionBits inputLength summary := by
    simp [normalizedCircuitDescriptionBits]
  have hinputLength : natBitLength inputLength ≤
      normalizedCircuitDescriptionBits inputLength summary := by
    simp [normalizedCircuitDescriptionBits]
  have hprepare := run_bits_mono
    (run_normalizedCircuitDescriptionPrepareProgram inputLength summary)
    (normalizedCircuitDescriptionPrepareBits_le inputLength summary)
  have hfamilyRun := run_bits_mono
    (run_normalizedCircuitDescriptionFamilyProgram_symmetric inputLength summary
      summaries hfamily hsummaries hcanonical)
    (normalizedCircuitDescriptionFamilyBits_le inputLength summary)
  rw [normalizedCircuitDescriptionProgram, normalizedCircuitDescriptionFuel]
  exact run_linkPrograms hpositive hinputLength hprepare hfamilyRun

theorem run_normalizedCircuitDescriptionProgram_threshold
    (inputLength summary : ℕ) (summaries : List ℕ)
    (threshold : ℤ) (weights : List ℤ)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 2)
    (hsummaries : decodeBalancedList
      (normalizedCircuitResourceBottomSummariesCode summary) = some summaries)
    (hstoredLength : normalizedCircuitResourceBottomLength summary =
      summaries.length)
    (hcanonical : NormalizedGateDescriptionSummariesCanonical summaries)
    (hthreshold : normalizedGateDescriptionThresholdCode
      (normalizedCircuitResourceTopSummary summary) = encodeInt threshold)
    (hweights : normalizedGateDescriptionSelectedWeightsCode
      (normalizedCircuitResourceTopSummary summary) = encodeIntList weights) :
    runNPOracleProgram normalizedCircuitDescriptionProgram
        (normalizedCircuitDescriptionBits inputLength summary)
        (normalizedCircuitDescriptionFuel inputLength summary)
        (initialNPOracleState inputLength summary) =
      some (normalizedCircuitDescriptionMetric inputLength summary) := by
  have hpositive : 1 ≤ normalizedCircuitDescriptionBits inputLength summary := by
    simp [normalizedCircuitDescriptionBits]
  have hinputLength : natBitLength inputLength ≤
      normalizedCircuitDescriptionBits inputLength summary := by
    simp [normalizedCircuitDescriptionBits]
  have hprepare := run_bits_mono
    (run_normalizedCircuitDescriptionPrepareProgram inputLength summary)
    (normalizedCircuitDescriptionPrepareBits_le inputLength summary)
  have hfamilyRun := run_bits_mono
    (run_normalizedCircuitDescriptionFamilyProgram_threshold inputLength summary
      summaries threshold weights hfamily hsummaries hstoredLength hcanonical
      hthreshold hweights)
    (normalizedCircuitDescriptionFamilyBits_le inputLength summary)
  rw [normalizedCircuitDescriptionProgram, normalizedCircuitDescriptionFuel]
  exact run_linkPrograms hpositive hinputLength hprepare hfamilyRun

/-! ## Typed semantic refinement -/

/-- The summary ABI emitted by validation for a typed supported gate.  Keeping
this definition at the validated-output boundary prevents a second circuit
decoder from becoming an alternative source of truth. -/
def normalizedGateValidatedSummary {inputLength : ℕ}
    (gate : SupportedNormalizedGate inputLength) : ℕ :=
  supportedGateRelationOutput inputLength (encodeSupportedNormalizedGate gate)

private def normalizedGateSupportBits {inputLength : ℕ}
    (gate : SupportedNormalizedGate inputLength) : List Bool :=
  List.ofFn fun index => decide (index ∈ gate.support)

theorem normalizedGateValidatedSummary_eq {inputLength : ℕ}
    (gate : SupportedNormalizedGate inputLength) :
    normalizedGateValidatedSummary gate =
      Nat.pair 1 (supportedGateCompressedPayload
        (encodeInt gate.gate.threshold)
        (encodeIntList (List.ofFn (supportCompressedGate gate).weight))
        gate.support.card
        (encodeBoolList (normalizedGateSupportBits gate))) := by
  let weights := List.ofFn gate.gate.weight
  let supportBits := normalizedGateSupportBits gate
  have hzeroOutside :
      List.Forall₂ (fun weight bit => bit = false → weight = 0)
        weights supportBits := by
    apply List.forall₂_of_length_eq_of_get
    · simp [weights, supportBits, normalizedGateSupportBits]
    · intro index hweights hsupport
      simp only [weights, supportBits, normalizedGateSupportBits, List.get_ofFn]
      intro hfalse
      apply gate.zeroOutside
      simpa using hfalse
  have hrelation := supportedGateRelationOutput_eq_of_fields inputLength
    (encodeSupportedNormalizedGate gate)
    (encodeIntList weights)
    (encodeInt gate.gate.threshold)
    (encodeBoolList supportBits)
    weights gate.gate.threshold supportBits
    (by simp [encodeSupportedNormalizedGate, weights, supportBits,
      normalizedGateSupportBits])
    (by simp [weights])
    (by simp)
    (by simp [supportBits])
    (by simp [weights])
    (by simp [supportBits, normalizedGateSupportBits])
    hzeroOutside
  rw [normalizedGateValidatedSummary]
  change supportedGateRelationOutput inputLength
      (encodeSupportedNormalizedGate gate) =
    Nat.pair 1 (supportedGateCompressedPayload
      (encodeInt gate.gate.threshold)
      (encodeBalancedList (supportedWeights
        ((List.ofFn gate.gate.weight).map encodeInt)
        (List.ofFn fun index => decide (index ∈ gate.support))))
      (nonzeroSupportCount
        (List.ofFn fun index => decide (index ∈ gate.support)))
      (encodeBoolList
        (List.ofFn fun index => decide (index ∈ gate.support)))) at hrelation
  rw [supportedWeights_eq_supportCompressedGate gate,
    nonzeroSupportCount_eq_supportCard gate] at hrelation
  simpa only [encodeIntList, normalizedGateSupportBits] using hrelation

private def semanticSupportedWeights : List ℤ → List Bool → List ℤ
  | weight :: weights, bit :: support =>
      if bit then
        weight :: semanticSupportedWeights weights support
      else
        semanticSupportedWeights weights support
  | _, _ => []

private theorem semanticSupportedWeights_map_encodeInt
    (weights : List ℤ) (support : List Bool) :
    (semanticSupportedWeights weights support).map encodeInt =
      supportedWeights (weights.map encodeInt) support := by
  induction weights generalizing support with
  | nil => simp [semanticSupportedWeights, supportedWeights]
  | cons weight weights inductionHypothesis =>
      cases support with
      | nil => simp [semanticSupportedWeights, supportedWeights]
      | cons bit support =>
          cases bit <;>
            simp [semanticSupportedWeights, supportedWeights,
              inductionHypothesis]

private theorem map_encodeInt_injective {left right : List ℤ}
    (hequal : left.map encodeInt = right.map encodeInt) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp_all
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => simp at hequal
      | cons otherHead otherTail =>
          simp only [List.map_cons, List.cons.injEq] at hequal
          have hhead : head = otherHead := by
            have := congrArg decodeInt hequal.1
            simpa using this
          rw [hhead, inductionHypothesis hequal.2]

private theorem nonzeroSupportCount_le_length (support : List Bool) :
    nonzeroSupportCount support ≤ support.length := by
  induction support with
  | nil => simp [nonzeroSupportCount]
  | cons bit support inductionHypothesis =>
      cases bit <;> simp [nonzeroSupportCount] <;> omega

private theorem semanticSupportedWeights_charge
    {weights : List ℤ} {support : List Bool}
    (hzeroOutside : List.Forall₂
      (fun weight bit => bit = false → weight = 0) weights support) :
    (weights.map intBitLength).sum =
      ((semanticSupportedWeights weights support).map intBitLength).sum +
        (weights.length - nonzeroSupportCount support) := by
  induction hzeroOutside with
  | nil => simp [semanticSupportedWeights, nonzeroSupportCount]
  | @cons weight bit weights support hzero htail inductionHypothesis =>
      cases bit with
      | false =>
          have hweight : weight = 0 := hzero rfl
          have hcount := nonzeroSupportCount_le_length support
          have hlength := List.Forall₂.length_eq htail
          subst weight
          simp [semanticSupportedWeights, nonzeroSupportCount,
            intBitLength, inductionHypothesis]
          omega
      | true =>
          have hcount := nonzeroSupportCount_le_length support
          have hlength := List.Forall₂.length_eq htail
          simp [semanticSupportedWeights, nonzeroSupportCount,
            inductionHypothesis]
          omega

private theorem normalizedGateSemanticSupportedWeights_eq
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    semanticSupportedWeights (List.ofFn gate.gate.weight)
        (normalizedGateSupportBits gate) =
      List.ofFn (supportCompressedGate gate).weight := by
  apply map_encodeInt_injective
  rw [semanticSupportedWeights_map_encodeInt]
  simpa only [normalizedGateSupportBits] using
    supportedWeights_eq_supportCompressedGate gate

private theorem normalizedGateWeightCharge
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    ((List.ofFn gate.gate.weight).map intBitLength).sum =
      ((List.ofFn (supportCompressedGate gate).weight).map
          intBitLength).sum +
        (inputLength - gate.support.card) := by
  have hzeroOutside : List.Forall₂
      (fun weight bit => bit = false → weight = 0)
      (List.ofFn gate.gate.weight) (normalizedGateSupportBits gate) := by
    apply List.forall₂_of_length_eq_of_get
    · simp [normalizedGateSupportBits]
    · intro index hweights hsupport
      simp only [normalizedGateSupportBits, List.get_ofFn]
      intro hfalse
      apply gate.zeroOutside
      simpa using hfalse
  have hcharge := semanticSupportedWeights_charge hzeroOutside
  rw [normalizedGateSemanticSupportedWeights_eq gate] at hcharge
  simpa [normalizedGateSupportBits,
    nonzeroSupportCount_eq_supportCard gate] using hcharge

@[simp] theorem normalizedGateValidatedSummary_thresholdCode
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    normalizedGateDescriptionThresholdCode
        (normalizedGateValidatedSummary gate) =
      encodeInt gate.gate.threshold := by
  rw [normalizedGateValidatedSummary_eq]
  simp [normalizedGateDescriptionThresholdCode,
    supportedGateCompressedPayload]

@[simp] theorem normalizedGateValidatedSummary_selectedWeightsCode
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    normalizedGateDescriptionSelectedWeightsCode
        (normalizedGateValidatedSummary gate) =
      encodeIntList (List.ofFn (supportCompressedGate gate).weight) := by
  rw [normalizedGateValidatedSummary_eq]
  simp [normalizedGateDescriptionSelectedWeightsCode,
    supportedGateCompressedPayload]

@[simp] theorem normalizedGateValidatedSummary_supportCount
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    normalizedGateDescriptionSupportCount
        (normalizedGateValidatedSummary gate) = gate.support.card := by
  rw [normalizedGateValidatedSummary_eq]
  simp [normalizedGateDescriptionSupportCount,
    supportedGateCompressedPayload]

theorem normalizedGateValidatedSummary_metric_eq_descriptionBits
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    normalizedGateDescriptionMetric inputLength
        (normalizedGateValidatedSummary gate) = gate.descriptionBits := by
  have hcharge := normalizedGateWeightCharge gate
  rw [normalizedGateDescriptionMetric]
  unfold normalizedGateDescriptionThreshold
    normalizedGateDescriptionSelectedWeights
  rw [
    normalizedGateValidatedSummary_thresholdCode,
    normalizedGateValidatedSummary_selectedWeightsCode,
    normalizedGateValidatedSummary_supportCount]
  simp only [decodeInt_encode,
    decodeIntList_encode, Option.getD_some]
  have hfull :
      (∑ index, intBitLength (gate.gate.weight index)) =
        ((List.ofFn (supportCompressedGate gate).weight).map
            intBitLength).sum +
          (inputLength - gate.support.card) := by
    rw [← List.sum_ofFn]
    change (List.ofFn (intBitLength ∘ gate.gate.weight)).sum =
      ((List.ofFn (supportCompressedGate gate).weight).map
          intBitLength).sum + (inputLength - gate.support.card)
    simpa only [List.map_ofFn] using hcharge
  rw [SupportedNormalizedGate.descriptionBits,
    NormalizedThresholdGate.encodingBits]
  omega

/-- Canonical validator summaries for a typed bottom layer, in circuit order. -/
def normalizedBottomValidatedSummaries {inputLength bottomCount : ℕ}
    (bottom : Fin bottomCount → SupportedNormalizedGate inputLength) : List ℕ :=
  List.ofFn fun index => normalizedGateValidatedSummary (bottom index)

theorem normalizedBottomValidatedSummaries_canonical
    {inputLength bottomCount : ℕ}
    (bottom : Fin bottomCount → SupportedNormalizedGate inputLength) :
    NormalizedGateDescriptionSummariesCanonical
      (normalizedBottomValidatedSummaries bottom) := by
  intro summary hsummary
  rw [normalizedBottomValidatedSummaries, List.mem_ofFn] at hsummary
  rcases hsummary with ⟨index, rfl⟩
  constructor
  · rw [normalizedGateValidatedSummary_thresholdCode]
    simp [normalizedGateDescriptionThreshold]
  · rw [normalizedGateValidatedSummary_selectedWeightsCode]
    simp [normalizedGateDescriptionSelectedWeights]

private theorem normalizedBottomValidatedDescriptionMetrics
    {inputLength bottomCount : ℕ}
    (bottom : Fin bottomCount → SupportedNormalizedGate inputLength) :
    normalizedGateDescriptionMetrics inputLength
        (normalizedBottomValidatedSummaries bottom) =
      List.ofFn fun index => (bottom index).descriptionBits := by
  rw [normalizedGateDescriptionMetrics, normalizedBottomValidatedSummaries,
    List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext index
  exact normalizedGateValidatedSummary_metric_eq_descriptionBits (bottom index)

theorem normalizedCircuitSymmetricDescriptionMetric_refines
    {inputLength : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit inputLength) :
    normalizedCircuitSymmetricDescriptionMetric inputLength
        circuit.bottomCount
        (normalizedBottomValidatedSummaries circuit.bottom) =
      circuit.descriptionBits := by
  rw [normalizedCircuitSymmetricDescriptionMetric,
    normalizedBottomValidatedDescriptionMetrics,
    NormalizedSymmetricThresholdCircuit.descriptionBits,
    List.sum_ofFn]
  omega

theorem normalizedCircuitThresholdDescriptionMetric_refines
    {inputLength : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit inputLength) :
    normalizedCircuitThresholdDescriptionMetric inputLength
        (normalizedGateValidatedSummary circuit.top)
        (normalizedBottomValidatedSummaries circuit.bottom) =
      circuit.descriptionBits := by
  have hlength :
      (normalizedBottomValidatedSummaries circuit.bottom).length =
        circuit.bottomCount := by
    simp [normalizedBottomValidatedSummaries]
  rw [normalizedCircuitThresholdDescriptionMetric, hlength,
    normalizedGateValidatedSummary_metric_eq_descriptionBits,
    normalizedBottomValidatedDescriptionMetrics,
    NormalizedThresholdThresholdCircuit.descriptionBits, List.sum_ofFn]

/-- The validated symmetric ABI fields determine the semantic description size
without retaining or reparsing raw circuit syntax. -/
theorem normalizedCircuitDescriptionMetric_refines_symmetric
    {inputLength : ℕ}
    (summary : ℕ)
    (circuit : NormalizedSymmetricThresholdCircuit inputLength)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 1)
    (hsummaries : normalizedCircuitResourceBottomSummariesCode summary =
      encodeBalancedList
        (normalizedBottomValidatedSummaries circuit.bottom))
    (hbottomLength : normalizedCircuitResourceBottomLength summary =
      circuit.bottomCount) :
    normalizedCircuitDescriptionMetric inputLength summary =
      circuit.descriptionBits := by
  have htag : normalizedCircuitDescriptionBranchTag summary = 0 := by
    simp [normalizedCircuitDescriptionBranchTag, hfamily]
  rw [normalizedCircuitDescriptionMetric, if_pos htag]
  rw [hbottomLength]
  have hdecoded : normalizedCircuitResourceSummaries summary =
      normalizedBottomValidatedSummaries circuit.bottom := by
    simp [normalizedCircuitResourceSummaries, hsummaries]
  rw [hdecoded]
  exact normalizedCircuitSymmetricDescriptionMetric_refines circuit

/-- The validated threshold ABI fields determine both the top and every bottom
gate's semantic description size, including omitted zero coefficients. -/
theorem normalizedCircuitDescriptionMetric_refines_threshold
    {inputLength : ℕ}
    (summary : ℕ)
    (circuit : NormalizedThresholdThresholdCircuit inputLength)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 2)
    (htop : normalizedCircuitResourceTopSummary summary =
      normalizedGateValidatedSummary circuit.top)
    (hsummaries : normalizedCircuitResourceBottomSummariesCode summary =
      encodeBalancedList
        (normalizedBottomValidatedSummaries circuit.bottom)) :
    normalizedCircuitDescriptionMetric inputLength summary =
      circuit.descriptionBits := by
  have htag : normalizedCircuitDescriptionBranchTag summary = 1 := by
    simp [normalizedCircuitDescriptionBranchTag, hfamily]
  have htagNonzero : normalizedCircuitDescriptionBranchTag summary ≠ 0 := by
    omega
  rw [normalizedCircuitDescriptionMetric, if_neg htagNonzero, htop]
  have hdecoded : normalizedCircuitResourceSummaries summary =
      normalizedBottomValidatedSummaries circuit.bottom := by
    simp [normalizedCircuitResourceSummaries, hsummaries]
  rw [hdecoded]
  exact normalizedCircuitThresholdDescriptionMetric_refines circuit

/-- End-to-end execution refinement for the symmetric circuit family. -/
theorem run_normalizedCircuitDescriptionProgram_refines_symmetric
    {inputLength : ℕ}
    (summary : ℕ)
    (circuit : NormalizedSymmetricThresholdCircuit inputLength)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 1)
    (hsummaries : normalizedCircuitResourceBottomSummariesCode summary =
      encodeBalancedList
        (normalizedBottomValidatedSummaries circuit.bottom))
    (hbottomLength : normalizedCircuitResourceBottomLength summary =
      circuit.bottomCount) :
    runNPOracleProgram normalizedCircuitDescriptionProgram
        (normalizedCircuitDescriptionBits inputLength summary)
        (normalizedCircuitDescriptionFuel inputLength summary)
        (initialNPOracleState inputLength summary) =
      some circuit.descriptionBits := by
  have hdecoded : decodeBalancedList
      (normalizedCircuitResourceBottomSummariesCode summary) =
      some (normalizedBottomValidatedSummaries circuit.bottom) := by
    simp [hsummaries]
  have hrun := run_normalizedCircuitDescriptionProgram_symmetric
    inputLength summary (normalizedBottomValidatedSummaries circuit.bottom)
    hfamily hdecoded
    (normalizedBottomValidatedSummaries_canonical circuit.bottom)
  rw [normalizedCircuitDescriptionMetric_refines_symmetric summary circuit
    hfamily hsummaries hbottomLength] at hrun
  exact hrun

/-- End-to-end execution refinement for the threshold circuit family. -/
theorem run_normalizedCircuitDescriptionProgram_refines_threshold
    {inputLength : ℕ}
    (summary : ℕ)
    (circuit : NormalizedThresholdThresholdCircuit inputLength)
    (hfamily : normalizedCircuitResourceFamilyTag summary = 2)
    (htop : normalizedCircuitResourceTopSummary summary =
      normalizedGateValidatedSummary circuit.top)
    (hsummaries : normalizedCircuitResourceBottomSummariesCode summary =
      encodeBalancedList
        (normalizedBottomValidatedSummaries circuit.bottom))
    (hbottomLength : normalizedCircuitResourceBottomLength summary =
      circuit.bottomCount) :
    runNPOracleProgram normalizedCircuitDescriptionProgram
        (normalizedCircuitDescriptionBits inputLength summary)
        (normalizedCircuitDescriptionFuel inputLength summary)
        (initialNPOracleState inputLength summary) =
      some circuit.descriptionBits := by
  have hdecoded : decodeBalancedList
      (normalizedCircuitResourceBottomSummariesCode summary) =
      some (normalizedBottomValidatedSummaries circuit.bottom) := by
    simp [hsummaries]
  have htopThreshold : normalizedGateDescriptionThresholdCode
      (normalizedCircuitResourceTopSummary summary) =
      encodeInt circuit.top.gate.threshold := by
    rw [htop]
    exact normalizedGateValidatedSummary_thresholdCode circuit.top
  have htopWeights : normalizedGateDescriptionSelectedWeightsCode
      (normalizedCircuitResourceTopSummary summary) =
      encodeIntList (List.ofFn (supportCompressedGate circuit.top).weight) := by
    rw [htop]
    exact normalizedGateValidatedSummary_selectedWeightsCode circuit.top
  have hstoredLength : normalizedCircuitResourceBottomLength summary =
      (normalizedBottomValidatedSummaries circuit.bottom).length := by
    rw [hbottomLength]
    simp [normalizedBottomValidatedSummaries]
  have hrun := run_normalizedCircuitDescriptionProgram_threshold
    inputLength summary (normalizedBottomValidatedSummaries circuit.bottom)
    circuit.top.gate.threshold
    (List.ofFn (supportCompressedGate circuit.top).weight)
    hfamily hdecoded hstoredLength
    (normalizedBottomValidatedSummaries_canonical circuit.bottom)
    htopThreshold htopWeights
  rw [normalizedCircuitDescriptionMetric_refines_threshold summary circuit
    hfamily htop hsummaries] at hrun
  exact hrun

end NearCubicWires.CanonicalNormalizedCircuitDescriptionProgram
