import Proof.MachineModel.CanonicalBalancedValidationMapProgram
import Proof.MachineModel.CanonicalBoolListValidationProgram
import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.MachineModel.CanonicalNativeEqualityProgram
import Proof.MachineModel.CanonicalNatValidationProgram
import Proof.MachineModel.CanonicalSupportedGateRelationProgram
import Proof.MachineModel.CanonicalTaggedTupleProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.MachineModel.TaggedProgramChoice

/-!
# Total normalized-circuit validation

The production validator shares one bottom-gate traversal across both
normalized circuit families.  This first layer is the common semantic
firewall: it validates every bottom gate at the declared arity while retaining
the mapped gate summaries, exact length, and original balanced tree for the
family-specific top validator.
-/

namespace NearCubicWires.CanonicalNormalizedCircuitValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBoolListValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalSupportedGateRelationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

def normalizedCircuitBottomRequestOutput (request : ℕ) : ℕ :=
  supportedGateRelationOutput (Nat.unpair request).1
    (Nat.unpair request).2

def normalizedCircuitBottomRequestFuel (request : ℕ) : ℕ :=
  supportedGateRelationFuel (Nat.unpair request).1
    (Nat.unpair request).2

def normalizedCircuitBottomRequestBits (request : ℕ) : ℕ :=
  supportedGateRelationBits (Nat.unpair request).1
    (Nat.unpair request).2

def normalizedCircuitBottomSummaryOutput
    (inputArity bottomTree : ℕ) : ℕ :=
  balancedValidationSummaryOutput inputArity bottomTree
    normalizedCircuitBottomRequestOutput

def normalizedCircuitBottomSummaryProgram : NPOracleProgram :=
  balancedValidationSummaryProgram supportedGateRelationProgram

@[simp] theorem normalizedCircuitBottomSummaryProgram_oracleFree :
    OracleFree normalizedCircuitBottomSummaryProgram :=
  balancedValidationSummaryProgram_oracleFree supportedGateRelationProgram
    supportedGateRelationProgram_oracleFree

def normalizedCircuitBottomSummaryFuel
    (inputArity bottomTree : ℕ) : ℕ :=
  balancedValidationSummaryFuel supportedGateRelationProgram
    normalizedCircuitBottomRequestFuel inputArity bottomTree
    normalizedCircuitBottomRequestOutput

def normalizedCircuitBottomSummaryBits
    (inputArity bottomTree : ℕ) : ℕ :=
  balancedValidationSummaryBits normalizedCircuitBottomRequestBits
    normalizedCircuitBottomRequestOutput inputArity bottomTree

theorem run_normalizedCircuitBottomSummaryProgram
    (inputArity bottomTree : ℕ) :
    runNPOracleProgram normalizedCircuitBottomSummaryProgram
        (normalizedCircuitBottomSummaryBits inputArity bottomTree)
        (normalizedCircuitBottomSummaryFuel inputArity bottomTree)
        (initialNPOracleState inputArity bottomTree) =
      some (normalizedCircuitBottomSummaryOutput inputArity bottomTree) := by
  apply run_balancedValidationSummaryProgram supportedGateRelationProgram
    normalizedCircuitBottomRequestBits
    normalizedCircuitBottomRequestFuel
    normalizedCircuitBottomRequestOutput inputArity bottomTree
  intro request _
  exact
    run_supportedGateRelationProgram
      (Nat.unpair request).1 (Nat.unpair request).2

theorem normalizedCircuitBottomSummaryOutput_ne_zero_iff
    (inputArity bottomTree : ℕ) :
    normalizedCircuitBottomSummaryOutput inputArity bottomTree ≠ 0 ↔
      ∃ codes,
        decodeBalancedList bottomTree = some codes ∧
          ∀ code, code ∈ codes →
            (decodeSupportedNormalizedGate inputArity code).isSome := by
  rw [normalizedCircuitBottomSummaryOutput,
    balancedValidationSummaryOutput_ne_zero_iff]
  constructor
  · rintro ⟨codes, hdecode, hvalid⟩
    refine ⟨codes, hdecode, ?_⟩
    intro code hcode
    have houtput :=
      hvalid code hcode
    have hrelation :
        supportedGateRelationOutput inputArity code ≠ 0 := by
      simpa [normalizedCircuitBottomRequestOutput, nativeInputRequest] using
        houtput
    exact
      (supportedGateRelationOutput_ne_zero_iff_decode
        inputArity code).1 hrelation
  · rintro ⟨codes, hdecode, hvalid⟩
    refine ⟨codes, hdecode, ?_⟩
    intro code hcode
    have hdecoded := hvalid code hcode
    simpa [normalizedCircuitBottomRequestOutput, nativeInputRequest] using
      (supportedGateRelationOutput_ne_zero_iff_decode
        inputArity code).2 hdecoded

theorem normalizedCircuitBottomSummaryOutput_payload
    (inputArity bottomTree : ℕ)
    (hnonzero :
      normalizedCircuitBottomSummaryOutput inputArity bottomTree ≠ 0) :
    (Nat.unpair
      (normalizedCircuitBottomSummaryOutput inputArity bottomTree)).2 =
        balancedValidationSummaryData inputArity bottomTree
          normalizedCircuitBottomRequestOutput := by
  exact balancedValidationSummaryOutput_payload inputArity bottomTree
    normalizedCircuitBottomRequestOutput hnonzero

/-! ## Exact four-field request prefix -/

def normalizedCircuitExpectedFamily (request : ℕ) : ℕ :=
  (Nat.unpair request).1

def normalizedCircuitRawCode (request : ℕ) : ℕ :=
  (Nat.unpair request).2

def normalizedCircuitTupleOutput (request : ℕ) : ℕ :=
  taggedTupleOutput 4 (normalizedCircuitRawCode request)

def normalizedCircuitTupleFlag (request : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitTupleOutput request)).1

def normalizedCircuitTupleFields (request : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitTupleOutput request)).2

def normalizedCircuitTopCode (request : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitTupleFields request)).2

def normalizedCircuitBeforeTop (request : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitTupleFields request)).1

def normalizedCircuitBottomCode (request : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitBeforeTop request)).2

def normalizedCircuitBeforeBottom (request : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitBeforeTop request)).1

def normalizedCircuitCountCode (request : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitBeforeBottom request)).2

def normalizedCircuitBeforeCount (request : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitBeforeBottom request)).1

def normalizedCircuitFamilyCode (request : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitBeforeCount request)).2

theorem normalizedCircuitTupleAccessors_of_decode
    {request familyCode countCode bottomCode topCode : ℕ}
    (hdecode :
      decodeTaggedList (normalizedCircuitRawCode request) =
        some [familyCode, countCode, bottomCode, topCode]) :
    normalizedCircuitTupleFlag request = 1 ∧
      normalizedCircuitFamilyCode request = familyCode ∧
      normalizedCircuitCountCode request = countCode ∧
      normalizedCircuitBottomCode request = bottomCode ∧
      normalizedCircuitTopCode request = topCode := by
  have hcode :=
    encodeTaggedList_of_decode hdecode
  simp only [normalizedCircuitTupleFlag, normalizedCircuitTupleOutput,
    normalizedCircuitTupleFields, normalizedCircuitTopCode,
    normalizedCircuitBeforeTop, normalizedCircuitBottomCode,
    normalizedCircuitBeforeBottom, normalizedCircuitCountCode,
    normalizedCircuitBeforeCount, normalizedCircuitFamilyCode]
  rw [← hcode]
  have htuple :
      decodeTaggedTuple 4
          (encodeTaggedList
            [familyCode, countCode, bottomCode, topCode]) =
        some
          (reversePairFields
            [familyCode, countCode, bottomCode, topCode]) := by
    simpa using
      decodeTaggedTuple_encode
        [familyCode, countCode, bottomCode, topCode]
  rw [taggedTupleOutput, htuple]
  simp [reversePairFields]

theorem normalizedCircuitTupleFlag_ne_zero_iff
    (request : ℕ) :
    normalizedCircuitTupleFlag request ≠ 0 ↔
      ∃ familyCode countCode bottomCode topCode,
        decodeTaggedList (normalizedCircuitRawCode request) =
          some [familyCode, countCode, bottomCode, topCode] := by
  have hflag :
      normalizedCircuitTupleFlag request ≠ 0 ↔
        normalizedCircuitTupleOutput request ≠ 0 := by
    unfold normalizedCircuitTupleFlag normalizedCircuitTupleOutput
    cases hdecode :
        decodeTaggedTuple 4 (normalizedCircuitRawCode request) with
    | none =>
        simp [taggedTupleOutput, hdecode]
    | some fields =>
        have hnonzero : Nat.pair 1 fields ≠ 0 := by
          have hleft := Nat.left_le_pair 1 fields
          omega
        simp [taggedTupleOutput, hdecode, hnonzero]
  rw [hflag, normalizedCircuitTupleOutput,
    taggedTupleOutput_ne_zero_iff_decodeTaggedList]
  constructor
  · rintro ⟨values, hdecode, hlength⟩
    rcases values with _ | ⟨familyCode, values⟩
    · simp at hlength
    rcases values with _ | ⟨countCode, values⟩
    · simp at hlength
    rcases values with _ | ⟨bottomCode, values⟩
    · simp at hlength
    rcases values with _ | ⟨topCode, values⟩
    · simp at hlength
    have htailLength : values.length = 0 := by
      simpa using hlength
    have htail : values = [] :=
      List.length_eq_zero_iff.mp htailLength
    subst values
    exact ⟨familyCode, countCode, bottomCode, topCode, hdecode⟩
  · rintro ⟨familyCode, countCode, bottomCode, topCode, hdecode⟩
    exact
      ⟨[familyCode, countCode, bottomCode, topCode],
        hdecode, by simp⟩

private theorem normalizedCircuit_bitLength_le_foldr_max
    {value : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    natBitLength value ≤
      (values.map natBitLength).foldr max 1 := by
  induction values with
  | nil => simp at hvalue
  | cons head tail ih =>
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact Nat.le_max_left _ _
      · exact (ih htail).trans (Nat.le_max_right _ _)

def normalizedCircuitTupleLoweringOutput (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitRawCode request) request

def normalizedCircuitTupleLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 3 0 0 3
  , .halt 0
  ]

@[simp] theorem normalizedCircuitTupleLoweringProgram_oracleFree :
    OracleFree normalizedCircuitTupleLoweringProgram := by
  rfl

private def normalizedCircuitTupleLoweringValues
    (inputLength request : ℕ) : List ℕ :=
  [ inputLength
  , request
  , normalizedCircuitExpectedFamily request
  , normalizedCircuitRawCode request
  , normalizedCircuitTupleLoweringOutput request
  ]

def normalizedCircuitTupleLoweringBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedCircuitTupleLoweringValues inputLength request).map
      natBitLength |>.foldr max 1

theorem run_normalizedCircuitTupleLoweringProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitTupleLoweringProgram
        (normalizedCircuitTupleLoweringBits inputLength request) 4
        (initialNPOracleState inputLength request) =
      some (normalizedCircuitTupleLoweringOutput request) := by
  have hbits :
      ∀ value ∈ normalizedCircuitTupleLoweringValues inputLength request,
        natBitLength value ≤
          normalizedCircuitTupleLoweringBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  have hexpected :=
    hbits (normalizedCircuitExpectedFamily request)
      (by simp [normalizedCircuitTupleLoweringValues])
  have hraw :=
    hbits (normalizedCircuitRawCode request)
      (by simp [normalizedCircuitTupleLoweringValues])
  have houtput :=
    hbits (normalizedCircuitTupleLoweringOutput request)
      (by simp [normalizedCircuitTupleLoweringValues])
  rw [show 4 = ((1 + 1) + 1) + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := normalizedCircuitExpectedFamily request)
    (by rfl) rfl
    (by simp [initialNPOracleState,
      normalizedCircuitExpectedFamily])
    hexpected]
  rw [run_unpairRight_instruction
    (value := normalizedCircuitRawCode request)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      normalizedCircuitRawCode])
    hraw]
  rw [run_pair_instruction
    (value := normalizedCircuitTupleLoweringOutput request)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      normalizedCircuitRawCode, normalizedCircuitTupleLoweringOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def normalizedCircuitTupleStageOutput (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitTupleOutput request) request

def normalizedCircuitTupleStageProgram : NPOracleProgram :=
  preserveRightProgram (taggedTupleProgram 4)

@[simp] theorem normalizedCircuitTupleStageProgram_oracleFree :
    OracleFree normalizedCircuitTupleStageProgram :=
  preserveRightProgram_oracleFree (taggedTupleProgram 4)
    (taggedTupleProgram_oracleFree 4)

def normalizedCircuitTupleStageFuel : ℕ :=
  preserveRightFuel (taggedTupleFuel 4)

def normalizedCircuitTupleStageBits
    (inputLength request : ℕ) : ℕ :=
  preserveRightBits
    (taggedTupleBits inputLength 4 (normalizedCircuitRawCode request))
    (normalizedCircuitRawCode request) request
    (normalizedCircuitTupleOutput request)

theorem run_normalizedCircuitTupleStageProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitTupleStageProgram
        (normalizedCircuitTupleStageBits inputLength request)
        normalizedCircuitTupleStageFuel
        (initialNPOracleState inputLength
          (normalizedCircuitTupleLoweringOutput request)) =
      some (normalizedCircuitTupleStageOutput request) := by
  exact run_preserveRightProgram (taggedTupleProgram 4) inputLength
    (taggedTupleBits inputLength 4 (normalizedCircuitRawCode request))
    (taggedTupleFuel 4) (normalizedCircuitRawCode request) request
    (normalizedCircuitTupleOutput request)
    (run_taggedTupleProgram inputLength 4
      (normalizedCircuitRawCode request))

def normalizedCircuitFamilyEqualityRequest (request : ℕ) : ℕ :=
  nativeNatEqInput (normalizedCircuitFamilyCode request)
    (encodeNat (normalizedCircuitExpectedFamily request))

def normalizedCircuitFamilyTail₀ (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitTopCode request) request

def normalizedCircuitFamilyTail₁ (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitBottomCode request)
    (normalizedCircuitFamilyTail₀ request)

def normalizedCircuitFamilyTail₂ (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitCountCode request)
    (normalizedCircuitFamilyTail₁ request)

def normalizedCircuitFamilyContext (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitTupleFlag request)
    (normalizedCircuitFamilyTail₂ request)

def normalizedCircuitFamilyPrepareOutput (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitFamilyEqualityRequest request)
    (normalizedCircuitFamilyContext request)

def normalizedCircuitFamilyPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairRight 5 6 5
  , .unpairLeft 5 5 6
  , .unpairRight 5 7 7
  , .unpairLeft 5 5 8
  , .unpairRight 5 8 9
  , .unpairLeft 5 5 10
  , .unpairRight 5 9 11
  , .unpairLeft 3 10 12
  , .encodeNat 10 11 13
  , .pair 9 11 12 14
  , .pair 6 3 13 15
  , .pair 7 13 13 16
  , .pair 8 13 13 17
  , .pair 4 13 13 18
  , .pair 12 13 0 19
  , .halt 0
  ]

@[simp] theorem normalizedCircuitFamilyPrepareProgram_oracleFree :
    OracleFree normalizedCircuitFamilyPrepareProgram := by
  rfl

private def normalizedCircuitFamilyPrepareValues
    (inputLength request : ℕ) : List ℕ :=
  [ inputLength
  , normalizedCircuitTupleStageOutput request
  , normalizedCircuitTupleOutput request
  , request
  , normalizedCircuitTupleFlag request
  , normalizedCircuitTupleFields request
  , normalizedCircuitBeforeTop request
  , normalizedCircuitTopCode request
  , normalizedCircuitBeforeBottom request
  , normalizedCircuitBottomCode request
  , normalizedCircuitBeforeCount request
  , normalizedCircuitCountCode request
  , normalizedCircuitFamilyCode request
  , normalizedCircuitExpectedFamily request
  , encodeNat (normalizedCircuitExpectedFamily request)
  , normalizedCircuitFamilyEqualityRequest request
  , normalizedCircuitFamilyTail₀ request
  , normalizedCircuitFamilyTail₁ request
  , normalizedCircuitFamilyTail₂ request
  , normalizedCircuitFamilyContext request
  , normalizedCircuitFamilyPrepareOutput request
  ]

def normalizedCircuitFamilyPrepareBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedCircuitFamilyPrepareValues inputLength request).map
      natBitLength |>.foldr max 1

def normalizedCircuitFamilyPrepareFuel : ℕ := 20

theorem run_normalizedCircuitFamilyPrepareProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitFamilyPrepareProgram
        (normalizedCircuitFamilyPrepareBits inputLength request)
        normalizedCircuitFamilyPrepareFuel
        (initialNPOracleState inputLength
          (normalizedCircuitTupleStageOutput request)) =
      some (normalizedCircuitFamilyPrepareOutput request) := by
  have hbits :
      ∀ value ∈ normalizedCircuitFamilyPrepareValues inputLength request,
        natBitLength value ≤
          normalizedCircuitFamilyPrepareBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  simp [normalizedCircuitFamilyPrepareFuel,
    normalizedCircuitFamilyPrepareProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    normalizedCircuitFamilyPrepareValues,
    normalizedCircuitTupleStageOutput,
    normalizedCircuitFamilyPrepareOutput,
    normalizedCircuitFamilyContext,
    normalizedCircuitFamilyTail₂, normalizedCircuitFamilyTail₁,
    normalizedCircuitFamilyTail₀,
    normalizedCircuitFamilyEqualityRequest, nativeNatEqInput,
    normalizedCircuitExpectedFamily,
    normalizedCircuitTupleFlag, normalizedCircuitTupleFields,
    normalizedCircuitBeforeTop, normalizedCircuitTopCode,
    normalizedCircuitBeforeBottom, normalizedCircuitBottomCode,
    normalizedCircuitBeforeCount, normalizedCircuitCountCode,
    normalizedCircuitFamilyCode]

def normalizedCircuitFamilyEqualityFlag (request : ℕ) : ℕ :=
  nativeNatEqOutput (normalizedCircuitFamilyCode request)
    (encodeNat (normalizedCircuitExpectedFamily request))

def normalizedCircuitFamilyStageOutput (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitFamilyEqualityFlag request)
    (normalizedCircuitFamilyContext request)

def normalizedCircuitFamilyStageProgram : NPOracleProgram :=
  preserveRightProgram nativeNatEqProgram

@[simp] theorem normalizedCircuitFamilyStageProgram_oracleFree :
    OracleFree normalizedCircuitFamilyStageProgram :=
  preserveRightProgram_oracleFree nativeNatEqProgram
    nativeNatEqProgram_oracleFree

def normalizedCircuitFamilyStageFuel (request : ℕ) : ℕ :=
  preserveRightFuel <|
    nativeNatEqFuel (normalizedCircuitFamilyCode request)
      (encodeNat (normalizedCircuitExpectedFamily request))

def normalizedCircuitFamilyStageBits
    (inputLength request : ℕ) : ℕ :=
  preserveRightBits
    (nativeNatEqBits inputLength
      (normalizedCircuitFamilyCode request)
      (encodeNat (normalizedCircuitExpectedFamily request)))
    (normalizedCircuitFamilyEqualityRequest request)
    (normalizedCircuitFamilyContext request)
    (normalizedCircuitFamilyEqualityFlag request)

theorem run_normalizedCircuitFamilyStageProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitFamilyStageProgram
        (normalizedCircuitFamilyStageBits inputLength request)
        (normalizedCircuitFamilyStageFuel request)
        (initialNPOracleState inputLength
          (normalizedCircuitFamilyPrepareOutput request)) =
      some (normalizedCircuitFamilyStageOutput request) := by
  exact run_preserveRightProgram nativeNatEqProgram inputLength
    (nativeNatEqBits inputLength
      (normalizedCircuitFamilyCode request)
      (encodeNat (normalizedCircuitExpectedFamily request)))
    (nativeNatEqFuel (normalizedCircuitFamilyCode request)
      (encodeNat (normalizedCircuitExpectedFamily request)))
    (normalizedCircuitFamilyEqualityRequest request)
    (normalizedCircuitFamilyContext request)
    (normalizedCircuitFamilyEqualityFlag request)
    (run_nativeNatEqProgram inputLength
      (normalizedCircuitFamilyCode request)
      (encodeNat (normalizedCircuitExpectedFamily request)))

def normalizedCircuitCountContext (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitFamilyEqualityFlag request)
    (normalizedCircuitFamilyContext request)

def normalizedCircuitCountPrepareOutput (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitCountCode request)
    (normalizedCircuitCountContext request)

def normalizedCircuitCountPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .unpairLeft 4 5 4
  , .pair 2 3 6 5
  , .pair 5 6 0 6
  , .halt 0
  ]

@[simp] theorem normalizedCircuitCountPrepareProgram_oracleFree :
    OracleFree normalizedCircuitCountPrepareProgram := by
  rfl

private def normalizedCircuitCountPrepareValues
    (inputLength request : ℕ) : List ℕ :=
  [ inputLength
  , normalizedCircuitFamilyStageOutput request
  , normalizedCircuitFamilyEqualityFlag request
  , normalizedCircuitFamilyContext request
  , normalizedCircuitFamilyTail₂ request
  , normalizedCircuitCountCode request
  , normalizedCircuitCountContext request
  , normalizedCircuitCountPrepareOutput request
  ]

def normalizedCircuitCountPrepareBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedCircuitCountPrepareValues inputLength request).map
      natBitLength |>.foldr max 1

def normalizedCircuitCountPrepareFuel : ℕ := 7

theorem run_normalizedCircuitCountPrepareProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitCountPrepareProgram
        (normalizedCircuitCountPrepareBits inputLength request)
        normalizedCircuitCountPrepareFuel
        (initialNPOracleState inputLength
          (normalizedCircuitFamilyStageOutput request)) =
      some (normalizedCircuitCountPrepareOutput request) := by
  have hbits :
      ∀ value ∈ normalizedCircuitCountPrepareValues inputLength request,
        natBitLength value ≤
          normalizedCircuitCountPrepareBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  simp [normalizedCircuitCountPrepareFuel,
    normalizedCircuitCountPrepareProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    normalizedCircuitCountPrepareValues,
    normalizedCircuitFamilyStageOutput,
    normalizedCircuitCountPrepareOutput,
    normalizedCircuitCountContext,
    normalizedCircuitFamilyContext, normalizedCircuitFamilyTail₂,
    normalizedCircuitCountCode]

def normalizedCircuitCountValidation (request : ℕ) : ℕ :=
  canonicalNatValidationOutput (normalizedCircuitCountCode request)

def normalizedCircuitCountStageOutput (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitCountValidation request)
    (normalizedCircuitCountContext request)

def normalizedCircuitCountStageProgram : NPOracleProgram :=
  preserveRightProgram canonicalNatValidationProgram

@[simp] theorem normalizedCircuitCountStageProgram_oracleFree :
    OracleFree normalizedCircuitCountStageProgram :=
  preserveRightProgram_oracleFree canonicalNatValidationProgram
    canonicalNatValidationProgram_oracleFree

def normalizedCircuitCountStageFuel (request : ℕ) : ℕ :=
  preserveRightFuel <|
    canonicalNatValidationFuel (normalizedCircuitCountCode request)

def normalizedCircuitCountStageBits
    (inputLength request : ℕ) : ℕ :=
  preserveRightBits
    (canonicalNatValidationBits inputLength
      (normalizedCircuitCountCode request))
    (normalizedCircuitCountCode request)
    (normalizedCircuitCountContext request)
    (normalizedCircuitCountValidation request)

theorem run_normalizedCircuitCountStageProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitCountStageProgram
        (normalizedCircuitCountStageBits inputLength request)
        (normalizedCircuitCountStageFuel request)
        (initialNPOracleState inputLength
          (normalizedCircuitCountPrepareOutput request)) =
      some (normalizedCircuitCountStageOutput request) := by
  exact
    run_preserveRightProgram canonicalNatValidationProgram inputLength
      (canonicalNatValidationBits inputLength
        (normalizedCircuitCountCode request))
      (canonicalNatValidationFuel (normalizedCircuitCountCode request))
      (normalizedCircuitCountCode request)
      (normalizedCircuitCountContext request)
      (normalizedCircuitCountValidation request)
      (run_canonicalNatValidationProgram inputLength
        (normalizedCircuitCountCode request))

def normalizedCircuitCountValue (request : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitCountValidation request)).2

def normalizedCircuitBottomContext (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitCountValue request)
    (normalizedCircuitCountStageOutput request)

def normalizedCircuitBottomPrepareOutput (request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitBottomCode request)
    (normalizedCircuitBottomContext request)

def normalizedCircuitBottomPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 2 4 3
  , .unpairRight 3 5 4
  , .unpairRight 5 6 5
  , .unpairRight 6 7 6
  , .unpairLeft 7 8 7
  , .pair 2 3 9 8
  , .pair 4 9 9 9
  , .pair 8 9 0 10
  , .halt 0
  ]

@[simp] theorem normalizedCircuitBottomPrepareProgram_oracleFree :
    OracleFree normalizedCircuitBottomPrepareProgram := by
  rfl

private def normalizedCircuitBottomPrepareValues
    (inputLength request : ℕ) : List ℕ :=
  [ inputLength
  , normalizedCircuitCountStageOutput request
  , normalizedCircuitCountValidation request
  , normalizedCircuitCountContext request
  , normalizedCircuitCountValue request
  , normalizedCircuitFamilyContext request
  , normalizedCircuitFamilyTail₂ request
  , normalizedCircuitFamilyTail₁ request
  , normalizedCircuitBottomCode request
  , normalizedCircuitBottomContext request
  , normalizedCircuitBottomPrepareOutput request
  ]

def normalizedCircuitBottomPrepareBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedCircuitBottomPrepareValues inputLength request).map
      natBitLength |>.foldr max 1

def normalizedCircuitBottomPrepareFuel : ℕ := 11

theorem run_normalizedCircuitBottomPrepareProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitBottomPrepareProgram
        (normalizedCircuitBottomPrepareBits inputLength request)
        normalizedCircuitBottomPrepareFuel
        (initialNPOracleState inputLength
          (normalizedCircuitCountStageOutput request)) =
      some (normalizedCircuitBottomPrepareOutput request) := by
  have hbits :
      ∀ value ∈ normalizedCircuitBottomPrepareValues inputLength request,
        natBitLength value ≤
          normalizedCircuitBottomPrepareBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  simp [normalizedCircuitBottomPrepareFuel,
    normalizedCircuitBottomPrepareProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    normalizedCircuitBottomPrepareValues,
    normalizedCircuitCountStageOutput,
    normalizedCircuitCountValidation, normalizedCircuitCountContext,
    normalizedCircuitCountValue, normalizedCircuitFamilyContext,
    normalizedCircuitFamilyTail₂, normalizedCircuitFamilyTail₁,
    normalizedCircuitBottomCode, normalizedCircuitBottomContext,
    normalizedCircuitBottomPrepareOutput]

def normalizedCircuitBottomStageOutput
    (inputLength request : ℕ) : ℕ :=
  Nat.pair
    (normalizedCircuitBottomSummaryOutput inputLength
      (normalizedCircuitBottomCode request))
    (normalizedCircuitBottomContext request)

def normalizedCircuitBottomStageProgram : NPOracleProgram :=
  preserveRightProgram normalizedCircuitBottomSummaryProgram

@[simp] theorem normalizedCircuitBottomStageProgram_oracleFree :
    OracleFree normalizedCircuitBottomStageProgram :=
  preserveRightProgram_oracleFree normalizedCircuitBottomSummaryProgram
    normalizedCircuitBottomSummaryProgram_oracleFree

def normalizedCircuitBottomStageFuel
    (inputLength request : ℕ) : ℕ :=
  preserveRightFuel <|
    normalizedCircuitBottomSummaryFuel inputLength
      (normalizedCircuitBottomCode request)

def normalizedCircuitBottomStageBits
    (inputLength request : ℕ) : ℕ :=
  preserveRightBits
    (normalizedCircuitBottomSummaryBits inputLength
      (normalizedCircuitBottomCode request))
    (normalizedCircuitBottomCode request)
    (normalizedCircuitBottomContext request)
    (normalizedCircuitBottomSummaryOutput inputLength
      (normalizedCircuitBottomCode request))

theorem run_normalizedCircuitBottomStageProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitBottomStageProgram
        (normalizedCircuitBottomStageBits inputLength request)
        (normalizedCircuitBottomStageFuel inputLength request)
        (initialNPOracleState inputLength
          (normalizedCircuitBottomPrepareOutput request)) =
      some (normalizedCircuitBottomStageOutput inputLength request) := by
  exact run_preserveRightProgram normalizedCircuitBottomSummaryProgram
    inputLength
    (normalizedCircuitBottomSummaryBits inputLength
      (normalizedCircuitBottomCode request))
    (normalizedCircuitBottomSummaryFuel inputLength
      (normalizedCircuitBottomCode request))
    (normalizedCircuitBottomCode request)
    (normalizedCircuitBottomContext request)
    (normalizedCircuitBottomSummaryOutput inputLength
      (normalizedCircuitBottomCode request))
    (run_normalizedCircuitBottomSummaryProgram inputLength
      (normalizedCircuitBottomCode request))

def normalizedCircuitBottomLength
    (inputLength request : ℕ) : ℕ :=
  let summary :=
    normalizedCircuitBottomSummaryOutput inputLength
      (normalizedCircuitBottomCode request)
  (Nat.unpair (Nat.unpair (Nat.unpair summary).2).2).1

def normalizedCircuitLengthEqualityRequest
    (inputLength request : ℕ) : ℕ :=
  nativeNatEqInput (normalizedCircuitCountValue request)
    (normalizedCircuitBottomLength inputLength request)

def normalizedCircuitLengthPrepareOutput
    (inputLength request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitLengthEqualityRequest inputLength request)
    (normalizedCircuitBottomStageOutput inputLength request)

def normalizedCircuitLengthPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 2 4 3
  , .unpairRight 4 5 4
  , .unpairLeft 5 6 5
  , .unpairLeft 3 7 6
  , .pair 7 6 8 7
  , .pair 8 0 0 8
  , .halt 0
  ]

@[simp] theorem normalizedCircuitLengthPrepareProgram_oracleFree :
    OracleFree normalizedCircuitLengthPrepareProgram := by
  rfl

private def normalizedCircuitLengthPrepareValues
    (inputLength request : ℕ) : List ℕ :=
  let summary :=
    normalizedCircuitBottomSummaryOutput inputLength
      (normalizedCircuitBottomCode request)
  let summaryData := (Nat.unpair summary).2
  let summaryTail := (Nat.unpair summaryData).2
  [ inputLength
  , normalizedCircuitBottomStageOutput inputLength request
  , summary
  , normalizedCircuitBottomContext request
  , summaryData
  , summaryTail
  , normalizedCircuitBottomLength inputLength request
  , normalizedCircuitCountValue request
  , normalizedCircuitLengthEqualityRequest inputLength request
  , normalizedCircuitLengthPrepareOutput inputLength request
  ]

def normalizedCircuitLengthPrepareBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedCircuitLengthPrepareValues inputLength request).map
      natBitLength |>.foldr max 1

def normalizedCircuitLengthPrepareFuel : ℕ := 9

theorem run_normalizedCircuitLengthPrepareProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitLengthPrepareProgram
        (normalizedCircuitLengthPrepareBits inputLength request)
        normalizedCircuitLengthPrepareFuel
        (initialNPOracleState inputLength
          (normalizedCircuitBottomStageOutput inputLength request)) =
      some
        (normalizedCircuitLengthPrepareOutput inputLength request) := by
  have hbits :
      ∀ value ∈ normalizedCircuitLengthPrepareValues inputLength request,
        natBitLength value ≤
          normalizedCircuitLengthPrepareBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  simp [normalizedCircuitLengthPrepareFuel,
    normalizedCircuitLengthPrepareProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    normalizedCircuitLengthPrepareValues,
    normalizedCircuitBottomStageOutput,
    normalizedCircuitBottomContext,
    normalizedCircuitBottomLength,
    normalizedCircuitCountValue,
    normalizedCircuitLengthEqualityRequest, nativeNatEqInput,
    normalizedCircuitLengthPrepareOutput]

def normalizedCircuitLengthEqualityFlag
    (inputLength request : ℕ) : ℕ :=
  nativeNatEqOutput (normalizedCircuitCountValue request)
    (normalizedCircuitBottomLength inputLength request)

def normalizedCircuitLengthStageOutput
    (inputLength request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitLengthEqualityFlag inputLength request)
    (normalizedCircuitBottomStageOutput inputLength request)

def normalizedCircuitLengthStageProgram : NPOracleProgram :=
  preserveRightProgram nativeNatEqProgram

@[simp] theorem normalizedCircuitLengthStageProgram_oracleFree :
    OracleFree normalizedCircuitLengthStageProgram :=
  preserveRightProgram_oracleFree nativeNatEqProgram
    nativeNatEqProgram_oracleFree

def normalizedCircuitLengthStageFuel
    (inputLength request : ℕ) : ℕ :=
  preserveRightFuel <|
    nativeNatEqFuel (normalizedCircuitCountValue request)
      (normalizedCircuitBottomLength inputLength request)

def normalizedCircuitLengthStageBits
    (inputLength request : ℕ) : ℕ :=
  preserveRightBits
    (nativeNatEqBits inputLength
      (normalizedCircuitCountValue request)
      (normalizedCircuitBottomLength inputLength request))
    (normalizedCircuitLengthEqualityRequest inputLength request)
    (normalizedCircuitBottomStageOutput inputLength request)
    (normalizedCircuitLengthEqualityFlag inputLength request)

theorem run_normalizedCircuitLengthStageProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitLengthStageProgram
        (normalizedCircuitLengthStageBits inputLength request)
        (normalizedCircuitLengthStageFuel inputLength request)
        (initialNPOracleState inputLength
          (normalizedCircuitLengthPrepareOutput inputLength request)) =
      some (normalizedCircuitLengthStageOutput inputLength request) := by
  exact run_preserveRightProgram nativeNatEqProgram inputLength
    (nativeNatEqBits inputLength
      (normalizedCircuitCountValue request)
      (normalizedCircuitBottomLength inputLength request))
    (nativeNatEqFuel (normalizedCircuitCountValue request)
      (normalizedCircuitBottomLength inputLength request))
    (normalizedCircuitLengthEqualityRequest inputLength request)
    (normalizedCircuitBottomStageOutput inputLength request)
    (normalizedCircuitLengthEqualityFlag inputLength request)
    (run_nativeNatEqProgram inputLength
      (normalizedCircuitCountValue request)
      (normalizedCircuitBottomLength inputLength request))

/-! ## Shared header/bottom gate -/

def normalizedCircuitBottomSummary
    (inputLength request : ℕ) : ℕ :=
  normalizedCircuitBottomSummaryOutput inputLength
    (normalizedCircuitBottomCode request)

def normalizedCircuitBottomSummaryData
    (inputLength request : ℕ) : ℕ :=
  (Nat.unpair (normalizedCircuitBottomSummary inputLength request)).2

def normalizedCircuitHeaderBottomPayload
    (inputLength request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitTopCode request) <|
    Nat.pair (normalizedCircuitCountValue request) <|
      Nat.pair (normalizedCircuitBottomSummaryData inputLength request)
        (normalizedCircuitRawCode request)

def normalizedCircuitHeaderBottomOutput
    (inputLength request : ℕ) : ℕ :=
  if normalizedCircuitLengthEqualityFlag inputLength request = 0 then
    0
  else if normalizedCircuitBottomSummary inputLength request = 0 then
    0
  else if normalizedCircuitCountValidation request = 0 then
    0
  else if normalizedCircuitFamilyEqualityFlag request = 0 then
    0
  else if normalizedCircuitTupleFlag request = 0 then
    0
  else if normalizedCircuitExpectedFamily request = 0 then
    Nat.pair 1
      (normalizedCircuitHeaderBottomPayload inputLength request)
  else if normalizedCircuitExpectedFamily request = 1 then
    Nat.pair 2
      (normalizedCircuitHeaderBottomPayload inputLength request)
  else
    0

def normalizedCircuitHeaderBottomGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .unpairLeft 9 10 9
  , .unpairRight 9 11 10
  , .unpairLeft 11 12 11
  , .unpairRight 11 13 12
  , .unpairRight 13 14 13
  , .unpairRight 14 15 14
  , .unpairLeft 15 16 15
  , .unpairRight 15 17 16
  , .unpairLeft 17 18 17
  , .unpairRight 17 19 18
  , .unpairRight 4 20 19
  , .branchZero 2 35 20
  , .branchZero 4 35 21
  , .branchZero 8 35 22
  , .branchZero 10 35 23
  , .branchZero 12 35 24
  , .branchZero 18 28 25
  , .copy 18 21 26
  , .decrement 21 27
  , .branchZero 21 29 35
  , .set 21 1 30
  , .set 21 2 30
  , .pair 20 19 22 31
  , .pair 6 22 22 32
  , .pair 16 22 22 33
  , .pair 21 22 0 34
  , .halt 0
  , .set 0 0 36
  , .halt 0
  ]

@[simp] theorem normalizedCircuitHeaderBottomGateProgram_oracleFree :
    OracleFree normalizedCircuitHeaderBottomGateProgram := by
  rfl

private def normalizedCircuitHeaderBottomGateValues
    (inputLength request : ℕ) : List ℕ :=
  let lengthFlag :=
    normalizedCircuitLengthEqualityFlag inputLength request
  let bottomSummary :=
    normalizedCircuitBottomSummary inputLength request
  let bottomContext := normalizedCircuitBottomContext request
  let countStage := normalizedCircuitCountStageOutput request
  let countContext := normalizedCircuitCountContext request
  let familyContext := normalizedCircuitFamilyContext request
  let tail₂ := normalizedCircuitFamilyTail₂ request
  let tail₁ := normalizedCircuitFamilyTail₁ request
  let tail₀ := normalizedCircuitFamilyTail₀ request
  let expected := normalizedCircuitExpectedFamily request
  let summaryData :=
    normalizedCircuitBottomSummaryData inputLength request
  let summaryRaw :=
    Nat.pair summaryData (normalizedCircuitRawCode request)
  let countSummary :=
    Nat.pair (normalizedCircuitCountValue request) summaryRaw
  let payload :=
    normalizedCircuitHeaderBottomPayload inputLength request
  [ inputLength
  , normalizedCircuitLengthStageOutput inputLength request
  , lengthFlag
  , normalizedCircuitBottomStageOutput inputLength request
  , bottomSummary
  , bottomContext
  , normalizedCircuitCountValue request
  , countStage
  , normalizedCircuitCountValidation request
  , countContext
  , normalizedCircuitFamilyEqualityFlag request
  , familyContext
  , normalizedCircuitTupleFlag request
  , tail₂
  , tail₁
  , tail₀
  , normalizedCircuitTopCode request
  , request
  , expected
  , normalizedCircuitRawCode request
  , summaryData
  , Nat.pred expected
  , 1
  , 2
  , summaryRaw
  , countSummary
  , payload
  , Nat.pair 1 payload
  , Nat.pair 2 payload
  , normalizedCircuitHeaderBottomOutput inputLength request
  , 0
  ]

def normalizedCircuitHeaderBottomGateBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedCircuitHeaderBottomGateValues inputLength request).map
      natBitLength |>.foldr max 1

def normalizedCircuitHeaderBottomGateFuel : ℕ := 37

private def normalizedCircuitHeaderBottomGatePrefixState
    (inputLength request : ℕ) : NPOracleState where
  pc := 19
  registers := fun register =>
    -- Match the interpreter's newest-write-first register frame exactly.  This
    -- keeps the executable trace opaque after the prefix has been checked.
    if register = 20 then
      normalizedCircuitBottomSummaryData inputLength request
    else if register = 19 then
      normalizedCircuitRawCode request
    else if register = 18 then
      normalizedCircuitExpectedFamily request
    else if register = 17 then
      request
    else if register = 16 then
      normalizedCircuitTopCode request
    else if register = 15 then
      normalizedCircuitFamilyTail₀ request
    else if register = 14 then
      normalizedCircuitFamilyTail₁ request
    else if register = 13 then
      normalizedCircuitFamilyTail₂ request
    else if register = 12 then
      normalizedCircuitTupleFlag request
    else if register = 11 then
      normalizedCircuitFamilyContext request
    else if register = 10 then
      normalizedCircuitFamilyEqualityFlag request
    else if register = 9 then
      normalizedCircuitCountContext request
    else if register = 8 then
      normalizedCircuitCountValidation request
    else if register = 7 then
      normalizedCircuitCountStageOutput request
    else if register = 6 then
      normalizedCircuitCountValue request
    else if register = 5 then
      normalizedCircuitBottomContext request
    else if register = 4 then
      normalizedCircuitBottomSummary inputLength request
    else if register = 3 then
      normalizedCircuitBottomStageOutput inputLength request
    else if register = 2 then
      normalizedCircuitLengthEqualityFlag inputLength request
    else if register = 0 then
      normalizedCircuitLengthStageOutput inputLength request
    else if register = 1 then
      inputLength
    else
      0

@[simp] private theorem normalizedCircuitHeaderBottomGatePrefixState_pc
    (inputLength request : ℕ) :
    (normalizedCircuitHeaderBottomGatePrefixState inputLength request).pc =
      19 := by
  simp [normalizedCircuitHeaderBottomGatePrefixState]

@[simp] private theorem normalizedCircuitHeaderBottomGatePrefixState_r2
    (inputLength request : ℕ) :
    (normalizedCircuitHeaderBottomGatePrefixState inputLength request).registers
        2 =
      normalizedCircuitLengthEqualityFlag inputLength request := by
  simp [normalizedCircuitHeaderBottomGatePrefixState]

@[simp] private theorem normalizedCircuitHeaderBottomGatePrefixState_r4
    (inputLength request : ℕ) :
    (normalizedCircuitHeaderBottomGatePrefixState inputLength request).registers
        4 =
      normalizedCircuitBottomSummary inputLength request := by
  simp [normalizedCircuitHeaderBottomGatePrefixState]

@[simp] private theorem normalizedCircuitHeaderBottomGatePrefixState_r6
    (inputLength request : ℕ) :
    (normalizedCircuitHeaderBottomGatePrefixState inputLength request).registers
        6 =
      normalizedCircuitCountValue request := by
  simp [normalizedCircuitHeaderBottomGatePrefixState]

@[simp] private theorem normalizedCircuitHeaderBottomGatePrefixState_r8
    (inputLength request : ℕ) :
    (normalizedCircuitHeaderBottomGatePrefixState inputLength request).registers
        8 =
      normalizedCircuitCountValidation request := by
  simp [normalizedCircuitHeaderBottomGatePrefixState]

@[simp] private theorem normalizedCircuitHeaderBottomGatePrefixState_r10
    (inputLength request : ℕ) :
    (normalizedCircuitHeaderBottomGatePrefixState inputLength request).registers
        10 =
      normalizedCircuitFamilyEqualityFlag request := by
  simp [normalizedCircuitHeaderBottomGatePrefixState]

@[simp] private theorem normalizedCircuitHeaderBottomGatePrefixState_r12
    (inputLength request : ℕ) :
    (normalizedCircuitHeaderBottomGatePrefixState inputLength request).registers
        12 =
      normalizedCircuitTupleFlag request := by
  simp [normalizedCircuitHeaderBottomGatePrefixState]

@[simp] private theorem normalizedCircuitHeaderBottomGatePrefixState_r16
    (inputLength request : ℕ) :
    (normalizedCircuitHeaderBottomGatePrefixState inputLength request).registers
        16 =
      normalizedCircuitTopCode request := by
  simp [normalizedCircuitHeaderBottomGatePrefixState]

@[simp] private theorem normalizedCircuitHeaderBottomGatePrefixState_r18
    (inputLength request : ℕ) :
    (normalizedCircuitHeaderBottomGatePrefixState inputLength request).registers
        18 =
      normalizedCircuitExpectedFamily request := by
  simp [normalizedCircuitHeaderBottomGatePrefixState]

@[simp] private theorem normalizedCircuitHeaderBottomGatePrefixState_r19
    (inputLength request : ℕ) :
    (normalizedCircuitHeaderBottomGatePrefixState inputLength request).registers
        19 =
      normalizedCircuitRawCode request := by
  simp [normalizedCircuitHeaderBottomGatePrefixState]

@[simp] private theorem normalizedCircuitHeaderBottomGatePrefixState_r20
    (inputLength request : ℕ) :
    (normalizedCircuitHeaderBottomGatePrefixState inputLength request).registers
        20 =
      normalizedCircuitBottomSummaryData inputLength request := by
  simp [normalizedCircuitHeaderBottomGatePrefixState]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- Normalize the fixed 19-instruction register-frame prefix once.
private theorem run_normalizedCircuitHeaderBottomGatePrefix
    (inputLength request extra : ℕ) :
    runNPOracleProgram normalizedCircuitHeaderBottomGateProgram
        (normalizedCircuitHeaderBottomGateBits inputLength request)
        (19 + extra)
        (initialNPOracleState inputLength
          (normalizedCircuitLengthStageOutput inputLength request)) =
      runNPOracleProgram normalizedCircuitHeaderBottomGateProgram
        (normalizedCircuitHeaderBottomGateBits inputLength request)
        extra
        (normalizedCircuitHeaderBottomGatePrefixState
          inputLength request) := by
  have hbits :
      ∀ value ∈
          normalizedCircuitHeaderBottomGateValues inputLength request,
        natBitLength value ≤
          normalizedCircuitHeaderBottomGateBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  rw [show 19 + extra = extra + 19 by omega]
  simp [normalizedCircuitHeaderBottomGateProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    normalizedCircuitHeaderBottomGateValues,
    normalizedCircuitHeaderBottomGatePrefixState,
    normalizedCircuitLengthStageOutput,
    normalizedCircuitBottomStageOutput,
    normalizedCircuitBottomContext,
    normalizedCircuitCountStageOutput,
    normalizedCircuitCountContext,
    normalizedCircuitFamilyContext,
    normalizedCircuitFamilyTail₂,
    normalizedCircuitFamilyTail₁,
    normalizedCircuitFamilyTail₀,
    normalizedCircuitExpectedFamily,
    normalizedCircuitRawCode,
    normalizedCircuitBottomSummary,
    normalizedCircuitBottomSummaryData]
  congr 1

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- Check every fail-closed branch of the fixed gate at its exact fuel.
theorem run_normalizedCircuitHeaderBottomGateProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitHeaderBottomGateProgram
        (normalizedCircuitHeaderBottomGateBits inputLength request)
        normalizedCircuitHeaderBottomGateFuel
        (initialNPOracleState inputLength
          (normalizedCircuitLengthStageOutput inputLength request)) =
      some (normalizedCircuitHeaderBottomOutput inputLength request) := by
  have hbits :
      ∀ value ∈
          normalizedCircuitHeaderBottomGateValues inputLength request,
        natBitLength value ≤
          normalizedCircuitHeaderBottomGateBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  have hlengthStageBits :=
    hbits (normalizedCircuitLengthStageOutput inputLength request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hlengthFlagBits :=
    hbits (normalizedCircuitLengthEqualityFlag inputLength request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hbottomStageBits :=
    hbits (normalizedCircuitBottomStageOutput inputLength request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hbottomSummaryBits :=
    hbits (normalizedCircuitBottomSummary inputLength request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hbottomContextBits :=
    hbits (normalizedCircuitBottomContext request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hcountValueBits :=
    hbits (normalizedCircuitCountValue request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hcountStageBits :=
    hbits (normalizedCircuitCountStageOutput request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hcountValidationBits :=
    hbits (normalizedCircuitCountValidation request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hcountContextBits :=
    hbits (normalizedCircuitCountContext request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hfamilyFlagBits :=
    hbits (normalizedCircuitFamilyEqualityFlag request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hfamilyContextBits :=
    hbits (normalizedCircuitFamilyContext request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have htupleFlagBits :=
    hbits (normalizedCircuitTupleFlag request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have htail₂Bits :=
    hbits (normalizedCircuitFamilyTail₂ request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have htail₁Bits :=
    hbits (normalizedCircuitFamilyTail₁ request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have htail₀Bits :=
    hbits (normalizedCircuitFamilyTail₀ request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have htopBits :=
    hbits (normalizedCircuitTopCode request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hrequestBits :=
    hbits request
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hexpectedBits :=
    hbits (normalizedCircuitExpectedFamily request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hrawBits :=
    hbits (normalizedCircuitRawCode request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hsummaryDataBits :=
    hbits (normalizedCircuitBottomSummaryData inputLength request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hpredBits :=
    hbits (Nat.pred (normalizedCircuitExpectedFamily request))
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have honeBits :=
    hbits 1 (by simp [normalizedCircuitHeaderBottomGateValues])
  have htwoBits :=
    hbits 2 (by simp [normalizedCircuitHeaderBottomGateValues])
  have hsummaryRawBits :=
    hbits
      (Nat.pair
        (normalizedCircuitBottomSummaryData inputLength request)
        (normalizedCircuitRawCode request))
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hcountSummaryBits :=
    hbits
      (Nat.pair (normalizedCircuitCountValue request)
        (Nat.pair
          (normalizedCircuitBottomSummaryData inputLength request)
          (normalizedCircuitRawCode request)))
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hpayloadBits :=
    hbits (normalizedCircuitHeaderBottomPayload inputLength request)
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hpairOneBits :=
    hbits
      (Nat.pair 1
        (normalizedCircuitHeaderBottomPayload inputLength request))
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hpairTwoBits :=
    hbits
      (Nat.pair 2
        (normalizedCircuitHeaderBottomPayload inputLength request))
      (by simp [normalizedCircuitHeaderBottomGateValues])
  have hzeroBits :=
    hbits 0 (by simp [normalizedCircuitHeaderBottomGateValues])
  clear hbits
  rw [show normalizedCircuitHeaderBottomGateFuel = 19 + 18 by
    rfl]
  rw [run_normalizedCircuitHeaderBottomGatePrefix
    inputLength request 18]
  by_cases hlength :
      normalizedCircuitLengthEqualityFlag inputLength request = 0
  · simp_all [normalizedCircuitHeaderBottomGateProgram,
      runNPOracleProgram, NPOracleState.boundedWrite,
      normalizedCircuitHeaderBottomOutput]
  · by_cases hbottom :
        normalizedCircuitBottomSummary inputLength request = 0
    · simp_all [normalizedCircuitHeaderBottomGateProgram,
        runNPOracleProgram, NPOracleState.boundedWrite,
        normalizedCircuitHeaderBottomOutput]
    · by_cases hcount :
          normalizedCircuitCountValidation request = 0
      · simp_all [normalizedCircuitHeaderBottomGateProgram,
          runNPOracleProgram, NPOracleState.boundedWrite,
          normalizedCircuitHeaderBottomOutput]
      · by_cases hfamily :
            normalizedCircuitFamilyEqualityFlag request = 0
        · simp_all [normalizedCircuitHeaderBottomGateProgram,
            runNPOracleProgram, NPOracleState.boundedWrite,
            normalizedCircuitHeaderBottomOutput]
        · by_cases htuple :
              normalizedCircuitTupleFlag request = 0
          · simp_all [normalizedCircuitHeaderBottomGateProgram,
              runNPOracleProgram, NPOracleState.boundedWrite,
              normalizedCircuitHeaderBottomOutput]
          · by_cases hexpectedZero :
                normalizedCircuitExpectedFamily request = 0
            · simp_all [normalizedCircuitHeaderBottomGateProgram,
                runNPOracleProgram, NPOracleState.boundedWrite,
                normalizedCircuitHeaderBottomOutput,
                normalizedCircuitHeaderBottomPayload]
            · by_cases hexpectedOne :
                  normalizedCircuitExpectedFamily request = 1
              · simp_all [normalizedCircuitHeaderBottomGateProgram,
                  runNPOracleProgram, NPOracleState.boundedWrite,
                  normalizedCircuitHeaderBottomOutput,
                  normalizedCircuitHeaderBottomPayload]
              · have hpred :
                    Nat.pred (normalizedCircuitExpectedFamily request) ≠
                      0 := by
                  cases hvalue :
                      normalizedCircuitExpectedFamily request with
                  | zero =>
                      exact (hexpectedZero hvalue).elim
                  | succ value =>
                      cases value with
                      | zero =>
                          exact (hexpectedOne (by omega)).elim
                      | succ value =>
                          simp
                simp_all [normalizedCircuitHeaderBottomGateProgram,
                  runNPOracleProgram, NPOracleState.boundedWrite,
                  normalizedCircuitHeaderBottomOutput]

theorem normalizedCircuitBottomLength_eq_of_decode
    {inputLength request : ℕ} {bottomCodes : List ℕ}
    (hsummary :
      normalizedCircuitBottomSummary inputLength request ≠ 0)
    (hdecode :
      decodeBalancedList (normalizedCircuitBottomCode request) =
        some bottomCodes) :
    normalizedCircuitBottomLength inputLength request =
      bottomCodes.length := by
  have hpayload :=
    normalizedCircuitBottomSummaryOutput_payload inputLength
      (normalizedCircuitBottomCode request)
      (by simpa only [normalizedCircuitBottomSummary] using hsummary)
  simp only [normalizedCircuitBottomLength]
  rw [hpayload]
  simp [balancedValidationSummaryData, balancedValidationMapOutputs,
    balancedValidationMapRequests, balancedValidationMapCodes, hdecode]

private theorem normalizedCircuitHeaderBottomOutput_ne_zero_iff_checks
    (inputLength request : ℕ) :
    normalizedCircuitHeaderBottomOutput inputLength request ≠ 0 ↔
      normalizedCircuitLengthEqualityFlag inputLength request ≠ 0 ∧
        normalizedCircuitBottomSummary inputLength request ≠ 0 ∧
        normalizedCircuitCountValidation request ≠ 0 ∧
        normalizedCircuitFamilyEqualityFlag request ≠ 0 ∧
        normalizedCircuitTupleFlag request ≠ 0 ∧
        (normalizedCircuitExpectedFamily request = 0 ∨
          normalizedCircuitExpectedFamily request = 1) := by
  by_cases hlength :
      normalizedCircuitLengthEqualityFlag inputLength request = 0
  · simp [normalizedCircuitHeaderBottomOutput, hlength]
  by_cases hbottom :
      normalizedCircuitBottomSummary inputLength request = 0
  · simp [normalizedCircuitHeaderBottomOutput, hlength, hbottom]
  by_cases hcount :
      normalizedCircuitCountValidation request = 0
  · simp [normalizedCircuitHeaderBottomOutput, hlength, hbottom, hcount]
  by_cases hfamily :
      normalizedCircuitFamilyEqualityFlag request = 0
  · simp [normalizedCircuitHeaderBottomOutput, hlength, hbottom, hcount,
      hfamily]
  by_cases htuple :
      normalizedCircuitTupleFlag request = 0
  · simp [normalizedCircuitHeaderBottomOutput, hlength, hbottom, hcount,
      hfamily, htuple]
  by_cases hzero : normalizedCircuitExpectedFamily request = 0
  · simp [normalizedCircuitHeaderBottomOutput, hlength, hbottom, hcount,
      hfamily, htuple, hzero]
    have hpair :=
      Nat.left_le_pair 1
        (normalizedCircuitHeaderBottomPayload inputLength request)
    omega
  by_cases hone : normalizedCircuitExpectedFamily request = 1
  · simp [normalizedCircuitHeaderBottomOutput, hlength, hbottom, hcount,
      hfamily, htuple, hone]
    have hpair :=
      Nat.left_le_pair 2
        (normalizedCircuitHeaderBottomPayload inputLength request)
    omega
  · simp [normalizedCircuitHeaderBottomOutput, hlength, hbottom, hcount,
      hfamily, htuple, hzero, hone]

theorem normalizedCircuitHeaderBottomOutput_ne_zero_iff_fields
    (inputLength request : ℕ) :
    normalizedCircuitHeaderBottomOutput inputLength request ≠ 0 ↔
      NormalizedCircuitCommonFieldsValid inputLength
        (normalizedCircuitExpectedFamily request)
        (normalizedCircuitRawCode request) := by
  rw [normalizedCircuitHeaderBottomOutput_ne_zero_iff_checks]
  constructor
  · rintro ⟨hlength, hbottom, hcount, hfamily, htuple, htag⟩
    obtain ⟨familyCode, countCode, bottomCode, topCode, hdecode⟩ :=
      (normalizedCircuitTupleFlag_ne_zero_iff request).1 htuple
    obtain ⟨_, hfamilyCode, hcountCode, hbottomCode, _⟩ :=
      normalizedCircuitTupleAccessors_of_decode hdecode
    have hfamilyEquality :
        normalizedCircuitFamilyCode request =
          encodeNat (normalizedCircuitExpectedFamily request) :=
      (nativeNatEqOutput_ne_zero_iff _ _).1 <| by
        simpa only [normalizedCircuitFamilyEqualityFlag] using hfamily
    have hfamilyDecode :
        decodeNat familyCode =
          some (normalizedCircuitExpectedFamily request) := by
      rw [← hfamilyCode, hfamilyEquality, decodeNat_encode]
    obtain ⟨bottomCount, hcountDecode'⟩ :=
      (canonicalNatValidationOutput_ne_zero_iff
        (normalizedCircuitCountCode request)).1 hcount
    have hcountDecode :
        decodeNat countCode = some bottomCount := by
      simpa only [hcountCode] using hcountDecode'
    have hcountOutput :=
      canonicalNatValidationOutput_of_decode hcountDecode'
    have hcountValue :
        normalizedCircuitCountValue request = bottomCount := by
      simp [normalizedCircuitCountValue, normalizedCircuitCountValidation,
        hcountOutput]
    obtain ⟨bottomCodes, hbottomDecode', hall⟩ :=
      (normalizedCircuitBottomSummaryOutput_ne_zero_iff inputLength
        (normalizedCircuitBottomCode request)).1 <| by
          simpa only [normalizedCircuitBottomSummary] using hbottom
    have hbottomDecode :
        decodeBalancedList bottomCode = some bottomCodes := by
      simpa only [hbottomCode] using hbottomDecode'
    have hbottomLength :=
      normalizedCircuitBottomLength_eq_of_decode hbottom hbottomDecode'
    have hlengthEquality :
        normalizedCircuitCountValue request =
          normalizedCircuitBottomLength inputLength request :=
      (nativeNatEqOutput_ne_zero_iff _ _).1 <| by
        simpa only [normalizedCircuitLengthEqualityFlag] using hlength
    have hdecodedLength : bottomCodes.length = bottomCount := by
      omega
    have hsemanticTag :
        normalizedCircuitExpectedFamily request =
            symmetricCircuitFamilyTag ∨
          normalizedCircuitExpectedFamily request =
            thresholdCircuitFamilyTag := by
      simpa [symmetricCircuitFamilyTag, thresholdCircuitFamilyTag] using htag
    exact
      ⟨hsemanticTag, familyCode, countCode, bottomCode, topCode,
        bottomCount, bottomCodes, hdecode, hfamilyDecode, hcountDecode,
        hbottomDecode, hall, hdecodedLength⟩
  · rintro
      ⟨htag, familyCode, countCode, bottomCode, topCode, bottomCount,
        bottomCodes, hdecode, hfamilyDecode, hcountDecode, hbottomDecode,
        hall, hdecodedLength⟩
    obtain ⟨_, hfamilyCode, hcountCode, hbottomCode, _⟩ :=
      normalizedCircuitTupleAccessors_of_decode hdecode
    have htuple :
        normalizedCircuitTupleFlag request ≠ 0 :=
      (normalizedCircuitTupleFlag_ne_zero_iff request).2
        ⟨familyCode, countCode, bottomCode, topCode, hdecode⟩
    have hfamily :
        normalizedCircuitFamilyEqualityFlag request ≠ 0 := by
      apply (nativeNatEqOutput_ne_zero_iff _ _).2
      rw [hfamilyCode, ← encodeNat_of_decode hfamilyDecode]
    have hcountDecode' :
        decodeNat (normalizedCircuitCountCode request) =
          some bottomCount := by
      simpa only [hcountCode] using hcountDecode
    have hcount :
        normalizedCircuitCountValidation request ≠ 0 :=
      (canonicalNatValidationOutput_ne_zero_iff
        (normalizedCircuitCountCode request)).2
        ⟨bottomCount, hcountDecode'⟩
    have hcountOutput :=
      canonicalNatValidationOutput_of_decode hcountDecode'
    have hcountValue :
        normalizedCircuitCountValue request = bottomCount := by
      simp [normalizedCircuitCountValue, normalizedCircuitCountValidation,
        hcountOutput]
    have hbottomDecode' :
        decodeBalancedList (normalizedCircuitBottomCode request) =
          some bottomCodes := by
      simpa only [hbottomCode] using hbottomDecode
    have hbottom :
        normalizedCircuitBottomSummary inputLength request ≠ 0 := by
      simpa only [normalizedCircuitBottomSummary] using
        (normalizedCircuitBottomSummaryOutput_ne_zero_iff inputLength
          (normalizedCircuitBottomCode request)).2
          ⟨bottomCodes, hbottomDecode', by
            intro code hcode
            exact hall code hcode⟩
    have hbottomLength :=
      normalizedCircuitBottomLength_eq_of_decode hbottom hbottomDecode'
    have hlength :
        normalizedCircuitLengthEqualityFlag inputLength request ≠ 0 := by
      apply (nativeNatEqOutput_ne_zero_iff _ _).2
      omega
    have hmachineTag :
        normalizedCircuitExpectedFamily request = 0 ∨
          normalizedCircuitExpectedFamily request = 1 := by
      simpa [symmetricCircuitFamilyTag, thresholdCircuitFamilyTag] using htag
    exact
      ⟨hlength, hbottom, hcount, hfamily, htuple, hmachineTag⟩

/-! ## Single shared header/bottom executable -/

def normalizedCircuitHeaderBottomProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms
      (linkPrograms
        (linkPrograms
          (linkPrograms
            (linkPrograms
              (linkPrograms
                (linkPrograms
                  (linkPrograms
                    (linkPrograms normalizedCircuitTupleLoweringProgram
                      normalizedCircuitTupleStageProgram)
                    normalizedCircuitFamilyPrepareProgram)
                  normalizedCircuitFamilyStageProgram)
                normalizedCircuitCountPrepareProgram)
              normalizedCircuitCountStageProgram)
            normalizedCircuitBottomPrepareProgram)
          normalizedCircuitBottomStageProgram)
        normalizedCircuitLengthPrepareProgram)
      normalizedCircuitLengthStageProgram)
    normalizedCircuitHeaderBottomGateProgram

@[simp] theorem normalizedCircuitHeaderBottomProgram_oracleFree :
    OracleFree normalizedCircuitHeaderBottomProgram := by
  exact oracleFree_linkPrograms
    (oracleFree_linkPrograms
      (oracleFree_linkPrograms
        (oracleFree_linkPrograms
          (oracleFree_linkPrograms
            (oracleFree_linkPrograms
              (oracleFree_linkPrograms
                (oracleFree_linkPrograms
                  (oracleFree_linkPrograms
                    (oracleFree_linkPrograms
                      normalizedCircuitTupleLoweringProgram_oracleFree
                      normalizedCircuitTupleStageProgram_oracleFree)
                    normalizedCircuitFamilyPrepareProgram_oracleFree)
                  normalizedCircuitFamilyStageProgram_oracleFree)
                normalizedCircuitCountPrepareProgram_oracleFree)
              normalizedCircuitCountStageProgram_oracleFree)
            normalizedCircuitBottomPrepareProgram_oracleFree)
          normalizedCircuitBottomStageProgram_oracleFree)
        normalizedCircuitLengthPrepareProgram_oracleFree)
      normalizedCircuitLengthStageProgram_oracleFree)
    normalizedCircuitHeaderBottomGateProgram_oracleFree

private def normalizedCircuitHeaderBottomStageBits
    (inputLength request : ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , normalizedCircuitTupleLoweringBits inputLength request
  , normalizedCircuitTupleStageBits inputLength request
  , normalizedCircuitFamilyPrepareBits inputLength request
  , normalizedCircuitFamilyStageBits inputLength request
  , normalizedCircuitCountPrepareBits inputLength request
  , normalizedCircuitCountStageBits inputLength request
  , normalizedCircuitBottomPrepareBits inputLength request
  , normalizedCircuitBottomStageBits inputLength request
  , normalizedCircuitLengthPrepareBits inputLength request
  , normalizedCircuitLengthStageBits inputLength request
  , normalizedCircuitHeaderBottomGateBits inputLength request
  ]

def normalizedCircuitHeaderBottomBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedCircuitHeaderBottomStageBits inputLength request).foldr max 1

private theorem normalizedCircuit_le_foldrMax
    {value : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max 1 := by
  revert hvalue
  induction values with
  | nil => simp
  | cons head tail ih =>
      intro hvalue
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact Nat.le_max_left _ _
      · exact (ih htail).trans (Nat.le_max_right _ _)

def normalizedCircuitHeaderBottomFuel
    (inputLength request : ℕ) : ℕ :=
  linkFuel normalizedCircuitHeaderBottomGateProgram
    (linkFuel normalizedCircuitLengthStageProgram
      (linkFuel normalizedCircuitLengthPrepareProgram
        (linkFuel normalizedCircuitBottomStageProgram
          (linkFuel normalizedCircuitBottomPrepareProgram
            (linkFuel normalizedCircuitCountStageProgram
              (linkFuel normalizedCircuitCountPrepareProgram
                (linkFuel normalizedCircuitFamilyStageProgram
                  (linkFuel normalizedCircuitFamilyPrepareProgram
                    (linkFuel normalizedCircuitTupleStageProgram 4
                      normalizedCircuitTupleStageFuel)
                    normalizedCircuitFamilyPrepareFuel)
                  (normalizedCircuitFamilyStageFuel request))
                normalizedCircuitCountPrepareFuel)
              (normalizedCircuitCountStageFuel request))
            normalizedCircuitBottomPrepareFuel)
          (normalizedCircuitBottomStageFuel inputLength request))
        normalizedCircuitLengthPrepareFuel)
      (normalizedCircuitLengthStageFuel inputLength request))
    normalizedCircuitHeaderBottomGateFuel

theorem run_normalizedCircuitHeaderBottomProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitHeaderBottomProgram
        (normalizedCircuitHeaderBottomBits inputLength request)
        (normalizedCircuitHeaderBottomFuel inputLength request)
        (initialNPOracleState inputLength request) =
      some (normalizedCircuitHeaderBottomOutput inputLength request) := by
  let maximumBits :=
    normalizedCircuitHeaderBottomBits inputLength request
  have hbound :
      ∀ value ∈ normalizedCircuitHeaderBottomStageBits inputLength request,
        value ≤ maximumBits := by
    intro value hvalue
    exact normalizedCircuit_le_foldrMax hvalue
  have hpositive : 1 ≤ maximumBits :=
    hbound 1 (by simp [normalizedCircuitHeaderBottomStageBits])
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    hbound (natBitLength inputLength)
      (by simp [normalizedCircuitHeaderBottomStageBits])
  have hlowering := run_bits_mono
    (run_normalizedCircuitTupleLoweringProgram inputLength request)
    (hbound (normalizedCircuitTupleLoweringBits inputLength request)
      (by simp [normalizedCircuitHeaderBottomStageBits]))
  have htuple := run_bits_mono
    (run_normalizedCircuitTupleStageProgram inputLength request)
    (hbound (normalizedCircuitTupleStageBits inputLength request)
      (by simp [normalizedCircuitHeaderBottomStageBits]))
  have hfamilyPrepare := run_bits_mono
    (run_normalizedCircuitFamilyPrepareProgram inputLength request)
    (hbound (normalizedCircuitFamilyPrepareBits inputLength request)
      (by simp [normalizedCircuitHeaderBottomStageBits]))
  have hfamily := run_bits_mono
    (run_normalizedCircuitFamilyStageProgram inputLength request)
    (hbound (normalizedCircuitFamilyStageBits inputLength request)
      (by simp [normalizedCircuitHeaderBottomStageBits]))
  have hcountPrepare := run_bits_mono
    (run_normalizedCircuitCountPrepareProgram inputLength request)
    (hbound (normalizedCircuitCountPrepareBits inputLength request)
      (by simp [normalizedCircuitHeaderBottomStageBits]))
  have hcount := run_bits_mono
    (run_normalizedCircuitCountStageProgram inputLength request)
    (hbound (normalizedCircuitCountStageBits inputLength request)
      (by simp [normalizedCircuitHeaderBottomStageBits]))
  have hbottomPrepare := run_bits_mono
    (run_normalizedCircuitBottomPrepareProgram inputLength request)
    (hbound (normalizedCircuitBottomPrepareBits inputLength request)
      (by simp [normalizedCircuitHeaderBottomStageBits]))
  have hbottom := run_bits_mono
    (run_normalizedCircuitBottomStageProgram inputLength request)
    (hbound (normalizedCircuitBottomStageBits inputLength request)
      (by simp [normalizedCircuitHeaderBottomStageBits]))
  have hlengthPrepare := run_bits_mono
    (run_normalizedCircuitLengthPrepareProgram inputLength request)
    (hbound (normalizedCircuitLengthPrepareBits inputLength request)
      (by simp [normalizedCircuitHeaderBottomStageBits]))
  have hlength := run_bits_mono
    (run_normalizedCircuitLengthStageProgram inputLength request)
    (hbound (normalizedCircuitLengthStageBits inputLength request)
      (by simp [normalizedCircuitHeaderBottomStageBits]))
  have hgate := run_bits_mono
    (run_normalizedCircuitHeaderBottomGateProgram inputLength request)
    (hbound (normalizedCircuitHeaderBottomGateBits inputLength request)
      (by simp [normalizedCircuitHeaderBottomStageBits]))
  have htuplePrefix :=
    run_linkPrograms hpositive hinputLength hlowering htuple
  have hfamilyPreparePrefix :=
    run_linkPrograms hpositive hinputLength htuplePrefix hfamilyPrepare
  have hfamilyPrefix :=
    run_linkPrograms hpositive hinputLength hfamilyPreparePrefix hfamily
  have hcountPreparePrefix :=
    run_linkPrograms hpositive hinputLength hfamilyPrefix hcountPrepare
  have hcountPrefix :=
    run_linkPrograms hpositive hinputLength hcountPreparePrefix hcount
  have hbottomPreparePrefix :=
    run_linkPrograms hpositive hinputLength hcountPrefix hbottomPrepare
  have hbottomPrefix :=
    run_linkPrograms hpositive hinputLength hbottomPreparePrefix hbottom
  have hlengthPreparePrefix :=
    run_linkPrograms hpositive hinputLength hbottomPrefix hlengthPrepare
  have hlengthPrefix :=
    run_linkPrograms hpositive hinputLength hlengthPreparePrefix hlength
  have hrun :=
    run_linkPrograms hpositive hinputLength hlengthPrefix hgate
  simpa only [maximumBits, normalizedCircuitHeaderBottomProgram,
    normalizedCircuitHeaderBottomFuel] using hrun

/-! ## Symmetric-family top validation -/

def normalizedCircuitTopContext
    (inputLength request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitCountValue request) <|
    Nat.pair (normalizedCircuitBottomSummaryData inputLength request)
      (normalizedCircuitRawCode request)

def normalizedSymmetricTopSummaryOutput
    (inputLength request : ℕ) : ℕ :=
  balancedValidationSummaryOutput inputLength
    (normalizedCircuitTopCode request) boolCodeRequestOutput

def normalizedSymmetricTopStageOutput
    (inputLength request : ℕ) : ℕ :=
  Nat.pair (normalizedSymmetricTopSummaryOutput inputLength request)
    (normalizedCircuitTopContext inputLength request)

def normalizedSymmetricTopStageProgram : NPOracleProgram :=
  preserveRightProgram <|
    balancedValidationSummaryProgram boolCodeValidationProgram

@[simp] theorem normalizedSymmetricTopStageProgram_oracleFree :
    OracleFree normalizedSymmetricTopStageProgram :=
  preserveRightProgram_oracleFree
    (balancedValidationSummaryProgram boolCodeValidationProgram)
    (balancedValidationSummaryProgram_oracleFree
      boolCodeValidationProgram boolCodeValidationProgram_oracleFree)

def normalizedSymmetricTopStageFuel
    (inputLength request : ℕ) : ℕ :=
  preserveRightFuel <|
    balancedValidationSummaryFuel boolCodeValidationProgram
      boolCodeRequestFuel inputLength
      (normalizedCircuitTopCode request) boolCodeRequestOutput

def normalizedSymmetricTopStageBits
    (inputLength request : ℕ) : ℕ :=
  preserveRightBits
    (balancedValidationSummaryBits boolCodeRequestBits
      boolCodeRequestOutput inputLength
      (normalizedCircuitTopCode request))
    (normalizedCircuitTopCode request)
    (normalizedCircuitTopContext inputLength request)
    (normalizedSymmetricTopSummaryOutput inputLength request)

theorem run_normalizedSymmetricTopStageProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedSymmetricTopStageProgram
        (normalizedSymmetricTopStageBits inputLength request)
        (normalizedSymmetricTopStageFuel inputLength request)
        (initialNPOracleState inputLength
          (normalizedCircuitHeaderBottomPayload inputLength request)) =
      some (normalizedSymmetricTopStageOutput inputLength request) := by
  apply run_preserveRightProgram
    (balancedValidationSummaryProgram boolCodeValidationProgram)
    inputLength
    (balancedValidationSummaryBits boolCodeRequestBits
      boolCodeRequestOutput inputLength
      (normalizedCircuitTopCode request))
    (balancedValidationSummaryFuel boolCodeValidationProgram
      boolCodeRequestFuel inputLength
      (normalizedCircuitTopCode request) boolCodeRequestOutput)
    (normalizedCircuitTopCode request)
    (normalizedCircuitTopContext inputLength request)
    (normalizedSymmetricTopSummaryOutput inputLength request)
  apply run_balancedValidationSummaryProgram boolCodeValidationProgram
    boolCodeRequestBits boolCodeRequestFuel boolCodeRequestOutput
  intro leafRequest _
  exact run_boolCodeValidationProgram
    (Nat.unpair leafRequest).1 (Nat.unpair leafRequest).2

def normalizedSymmetricTopLength
    (inputLength request : ℕ) : ℕ :=
  let summary :=
    normalizedSymmetricTopSummaryOutput inputLength request
  (Nat.unpair (Nat.unpair (Nat.unpair summary).2).2).1

def normalizedSymmetricExpectedTopLength (request : ℕ) : ℕ :=
  normalizedCircuitCountValue request + 1

def normalizedSymmetricLengthEqualityRequest
    (inputLength request : ℕ) : ℕ :=
  nativeNatEqInput (normalizedSymmetricTopLength inputLength request)
    (normalizedSymmetricExpectedTopLength request)

def normalizedSymmetricEqualityRetained
    (inputLength request : ℕ) : ℕ :=
  Nat.pair (normalizedSymmetricTopSummaryOutput inputLength request)
    (normalizedCircuitTopContext inputLength request)

def normalizedSymmetricLengthPrepareOutput
    (inputLength request : ℕ) : ℕ :=
  Nat.pair
    (normalizedSymmetricLengthEqualityRequest inputLength request)
    (normalizedSymmetricEqualityRetained inputLength request)

def normalizedSymmetricLengthPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 2 4 3
  , .unpairRight 4 5 4
  , .unpairLeft 5 6 5
  , .unpairLeft 3 7 6
  , .copy 7 8 7
  , .increment 8 8
  , .pair 6 8 9 9
  , .pair 2 3 10 10
  , .pair 9 10 0 11
  , .halt 0
  ]

@[simp] theorem normalizedSymmetricLengthPrepareProgram_oracleFree :
    OracleFree normalizedSymmetricLengthPrepareProgram := by
  rfl

private def normalizedSymmetricLengthPrepareValues
    (inputLength request : ℕ) : List ℕ :=
  let summary :=
    normalizedSymmetricTopSummaryOutput inputLength request
  let summaryData := (Nat.unpair summary).2
  let summaryTail := (Nat.unpair summaryData).2
  [ inputLength
  , normalizedSymmetricTopStageOutput inputLength request
  , summary
  , normalizedCircuitTopContext inputLength request
  , summaryData
  , summaryTail
  , normalizedSymmetricTopLength inputLength request
  , normalizedCircuitCountValue request
  , normalizedSymmetricExpectedTopLength request
  , normalizedSymmetricLengthEqualityRequest inputLength request
  , normalizedSymmetricEqualityRetained inputLength request
  , normalizedSymmetricLengthPrepareOutput inputLength request
  ]

def normalizedSymmetricLengthPrepareBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedSymmetricLengthPrepareValues inputLength request).map
      natBitLength |>.foldr max 1

def normalizedSymmetricLengthPrepareFuel : ℕ := 12

theorem run_normalizedSymmetricLengthPrepareProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedSymmetricLengthPrepareProgram
        (normalizedSymmetricLengthPrepareBits inputLength request)
        normalizedSymmetricLengthPrepareFuel
        (initialNPOracleState inputLength
          (normalizedSymmetricTopStageOutput inputLength request)) =
      some
        (normalizedSymmetricLengthPrepareOutput inputLength request) := by
  have hbits :
      ∀ value ∈ normalizedSymmetricLengthPrepareValues inputLength request,
        natBitLength value ≤
          normalizedSymmetricLengthPrepareBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  simp [normalizedSymmetricLengthPrepareFuel,
    normalizedSymmetricLengthPrepareProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    normalizedSymmetricLengthPrepareValues,
    normalizedSymmetricTopStageOutput,
    normalizedCircuitTopContext,
    normalizedSymmetricTopLength,
    normalizedSymmetricExpectedTopLength,
    normalizedSymmetricLengthEqualityRequest, nativeNatEqInput,
    normalizedSymmetricEqualityRetained,
    normalizedSymmetricLengthPrepareOutput]

def normalizedSymmetricLengthEqualityFlag
    (inputLength request : ℕ) : ℕ :=
  nativeNatEqOutput
    (normalizedSymmetricTopLength inputLength request)
    (normalizedSymmetricExpectedTopLength request)

def normalizedSymmetricLengthStageOutput
    (inputLength request : ℕ) : ℕ :=
  Nat.pair
    (normalizedSymmetricLengthEqualityFlag inputLength request)
    (normalizedSymmetricEqualityRetained inputLength request)

def normalizedSymmetricLengthStageProgram : NPOracleProgram :=
  preserveRightProgram nativeNatEqProgram

@[simp] theorem normalizedSymmetricLengthStageProgram_oracleFree :
    OracleFree normalizedSymmetricLengthStageProgram :=
  preserveRightProgram_oracleFree nativeNatEqProgram
    nativeNatEqProgram_oracleFree

def normalizedSymmetricLengthStageFuel
    (inputLength request : ℕ) : ℕ :=
  preserveRightFuel <|
    nativeNatEqFuel
      (normalizedSymmetricTopLength inputLength request)
      (normalizedSymmetricExpectedTopLength request)

def normalizedSymmetricLengthStageBits
    (inputLength request : ℕ) : ℕ :=
  preserveRightBits
    (nativeNatEqBits inputLength
      (normalizedSymmetricTopLength inputLength request)
      (normalizedSymmetricExpectedTopLength request))
    (normalizedSymmetricLengthEqualityRequest inputLength request)
    (normalizedSymmetricEqualityRetained inputLength request)
    (normalizedSymmetricLengthEqualityFlag inputLength request)

theorem run_normalizedSymmetricLengthStageProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedSymmetricLengthStageProgram
        (normalizedSymmetricLengthStageBits inputLength request)
        (normalizedSymmetricLengthStageFuel inputLength request)
        (initialNPOracleState inputLength
          (normalizedSymmetricLengthPrepareOutput inputLength request)) =
      some (normalizedSymmetricLengthStageOutput inputLength request) := by
  exact run_preserveRightProgram nativeNatEqProgram inputLength
    (nativeNatEqBits inputLength
      (normalizedSymmetricTopLength inputLength request)
      (normalizedSymmetricExpectedTopLength request))
    (nativeNatEqFuel
      (normalizedSymmetricTopLength inputLength request)
      (normalizedSymmetricExpectedTopLength request))
    (normalizedSymmetricLengthEqualityRequest inputLength request)
    (normalizedSymmetricEqualityRetained inputLength request)
    (normalizedSymmetricLengthEqualityFlag inputLength request)
    (run_nativeNatEqProgram inputLength
      (normalizedSymmetricTopLength inputLength request)
      (normalizedSymmetricExpectedTopLength request))

def normalizedSymmetricTopSummaryData
    (inputLength request : ℕ) : ℕ :=
  (Nat.unpair
    (normalizedSymmetricTopSummaryOutput inputLength request)).2

def normalizedSymmetricBranchContext
    (inputLength request : ℕ) : ℕ :=
  Nat.pair 1 <|
    Nat.pair (normalizedCircuitBottomSummaryData inputLength request)
      (normalizedCircuitRawCode request)

def normalizedSymmetricValidationOutput
    (inputLength request : ℕ) : ℕ :=
  if normalizedSymmetricLengthEqualityFlag inputLength request = 0 then
    0
  else if normalizedSymmetricTopSummaryOutput inputLength request = 0 then
    0
  else
    Nat.pair (normalizedSymmetricTopSummaryOutput inputLength request)
      (normalizedSymmetricBranchContext inputLength request)

def normalizedSymmetricValidationGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairRight 5 7 5
  , .unpairLeft 7 8 6
  , .unpairRight 7 9 7
  , .branchZero 2 14 8
  , .branchZero 4 14 9
  , .pair 8 9 10 10
  , .set 11 1 11
  , .pair 11 10 10 12
  , .pair 4 10 0 13
  , .halt 0
  , .set 0 0 15
  , .halt 0
  ]

@[simp] theorem normalizedSymmetricValidationGateProgram_oracleFree :
    OracleFree normalizedSymmetricValidationGateProgram := by
  rfl

private def normalizedSymmetricValidationGateValues
    (inputLength request : ℕ) : List ℕ :=
  let flag :=
    normalizedSymmetricLengthEqualityFlag inputLength request
  let summary :=
    normalizedSymmetricTopSummaryOutput inputLength request
  let context := normalizedCircuitTopContext inputLength request
  let bottomRaw :=
    Nat.pair (normalizedCircuitBottomSummaryData inputLength request)
      (normalizedCircuitRawCode request)
  [ inputLength
  , normalizedSymmetricLengthStageOutput inputLength request
  , flag
  , normalizedSymmetricEqualityRetained inputLength request
  , summary
  , context
  , bottomRaw
  , normalizedCircuitBottomSummaryData inputLength request
  , normalizedCircuitRawCode request
  , 1
  , normalizedSymmetricBranchContext inputLength request
  , Nat.pair summary
      (normalizedSymmetricBranchContext inputLength request)
  , normalizedSymmetricValidationOutput inputLength request
  , 0
  ]

def normalizedSymmetricValidationGateBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedSymmetricValidationGateValues inputLength request).map
      natBitLength |>.foldr max 1

def normalizedSymmetricValidationGateFuel : ℕ := 16

private def normalizedSymmetricValidationGatePrefixState
    (inputLength request : ℕ) : NPOracleState where
  pc := 7
  registers := fun register =>
    if register = 9 then
      normalizedCircuitRawCode request
    else if register = 8 then
      normalizedCircuitBottomSummaryData inputLength request
    else if register = 7 then
      Nat.pair (normalizedCircuitBottomSummaryData inputLength request)
        (normalizedCircuitRawCode request)
    else if register = 5 then
      normalizedCircuitTopContext inputLength request
    else if register = 4 then
      normalizedSymmetricTopSummaryOutput inputLength request
    else if register = 3 then
      normalizedSymmetricEqualityRetained inputLength request
    else if register = 2 then
      normalizedSymmetricLengthEqualityFlag inputLength request
    else if register = 0 then
      normalizedSymmetricLengthStageOutput inputLength request
    else if register = 1 then
      inputLength
    else
      0

@[simp] private theorem normalizedSymmetricValidationGatePrefixState_pc
    (inputLength request : ℕ) :
    (normalizedSymmetricValidationGatePrefixState inputLength request).pc =
      7 := by
  rfl

@[simp] private theorem normalizedSymmetricValidationGatePrefixState_r2
    (inputLength request : ℕ) :
    (normalizedSymmetricValidationGatePrefixState inputLength request).registers
        2 =
      normalizedSymmetricLengthEqualityFlag inputLength request := by
  simp [normalizedSymmetricValidationGatePrefixState]

@[simp] private theorem normalizedSymmetricValidationGatePrefixState_r4
    (inputLength request : ℕ) :
    (normalizedSymmetricValidationGatePrefixState inputLength request).registers
        4 =
      normalizedSymmetricTopSummaryOutput inputLength request := by
  simp [normalizedSymmetricValidationGatePrefixState]

@[simp] private theorem normalizedSymmetricValidationGatePrefixState_r8
    (inputLength request : ℕ) :
    (normalizedSymmetricValidationGatePrefixState inputLength request).registers
        8 =
      normalizedCircuitBottomSummaryData inputLength request := by
  simp [normalizedSymmetricValidationGatePrefixState]

@[simp] private theorem normalizedSymmetricValidationGatePrefixState_r9
    (inputLength request : ℕ) :
    (normalizedSymmetricValidationGatePrefixState inputLength request).registers
        9 =
      normalizedCircuitRawCode request := by
  simp [normalizedSymmetricValidationGatePrefixState]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- Check the fixed seven-instruction projection frame once.
private theorem run_normalizedSymmetricValidationGatePrefix
    (inputLength request extra : ℕ) :
    runNPOracleProgram normalizedSymmetricValidationGateProgram
        (normalizedSymmetricValidationGateBits inputLength request)
        (7 + extra)
        (initialNPOracleState inputLength
          (normalizedSymmetricLengthStageOutput inputLength request)) =
      runNPOracleProgram normalizedSymmetricValidationGateProgram
        (normalizedSymmetricValidationGateBits inputLength request)
        extra
        (normalizedSymmetricValidationGatePrefixState
          inputLength request) := by
  have hbits :
      ∀ value ∈
          normalizedSymmetricValidationGateValues inputLength request,
        natBitLength value ≤
          normalizedSymmetricValidationGateBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  rw [show 7 + extra = extra + 7 by omega]
  simp [normalizedSymmetricValidationGateProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    normalizedSymmetricValidationGateValues,
    normalizedSymmetricValidationGatePrefixState,
    normalizedSymmetricLengthStageOutput,
    normalizedSymmetricEqualityRetained,
    normalizedCircuitTopContext]
  congr 1

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- Normalize the fixed packaging gate across both fail-closed branches.
theorem run_normalizedSymmetricValidationGateProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedSymmetricValidationGateProgram
        (normalizedSymmetricValidationGateBits inputLength request)
        normalizedSymmetricValidationGateFuel
        (initialNPOracleState inputLength
          (normalizedSymmetricLengthStageOutput inputLength request)) =
      some (normalizedSymmetricValidationOutput inputLength request) := by
  have hbits :
      ∀ value ∈
          normalizedSymmetricValidationGateValues inputLength request,
        natBitLength value ≤
          normalizedSymmetricValidationGateBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  rw [show normalizedSymmetricValidationGateFuel = 7 + 9 by rfl]
  rw [run_normalizedSymmetricValidationGatePrefix inputLength request 9]
  by_cases hflag :
      normalizedSymmetricLengthEqualityFlag inputLength request = 0
  · simp [normalizedSymmetricValidationGateProgram, runNPOracleProgram,
      NPOracleState.boundedWrite, hbits,
      normalizedSymmetricValidationGateValues,
      normalizedSymmetricValidationOutput, hflag]
  · by_cases hsummary :
        normalizedSymmetricTopSummaryOutput inputLength request = 0
    · simp [normalizedSymmetricValidationGateProgram, runNPOracleProgram,
        NPOracleState.boundedWrite, hbits,
        normalizedSymmetricValidationGateValues,
        normalizedSymmetricValidationOutput, hflag, hsummary]
    · simp [normalizedSymmetricValidationGateProgram, runNPOracleProgram,
        NPOracleState.boundedWrite, hbits,
        normalizedSymmetricValidationGateValues,
        normalizedSymmetricValidationOutput,
        normalizedSymmetricBranchContext, hflag, hsummary]

def normalizedSymmetricBranchProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms
      (linkPrograms normalizedSymmetricTopStageProgram
        normalizedSymmetricLengthPrepareProgram)
      normalizedSymmetricLengthStageProgram)
    normalizedSymmetricValidationGateProgram

@[simp] theorem normalizedSymmetricBranchProgram_oracleFree :
    OracleFree normalizedSymmetricBranchProgram := by
  exact oracleFree_linkPrograms
    (oracleFree_linkPrograms
      (oracleFree_linkPrograms normalizedSymmetricTopStageProgram_oracleFree
        normalizedSymmetricLengthPrepareProgram_oracleFree)
      normalizedSymmetricLengthStageProgram_oracleFree)
    normalizedSymmetricValidationGateProgram_oracleFree

private def normalizedSymmetricBranchStageBits
    (inputLength request : ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , normalizedSymmetricTopStageBits inputLength request
  , normalizedSymmetricLengthPrepareBits inputLength request
  , normalizedSymmetricLengthStageBits inputLength request
  , normalizedSymmetricValidationGateBits inputLength request
  ]

def normalizedSymmetricBranchBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedSymmetricBranchStageBits inputLength request).foldr max 1

def normalizedSymmetricBranchFuel
    (inputLength request : ℕ) : ℕ :=
  linkFuel normalizedSymmetricValidationGateProgram
    (linkFuel normalizedSymmetricLengthStageProgram
      (linkFuel normalizedSymmetricLengthPrepareProgram
        (normalizedSymmetricTopStageFuel inputLength request)
        normalizedSymmetricLengthPrepareFuel)
      (normalizedSymmetricLengthStageFuel inputLength request))
    normalizedSymmetricValidationGateFuel

theorem run_normalizedSymmetricBranchProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedSymmetricBranchProgram
        (normalizedSymmetricBranchBits inputLength request)
        (normalizedSymmetricBranchFuel inputLength request)
        (initialNPOracleState inputLength
          (normalizedCircuitHeaderBottomPayload inputLength request)) =
      some (normalizedSymmetricValidationOutput inputLength request) := by
  let maximumBits := normalizedSymmetricBranchBits inputLength request
  have hbound :
      ∀ value ∈ normalizedSymmetricBranchStageBits inputLength request,
        value ≤ maximumBits := by
    intro value hvalue
    exact normalizedCircuit_le_foldrMax hvalue
  have hpositive : 1 ≤ maximumBits :=
    hbound 1 (by simp [normalizedSymmetricBranchStageBits])
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    hbound (natBitLength inputLength)
      (by simp [normalizedSymmetricBranchStageBits])
  have htop := run_bits_mono
    (run_normalizedSymmetricTopStageProgram inputLength request)
    (hbound (normalizedSymmetricTopStageBits inputLength request)
      (by simp [normalizedSymmetricBranchStageBits]))
  have hprepare := run_bits_mono
    (run_normalizedSymmetricLengthPrepareProgram inputLength request)
    (hbound (normalizedSymmetricLengthPrepareBits inputLength request)
      (by simp [normalizedSymmetricBranchStageBits]))
  have hlength := run_bits_mono
    (run_normalizedSymmetricLengthStageProgram inputLength request)
    (hbound (normalizedSymmetricLengthStageBits inputLength request)
      (by simp [normalizedSymmetricBranchStageBits]))
  have hgate := run_bits_mono
    (run_normalizedSymmetricValidationGateProgram inputLength request)
    (hbound (normalizedSymmetricValidationGateBits inputLength request)
      (by simp [normalizedSymmetricBranchStageBits]))
  have hpreparePrefix :=
    run_linkPrograms hpositive hinputLength htop hprepare
  have hlengthPrefix :=
    run_linkPrograms hpositive hinputLength hpreparePrefix hlength
  have hrun :=
    run_linkPrograms hpositive hinputLength hlengthPrefix hgate
  simpa only [maximumBits, normalizedSymmetricBranchProgram,
    normalizedSymmetricBranchFuel] using hrun

/-! ## Threshold-family top validation -/

def normalizedThresholdTopResult (request : ℕ) : ℕ :=
  supportedGateRelationOutput
    (normalizedCircuitCountValue request)
    (normalizedCircuitTopCode request)

def normalizedThresholdTopContext
    (inputLength request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitBottomSummaryData inputLength request)
    (normalizedCircuitRawCode request)

def normalizedThresholdTopStageOutput
    (inputLength request : ℕ) : ℕ :=
  Nat.pair (normalizedThresholdTopResult request) <|
    Nat.pair (normalizedCircuitCountValue request)
      (normalizedThresholdTopContext inputLength request)

def normalizedThresholdTopStageProgram : NPOracleProgram :=
  nativeContextCallProgram supportedGateRelationProgram

@[simp] theorem normalizedThresholdTopStageProgram_oracleFree :
    OracleFree normalizedThresholdTopStageProgram :=
  nativeContextCallProgram_oracleFree supportedGateRelationProgram_oracleFree

def normalizedThresholdTopStageFuel (request : ℕ) : ℕ :=
  nativeContextCallFuel supportedGateRelationProgram
    (supportedGateRelationFuel
      (normalizedCircuitCountValue request)
      (normalizedCircuitTopCode request))
    (normalizedCircuitCountValue request)
    (normalizedCircuitTopCode request)

def normalizedThresholdTopStageBits
    (inputLength request : ℕ) : ℕ :=
  nativeContextCallBits inputLength
    (normalizedCircuitCountValue request)
    (normalizedCircuitTopCode request)
    (normalizedThresholdTopContext inputLength request)
    (normalizedThresholdTopResult request)
    (supportedGateRelationBits
      (normalizedCircuitCountValue request)
      (normalizedCircuitTopCode request))

theorem run_normalizedThresholdTopStageProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedThresholdTopStageProgram
        (normalizedThresholdTopStageBits inputLength request)
        (normalizedThresholdTopStageFuel request)
        (initialNPOracleState inputLength
          (normalizedCircuitHeaderBottomPayload inputLength request)) =
      some (normalizedThresholdTopStageOutput inputLength request) := by
  simpa [normalizedThresholdTopStageProgram,
    normalizedThresholdTopStageBits, normalizedThresholdTopStageFuel,
    normalizedThresholdTopResult, normalizedThresholdTopContext,
    normalizedThresholdTopStageOutput,
    normalizedCircuitHeaderBottomPayload] using
      (run_nativeContextCallProgram supportedGateRelationProgram inputLength
        (normalizedCircuitCountValue request)
        (normalizedCircuitTopCode request)
        (normalizedThresholdTopContext inputLength request)
        (normalizedThresholdTopResult request)
        (supportedGateRelationBits
          (normalizedCircuitCountValue request)
          (normalizedCircuitTopCode request))
        (supportedGateRelationFuel
          (normalizedCircuitCountValue request)
          (normalizedCircuitTopCode request))
        (run_supportedGateRelationProgram
          (normalizedCircuitCountValue request)
          (normalizedCircuitTopCode request)))

def normalizedThresholdValidationOutput
    (inputLength request : ℕ) : ℕ :=
  if normalizedThresholdTopResult request = 0 then
    0
  else
    Nat.pair (normalizedThresholdTopResult request) <|
      Nat.pair 2 (normalizedThresholdTopContext inputLength request)

def normalizedThresholdValidationAdapterProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .branchZero 2 8 4
  , .set 5 2 5
  , .pair 5 4 6 6
  , .pair 2 6 0 7
  , .halt 0
  , .set 0 0 9
  , .halt 0
  ]

@[simp] theorem normalizedThresholdValidationAdapterProgram_oracleFree :
    OracleFree normalizedThresholdValidationAdapterProgram := by
  rfl

private def normalizedThresholdValidationAdapterValues
    (inputLength request : ℕ) : List ℕ :=
  [ inputLength
  , normalizedThresholdTopStageOutput inputLength request
  , normalizedThresholdTopResult request
  , Nat.pair (normalizedCircuitCountValue request)
      (normalizedThresholdTopContext inputLength request)
  , normalizedThresholdTopContext inputLength request
  , 2
  , Nat.pair 2 (normalizedThresholdTopContext inputLength request)
  , normalizedThresholdValidationOutput inputLength request
  , 0
  ]

def normalizedThresholdValidationAdapterBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedThresholdValidationAdapterValues inputLength request).map
      natBitLength |>.foldr max 1

def normalizedThresholdValidationAdapterFuel (request : ℕ) : ℕ :=
  if normalizedThresholdTopResult request = 0 then 6 else 8

theorem run_normalizedThresholdValidationAdapterProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedThresholdValidationAdapterProgram
        (normalizedThresholdValidationAdapterBits inputLength request)
        (normalizedThresholdValidationAdapterFuel request)
        (initialNPOracleState inputLength
          (normalizedThresholdTopStageOutput inputLength request)) =
      some (normalizedThresholdValidationOutput inputLength request) := by
  have hbits :
      ∀ value ∈
          normalizedThresholdValidationAdapterValues inputLength request,
        natBitLength value ≤
          normalizedThresholdValidationAdapterBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  by_cases hresult : normalizedThresholdTopResult request = 0
  · simp [normalizedThresholdValidationAdapterFuel,
      normalizedThresholdValidationAdapterProgram, runNPOracleProgram,
      initialNPOracleState, NPOracleState.boundedWrite, hbits,
      normalizedThresholdValidationAdapterValues,
      normalizedThresholdTopStageOutput,
      normalizedThresholdValidationOutput, hresult]
  · simp [normalizedThresholdValidationAdapterFuel,
      normalizedThresholdValidationAdapterProgram, runNPOracleProgram,
      initialNPOracleState, NPOracleState.boundedWrite, hbits,
      normalizedThresholdValidationAdapterValues,
      normalizedThresholdTopStageOutput,
      normalizedThresholdValidationOutput, hresult]

def normalizedThresholdBranchProgram : NPOracleProgram :=
  linkPrograms normalizedThresholdTopStageProgram
    normalizedThresholdValidationAdapterProgram

@[simp] theorem normalizedThresholdBranchProgram_oracleFree :
    OracleFree normalizedThresholdBranchProgram :=
  oracleFree_linkPrograms normalizedThresholdTopStageProgram_oracleFree
    normalizedThresholdValidationAdapterProgram_oracleFree

private def normalizedThresholdBranchStageBits
    (inputLength request : ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , normalizedThresholdTopStageBits inputLength request
  , normalizedThresholdValidationAdapterBits inputLength request
  ]

def normalizedThresholdBranchBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedThresholdBranchStageBits inputLength request).foldr max 1

def normalizedThresholdBranchFuel (request : ℕ) : ℕ :=
  linkFuel normalizedThresholdValidationAdapterProgram
    (normalizedThresholdTopStageFuel request)
    (normalizedThresholdValidationAdapterFuel request)

theorem run_normalizedThresholdBranchProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedThresholdBranchProgram
        (normalizedThresholdBranchBits inputLength request)
        (normalizedThresholdBranchFuel request)
        (initialNPOracleState inputLength
          (normalizedCircuitHeaderBottomPayload inputLength request)) =
      some (normalizedThresholdValidationOutput inputLength request) := by
  let maximumBits := normalizedThresholdBranchBits inputLength request
  have hbound :
      ∀ value ∈ normalizedThresholdBranchStageBits inputLength request,
        value ≤ maximumBits := by
    intro value hvalue
    exact normalizedCircuit_le_foldrMax hvalue
  have hpositive : 1 ≤ maximumBits :=
    hbound 1 (by simp [normalizedThresholdBranchStageBits])
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    hbound (natBitLength inputLength)
      (by simp [normalizedThresholdBranchStageBits])
  have htop := run_bits_mono
    (run_normalizedThresholdTopStageProgram inputLength request)
    (hbound (normalizedThresholdTopStageBits inputLength request)
      (by simp [normalizedThresholdBranchStageBits]))
  have hadapter := run_bits_mono
    (run_normalizedThresholdValidationAdapterProgram inputLength request)
    (hbound
      (normalizedThresholdValidationAdapterBits inputLength request)
      (by simp [normalizedThresholdBranchStageBits]))
  have hrun :=
    run_linkPrograms hpositive hinputLength htop hadapter
  simpa only [maximumBits, normalizedThresholdBranchProgram,
    normalizedThresholdBranchFuel] using hrun

/-! ## Fail-closed family dispatch -/

def normalizedCircuitHeaderTag
    (inputLength request : ℕ) : ℕ :=
  (Nat.unpair
    (normalizedCircuitHeaderBottomOutput inputLength request)).1

def normalizedCircuitHeaderPayload
    (inputLength request : ℕ) : ℕ :=
  (Nat.unpair
    (normalizedCircuitHeaderBottomOutput inputLength request)).2

def normalizedCircuitDispatchInput
    (inputLength request : ℕ) : ℕ :=
  let tag := normalizedCircuitHeaderTag inputLength request
  if tag = 0 then
    0
  else
    Nat.pair 1 <|
      Nat.pair tag.pred
        (normalizedCircuitHeaderPayload inputLength request)

/-- Lower common validation into two zero/nonzero dispatch levels.  The common
producer emits only tags `0`, `1`, and `2`, so predecessor maps the two valid
families to the inner choice's `0` and `1` branches. -/
def normalizedCircuitDispatchLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .branchZero 2 8 3
  , .decrement 2 4
  , .pair 2 3 5 5
  , .set 4 1 6
  , .pair 4 5 0 7
  , .halt 0
  , .set 0 0 9
  , .halt 0
  ]

@[simp] theorem normalizedCircuitDispatchLoweringProgram_oracleFree :
    OracleFree normalizedCircuitDispatchLoweringProgram := by
  rfl

private def normalizedCircuitDispatchLoweringValues
    (inputLength request : ℕ) : List ℕ :=
  let tag := normalizedCircuitHeaderTag inputLength request
  let payload := normalizedCircuitHeaderPayload inputLength request
  [ inputLength
  , normalizedCircuitHeaderBottomOutput inputLength request
  , tag
  , payload
  , tag.pred
  , Nat.pair tag.pred payload
  , 1
  , normalizedCircuitDispatchInput inputLength request
  , 0
  ]

def normalizedCircuitDispatchLoweringBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedCircuitDispatchLoweringValues inputLength request).map
      natBitLength |>.foldr max 1

def normalizedCircuitDispatchLoweringFuel
    (inputLength request : ℕ) : ℕ :=
  if normalizedCircuitHeaderTag inputLength request = 0 then 5 else 8

theorem run_normalizedCircuitDispatchLoweringProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitDispatchLoweringProgram
        (normalizedCircuitDispatchLoweringBits inputLength request)
        (normalizedCircuitDispatchLoweringFuel inputLength request)
        (initialNPOracleState inputLength
          (normalizedCircuitHeaderBottomOutput inputLength request)) =
      some (normalizedCircuitDispatchInput inputLength request) := by
  have hbits :
      ∀ value ∈
          normalizedCircuitDispatchLoweringValues inputLength request,
        natBitLength value ≤
          normalizedCircuitDispatchLoweringBits inputLength request := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  by_cases htag : normalizedCircuitHeaderTag inputLength request = 0
  · have htag' :
        (Nat.unpair
          (normalizedCircuitHeaderBottomOutput inputLength request)).1 =
            0 := by
      simpa [normalizedCircuitHeaderTag] using htag
    simp [normalizedCircuitDispatchLoweringFuel,
      normalizedCircuitDispatchLoweringProgram, runNPOracleProgram,
      initialNPOracleState, NPOracleState.boundedWrite, hbits,
      normalizedCircuitDispatchLoweringValues,
      normalizedCircuitHeaderTag, normalizedCircuitHeaderPayload,
      normalizedCircuitDispatchInput, htag']
  · have htag' :
        (Nat.unpair
          (normalizedCircuitHeaderBottomOutput inputLength request)).1 ≠
            0 := by
      simpa [normalizedCircuitHeaderTag] using htag
    simp [normalizedCircuitDispatchLoweringFuel,
      normalizedCircuitDispatchLoweringProgram, runNPOracleProgram,
      initialNPOracleState, NPOracleState.boundedWrite, hbits,
      normalizedCircuitDispatchLoweringValues,
      normalizedCircuitHeaderTag, normalizedCircuitHeaderPayload,
      normalizedCircuitDispatchInput, htag']

private theorem normalizedCircuitHeaderPayload_eq_of_tag_ne_zero
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request ≠ 0) :
    normalizedCircuitHeaderPayload inputLength request =
      normalizedCircuitHeaderBottomPayload inputLength request := by
  simp only [normalizedCircuitHeaderTag] at htag
  simp only [normalizedCircuitHeaderPayload]
  unfold normalizedCircuitHeaderBottomOutput at htag ⊢
  split_ifs at htag ⊢ <;> simp_all

private theorem normalizedCircuitHeaderTag_eq_one_or_two_of_ne_zero
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request ≠ 0) :
    normalizedCircuitHeaderTag inputLength request = 1 ∨
      normalizedCircuitHeaderTag inputLength request = 2 := by
  unfold normalizedCircuitHeaderTag at htag ⊢
  unfold normalizedCircuitHeaderBottomOutput at htag ⊢
  split_ifs at htag ⊢ <;> simp_all

def normalizedCircuitFamilyChoiceProgram : NPOracleProgram :=
  taggedProgramChoice normalizedSymmetricBranchProgram
    normalizedThresholdBranchProgram

def normalizedCircuitDispatchProgram : NPOracleProgram :=
  taggedProgramChoice rejectProgram normalizedCircuitFamilyChoiceProgram

@[simp] theorem normalizedCircuitDispatchProgram_oracleFree :
    OracleFree normalizedCircuitDispatchProgram := by
  exact taggedProgramChoice_oracleFree rejectProgram
    normalizedCircuitFamilyChoiceProgram rejectProgram_oracleFree <|
      taggedProgramChoice_oracleFree normalizedSymmetricBranchProgram
        normalizedThresholdBranchProgram
        normalizedSymmetricBranchProgram_oracleFree
        normalizedThresholdBranchProgram_oracleFree

def normalizedCircuitDispatchOutput
    (inputLength request : ℕ) : ℕ :=
  let tag := normalizedCircuitHeaderTag inputLength request
  if tag = 0 then
    0
  else if tag.pred = 0 then
    normalizedSymmetricValidationOutput inputLength request
  else
    normalizedThresholdValidationOutput inputLength request

private def normalizedCircuitFamilyChoiceInput
    (inputLength request : ℕ) : ℕ :=
  Nat.pair (normalizedCircuitHeaderTag inputLength request).pred
    (normalizedCircuitHeaderPayload inputLength request)

private def normalizedCircuitDispatchStageBits
    (inputLength request : ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , natBitLength 0
  , natBitLength
      (Nat.pair inputLength
        (normalizedCircuitDispatchInput inputLength request))
  , natBitLength
      (Nat.pair inputLength
        (normalizedCircuitFamilyChoiceInput inputLength request))
  , normalizedSymmetricBranchBits inputLength request
  , normalizedThresholdBranchBits inputLength request
  , natBitLength (normalizedSymmetricValidationOutput inputLength request)
  , natBitLength (normalizedThresholdValidationOutput inputLength request)
  ]

def normalizedCircuitDispatchBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedCircuitDispatchStageBits inputLength request).foldr max 1

def normalizedCircuitFamilyChoiceFuel
    (inputLength request : ℕ) : ℕ :=
  if (normalizedCircuitHeaderTag inputLength request).pred = 0 then
    taggedProgramChoiceFuel
      (normalizedSymmetricBranchFuel inputLength request)
  else
    taggedProgramChoiceFuel (normalizedThresholdBranchFuel request)

def normalizedCircuitDispatchFuel
    (inputLength request : ℕ) : ℕ :=
  if normalizedCircuitHeaderTag inputLength request = 0 then
    taggedProgramChoiceFuel 2
  else
    taggedProgramChoiceFuel <|
      normalizedCircuitFamilyChoiceFuel inputLength request

theorem run_normalizedCircuitDispatchProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitDispatchProgram
        (normalizedCircuitDispatchBits inputLength request)
        (normalizedCircuitDispatchFuel inputLength request)
        (initialNPOracleState inputLength
          (normalizedCircuitDispatchInput inputLength request)) =
      some (normalizedCircuitDispatchOutput inputLength request) := by
  let maximumBits := normalizedCircuitDispatchBits inputLength request
  have hbound :
      ∀ value ∈ normalizedCircuitDispatchStageBits inputLength request,
        value ≤ maximumBits := by
    intro value hvalue
    exact normalizedCircuit_le_foldrMax hvalue
  have hzero : natBitLength 0 ≤ maximumBits :=
    hbound (natBitLength 0)
      (by simp [normalizedCircuitDispatchStageBits])
  by_cases htag : normalizedCircuitHeaderTag inputLength request = 0
  · have houterInput :
        natBitLength (Nat.pair inputLength 0) ≤
          maximumBits := by
      simpa [normalizedCircuitDispatchInput, htag] using
        hbound
          (natBitLength
            (Nat.pair inputLength
              (normalizedCircuitDispatchInput inputLength request)))
          (by simp [normalizedCircuitDispatchStageBits])
    have hrejected :
        runNPOracleProgram rejectProgram maximumBits 2
            (initialNPOracleState inputLength 0) =
          some 0 := by
      simpa using run_rejectProgram inputLength 0 maximumBits 0 hzero
    simpa [maximumBits, normalizedCircuitDispatchProgram,
      normalizedCircuitDispatchFuel, normalizedCircuitDispatchOutput,
      normalizedCircuitDispatchInput, htag,
      show Nat.pair 0 0 = 0 by rfl] using
        (run_taggedProgramChoice_zero rejectProgram
          normalizedCircuitFamilyChoiceProgram inputLength 0 maximumBits 2 0
          houterInput hrejected hzero)
  · have hpayload :=
      normalizedCircuitHeaderPayload_eq_of_tag_ne_zero htag
    rcases
        normalizedCircuitHeaderTag_eq_one_or_two_of_ne_zero htag with
      hone | htwo
    · have hinnerInput :
          natBitLength
              (Nat.pair inputLength
                (Nat.pair 0
                  (normalizedCircuitHeaderBottomPayload
                    inputLength request))) ≤
            maximumBits := by
        simpa [normalizedCircuitFamilyChoiceInput, hone, hpayload] using
          hbound
            (natBitLength
              (Nat.pair inputLength
                (normalizedCircuitFamilyChoiceInput inputLength request)))
            (by simp [normalizedCircuitDispatchStageBits])
      have houterInput :
          natBitLength
              (Nat.pair inputLength
                (Nat.pair 1
                  (Nat.pair 0
                    (normalizedCircuitHeaderBottomPayload
                      inputLength request)))) ≤
            maximumBits := by
        simpa [normalizedCircuitDispatchInput, hone, hpayload] using
          hbound
            (natBitLength
              (Nat.pair inputLength
                (normalizedCircuitDispatchInput inputLength request)))
            (by simp [normalizedCircuitDispatchStageBits])
      have houtput :
          natBitLength
              (normalizedSymmetricValidationOutput inputLength request) ≤
            maximumBits :=
        hbound
          (natBitLength
            (normalizedSymmetricValidationOutput inputLength request))
          (by simp [normalizedCircuitDispatchStageBits])
      have hsymmetricRun := run_bits_mono
        (run_normalizedSymmetricBranchProgram inputLength request)
        (hbound (normalizedSymmetricBranchBits inputLength request)
          (by simp [normalizedCircuitDispatchStageBits]))
      have hinnerRun :=
        run_taggedProgramChoice_zero normalizedSymmetricBranchProgram
          normalizedThresholdBranchProgram inputLength
          (normalizedCircuitHeaderBottomPayload inputLength request)
          maximumBits (normalizedSymmetricBranchFuel inputLength request)
          (normalizedSymmetricValidationOutput inputLength request)
          hinnerInput hsymmetricRun houtput
      simpa [maximumBits, normalizedCircuitDispatchProgram,
        normalizedCircuitFamilyChoiceProgram, normalizedCircuitDispatchFuel,
        normalizedCircuitFamilyChoiceFuel, normalizedCircuitDispatchOutput,
        normalizedCircuitDispatchInput, hone, hpayload] using
          (run_taggedProgramChoice_nonzero rejectProgram
            normalizedCircuitFamilyChoiceProgram inputLength 1
            (Nat.pair 0
              (normalizedCircuitHeaderBottomPayload inputLength request))
            maximumBits
            (taggedProgramChoiceFuel
              (normalizedSymmetricBranchFuel inputLength request))
            (normalizedSymmetricValidationOutput inputLength request)
            (by omega) houterInput hinnerRun houtput)
    · have hinnerInput :
          natBitLength
              (Nat.pair inputLength
                (Nat.pair 1
                  (normalizedCircuitHeaderBottomPayload
                    inputLength request))) ≤
            maximumBits := by
        simpa [normalizedCircuitFamilyChoiceInput, htwo, hpayload] using
          hbound
            (natBitLength
              (Nat.pair inputLength
                (normalizedCircuitFamilyChoiceInput inputLength request)))
            (by simp [normalizedCircuitDispatchStageBits])
      have houterInput :
          natBitLength
              (Nat.pair inputLength
                (Nat.pair 1
                  (Nat.pair 1
                    (normalizedCircuitHeaderBottomPayload
                      inputLength request)))) ≤
            maximumBits := by
        simpa [normalizedCircuitDispatchInput, htwo, hpayload] using
          hbound
            (natBitLength
              (Nat.pair inputLength
                (normalizedCircuitDispatchInput inputLength request)))
            (by simp [normalizedCircuitDispatchStageBits])
      have houtput :
          natBitLength
              (normalizedThresholdValidationOutput inputLength request) ≤
            maximumBits :=
        hbound
          (natBitLength
            (normalizedThresholdValidationOutput inputLength request))
          (by simp [normalizedCircuitDispatchStageBits])
      have hthresholdRun := run_bits_mono
        (run_normalizedThresholdBranchProgram inputLength request)
        (hbound (normalizedThresholdBranchBits inputLength request)
          (by simp [normalizedCircuitDispatchStageBits]))
      have hinnerRun :=
        run_taggedProgramChoice_nonzero normalizedSymmetricBranchProgram
          normalizedThresholdBranchProgram inputLength 1
          (normalizedCircuitHeaderBottomPayload inputLength request)
          maximumBits (normalizedThresholdBranchFuel request)
          (normalizedThresholdValidationOutput inputLength request)
          (by omega) hinnerInput hthresholdRun houtput
      simpa [maximumBits, normalizedCircuitDispatchProgram,
        normalizedCircuitFamilyChoiceProgram, normalizedCircuitDispatchFuel,
        normalizedCircuitFamilyChoiceFuel, normalizedCircuitDispatchOutput,
        normalizedCircuitDispatchInput, htwo, hpayload] using
          (run_taggedProgramChoice_nonzero rejectProgram
            normalizedCircuitFamilyChoiceProgram inputLength 1
            (Nat.pair 1
              (normalizedCircuitHeaderBottomPayload inputLength request))
            maximumBits
            (taggedProgramChoiceFuel
              (normalizedThresholdBranchFuel request))
            (normalizedThresholdValidationOutput inputLength request)
            (by omega) houterInput hinnerRun houtput)

/-! ## Shared final packaging -/

/-- Both family branches expose the same internal ABI:
`pair topSummary (pair familyTag (pair bottomSummary raw))`.  Packaging is
therefore centralized here, after all validation and dispatch decisions. -/
def normalizedCircuitFinalOutput (branchOutput : ℕ) : ℕ :=
  let topSummary := (Nat.unpair branchOutput).1
  let context := (Nat.unpair branchOutput).2
  let familyTag := (Nat.unpair context).1
  let bottomAndRaw := (Nat.unpair context).2
  if topSummary = 0 then
    0
  else
    Nat.pair familyTag (Nat.pair topSummary bottomAndRaw)

def normalizedCircuitFinalGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .branchZero 2 8 5
  , .pair 2 5 6 6
  , .pair 4 6 0 7
  , .halt 0
  , .set 0 0 9
  , .halt 0
  ]

@[simp] theorem normalizedCircuitFinalGateProgram_oracleFree :
    OracleFree normalizedCircuitFinalGateProgram := by
  rfl

private def normalizedCircuitFinalGateValues
    (inputLength branchOutput : ℕ) : List ℕ :=
  let topSummary := (Nat.unpair branchOutput).1
  let context := (Nat.unpair branchOutput).2
  let familyTag := (Nat.unpair context).1
  let bottomAndRaw := (Nat.unpair context).2
  [ inputLength
  , branchOutput
  , topSummary
  , context
  , familyTag
  , bottomAndRaw
  , Nat.pair topSummary bottomAndRaw
  , normalizedCircuitFinalOutput branchOutput
  , 0
  ]

def normalizedCircuitFinalGateBits
    (inputLength branchOutput : ℕ) : ℕ :=
  (normalizedCircuitFinalGateValues inputLength branchOutput).map
      natBitLength |>.foldr max 1

def normalizedCircuitFinalGateFuel (branchOutput : ℕ) : ℕ :=
  if (Nat.unpair branchOutput).1 = 0 then 7 else 8

theorem run_normalizedCircuitFinalGateProgram
    (inputLength branchOutput : ℕ) :
    runNPOracleProgram normalizedCircuitFinalGateProgram
        (normalizedCircuitFinalGateBits inputLength branchOutput)
        (normalizedCircuitFinalGateFuel branchOutput)
        (initialNPOracleState inputLength branchOutput) =
      some (normalizedCircuitFinalOutput branchOutput) := by
  have hbits :
      ∀ value ∈ normalizedCircuitFinalGateValues inputLength branchOutput,
        natBitLength value ≤
          normalizedCircuitFinalGateBits inputLength branchOutput := by
    intro value hvalue
    exact normalizedCircuit_bitLength_le_foldr_max hvalue
  by_cases htop : (Nat.unpair branchOutput).1 = 0
  · simp [normalizedCircuitFinalGateFuel,
      normalizedCircuitFinalGateProgram, runNPOracleProgram,
      initialNPOracleState, NPOracleState.boundedWrite, hbits,
      normalizedCircuitFinalGateValues, normalizedCircuitFinalOutput, htop]
  · simp [normalizedCircuitFinalGateFuel,
      normalizedCircuitFinalGateProgram, runNPOracleProgram,
      initialNPOracleState, NPOracleState.boundedWrite, hbits,
      normalizedCircuitFinalGateValues, normalizedCircuitFinalOutput, htop]

/-! ## Unique production validator -/

def normalizedCircuitValidationOutput
    (inputLength request : ℕ) : ℕ :=
  normalizedCircuitFinalOutput <|
    normalizedCircuitDispatchOutput inputLength request

def normalizedCircuitValidationProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms
      (linkPrograms normalizedCircuitHeaderBottomProgram
        normalizedCircuitDispatchLoweringProgram)
      normalizedCircuitDispatchProgram)
    normalizedCircuitFinalGateProgram

@[simp] theorem normalizedCircuitValidationProgram_oracleFree :
    OracleFree normalizedCircuitValidationProgram := by
  exact oracleFree_linkPrograms
    (oracleFree_linkPrograms
      (oracleFree_linkPrograms
        normalizedCircuitHeaderBottomProgram_oracleFree
        normalizedCircuitDispatchLoweringProgram_oracleFree)
      normalizedCircuitDispatchProgram_oracleFree)
    normalizedCircuitFinalGateProgram_oracleFree

private def normalizedCircuitValidationStageBits
    (inputLength request : ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , normalizedCircuitHeaderBottomBits inputLength request
  , normalizedCircuitDispatchLoweringBits inputLength request
  , normalizedCircuitDispatchBits inputLength request
  , normalizedCircuitFinalGateBits inputLength
      (normalizedCircuitDispatchOutput inputLength request)
  ]

def normalizedCircuitValidationBits
    (inputLength request : ℕ) : ℕ :=
  (normalizedCircuitValidationStageBits inputLength request).foldr max 1

def normalizedCircuitValidationFuel
    (inputLength request : ℕ) : ℕ :=
  linkFuel normalizedCircuitFinalGateProgram
    (linkFuel normalizedCircuitDispatchProgram
      (linkFuel normalizedCircuitDispatchLoweringProgram
        (normalizedCircuitHeaderBottomFuel inputLength request)
        (normalizedCircuitDispatchLoweringFuel inputLength request))
      (normalizedCircuitDispatchFuel inputLength request))
    (normalizedCircuitFinalGateFuel
      (normalizedCircuitDispatchOutput inputLength request))

theorem run_normalizedCircuitValidationProgram
    (inputLength request : ℕ) :
    runNPOracleProgram normalizedCircuitValidationProgram
        (normalizedCircuitValidationBits inputLength request)
        (normalizedCircuitValidationFuel inputLength request)
        (initialNPOracleState inputLength request) =
      some (normalizedCircuitValidationOutput inputLength request) := by
  let maximumBits := normalizedCircuitValidationBits inputLength request
  have hbound :
      ∀ value ∈ normalizedCircuitValidationStageBits inputLength request,
        value ≤ maximumBits := by
    intro value hvalue
    exact normalizedCircuit_le_foldrMax hvalue
  have hpositive : 1 ≤ maximumBits :=
    hbound 1 (by simp [normalizedCircuitValidationStageBits])
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    hbound (natBitLength inputLength)
      (by simp [normalizedCircuitValidationStageBits])
  have hcommon := run_bits_mono
    (run_normalizedCircuitHeaderBottomProgram inputLength request)
    (hbound (normalizedCircuitHeaderBottomBits inputLength request)
      (by simp [normalizedCircuitValidationStageBits]))
  have hlowering := run_bits_mono
    (run_normalizedCircuitDispatchLoweringProgram inputLength request)
    (hbound (normalizedCircuitDispatchLoweringBits inputLength request)
      (by simp [normalizedCircuitValidationStageBits]))
  have hdispatch := run_bits_mono
    (run_normalizedCircuitDispatchProgram inputLength request)
    (hbound (normalizedCircuitDispatchBits inputLength request)
      (by simp [normalizedCircuitValidationStageBits]))
  have hfinal := run_bits_mono
    (run_normalizedCircuitFinalGateProgram inputLength
      (normalizedCircuitDispatchOutput inputLength request))
    (hbound
      (normalizedCircuitFinalGateBits inputLength
        (normalizedCircuitDispatchOutput inputLength request))
      (by simp [normalizedCircuitValidationStageBits]))
  have hloweringPrefix :=
    run_linkPrograms hpositive hinputLength hcommon hlowering
  have hdispatchPrefix :=
    run_linkPrograms hpositive hinputLength hloweringPrefix hdispatch
  have hrun :=
    run_linkPrograms hpositive hinputLength hdispatchPrefix hfinal
  simpa only [maximumBits, normalizedCircuitValidationProgram,
    normalizedCircuitValidationFuel, normalizedCircuitValidationOutput]
    using hrun

/-! ## Exact family semantics -/

theorem normalizedSymmetricTopSummaryOutput_ne_zero_iff_decode
    (inputLength request : ℕ) :
    normalizedSymmetricTopSummaryOutput inputLength request ≠ 0 ↔
      (decodeBoolList (normalizedCircuitTopCode request)).isSome := by
  unfold normalizedSymmetricTopSummaryOutput
  rw [balancedValidationSummaryOutput_ne_zero_iff,
    decodeBoolList_isSome_iff]
  constructor
  · rintro ⟨codes, hdecode, hall⟩
    refine ⟨codes, hdecode, ?_⟩
    intro code hcode
    have hvalid := hall code hcode
    have hraw : boolCodeValidationOutput code ≠ 0 := by
      simpa [boolCodeRequestOutput, nativeInputRequest] using hvalid
    exact (boolCodeValidationOutput_ne_zero_iff code).1 hraw
  · rintro ⟨codes, hdecode, hall⟩
    refine ⟨codes, hdecode, ?_⟩
    intro code hcode
    have hvalid :=
      (boolCodeValidationOutput_ne_zero_iff code).2 (hall code hcode)
    change
      boolCodeRequestOutput (nativeInputRequest inputLength code) ≠ 0
    simpa [boolCodeRequestOutput, nativeInputRequest] using hvalid

theorem normalizedSymmetricTopLength_eq_of_decode
    {inputLength request : ℕ} {top : List Bool}
    (hdecode :
      decodeBoolList (normalizedCircuitTopCode request) = some top) :
    normalizedSymmetricTopLength inputLength request = top.length := by
  have hsummary :
      normalizedSymmetricTopSummaryOutput inputLength request ≠ 0 :=
    (normalizedSymmetricTopSummaryOutput_ne_zero_iff_decode
      inputLength request).2 (by simp [hdecode])
  have hpayload :=
    balancedValidationSummaryOutput_payload inputLength
      (normalizedCircuitTopCode request) boolCodeRequestOutput hsummary
  have hcanonical :
      encodeBoolList top = normalizedCircuitTopCode request :=
    encodeBoolList_of_decode hdecode
  have hbalanced :
      decodeBalancedList (normalizedCircuitTopCode request) =
        some (top.map boolCode) := by
    rw [← hcanonical, encodeBoolList, decodeBalancedList_encode]
  change
    (Nat.unpair
      (normalizedSymmetricTopSummaryOutput inputLength request)).2 =
        balancedValidationSummaryData inputLength
          (normalizedCircuitTopCode request) boolCodeRequestOutput
    at hpayload
  simp only [normalizedSymmetricTopLength]
  rw [hpayload]
  simp [balancedValidationSummaryData, balancedValidationMapOutputs,
    balancedValidationMapRequests, balancedValidationMapCodes, hbalanced]

private theorem normalizedSymmetricValidationOutput_ne_zero_iff_checks
    (inputLength request : ℕ) :
    normalizedSymmetricValidationOutput inputLength request ≠ 0 ↔
      normalizedSymmetricLengthEqualityFlag inputLength request ≠ 0 ∧
        normalizedSymmetricTopSummaryOutput inputLength request ≠ 0 := by
  by_cases hlength :
      normalizedSymmetricLengthEqualityFlag inputLength request = 0
  · simp [normalizedSymmetricValidationOutput, hlength]
  · by_cases hsummary :
        normalizedSymmetricTopSummaryOutput inputLength request = 0
    · simp [normalizedSymmetricValidationOutput, hlength, hsummary]
    · simp [normalizedSymmetricValidationOutput, hlength, hsummary]
      have hpair :=
        Nat.left_le_pair
          (normalizedSymmetricTopSummaryOutput inputLength request)
          (normalizedSymmetricBranchContext inputLength request)
      omega

theorem normalizedSymmetricValidationOutput_ne_zero_iff
    (inputLength request : ℕ) :
    normalizedSymmetricValidationOutput inputLength request ≠ 0 ↔
      ∃ top,
        decodeBoolList (normalizedCircuitTopCode request) = some top ∧
          top.length = normalizedCircuitCountValue request + 1 := by
  rw [normalizedSymmetricValidationOutput_ne_zero_iff_checks]
  constructor
  · rintro ⟨hlength, hsummary⟩
    obtain ⟨top, hdecode⟩ := Option.isSome_iff_exists.mp <|
      (normalizedSymmetricTopSummaryOutput_ne_zero_iff_decode
        inputLength request).1 hsummary
    have hequality :
        normalizedSymmetricTopLength inputLength request =
          normalizedSymmetricExpectedTopLength request :=
      (nativeNatEqOutput_ne_zero_iff _ _).1 <| by
        simpa only [normalizedSymmetricLengthEqualityFlag] using hlength
    refine ⟨top, hdecode, ?_⟩
    rw [← normalizedSymmetricTopLength_eq_of_decode hdecode]
    simpa only [normalizedSymmetricExpectedTopLength] using hequality
  · rintro ⟨top, hdecode, hlength⟩
    have hsummary :
        normalizedSymmetricTopSummaryOutput inputLength request ≠ 0 :=
      (normalizedSymmetricTopSummaryOutput_ne_zero_iff_decode
        inputLength request).2 (by simp [hdecode])
    have hequality :
        normalizedSymmetricTopLength inputLength request =
          normalizedSymmetricExpectedTopLength request := by
      rw [normalizedSymmetricTopLength_eq_of_decode hdecode]
      simpa only [normalizedSymmetricExpectedTopLength] using hlength
    have hlengthFlag :
        normalizedSymmetricLengthEqualityFlag inputLength request ≠ 0 := by
      apply (nativeNatEqOutput_ne_zero_iff _ _).2
      exact hequality
    exact ⟨hlengthFlag, hsummary⟩

theorem normalizedThresholdValidationOutput_ne_zero_iff
    (inputLength request : ℕ) :
    normalizedThresholdValidationOutput inputLength request ≠ 0 ↔
      (decodeSupportedNormalizedGate
        (normalizedCircuitCountValue request)
        (normalizedCircuitTopCode request)).isSome := by
  rw [← supportedGateRelationOutput_ne_zero_iff_decode]
  unfold normalizedThresholdValidationOutput normalizedThresholdTopResult
  by_cases hresult :
      supportedGateRelationOutput
        (normalizedCircuitCountValue request)
        (normalizedCircuitTopCode request) = 0
  · simp [hresult]
  · simp [hresult]
    have hpair :=
      Nat.left_le_pair
        (supportedGateRelationOutput
          (normalizedCircuitCountValue request)
          (normalizedCircuitTopCode request))
        (Nat.pair 2 (normalizedThresholdTopContext inputLength request))
    omega

theorem normalizedCircuitFinalOutput_ne_zero_iff
    (branchOutput : ℕ) :
    normalizedCircuitFinalOutput branchOutput ≠ 0 ↔
      (Nat.unpair branchOutput).1 ≠ 0 := by
  unfold normalizedCircuitFinalOutput
  by_cases htop : (Nat.unpair branchOutput).1 = 0
  · rw [if_pos htop]
    constructor
    · intro hfalse
      exact False.elim (hfalse rfl)
    · intro hfalse
      exact False.elim (hfalse htop)
  · rw [if_neg htop]
    constructor
    · intro _
      exact htop
    · intro _ hpair
      have hinner :=
        Nat.left_le_pair (Nat.unpair branchOutput).1
          (Nat.unpair (Nat.unpair branchOutput).2).2
      have houter :=
        Nat.right_le_pair (Nat.unpair (Nat.unpair branchOutput).2).1
          (Nat.pair (Nat.unpair branchOutput).1
            (Nat.unpair (Nat.unpair branchOutput).2).2)
      rw [hpair] at houter
      omega

theorem normalizedCircuitValidationOutput_ne_zero_iff_branches
    (inputLength request : ℕ) :
    normalizedCircuitValidationOutput inputLength request ≠ 0 ↔
      (normalizedCircuitHeaderTag inputLength request = 1 ∧
        normalizedSymmetricValidationOutput inputLength request ≠ 0) ∨
      (normalizedCircuitHeaderTag inputLength request = 2 ∧
        normalizedThresholdValidationOutput inputLength request ≠ 0) := by
  rw [normalizedCircuitValidationOutput,
    normalizedCircuitFinalOutput_ne_zero_iff]
  by_cases hzero :
      normalizedCircuitHeaderTag inputLength request = 0
  · simp [normalizedCircuitDispatchOutput, hzero]
  · rcases
        normalizedCircuitHeaderTag_eq_one_or_two_of_ne_zero hzero with
      hone | htwo
    · by_cases hlength :
          normalizedSymmetricLengthEqualityFlag inputLength request = 0
      · simp [normalizedCircuitDispatchOutput,
          normalizedSymmetricValidationOutput, hone, hlength]
      · by_cases hsummary :
            normalizedSymmetricTopSummaryOutput inputLength request = 0
        · simp [normalizedCircuitDispatchOutput,
            normalizedSymmetricValidationOutput, hone, hlength, hsummary]
        · simp [normalizedCircuitDispatchOutput,
            normalizedSymmetricValidationOutput, hone, hlength, hsummary]
          have hpair :=
            Nat.left_le_pair
              (normalizedSymmetricTopSummaryOutput inputLength request)
              (normalizedSymmetricBranchContext inputLength request)
          omega
    · by_cases hresult : normalizedThresholdTopResult request = 0
      · simp [normalizedCircuitDispatchOutput,
          normalizedThresholdValidationOutput, htwo, hresult]
      · simp [normalizedCircuitDispatchOutput,
          normalizedThresholdValidationOutput, htwo, hresult]
        have hpair :=
          Nat.left_le_pair (normalizedThresholdTopResult request)
            (Nat.pair 2 (normalizedThresholdTopContext inputLength request))
        omega

private theorem normalizedCircuitCountValue_eq_of_decode
    {request countCode bottomCount : ℕ}
    (hcountCode : normalizedCircuitCountCode request = countCode)
    (hcount : decodeNat countCode = some bottomCount) :
    normalizedCircuitCountValue request = bottomCount := by
  have hcountDecode :
      decodeNat (normalizedCircuitCountCode request) = some bottomCount := by
    simpa only [hcountCode] using hcount
  have hcountOutput :=
    canonicalNatValidationOutput_of_decode hcountDecode
  simp [normalizedCircuitCountValue, normalizedCircuitCountValidation,
    hcountOutput]

theorem normalizedSymmetricDecoder_isSome_iff_common_branch
    (inputLength request : ℕ)
    (hfamily : normalizedCircuitExpectedFamily request = 0) :
    (decodeNormalizedSymmetricThresholdCircuit inputLength
        (normalizedCircuitRawCode request)).isSome ↔
      NormalizedCircuitCommonFieldsValid inputLength
          (normalizedCircuitExpectedFamily request)
          (normalizedCircuitRawCode request) ∧
        normalizedSymmetricValidationOutput inputLength request ≠ 0 := by
  rw [decodeNormalizedSymmetricThresholdCircuit_isSome_iff_fields]
  constructor
  · rintro ⟨familyCode, countCode, bottomCode, topCode, bottomCount,
      bottomCodes, top, htuple, hfamilyDecode, hcount, hbottom, hall,
      htop, hbottomLength, htopLength⟩
    obtain ⟨_, _, hcountCode, _, htopCode⟩ :=
      normalizedCircuitTupleAccessors_of_decode htuple
    have hcountValue :=
      normalizedCircuitCountValue_eq_of_decode hcountCode hcount
    constructor
    · refine ⟨?_, familyCode, countCode, bottomCode, topCode,
        bottomCount, bottomCodes, htuple, ?_, hcount, hbottom, hall,
        hbottomLength⟩
      · left
        simpa [symmetricCircuitFamilyTag] using hfamily
      · simpa [hfamily, symmetricCircuitFamilyTag] using hfamilyDecode
    · apply (normalizedSymmetricValidationOutput_ne_zero_iff
        inputLength request).2
      refine ⟨top, ?_, ?_⟩
      · simpa only [htopCode] using htop
      · omega
  · rintro
      ⟨⟨_, familyCode, countCode, bottomCode, topCode, bottomCount,
          bottomCodes, htuple, hfamilyDecode, hcount, hbottom, hall,
          hbottomLength⟩, htopValid⟩
    obtain ⟨_, _, hcountCode, _, htopCode⟩ :=
      normalizedCircuitTupleAccessors_of_decode htuple
    have hcountValue :=
      normalizedCircuitCountValue_eq_of_decode hcountCode hcount
    obtain ⟨top, htop, htopLength⟩ :=
      (normalizedSymmetricValidationOutput_ne_zero_iff
        inputLength request).1 htopValid
    refine ⟨familyCode, countCode, bottomCode, topCode, bottomCount,
      bottomCodes, top, htuple, ?_, hcount, hbottom, hall, ?_,
      hbottomLength, ?_⟩
    · simpa [hfamily, symmetricCircuitFamilyTag] using hfamilyDecode
    · simpa only [htopCode] using htop
    · omega

theorem normalizedThresholdDecoder_isSome_iff_common_branch
    (inputLength request : ℕ)
    (hfamily : normalizedCircuitExpectedFamily request = 1) :
    (decodeNormalizedThresholdThresholdCircuit inputLength
        (normalizedCircuitRawCode request)).isSome ↔
      NormalizedCircuitCommonFieldsValid inputLength
          (normalizedCircuitExpectedFamily request)
          (normalizedCircuitRawCode request) ∧
        normalizedThresholdValidationOutput inputLength request ≠ 0 := by
  rw [decodeNormalizedThresholdThresholdCircuit_isSome_iff_fields]
  constructor
  · rintro ⟨familyCode, countCode, bottomCode, topCode, bottomCount,
      bottomCodes, htuple, hfamilyDecode, hcount, hbottom, hall,
      htop, hbottomLength⟩
    obtain ⟨_, _, hcountCode, _, htopCode⟩ :=
      normalizedCircuitTupleAccessors_of_decode htuple
    have hcountValue :=
      normalizedCircuitCountValue_eq_of_decode hcountCode hcount
    constructor
    · refine ⟨?_, familyCode, countCode, bottomCode, topCode,
        bottomCount, bottomCodes, htuple, ?_, hcount, hbottom, hall,
        hbottomLength⟩
      · right
        simpa [thresholdCircuitFamilyTag] using hfamily
      · simpa [hfamily, thresholdCircuitFamilyTag] using hfamilyDecode
    · apply (normalizedThresholdValidationOutput_ne_zero_iff
        inputLength request).2
      rw [hcountValue, htopCode]
      exact htop
  · rintro
      ⟨⟨_, familyCode, countCode, bottomCode, topCode, bottomCount,
          bottomCodes, htuple, hfamilyDecode, hcount, hbottom, hall,
          hbottomLength⟩, htopValid⟩
    obtain ⟨_, _, hcountCode, _, htopCode⟩ :=
      normalizedCircuitTupleAccessors_of_decode htuple
    have hcountValue :=
      normalizedCircuitCountValue_eq_of_decode hcountCode hcount
    have htop :=
      (normalizedThresholdValidationOutput_ne_zero_iff
        inputLength request).1 htopValid
    refine ⟨familyCode, countCode, bottomCode, topCode, bottomCount,
      bottomCodes, htuple, ?_, hcount, hbottom, hall, ?_,
      hbottomLength⟩
    · simpa [hfamily, thresholdCircuitFamilyTag] using hfamilyDecode
    · rw [hcountValue, htopCode] at htop
      exact htop

theorem normalizedCircuitHeaderTag_eq_one_iff
    (inputLength request : ℕ) :
    normalizedCircuitHeaderTag inputLength request = 1 ↔
      normalizedCircuitExpectedFamily request = 0 ∧
        NormalizedCircuitCommonFieldsValid inputLength
          (normalizedCircuitExpectedFamily request)
          (normalizedCircuitRawCode request) := by
  constructor
  · intro htag
    have houtput :
        normalizedCircuitHeaderBottomOutput inputLength request ≠ 0 := by
      intro hzero
      simp [normalizedCircuitHeaderTag, hzero] at htag
    have hfamily : normalizedCircuitExpectedFamily request = 0 := by
      unfold normalizedCircuitHeaderTag at htag
      unfold normalizedCircuitHeaderBottomOutput at htag
      split_ifs at htag <;> simp_all
    exact ⟨hfamily,
      (normalizedCircuitHeaderBottomOutput_ne_zero_iff_fields
        inputLength request).1 houtput⟩
  · rintro ⟨hfamily, hfields⟩
    have houtput :
        normalizedCircuitHeaderBottomOutput inputLength request ≠ 0 :=
      (normalizedCircuitHeaderBottomOutput_ne_zero_iff_fields
        inputLength request).2 hfields
    obtain ⟨hlength, hbottom, hcount, hfamilyFlag, htuple, _⟩ :=
      (normalizedCircuitHeaderBottomOutput_ne_zero_iff_checks
        inputLength request).1 houtput
    simp [normalizedCircuitHeaderTag, normalizedCircuitHeaderBottomOutput,
      hlength, hbottom, hcount, hfamilyFlag, htuple, hfamily]

theorem normalizedCircuitHeaderTag_eq_two_iff
    (inputLength request : ℕ) :
    normalizedCircuitHeaderTag inputLength request = 2 ↔
      normalizedCircuitExpectedFamily request = 1 ∧
        NormalizedCircuitCommonFieldsValid inputLength
          (normalizedCircuitExpectedFamily request)
          (normalizedCircuitRawCode request) := by
  constructor
  · intro htag
    have houtput :
        normalizedCircuitHeaderBottomOutput inputLength request ≠ 0 := by
      intro hzero
      simp [normalizedCircuitHeaderTag, hzero] at htag
    have hfamily : normalizedCircuitExpectedFamily request = 1 := by
      unfold normalizedCircuitHeaderTag at htag
      unfold normalizedCircuitHeaderBottomOutput at htag
      split_ifs at htag <;> simp_all
    exact ⟨hfamily,
      (normalizedCircuitHeaderBottomOutput_ne_zero_iff_fields
        inputLength request).1 houtput⟩
  · rintro ⟨hfamily, hfields⟩
    have houtput :
        normalizedCircuitHeaderBottomOutput inputLength request ≠ 0 :=
      (normalizedCircuitHeaderBottomOutput_ne_zero_iff_fields
        inputLength request).2 hfields
    obtain ⟨hlength, hbottom, hcount, hfamilyFlag, htuple, _⟩ :=
      (normalizedCircuitHeaderBottomOutput_ne_zero_iff_checks
        inputLength request).1 houtput
    simp [normalizedCircuitHeaderTag, normalizedCircuitHeaderBottomOutput,
      hlength, hbottom, hcount, hfamilyFlag, htuple, hfamily]

theorem normalizedCircuitValidationOutput_ne_zero_iff
    (inputLength request : ℕ) :
    normalizedCircuitValidationOutput inputLength request ≠ 0 ↔
      (normalizedCircuitExpectedFamily request = 0 ∧
        (decodeNormalizedSymmetricThresholdCircuit inputLength
          (normalizedCircuitRawCode request)).isSome) ∨
      (normalizedCircuitExpectedFamily request = 1 ∧
        (decodeNormalizedThresholdThresholdCircuit inputLength
          (normalizedCircuitRawCode request)).isSome) := by
  rw [normalizedCircuitValidationOutput_ne_zero_iff_branches]
  constructor
  · intro hvalid
    rcases hvalid with hvalid | hvalid
    · obtain ⟨htag, hbranch⟩ := hvalid
      obtain ⟨hfamily, hcommon⟩ :=
        (normalizedCircuitHeaderTag_eq_one_iff
          inputLength request).1 htag
      left
      exact ⟨hfamily,
        (normalizedSymmetricDecoder_isSome_iff_common_branch
          inputLength request hfamily).2 ⟨hcommon, hbranch⟩⟩
    · obtain ⟨htag, hbranch⟩ := hvalid
      obtain ⟨hfamily, hcommon⟩ :=
        (normalizedCircuitHeaderTag_eq_two_iff
          inputLength request).1 htag
      right
      exact ⟨hfamily,
        (normalizedThresholdDecoder_isSome_iff_common_branch
          inputLength request hfamily).2 ⟨hcommon, hbranch⟩⟩
  · intro hdecode
    rcases hdecode with hdecode | hdecode
    · obtain ⟨hfamily, hdecode⟩ := hdecode
      obtain ⟨hcommon, hbranch⟩ :=
        (normalizedSymmetricDecoder_isSome_iff_common_branch
          inputLength request hfamily).1 hdecode
      left
      exact
        ⟨(normalizedCircuitHeaderTag_eq_one_iff
            inputLength request).2 ⟨hfamily, hcommon⟩,
          hbranch⟩
    · obtain ⟨hfamily, hdecode⟩ := hdecode
      obtain ⟨hcommon, hbranch⟩ :=
        (normalizedThresholdDecoder_isSome_iff_common_branch
          inputLength request hfamily).1 hdecode
      right
      exact
        ⟨(normalizedCircuitHeaderTag_eq_two_iff
            inputLength request).2 ⟨hfamily, hcommon⟩,
          hbranch⟩

/-! ## Validated summary ABI

The single public validator output is
`pair familyTag (pair topSummary (pair bottomSummaryData rawCircuit))`.  Every
downstream resource reducer projects exactly those fields, so both the shape of
that value and the exact contents of its retained bottom-summary list are
established here, at the producing boundary.  No later stage reparses circuit
syntax, and nothing below unpairs a zero sentinel: each projection theorem
carries the owning gate's acceptance hypothesis. -/

/-- The per-gate validator outputs retained by the shared bottom traversal. -/
def normalizedCircuitBottomOutputs
    (inputLength request : ℕ) : List ℕ :=
  balancedValidationMapOutputs inputLength
    (normalizedCircuitBottomCode request)
    normalizedCircuitBottomRequestOutput

private theorem normalizedCircuitHeaderBottomOutput_ne_zero_of_tag
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request ≠ 0) :
    normalizedCircuitHeaderBottomOutput inputLength request ≠ 0 := by
  intro hzero
  exact htag (by simp [normalizedCircuitHeaderTag, hzero])

theorem normalizedCircuitBottomSummary_ne_zero_of_headerTag
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request ≠ 0) :
    normalizedCircuitBottomSummary inputLength request ≠ 0 :=
  ((normalizedCircuitHeaderBottomOutput_ne_zero_iff_checks
    inputLength request).1
      (normalizedCircuitHeaderBottomOutput_ne_zero_of_tag htag)).2.1

theorem normalizedCircuitBottomOutputs_eq_of_decode
    {inputLength request : ℕ} {bottomCodes : List ℕ}
    (hdecode :
      decodeBalancedList (normalizedCircuitBottomCode request) =
        some bottomCodes) :
    normalizedCircuitBottomOutputs inputLength request =
      bottomCodes.map (supportedGateRelationOutput inputLength) := by
  simp [normalizedCircuitBottomOutputs, balancedValidationMapOutputs,
    balancedValidationMapRequests, balancedValidationMapCodes, hdecode,
    normalizedCircuitBottomRequestOutput, nativeInputRequest,
    Function.comp_def]

/-- The bottom summary retained by the shared header gate is exactly the
mapped per-gate summaries, their length, and the source balanced tree. -/
theorem normalizedCircuitBottomSummaryData_eq_of_headerTag
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request ≠ 0) :
    normalizedCircuitBottomSummaryData inputLength request =
      Nat.pair
        (encodeBalancedList
          (normalizedCircuitBottomOutputs inputLength request))
        (Nat.pair
          (normalizedCircuitBottomOutputs inputLength request).length
          (normalizedCircuitBottomCode request)) := by
  have hsummary :
      normalizedCircuitBottomSummaryOutput inputLength
        (normalizedCircuitBottomCode request) ≠ 0 := by
    simpa only [normalizedCircuitBottomSummary] using
      normalizedCircuitBottomSummary_ne_zero_of_headerTag htag
  have hpayload :=
    normalizedCircuitBottomSummaryOutput_payload inputLength
      (normalizedCircuitBottomCode request) hsummary
  simpa only [normalizedCircuitBottomSummaryData,
    normalizedCircuitBottomSummary, balancedValidationSummaryData,
    normalizedCircuitBottomOutputs] using hpayload

/-- The retained bottom length is exact, and the declared bottom count was
already compared against it by the shared header gate. -/
theorem normalizedCircuitCountValue_eq_bottomOutputs_length_of_headerTag
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request ≠ 0) :
    normalizedCircuitCountValue request =
      (normalizedCircuitBottomOutputs inputLength request).length := by
  obtain ⟨hlength, hbottom, _⟩ :=
    (normalizedCircuitHeaderBottomOutput_ne_zero_iff_checks
      inputLength request).1
        (normalizedCircuitHeaderBottomOutput_ne_zero_of_tag htag)
  have hsummary :
      normalizedCircuitBottomSummaryOutput inputLength
        (normalizedCircuitBottomCode request) ≠ 0 := by
    simpa only [normalizedCircuitBottomSummary] using hbottom
  have hpayload :=
    normalizedCircuitBottomSummaryOutput_payload inputLength
      (normalizedCircuitBottomCode request) hsummary
  have hequality :
      normalizedCircuitCountValue request =
        normalizedCircuitBottomLength inputLength request :=
    (nativeNatEqOutput_ne_zero_iff _ _).1 <| by
      simpa only [normalizedCircuitLengthEqualityFlag] using hlength
  rw [hequality]
  simp only [normalizedCircuitBottomLength]
  rw [hpayload]
  simp [balancedValidationSummaryData, normalizedCircuitBottomOutputs]

/-- Accepted symmetric-family shape of the unique public validator output. -/
theorem normalizedCircuitValidationOutput_eq_symmetric
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request = 1)
    (hbranch : normalizedSymmetricValidationOutput inputLength request ≠ 0) :
    normalizedCircuitValidationOutput inputLength request =
      Nat.pair 1
        (Nat.pair (normalizedSymmetricTopSummaryOutput inputLength request)
          (Nat.pair (normalizedCircuitBottomSummaryData inputLength request)
            (normalizedCircuitRawCode request))) := by
  obtain ⟨hlength, hsummary⟩ :=
    (normalizedSymmetricValidationOutput_ne_zero_iff_checks
      inputLength request).1 hbranch
  have hdispatch :
      normalizedCircuitDispatchOutput inputLength request =
        Nat.pair (normalizedSymmetricTopSummaryOutput inputLength request)
          (normalizedSymmetricBranchContext inputLength request) := by
    simp [normalizedCircuitDispatchOutput, htag,
      normalizedSymmetricValidationOutput, hlength, hsummary]
  simp [normalizedCircuitValidationOutput, hdispatch,
    normalizedCircuitFinalOutput, normalizedSymmetricBranchContext,
    hsummary]

/-- Accepted threshold-family shape of the unique public validator output. -/
theorem normalizedCircuitValidationOutput_eq_threshold
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request = 2)
    (hbranch : normalizedThresholdValidationOutput inputLength request ≠ 0) :
    normalizedCircuitValidationOutput inputLength request =
      Nat.pair 2
        (Nat.pair (normalizedThresholdTopResult request)
          (Nat.pair (normalizedCircuitBottomSummaryData inputLength request)
            (normalizedCircuitRawCode request))) := by
  have hresult : normalizedThresholdTopResult request ≠ 0 := by
    intro hzero
    exact hbranch (by simp [normalizedThresholdValidationOutput, hzero])
  have hdispatch :
      normalizedCircuitDispatchOutput inputLength request =
        Nat.pair (normalizedThresholdTopResult request)
          (Nat.pair 2 (normalizedThresholdTopContext inputLength request)) := by
    simp [normalizedCircuitDispatchOutput, htag,
      normalizedThresholdValidationOutput, hresult]
  simp [normalizedCircuitValidationOutput, hdispatch,
    normalizedCircuitFinalOutput, normalizedThresholdTopContext, hresult]

/-! ### Typed field recovery

The canonical circuit codecs are injective on accepted codes, so a successful
decode determines the exact four request fields the validator projected.  These
lemmas are the only place where a typed circuit is related back to the request
syntax; the executable stages never repeat the comparison. -/

theorem normalizedCircuitFields_of_symmetric_decode
    {inputLength request : ℕ}
    {circuit : NormalizedSymmetricThresholdCircuit inputLength}
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitCountCode request = encodeNat circuit.bottomCount ∧
      normalizedCircuitBottomCode request =
        encodeBalancedList
          (List.ofFn fun index =>
            encodeSupportedNormalizedGate (circuit.bottom index)) ∧
      normalizedCircuitTopCode request =
        encodeBoolList (List.ofFn circuit.top) := by
  have htuple :
      decodeTaggedList (normalizedCircuitRawCode request) =
        some
          [encodeNat symmetricCircuitFamilyTag,
            encodeNat circuit.bottomCount,
            encodeBalancedList
              (List.ofFn fun index =>
                encodeSupportedNormalizedGate (circuit.bottom index)),
            encodeBoolList (List.ofFn circuit.top)] := by
    rw [← encodeNormalizedSymmetricThresholdCircuit_of_decode hdecode]
    simp [encodeNormalizedSymmetricThresholdCircuit]
  obtain ⟨_, _, hcount, hbottom, htop⟩ :=
    normalizedCircuitTupleAccessors_of_decode htuple
  exact ⟨hcount, hbottom, htop⟩

theorem normalizedCircuitFields_of_threshold_decode
    {inputLength request : ℕ}
    {circuit : NormalizedThresholdThresholdCircuit inputLength}
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitCountCode request = encodeNat circuit.bottomCount ∧
      normalizedCircuitBottomCode request =
        encodeBalancedList
          (List.ofFn fun index =>
            encodeSupportedNormalizedGate (circuit.bottom index)) ∧
      normalizedCircuitTopCode request =
        encodeSupportedNormalizedGate circuit.top := by
  have htuple :
      decodeTaggedList (normalizedCircuitRawCode request) =
        some
          [encodeNat thresholdCircuitFamilyTag,
            encodeNat circuit.bottomCount,
            encodeBalancedList
              (List.ofFn fun index =>
                encodeSupportedNormalizedGate (circuit.bottom index)),
            encodeSupportedNormalizedGate circuit.top] := by
    rw [← encodeNormalizedThresholdThresholdCircuit_of_decode hdecode]
    simp [encodeNormalizedThresholdThresholdCircuit]
  obtain ⟨_, _, hcount, hbottom, htop⟩ :=
    normalizedCircuitTupleAccessors_of_decode htuple
  exact ⟨hcount, hbottom, htop⟩

theorem normalizedCircuitCountValue_eq_of_symmetric_decode
    {inputLength request : ℕ}
    {circuit : NormalizedSymmetricThresholdCircuit inputLength}
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitCountValue request = circuit.bottomCount :=
  normalizedCircuitCountValue_eq_of_decode
    (normalizedCircuitFields_of_symmetric_decode hdecode).1 (by simp)

theorem normalizedCircuitCountValue_eq_of_threshold_decode
    {inputLength request : ℕ}
    {circuit : NormalizedThresholdThresholdCircuit inputLength}
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitCountValue request = circuit.bottomCount :=
  normalizedCircuitCountValue_eq_of_decode
    (normalizedCircuitFields_of_threshold_decode hdecode).1 (by simp)

theorem normalizedCircuitBottomOutputs_eq_of_symmetric_decode
    {inputLength request : ℕ}
    {circuit : NormalizedSymmetricThresholdCircuit inputLength}
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitBottomOutputs inputLength request =
      List.ofFn fun index =>
        supportedGateRelationOutput inputLength
          (encodeSupportedNormalizedGate (circuit.bottom index)) := by
  have hbottom := (normalizedCircuitFields_of_symmetric_decode hdecode).2.1
  rw [normalizedCircuitBottomOutputs_eq_of_decode
    (bottomCodes :=
      List.ofFn fun index =>
        encodeSupportedNormalizedGate (circuit.bottom index))
    (by rw [hbottom]; simp)]
  simp [Function.comp_def]

theorem normalizedCircuitBottomOutputs_eq_of_threshold_decode
    {inputLength request : ℕ}
    {circuit : NormalizedThresholdThresholdCircuit inputLength}
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitBottomOutputs inputLength request =
      List.ofFn fun index =>
        supportedGateRelationOutput inputLength
          (encodeSupportedNormalizedGate (circuit.bottom index)) := by
  have hbottom := (normalizedCircuitFields_of_threshold_decode hdecode).2.1
  rw [normalizedCircuitBottomOutputs_eq_of_decode
    (bottomCodes :=
      List.ofFn fun index =>
        encodeSupportedNormalizedGate (circuit.bottom index))
    (by rw [hbottom]; simp)]
  simp [Function.comp_def]

/-- Every retained bottom summary is the accepted per-gate validator output of
a canonically decodable normalized gate. -/
theorem normalizedCircuitBottomOutputs_mem_of_headerTag
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request ≠ 0)
    {summary : ℕ}
    (hsummary : summary ∈ normalizedCircuitBottomOutputs inputLength request) :
    ∃ gate : SupportedNormalizedGate inputLength,
      summary =
        supportedGateRelationOutput inputLength
          (encodeSupportedNormalizedGate gate) := by
  have hbottom :
      normalizedCircuitBottomSummaryOutput inputLength
        (normalizedCircuitBottomCode request) ≠ 0 := by
    simpa only [normalizedCircuitBottomSummary] using
      normalizedCircuitBottomSummary_ne_zero_of_headerTag htag
  obtain ⟨codes, hdecode, hall⟩ :=
    (normalizedCircuitBottomSummaryOutput_ne_zero_iff inputLength
      (normalizedCircuitBottomCode request)).1 hbottom
  rw [normalizedCircuitBottomOutputs_eq_of_decode hdecode] at hsummary
  obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp hsummary
  obtain ⟨gate, hgate⟩ :=
    Option.isSome_iff_exists.mp (hall code hcode)
  exact ⟨gate, by rw [encodeSupportedNormalizedGate_of_decode hgate]⟩

end NearCubicWires.CanonicalNormalizedCircuitValidationProgram
