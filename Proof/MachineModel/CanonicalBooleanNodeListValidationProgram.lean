import Proof.MachineModel.CanonicalBalancedValidationProgram
import Proof.MachineModel.CanonicalBooleanCircuitPreparationProgram
import Proof.MachineModel.CanonicalBooleanNodeTopologyProgram
import Proof.Circuits.CanonicalForkCall
import Proof.MachineModel.CanonicalNativeEqualityProgram
import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.VerifiedLinker

/-!
# Canonical Boolean-node-list validation

This module closes the raw balanced-list boundary in one path.  The machine
normalizes an arbitrary raw tree while independently checking canonicality,
derives the node count and sole structural descriptor stream, and checks every
descriptor at its machine-generated topological index.  No count, traversal
limit, descriptor list, or validation callback is accepted from the caller.
-/

namespace NearCubicWires.CanonicalBooleanNodeListValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.VerifiedLinker

def booleanNodeListAtoms (raw : ℕ) : List ℕ :=
  (rawBalancedTraversalTree raw).atoms

def booleanNodeListDescriptors (raw : ℕ) : List ℕ :=
  booleanNodeOutputs (booleanNodeListAtoms raw)

def booleanNodeListNormalizedCode (raw : ℕ) : ℕ :=
  encodeBalancedList (booleanNodeListAtoms raw)

def booleanNodeListPreparationOutput (raw : ℕ) : ℕ :=
  booleanCircuitPreparationOutput (booleanNodeListAtoms raw)

/-! ## Canonicality and normalization from the same raw word -/

def booleanNodeListNormalizeProgram : NPOracleProgram :=
  forkCallProgram balancedCanonicalityProgram
    balancedRawCanonicalizeProgram

@[simp] theorem booleanNodeListNormalizeProgram_oracleFree :
    OracleFree booleanNodeListNormalizeProgram := by
  exact forkCallProgram_oracleFree
    balancedCanonicalityProgram balancedRawCanonicalizeProgram
    balancedCanonicalityProgram_oracleFree
    balancedRawCanonicalizeProgram_oracleFree

def booleanNodeListNormalizeBits
    (inputLength raw : ℕ) : ℕ :=
  forkCallBits inputLength raw
    (balancedCanonicalityBits inputLength raw)
    (balancedRawCanonicalizeBits inputLength
      (rawBalancedTraversalTree raw))
    (balancedCanonicalityOutput raw)
    (booleanNodeListNormalizedCode raw)

def booleanNodeListNormalizeFuel (raw : ℕ) : ℕ :=
  forkCallFuel balancedCanonicalityProgram
    balancedRawCanonicalizeProgram
    (balancedCanonicalityFuel raw)
    (balancedRawCanonicalizeFuel
      (rawBalancedTraversalTree raw))

set_option maxRecDepth 4000 in
-- The fork's linked budget unfolds both total raw traversals during elaboration.
theorem run_booleanNodeListNormalizeProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeListNormalizeProgram
        (booleanNodeListNormalizeBits inputLength raw)
        (booleanNodeListNormalizeFuel raw)
        (initialNPOracleState inputLength raw) =
      some
        (Nat.pair (balancedCanonicalityOutput raw)
          (booleanNodeListNormalizedCode raw)) := by
  exact run_forkCallProgram
    balancedCanonicalityProgram balancedRawCanonicalizeProgram
    inputLength raw
    (balancedCanonicalityBits inputLength raw)
    (balancedRawCanonicalizeBits inputLength
      (rawBalancedTraversalTree raw))
    (balancedCanonicalityFuel raw)
    (balancedRawCanonicalizeFuel
      (rawBalancedTraversalTree raw))
    (balancedCanonicalityOutput raw)
    (booleanNodeListNormalizedCode raw)
    (run_balancedCanonicalityProgram inputLength raw)
    (by
      simpa [booleanNodeListNormalizedCode,
        booleanNodeListAtoms] using
        run_balancedRawCanonicalizeProgram_total inputLength raw)

/-! ## Machine-derived count and descriptor tree -/

def booleanNodeListPrepareProgram : NPOracleProgram :=
  linkPrograms swapPairProgram <|
    preserveRightProgram booleanCircuitPreparationProgram

@[simp] theorem booleanNodeListPrepareProgram_oracleFree :
    OracleFree booleanNodeListPrepareProgram := by
  exact oracleFree_linkPrograms swapPairProgram_oracleFree <|
    preserveRightProgram_oracleFree booleanCircuitPreparationProgram
      booleanCircuitPreparationProgram_oracleFree

def booleanNodeListPrepareFuel
    (inputLength raw : ℕ) : ℕ :=
  linkFuel (preserveRightProgram booleanCircuitPreparationProgram) 4 <|
    preserveRightFuel
      (booleanCircuitPreparationFuel inputLength
        (booleanNodeListAtoms raw))

def booleanNodeListPrepareBits
    (inputLength raw : ℕ) : ℕ :=
  let flag := balancedCanonicalityOutput raw
  let normalized := booleanNodeListNormalizedCode raw
  let prepared := booleanNodeListPreparationOutput raw
  max 1 <| max (natBitLength inputLength) <|
    max (swapPairBits flag normalized) <|
      preserveRightBits
        (booleanCircuitPreparationBits inputLength
          (booleanNodeListAtoms raw))
        normalized flag prepared

theorem run_booleanNodeListPrepareProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeListPrepareProgram
        (booleanNodeListPrepareBits inputLength raw)
        (booleanNodeListPrepareFuel inputLength raw)
        (initialNPOracleState inputLength
          (Nat.pair (balancedCanonicalityOutput raw)
            (booleanNodeListNormalizedCode raw))) =
      some
        (Nat.pair (booleanNodeListPreparationOutput raw)
          (balancedCanonicalityOutput raw)) := by
  let flag := balancedCanonicalityOutput raw
  let normalized := booleanNodeListNormalizedCode raw
  let prepared := booleanNodeListPreparationOutput raw
  let maximumBits :=
    booleanNodeListPrepareBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, booleanNodeListPrepareBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, booleanNodeListPrepareBits]
  have hswap :
      swapPairBits flag normalized ≤ maximumBits := by
    simp [maximumBits, booleanNodeListPrepareBits,
      flag, normalized]
  have hprepare :
      preserveRightBits
          (booleanCircuitPreparationBits inputLength
            (booleanNodeListAtoms raw))
          normalized flag prepared ≤ maximumBits := by
    simp [maximumBits, booleanNodeListPrepareBits,
      flag, normalized, prepared]
  have hfirst :
      runNPOracleProgram swapPairProgram maximumBits 4
          (initialNPOracleState inputLength
            (Nat.pair flag normalized)) =
        some (Nat.pair normalized flag) := by
    exact run_bits_mono
      (run_swapPairProgram inputLength flag normalized) hswap
  have hsecond :
      runNPOracleProgram
          (preserveRightProgram booleanCircuitPreparationProgram)
          maximumBits
          (preserveRightFuel
            (booleanCircuitPreparationFuel inputLength
              (booleanNodeListAtoms raw)))
          (initialNPOracleState inputLength
            (Nat.pair normalized flag)) =
        some (Nat.pair prepared flag) := by
    apply run_bits_mono
    · exact run_preserveRightProgram
        booleanCircuitPreparationProgram inputLength
        (booleanCircuitPreparationBits inputLength
          (booleanNodeListAtoms raw))
        (booleanCircuitPreparationFuel inputLength
          (booleanNodeListAtoms raw))
        normalized flag prepared
        (by
          simpa [normalized, prepared,
            booleanNodeListNormalizedCode,
            booleanNodeListPreparationOutput,
            booleanNodeListAtoms] using
            run_booleanCircuitPreparationProgram inputLength
              (booleanNodeListAtoms raw))
    · exact hprepare
  simpa [booleanNodeListPrepareProgram,
    booleanNodeListPrepareFuel, flag, normalized, prepared] using
    run_linkPrograms hpositive hlength hfirst hsecond

/-! ## Fixed topology-call lowering -/

def booleanNodeListRangeInput (raw : ℕ) : ℕ :=
  let prepared := booleanNodeListPreparationOutput raw
  let count := (Nat.unpair prepared).1
  Nat.pair count prepared

def booleanNodeListRangeContext (raw : ℕ) : ℕ :=
  Nat.pair
    (Nat.unpair (booleanNodeListPreparationOutput raw)).1
    (balancedCanonicalityOutput raw)

def booleanNodeListRangeLoweringOutput (raw : ℕ) : ℕ :=
  Nat.pair (booleanNodeListRangeInput raw)
    (booleanNodeListRangeContext raw)

def booleanNodeListRangeLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .pair 4 2 5 4
  , .pair 4 3 6 5
  , .pair 5 6 0 6
  , .halt 0
  ]

@[simp] theorem booleanNodeListRangeLoweringProgram_oracleFree :
    OracleFree booleanNodeListRangeLoweringProgram := by
  rfl

def booleanNodeListRangeLoweringFuel : ℕ := 7

private def booleanNodeListRangeLoweringValues
    (inputLength raw : ℕ) : List ℕ :=
  let prepared := booleanNodeListPreparationOutput raw
  let flag := balancedCanonicalityOutput raw
  let count := (Nat.unpair prepared).1
  [ inputLength
  , Nat.pair prepared flag
  , prepared
  , flag
  , count
  , booleanNodeListRangeInput raw
  , booleanNodeListRangeContext raw
  , booleanNodeListRangeLoweringOutput raw
  ]

def booleanNodeListRangeLoweringBits
    (inputLength raw : ℕ) : ℕ :=
  (booleanNodeListRangeLoweringValues inputLength raw).map
    natBitLength |>.foldr max 1

private theorem value_le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 1 := by
  induction values with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (ih hmem).trans (Nat.le_max_right _ _)

private theorem booleanNodeListRangeLoweringValue_bits
    (inputLength raw value : ℕ)
    (hvalue :
      value ∈ booleanNodeListRangeLoweringValues inputLength raw) :
    natBitLength value ≤
      booleanNodeListRangeLoweringBits inputLength raw := by
  unfold booleanNodeListRangeLoweringBits
  apply value_le_foldr_max_of_mem
  exact List.mem_map.mpr ⟨value, hvalue, rfl⟩

theorem run_booleanNodeListRangeLoweringProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeListRangeLoweringProgram
        (booleanNodeListRangeLoweringBits inputLength raw)
        booleanNodeListRangeLoweringFuel
        (initialNPOracleState inputLength
          (Nat.pair (booleanNodeListPreparationOutput raw)
            (balancedCanonicalityOutput raw))) =
      some (booleanNodeListRangeLoweringOutput raw) := by
  let prepared := booleanNodeListPreparationOutput raw
  let flag := balancedCanonicalityOutput raw
  let count := (Nat.unpair prepared).1
  have hprepared :
      natBitLength prepared ≤
        booleanNodeListRangeLoweringBits inputLength raw := by
    apply booleanNodeListRangeLoweringValue_bits
    simp [booleanNodeListRangeLoweringValues, prepared]
  have hflag :
      natBitLength flag ≤
        booleanNodeListRangeLoweringBits inputLength raw := by
    apply booleanNodeListRangeLoweringValue_bits
    simp [booleanNodeListRangeLoweringValues, flag]
  have hcount :
      natBitLength count ≤
        booleanNodeListRangeLoweringBits inputLength raw := by
    apply booleanNodeListRangeLoweringValue_bits
    simp [booleanNodeListRangeLoweringValues, count, prepared]
  have hrangeInput :
      natBitLength (booleanNodeListRangeInput raw) ≤
        booleanNodeListRangeLoweringBits inputLength raw := by
    apply booleanNodeListRangeLoweringValue_bits
    simp [booleanNodeListRangeLoweringValues]
  have hcontext :
      natBitLength (booleanNodeListRangeContext raw) ≤
        booleanNodeListRangeLoweringBits inputLength raw := by
    apply booleanNodeListRangeLoweringValue_bits
    simp [booleanNodeListRangeLoweringValues]
  have houtput :
      natBitLength (booleanNodeListRangeLoweringOutput raw) ≤
        booleanNodeListRangeLoweringBits inputLength raw := by
    apply booleanNodeListRangeLoweringValue_bits
    simp [booleanNodeListRangeLoweringValues]
  have hrangeInput' :
      natBitLength (Nat.pair count prepared) ≤
        booleanNodeListRangeLoweringBits inputLength raw := by
    simpa [booleanNodeListRangeInput, count, prepared] using hrangeInput
  have hcontext' :
      natBitLength (Nat.pair count flag) ≤
        booleanNodeListRangeLoweringBits inputLength raw := by
    simpa [booleanNodeListRangeContext, count, prepared, flag] using
      hcontext
  have houtput' :
      natBitLength
          (Nat.pair (Nat.pair count prepared)
            (Nat.pair count flag)) ≤
        booleanNodeListRangeLoweringBits inputLength raw := by
    simpa [booleanNodeListRangeLoweringOutput,
      booleanNodeListRangeInput, booleanNodeListRangeContext,
      count, prepared, flag] using houtput
  simp [booleanNodeListRangeLoweringProgram,
    booleanNodeListRangeLoweringFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    prepared, flag, count, booleanNodeListRangeInput,
    booleanNodeListRangeContext, booleanNodeListRangeLoweringOutput,
    hprepared, hflag, hcount, hrangeInput', hcontext', houtput']

/-! ## Fixed all-node topology call -/

def booleanNodeListTopologyOutput
    (inputLength raw : ℕ) : ℕ :=
  booleanNodeTopologyRangeOutput inputLength
    (booleanNodeListDescriptors raw)

def booleanNodeListTopologyStageOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (booleanNodeListTopologyOutput inputLength raw)
    (booleanNodeListRangeContext raw)

def booleanNodeListTopologyProgram : NPOracleProgram :=
  preserveRightProgram booleanNodeTopologyRangeProgram

@[simp] theorem booleanNodeListTopologyProgram_oracleFree :
    OracleFree booleanNodeListTopologyProgram := by
  exact preserveRightProgram_oracleFree booleanNodeTopologyRangeProgram
    booleanNodeTopologyRangeProgram_oracleFree

def booleanNodeListTopologyFuel
    (inputLength raw : ℕ) : ℕ :=
  preserveRightFuel
    (booleanNodeTopologyRangeFuel inputLength
      (booleanNodeListDescriptors raw))

def booleanNodeListTopologyBits
    (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (booleanNodeTopologyRangeBits inputLength
      (booleanNodeListDescriptors raw))
    (booleanNodeListRangeInput raw)
    (booleanNodeListRangeContext raw)
    (booleanNodeListTopologyOutput inputLength raw)

private theorem booleanNodeListDescriptors_length (raw : ℕ) :
    (booleanNodeListDescriptors raw).length =
      (booleanNodeListAtoms raw).length := by
  simp [booleanNodeListDescriptors, booleanNodeOutputs]

private theorem booleanNodeListPreparationOutput_eq
    (raw : ℕ) :
    booleanNodeListPreparationOutput raw =
      Nat.pair (booleanNodeListDescriptors raw).length
        (encodeBalancedList (booleanNodeListDescriptors raw)) := by
  simp [booleanNodeListPreparationOutput,
    booleanCircuitPreparationOutput, booleanNodeListDescriptors,
    booleanNodeListAtoms, booleanNodeOutputs]

private theorem booleanNodeListRangeInput_eq
    (raw : ℕ) :
    booleanNodeListRangeInput raw =
      generatedBalancedRangeInput
        (booleanNodeListDescriptors raw).length
        (booleanNodeTopologyRangeContext
          (booleanNodeListDescriptors raw)) := by
  unfold booleanNodeListRangeInput
  rw [booleanNodeListPreparationOutput_eq]
  simp [generatedBalancedRangeInput,
    booleanNodeTopologyRangeContext]

set_option maxRecDepth 4000 in
-- The linked topology controller exposes its complete fixed range budget here.
theorem run_booleanNodeListTopologyProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeListTopologyProgram
        (booleanNodeListTopologyBits inputLength raw)
        (booleanNodeListTopologyFuel inputLength raw)
        (initialNPOracleState inputLength
          (booleanNodeListRangeLoweringOutput raw)) =
      some (booleanNodeListTopologyStageOutput inputLength raw) := by
  have hrun :=
    run_preserveRightProgram booleanNodeTopologyRangeProgram inputLength
      (booleanNodeTopologyRangeBits inputLength
        (booleanNodeListDescriptors raw))
      (booleanNodeTopologyRangeFuel inputLength
        (booleanNodeListDescriptors raw))
      (booleanNodeListRangeInput raw)
      (booleanNodeListRangeContext raw)
      (booleanNodeListTopologyOutput inputLength raw)
      (by
        rw [booleanNodeListRangeInput_eq]
        exact run_booleanNodeTopologyRangeProgram inputLength
          (booleanNodeListDescriptors raw))
  simpa [booleanNodeListTopologyProgram,
    booleanNodeListTopologyBits, booleanNodeListTopologyFuel,
    booleanNodeListRangeLoweringOutput,
    booleanNodeListTopologyStageOutput] using hrun

/-! ## Machine-derived topology-count equality request -/

def booleanNodeListTopologyCount
    (inputLength raw : ℕ) : ℕ :=
  (Nat.unpair (booleanNodeListTopologyOutput inputLength raw)).1

def booleanNodeListNodeCount (raw : ℕ) : ℕ :=
  (Nat.unpair (booleanNodeListRangeContext raw)).1

def booleanNodeListTopologyEqualityInput
    (inputLength raw : ℕ) : ℕ :=
  nativeNatEqInput
    (booleanNodeListTopologyCount inputLength raw)
    (booleanNodeListNodeCount raw)

def booleanNodeListTopologyEqualityLoweringOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (booleanNodeListTopologyEqualityInput inputLength raw)
    (booleanNodeListRangeContext raw)

def booleanNodeListTopologyEqualityLoweringProgram :
    NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairLeft 3 5 4
  , .pair 4 5 6 5
  , .pair 6 3 0 6
  , .halt 0
  ]

@[simp] theorem
    booleanNodeListTopologyEqualityLoweringProgram_oracleFree :
    OracleFree booleanNodeListTopologyEqualityLoweringProgram := by
  rfl

def booleanNodeListTopologyEqualityLoweringFuel : ℕ := 7

private def booleanNodeListTopologyEqualityLoweringValues
    (inputLength raw : ℕ) : List ℕ :=
  let topology := booleanNodeListTopologyOutput inputLength raw
  let context := booleanNodeListRangeContext raw
  let validCount := booleanNodeListTopologyCount inputLength raw
  let nodeCount := booleanNodeListNodeCount raw
  [ inputLength
  , Nat.pair topology context
  , topology
  , context
  , validCount
  , nodeCount
  , booleanNodeListTopologyEqualityInput inputLength raw
  , booleanNodeListTopologyEqualityLoweringOutput inputLength raw
  ]

def booleanNodeListTopologyEqualityLoweringBits
    (inputLength raw : ℕ) : ℕ :=
  (booleanNodeListTopologyEqualityLoweringValues inputLength raw).map
    natBitLength |>.foldr max 1

private theorem booleanNodeListTopologyEqualityLoweringValue_bits
    (inputLength raw value : ℕ)
    (hvalue :
      value ∈
        booleanNodeListTopologyEqualityLoweringValues inputLength raw) :
    natBitLength value ≤
      booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
  unfold booleanNodeListTopologyEqualityLoweringBits
  apply value_le_foldr_max_of_mem
  exact List.mem_map.mpr ⟨value, hvalue, rfl⟩

theorem run_booleanNodeListTopologyEqualityLoweringProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram
        booleanNodeListTopologyEqualityLoweringProgram
        (booleanNodeListTopologyEqualityLoweringBits inputLength raw)
        booleanNodeListTopologyEqualityLoweringFuel
        (initialNPOracleState inputLength
          (booleanNodeListTopologyStageOutput inputLength raw)) =
      some
        (booleanNodeListTopologyEqualityLoweringOutput
          inputLength raw) := by
  let topology := booleanNodeListTopologyOutput inputLength raw
  let context := booleanNodeListRangeContext raw
  let validCount := booleanNodeListTopologyCount inputLength raw
  let nodeCount := booleanNodeListNodeCount raw
  have htopology :
      natBitLength topology ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    apply booleanNodeListTopologyEqualityLoweringValue_bits
    simp [booleanNodeListTopologyEqualityLoweringValues, topology]
  have hcontext :
      natBitLength context ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    apply booleanNodeListTopologyEqualityLoweringValue_bits
    simp [booleanNodeListTopologyEqualityLoweringValues, context]
  have hvalidCount :
      natBitLength validCount ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    apply booleanNodeListTopologyEqualityLoweringValue_bits
    simp [booleanNodeListTopologyEqualityLoweringValues,
      validCount]
  have hnodeCount :
      natBitLength nodeCount ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    apply booleanNodeListTopologyEqualityLoweringValue_bits
    simp [booleanNodeListTopologyEqualityLoweringValues, nodeCount]
  have hequalityInput :
      natBitLength (Nat.pair validCount nodeCount) ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    apply booleanNodeListTopologyEqualityLoweringValue_bits
    simp [booleanNodeListTopologyEqualityLoweringValues,
      booleanNodeListTopologyEqualityInput, nativeNatEqInput,
      validCount, nodeCount]
  have houtput :
      natBitLength
          (Nat.pair (Nat.pair validCount nodeCount) context) ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    apply booleanNodeListTopologyEqualityLoweringValue_bits
    simp [booleanNodeListTopologyEqualityLoweringValues,
      booleanNodeListTopologyEqualityLoweringOutput,
      booleanNodeListTopologyEqualityInput, nativeNatEqInput,
      validCount, nodeCount, context]
  have htopology' :
      natBitLength (booleanNodeListTopologyOutput inputLength raw) ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    simpa [topology] using htopology
  have hcontext' :
      natBitLength (booleanNodeListRangeContext raw) ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    simpa [context] using hcontext
  have hvalidCount' :
      natBitLength
          (Nat.unpair
            (booleanNodeListTopologyOutput inputLength raw)).1 ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    simpa [validCount, booleanNodeListTopologyCount] using hvalidCount
  have hnodeCount' :
      natBitLength
          (Nat.unpair (booleanNodeListRangeContext raw)).1 ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    simpa [nodeCount, booleanNodeListNodeCount] using hnodeCount
  have hequalityInput' :
      natBitLength
          (Nat.pair
            (Nat.unpair
              (booleanNodeListTopologyOutput inputLength raw)).1
            (Nat.unpair (booleanNodeListRangeContext raw)).1) ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    simpa [validCount, nodeCount, booleanNodeListTopologyCount,
      booleanNodeListNodeCount] using hequalityInput
  have houtput' :
      natBitLength
          (Nat.pair
            (Nat.pair
              (Nat.unpair
                (booleanNodeListTopologyOutput inputLength raw)).1
              (Nat.unpair (booleanNodeListRangeContext raw)).1)
            (booleanNodeListRangeContext raw)) ≤
        booleanNodeListTopologyEqualityLoweringBits inputLength raw := by
    simpa [validCount, nodeCount, topology, context,
      booleanNodeListTopologyCount, booleanNodeListNodeCount] using
      houtput
  simp [booleanNodeListTopologyEqualityLoweringProgram,
    booleanNodeListTopologyEqualityLoweringFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    booleanNodeListTopologyStageOutput,
    booleanNodeListTopologyCount,
    booleanNodeListNodeCount, booleanNodeListTopologyEqualityInput,
    nativeNatEqInput,
    booleanNodeListTopologyEqualityLoweringOutput,
    htopology', hcontext', hvalidCount', hnodeCount',
    hequalityInput', houtput']

/-! ## Fixed equality call and final fail-closed gate -/

def booleanNodeListTopologyEqualityOutput
    (inputLength raw : ℕ) : ℕ :=
  nativeNatEqOutput
    (booleanNodeListTopologyCount inputLength raw)
    (booleanNodeListNodeCount raw)

def booleanNodeListTopologyEqualityStageOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair
    (booleanNodeListTopologyEqualityOutput inputLength raw)
    (booleanNodeListRangeContext raw)

def booleanNodeListTopologyEqualityProgram : NPOracleProgram :=
  preserveRightProgram nativeNatEqProgram

@[simp] theorem booleanNodeListTopologyEqualityProgram_oracleFree :
    OracleFree booleanNodeListTopologyEqualityProgram := by
  exact preserveRightProgram_oracleFree nativeNatEqProgram
    nativeNatEqProgram_oracleFree

def booleanNodeListTopologyEqualityFuel
    (inputLength raw : ℕ) : ℕ :=
  preserveRightFuel <|
    nativeNatEqFuel
      (booleanNodeListTopologyCount inputLength raw)
      (booleanNodeListNodeCount raw)

def booleanNodeListTopologyEqualityBits
    (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (nativeNatEqBits inputLength
      (booleanNodeListTopologyCount inputLength raw)
      (booleanNodeListNodeCount raw))
    (booleanNodeListTopologyEqualityInput inputLength raw)
    (booleanNodeListRangeContext raw)
    (booleanNodeListTopologyEqualityOutput inputLength raw)

theorem run_booleanNodeListTopologyEqualityProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeListTopologyEqualityProgram
        (booleanNodeListTopologyEqualityBits inputLength raw)
        (booleanNodeListTopologyEqualityFuel inputLength raw)
        (initialNPOracleState inputLength
          (booleanNodeListTopologyEqualityLoweringOutput
            inputLength raw)) =
      some
        (booleanNodeListTopologyEqualityStageOutput
          inputLength raw) := by
  exact run_preserveRightProgram nativeNatEqProgram inputLength
    (nativeNatEqBits inputLength
      (booleanNodeListTopologyCount inputLength raw)
      (booleanNodeListNodeCount raw))
    (nativeNatEqFuel
      (booleanNodeListTopologyCount inputLength raw)
      (booleanNodeListNodeCount raw))
    (booleanNodeListTopologyEqualityInput inputLength raw)
    (booleanNodeListRangeContext raw)
    (booleanNodeListTopologyEqualityOutput inputLength raw)
    (by
      simpa [booleanNodeListTopologyEqualityInput,
        booleanNodeListTopologyEqualityOutput] using
        run_nativeNatEqProgram inputLength
          (booleanNodeListTopologyCount inputLength raw)
          (booleanNodeListNodeCount raw))

def booleanNodeListValidationOutput
    (inputLength raw : ℕ) : ℕ :=
  if booleanNodeListTopologyEqualityOutput inputLength raw = 0 then
    0
  else if balancedCanonicalityOutput raw = 0 then
    0
  else
    Nat.pair 1 (booleanNodeListNodeCount raw)

def booleanNodeListValidationGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 8 2
  , .unpairRight 0 3 3
  , .unpairRight 3 4 4
  , .branchZero 4 8 5
  , .unpairLeft 3 5 6
  , .set 6 1 7
  , .pair 6 5 0 9
  , .set 0 0 9
  , .halt 0
  ]

@[simp] theorem booleanNodeListValidationGateProgram_oracleFree :
    OracleFree booleanNodeListValidationGateProgram := by
  rfl

def booleanNodeListValidationGateFuel : ℕ := 10

private def booleanNodeListValidationGateValues
    (inputLength raw : ℕ) : List ℕ :=
  let equality :=
    booleanNodeListTopologyEqualityOutput inputLength raw
  let count := booleanNodeListNodeCount raw
  let canonical := balancedCanonicalityOutput raw
  let context := Nat.pair count canonical
  [ inputLength
  , Nat.pair equality context
  , equality
  , context
  , canonical
  , count
  , 1
  , Nat.pair 1 count
  , 0
  ]

def booleanNodeListValidationGateBits
    (inputLength raw : ℕ) : ℕ :=
  (booleanNodeListValidationGateValues inputLength raw).map
    natBitLength |>.foldr max 1

private theorem booleanNodeListValidationGateValue_bits
    (inputLength raw value : ℕ)
    (hvalue :
      value ∈ booleanNodeListValidationGateValues inputLength raw) :
    natBitLength value ≤
      booleanNodeListValidationGateBits inputLength raw := by
  unfold booleanNodeListValidationGateBits
  apply value_le_foldr_max_of_mem
  exact List.mem_map.mpr ⟨value, hvalue, rfl⟩

set_option maxHeartbeats 800000 in
-- Symbolic reduction covers both fail-closed branches of this fixed gate.
theorem run_booleanNodeListValidationGateProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeListValidationGateProgram
        (booleanNodeListValidationGateBits inputLength raw)
        booleanNodeListValidationGateFuel
        (initialNPOracleState inputLength
          (booleanNodeListTopologyEqualityStageOutput
            inputLength raw)) =
      some (booleanNodeListValidationOutput inputLength raw) := by
  let equality :=
    booleanNodeListTopologyEqualityOutput inputLength raw
  let count := booleanNodeListNodeCount raw
  let canonical := balancedCanonicalityOutput raw
  let context := Nat.pair count canonical
  have hequality :
      natBitLength equality ≤
        booleanNodeListValidationGateBits inputLength raw := by
    apply booleanNodeListValidationGateValue_bits
    simp [booleanNodeListValidationGateValues, equality]
  have hcontext :
      natBitLength context ≤
        booleanNodeListValidationGateBits inputLength raw := by
    apply booleanNodeListValidationGateValue_bits
    simp [booleanNodeListValidationGateValues, context,
      count, canonical]
  have hcanonical :
      natBitLength canonical ≤
        booleanNodeListValidationGateBits inputLength raw := by
    apply booleanNodeListValidationGateValue_bits
    simp [booleanNodeListValidationGateValues, canonical]
  have hcount :
      natBitLength count ≤
        booleanNodeListValidationGateBits inputLength raw := by
    apply booleanNodeListValidationGateValue_bits
    simp [booleanNodeListValidationGateValues, count]
  have hone :
      natBitLength 1 ≤
        booleanNodeListValidationGateBits inputLength raw := by
    apply booleanNodeListValidationGateValue_bits
    simp [booleanNodeListValidationGateValues]
  have haccepted :
      natBitLength (Nat.pair 1 count) ≤
        booleanNodeListValidationGateBits inputLength raw := by
    apply booleanNodeListValidationGateValue_bits
    simp [booleanNodeListValidationGateValues, count]
  have hzero :
      natBitLength 0 ≤
        booleanNodeListValidationGateBits inputLength raw := by
    apply booleanNodeListValidationGateValue_bits
    simp [booleanNodeListValidationGateValues]
  have hrangeContext :
      booleanNodeListRangeContext raw = context := by
    simp [context, count, canonical, booleanNodeListNodeCount,
      booleanNodeListRangeContext]
  rw [show
    booleanNodeListTopologyEqualityStageOutput inputLength raw =
        Nat.pair equality context by
      simp [booleanNodeListTopologyEqualityStageOutput,
        equality, hrangeContext]]
  by_cases hequalityZero : equality = 0
  · rw [show booleanNodeListValidationOutput inputLength raw = 0 by
      simp [booleanNodeListValidationOutput, equality,
        hequalityZero]]
    rw [show booleanNodeListValidationGateFuel = 9 + 1 by rfl]
    rw [run_unpairLeft_instruction
      (program := booleanNodeListValidationGateProgram)
      (maximumBits :=
        booleanNodeListValidationGateBits inputLength raw)
      (fuel := 9) (pc := 0) (source := 0) (destination := 2)
      (next := 1) (value := equality)
      (by rfl) (by rfl)
      (by simp [initialNPOracleState])
      hequality]
    rw [show (9 : ℕ) = 8 + 1 by omega]
    rw [run_branchZero_instruction
      (program := booleanNodeListValidationGateProgram)
      (maximumBits :=
        booleanNodeListValidationGateBits inputLength raw)
      (fuel := 8) (pc := 1) (register := 2)
      (zeroTarget := 8) (nonzeroTarget := 2)
      (by rfl) (by rfl)]
    rw [if_pos (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, hequalityZero])]
    rw [show (8 : ℕ) = 7 + 1 by omega]
    rw [run_set_instruction
      (program := booleanNodeListValidationGateProgram)
      (maximumBits :=
        booleanNodeListValidationGateBits inputLength raw)
      (fuel := 7) (pc := 8) (register := 0) (value := 0)
      (next := 9) (by rfl) (by rfl) hzero]
    exact run_halt_instruction
      (program := booleanNodeListValidationGateProgram)
      (maximumBits :=
        booleanNodeListValidationGateBits inputLength raw)
      (fuel := 6) (pc := 9) (outputRegister := 0) (value := 0)
      (by rfl) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump]) hzero
  · by_cases hcanonicalZero : canonical = 0
    · rw [show booleanNodeListValidationOutput inputLength raw = 0 by
        simp [booleanNodeListValidationOutput, equality,
          canonical, hequalityZero, hcanonicalZero]]
      rw [show booleanNodeListValidationGateFuel = 9 + 1 by rfl]
      rw [run_unpairLeft_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 9) (pc := 0) (source := 0) (destination := 2)
        (next := 1) (value := equality)
        (by rfl) (by rfl)
        (by simp [initialNPOracleState])
        hequality]
      rw [show (9 : ℕ) = 8 + 1 by omega]
      rw [run_branchZero_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 8) (pc := 1) (register := 2)
        (zeroTarget := 8) (nonzeroTarget := 2)
        (by rfl) (by rfl)]
      rw [if_neg (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, hequalityZero])]
      rw [show (8 : ℕ) = 7 + 1 by omega]
      rw [run_unpairRight_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 7) (pc := 2) (source := 0) (destination := 3)
        (next := 3) (value := context)
        (by rfl) (by rfl)
        (by simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump])
        hcontext]
      rw [show (7 : ℕ) = 6 + 1 by omega]
      rw [run_unpairRight_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 6) (pc := 3) (source := 3) (destination := 4)
        (next := 4) (value := canonical)
        (by rfl) (by rfl)
        (by simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, context])
        hcanonical]
      rw [show (6 : ℕ) = 5 + 1 by omega]
      rw [run_branchZero_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 5) (pc := 4) (register := 4)
        (zeroTarget := 8) (nonzeroTarget := 5)
        (by rfl) (by rfl)]
      rw [if_pos (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, hcanonicalZero])]
      rw [show (5 : ℕ) = 4 + 1 by omega]
      rw [run_set_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 4) (pc := 8) (register := 0) (value := 0)
        (next := 9) (by rfl) (by rfl) hzero]
      exact run_halt_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 3) (pc := 9) (outputRegister := 0) (value := 0)
        (by rfl) (by rfl)
        (by simp [NPOracleState.write, NPOracleState.jump]) hzero
    · rw [show booleanNodeListValidationOutput inputLength raw =
          Nat.pair 1 count by
        simp [booleanNodeListValidationOutput, equality, count,
          canonical, hequalityZero, hcanonicalZero]]
      rw [show booleanNodeListValidationGateFuel = 9 + 1 by rfl]
      rw [run_unpairLeft_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 9) (pc := 0) (source := 0) (destination := 2)
        (next := 1) (value := equality)
        (by rfl) (by rfl)
        (by simp [initialNPOracleState])
        hequality]
      rw [show (9 : ℕ) = 8 + 1 by omega]
      rw [run_branchZero_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 8) (pc := 1) (register := 2)
        (zeroTarget := 8) (nonzeroTarget := 2)
        (by rfl) (by rfl)]
      rw [if_neg (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, hequalityZero])]
      rw [show (8 : ℕ) = 7 + 1 by omega]
      rw [run_unpairRight_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 7) (pc := 2) (source := 0) (destination := 3)
        (next := 3) (value := context)
        (by rfl) (by rfl)
        (by simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump])
        hcontext]
      rw [show (7 : ℕ) = 6 + 1 by omega]
      rw [run_unpairRight_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 6) (pc := 3) (source := 3) (destination := 4)
        (next := 4) (value := canonical)
        (by rfl) (by rfl)
        (by simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, context])
        hcanonical]
      rw [show (6 : ℕ) = 5 + 1 by omega]
      rw [run_branchZero_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 5) (pc := 4) (register := 4)
        (zeroTarget := 8) (nonzeroTarget := 5)
        (by rfl) (by rfl)]
      rw [if_neg (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, hcanonicalZero])]
      rw [show (5 : ℕ) = 4 + 1 by omega]
      rw [run_unpairLeft_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 4) (pc := 5) (source := 3) (destination := 5)
        (next := 6) (value := count)
        (by rfl) (by rfl)
        (by simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, context])
        hcount]
      rw [show (4 : ℕ) = 3 + 1 by omega]
      rw [run_set_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 3) (pc := 6) (register := 6) (value := 1)
        (next := 7) (by rfl) (by rfl) hone]
      rw [show (3 : ℕ) = 2 + 1 by omega]
      rw [run_pair_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 2) (pc := 7) (left := 6) (right := 5)
        (destination := 0) (next := 9) (value := Nat.pair 1 count)
        (by rfl) (by rfl)
        (by simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump])
        haccepted]
      exact run_halt_instruction
        (program := booleanNodeListValidationGateProgram)
        (maximumBits :=
          booleanNodeListValidationGateBits inputLength raw)
        (fuel := 1) (pc := 9) (outputRegister := 0)
        (value := Nat.pair 1 count)
        (by rfl) (by rfl)
        (by simp [NPOracleState.write, NPOracleState.jump])
        haccepted

/-! ## Unique total node-list validator -/

def booleanNodeListValidationProgram : NPOracleProgram :=
  linkPrograms booleanNodeListNormalizeProgram <|
    linkPrograms booleanNodeListPrepareProgram <|
      linkPrograms booleanNodeListRangeLoweringProgram <|
        linkPrograms booleanNodeListTopologyProgram <|
          linkPrograms booleanNodeListTopologyEqualityLoweringProgram <|
            linkPrograms booleanNodeListTopologyEqualityProgram
              booleanNodeListValidationGateProgram

@[simp] theorem booleanNodeListValidationProgram_oracleFree :
    OracleFree booleanNodeListValidationProgram := by
  exact oracleFree_linkPrograms booleanNodeListNormalizeProgram_oracleFree <|
    oracleFree_linkPrograms booleanNodeListPrepareProgram_oracleFree <|
      oracleFree_linkPrograms
        booleanNodeListRangeLoweringProgram_oracleFree <|
        oracleFree_linkPrograms booleanNodeListTopologyProgram_oracleFree <|
          oracleFree_linkPrograms
            booleanNodeListTopologyEqualityLoweringProgram_oracleFree <|
            oracleFree_linkPrograms
              booleanNodeListTopologyEqualityProgram_oracleFree
              booleanNodeListValidationGateProgram_oracleFree

def booleanNodeListValidationFuel
    (inputLength raw : ℕ) : ℕ :=
  linkFuel
      (linkPrograms booleanNodeListPrepareProgram <|
        linkPrograms booleanNodeListRangeLoweringProgram <|
          linkPrograms booleanNodeListTopologyProgram <|
            linkPrograms
              booleanNodeListTopologyEqualityLoweringProgram <|
              linkPrograms booleanNodeListTopologyEqualityProgram
                booleanNodeListValidationGateProgram)
      (booleanNodeListNormalizeFuel raw) <|
    linkFuel
        (linkPrograms booleanNodeListRangeLoweringProgram <|
          linkPrograms booleanNodeListTopologyProgram <|
            linkPrograms
              booleanNodeListTopologyEqualityLoweringProgram <|
              linkPrograms booleanNodeListTopologyEqualityProgram
                booleanNodeListValidationGateProgram)
        (booleanNodeListPrepareFuel inputLength raw) <|
      linkFuel
          (linkPrograms booleanNodeListTopologyProgram <|
            linkPrograms
              booleanNodeListTopologyEqualityLoweringProgram <|
              linkPrograms booleanNodeListTopologyEqualityProgram
                booleanNodeListValidationGateProgram)
          booleanNodeListRangeLoweringFuel <|
        linkFuel
            (linkPrograms
              booleanNodeListTopologyEqualityLoweringProgram <|
              linkPrograms booleanNodeListTopologyEqualityProgram
                booleanNodeListValidationGateProgram)
            (booleanNodeListTopologyFuel inputLength raw) <|
          linkFuel
              (linkPrograms booleanNodeListTopologyEqualityProgram
                booleanNodeListValidationGateProgram)
              booleanNodeListTopologyEqualityLoweringFuel <|
            linkFuel booleanNodeListValidationGateProgram
              (booleanNodeListTopologyEqualityFuel inputLength raw)
              booleanNodeListValidationGateFuel

def booleanNodeListValidationBits
    (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (booleanNodeListNormalizeBits inputLength raw) <|
      max (booleanNodeListPrepareBits inputLength raw) <|
        max (booleanNodeListRangeLoweringBits inputLength raw) <|
          max (booleanNodeListTopologyBits inputLength raw) <|
            max
              (booleanNodeListTopologyEqualityLoweringBits
                inputLength raw) <|
              max (booleanNodeListTopologyEqualityBits inputLength raw)
                (booleanNodeListValidationGateBits inputLength raw)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- The proof links seven fixed exact runners; each individual stage remains bounded.
theorem run_booleanNodeListValidationProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanNodeListValidationProgram
        (booleanNodeListValidationBits inputLength raw)
        (booleanNodeListValidationFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (booleanNodeListValidationOutput inputLength raw) := by
  let maximumBits :=
    booleanNodeListValidationBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationBits]
  have hnormalizeBits :
      booleanNodeListNormalizeBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationBits]
  have hprepareBits :
      booleanNodeListPrepareBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationBits]
  have hloweringBits :
      booleanNodeListRangeLoweringBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationBits]
  have htopologyBits :
      booleanNodeListTopologyBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanNodeListValidationBits]
  have hequalityLoweringBits :
      booleanNodeListTopologyEqualityLoweringBits inputLength raw ≤
        maximumBits := by
    simp [maximumBits, booleanNodeListValidationBits]
  have hequalityBits :
      booleanNodeListTopologyEqualityBits inputLength raw ≤
        maximumBits := by
    simp [maximumBits, booleanNodeListValidationBits]
  have hgateBits :
      booleanNodeListValidationGateBits inputLength raw ≤
        maximumBits := by
    simp [maximumBits, booleanNodeListValidationBits]
  have hnormalize :=
    run_bits_mono
      (run_booleanNodeListNormalizeProgram inputLength raw)
      hnormalizeBits
  have hprepare :=
    run_bits_mono
      (run_booleanNodeListPrepareProgram inputLength raw)
      hprepareBits
  have hlowering :=
    run_bits_mono
      (run_booleanNodeListRangeLoweringProgram inputLength raw)
      hloweringBits
  have htopology :=
    run_bits_mono
      (run_booleanNodeListTopologyProgram inputLength raw)
      htopologyBits
  have hequalityLowering :=
    run_bits_mono
      (run_booleanNodeListTopologyEqualityLoweringProgram
        inputLength raw)
      hequalityLoweringBits
  have hequality :=
    run_bits_mono
      (run_booleanNodeListTopologyEqualityProgram inputLength raw)
      hequalityBits
  have hgate :=
    run_bits_mono
      (run_booleanNodeListValidationGateProgram inputLength raw)
      hgateBits
  have hequalityTail :=
    run_linkPrograms hpositive hlength hequality hgate
  have hequalityLoweringTail :=
    run_linkPrograms hpositive hlength hequalityLowering
      hequalityTail
  have htopologyTail :=
    run_linkPrograms hpositive hlength htopology
      hequalityLoweringTail
  have hloweringTail :=
    run_linkPrograms hpositive hlength hlowering htopologyTail
  have hprepareTail :=
    run_linkPrograms hpositive hlength hprepare hloweringTail
  have hrun :=
    run_linkPrograms hpositive hlength hnormalize hprepareTail
  simpa [booleanNodeListValidationProgram,
    booleanNodeListValidationFuel] using hrun

/-! ## Typed-code refinement -/

theorem booleanNodeTopologyOutput_ne_zero_iff_decode
    (inputLength raw index : ℕ) :
    booleanNodeTopologyOutput inputLength
        (booleanNodeStructuralOutput raw) index ≠ 0 ↔
      ∃ node : BooleanNode inputLength,
        decodeBooleanNode inputLength raw = some node ∧
          node.WellFormedAt index := by
  constructor
  · intro htopology
    have hstructural :
        booleanNodeStructuralOutput raw ≠ 0 := by
      intro hzero
      simp [booleanNodeTopologyOutput,
        booleanTopologyComparisonRequests, booleanTopologyAndOutput,
        topologyFalseRequest, nativeLtRequestOutput,
        nativeLtRequest, nativeInputRequest, hzero] at htopology
    rcases
        (booleanNodeStructuralOutput_ne_zero_iff raw).1 hstructural with
      (hfalse | htrue) | ⟨input, hinput⟩ |
        ⟨child, hchild⟩ | ⟨left, right, hand⟩ |
        ⟨left, right, hor⟩
    · subst raw
      let node : BooleanNode inputLength := .const false
      exact ⟨node, by
        change decodeBooleanNode inputLength (encodeBooleanNode node) =
          some node
        exact decodeBooleanNode_encode node,
        by simp [node, BooleanNode.WellFormedAt]⟩
    · subst raw
      let node : BooleanNode inputLength := .const true
      exact ⟨node, by
        change decodeBooleanNode inputLength (encodeBooleanNode node) =
          some node
        exact decodeBooleanNode_encode node,
        by simp [node, BooleanNode.WellFormedAt]⟩
    · subst raw
      let witnessNode : BooleanNode (input + 1) :=
        .input ⟨input, by omega⟩
      have hdescriptor :
          booleanNodeStructuralOutput
              (encodeTaggedList [encodeNat 1, encodeNat input]) =
            Nat.pair 1 (Nat.pair 1 input) := by
        change
          booleanNodeStructuralOutput (encodeBooleanNode witnessNode) =
            Nat.pair 1 (Nat.pair 1 input)
        exact booleanNodeStructuralOutput_encodeBooleanNode witnessNode
      have hbound : input < inputLength := by
        simpa [hdescriptor, booleanNodeTopologyOutput,
          booleanTopologyComparisonRequests, booleanTopologyAndOutput,
          topologyTrueRequest, nativeLtRequestOutput,
          nativeLtRequest, nativeInputRequest] using htopology
      let node : BooleanNode inputLength := .input ⟨input, hbound⟩
      exact ⟨node, by
        change decodeBooleanNode inputLength (encodeBooleanNode node) =
          some node
        exact decodeBooleanNode_encode node,
        by simp [node, BooleanNode.WellFormedAt]⟩
    · subst raw
      let witnessNode : BooleanNode 0 := .not child
      have hdescriptor :
          booleanNodeStructuralOutput
              (encodeTaggedList [encodeNat 2, encodeNat child]) =
            Nat.pair 1 (Nat.pair 2 child) := by
        change
          booleanNodeStructuralOutput (encodeBooleanNode witnessNode) =
            Nat.pair 1 (Nat.pair 2 child)
        exact booleanNodeStructuralOutput_encodeBooleanNode witnessNode
      have hbound : child < index := by
        simpa [hdescriptor, booleanNodeTopologyOutput,
          booleanTopologyComparisonRequests, booleanTopologyAndOutput,
          topologyTrueRequest, nativeLtRequestOutput,
          nativeLtRequest, nativeInputRequest] using htopology
      let node : BooleanNode inputLength := .not child
      exact ⟨node, by
        change decodeBooleanNode inputLength (encodeBooleanNode node) =
          some node
        exact decodeBooleanNode_encode node,
        by simpa [node, BooleanNode.WellFormedAt] using hbound⟩
    · subst raw
      let witnessNode : BooleanNode 0 := .and left right
      have hdescriptor :
          booleanNodeStructuralOutput
              (encodeTaggedList
                [encodeNat 3, encodeNat left, encodeNat right]) =
            Nat.pair 1 (Nat.pair 3 (Nat.pair left right)) := by
        change
          booleanNodeStructuralOutput (encodeBooleanNode witnessNode) =
            Nat.pair 1 (Nat.pair 3 (Nat.pair left right))
        exact booleanNodeStructuralOutput_encodeBooleanNode witnessNode
      have hbound : left < index ∧ right < index := by
        simpa [hdescriptor, booleanNodeTopologyOutput,
          booleanTopologyComparisonRequests, booleanTopologyAndOutput,
          nativeLtRequestOutput, nativeLtRequest,
          nativeInputRequest] using htopology
      let node : BooleanNode inputLength := .and left right
      exact ⟨node, by
        change decodeBooleanNode inputLength (encodeBooleanNode node) =
          some node
        exact decodeBooleanNode_encode node,
        by simpa [node, BooleanNode.WellFormedAt] using hbound⟩
    · subst raw
      let witnessNode : BooleanNode 0 := .or left right
      have hdescriptor :
          booleanNodeStructuralOutput
              (encodeTaggedList
                [encodeNat 4, encodeNat left, encodeNat right]) =
            Nat.pair 1 (Nat.pair 4 (Nat.pair left right)) := by
        change
          booleanNodeStructuralOutput (encodeBooleanNode witnessNode) =
            Nat.pair 1 (Nat.pair 4 (Nat.pair left right))
        exact booleanNodeStructuralOutput_encodeBooleanNode witnessNode
      have hbound : left < index ∧ right < index := by
        simpa [hdescriptor, booleanNodeTopologyOutput,
          booleanTopologyComparisonRequests, booleanTopologyAndOutput,
          nativeLtRequestOutput, nativeLtRequest,
          nativeInputRequest] using htopology
      let node : BooleanNode inputLength := .or left right
      exact ⟨node, by
        change decodeBooleanNode inputLength (encodeBooleanNode node) =
          some node
        exact decodeBooleanNode_encode node,
        by simpa [node, BooleanNode.WellFormedAt] using hbound⟩
  · rintro ⟨node, hdecode, hwellFormed⟩
    have hcode : encodeBooleanNode node = raw :=
      encodeBooleanNode_of_decode hdecode
    rw [← hcode]
    rw [booleanNodeTopologyOutput_encodeBooleanNode]
    simp [hwellFormed]

@[simp] theorem booleanNodeListAtoms_encodeBalancedList
    (values : List ℕ) :
    booleanNodeListAtoms (encodeBalancedList values) = values := by
  unfold booleanNodeListAtoms RawBalancedTraversalTree.atoms
  rw [← balancedTraversalTree_code values]
  rw [rawBalancedTraversalTree_normalized_code]
  exact balancedTraversalTree_atoms values

private theorem nonzeroSupportCount_le_length
    (values : List Bool) :
    nonzeroSupportCount values ≤ values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      cases value <;>
        simp [nonzeroSupportCount] <;> omega

private theorem all_true_of_nonzeroSupportCount_eq_length
    {values : List Bool}
    (hcount : nonzeroSupportCount values = values.length) :
    ∀ value ∈ values, value = true := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      cases head with
      | false =>
          simp only [nonzeroSupportCount, Bool.false_eq_true,
            if_false, Nat.zero_add, List.length_cons] at hcount
          have hle := nonzeroSupportCount_le_length tail
          omega
      | true =>
          simp only [nonzeroSupportCount, if_true,
            List.length_cons] at hcount
          have htailCount :
              nonzeroSupportCount tail = tail.length := by
            omega
          intro value hvalue
          rcases List.mem_cons.mp hvalue with rfl | htail
          · rfl
          · exact ih htailCount value htail

set_option maxHeartbeats 800000 in
-- Reconstructing the dependent node list expands the fixed range semantics.
/-- Acceptance of the total list validator reconstructs one and only one
public node at every machine-generated index.  This is the soundness bridge
used by the outer circuit decoder; no proof-only alternate parser is involved.
-/
theorem booleanNodeListValidationOutput_sound
    (inputLength raw : ℕ)
    (haccept :
      booleanNodeListValidationOutput inputLength raw ≠ 0) :
    ∃ nodes : List (BooleanNode inputLength),
      raw =
          encodeBalancedList (nodes.map encodeBooleanNode) ∧
        ∀ index : Fin nodes.length,
          (nodes.get index).WellFormedAt index.val := by
  have hequality :
      booleanNodeListTopologyEqualityOutput inputLength raw ≠ 0 := by
    intro hzero
    simp [booleanNodeListValidationOutput, hzero] at haccept
  have hcanonical :
      balancedCanonicalityOutput raw ≠ 0 := by
    intro hzero
    simp [booleanNodeListValidationOutput, hequality, hzero] at haccept
  have hcanonicalOne :
      balancedCanonicalityOutput raw = 1 := by
    by_cases hcode :
        encodeBalancedList (rawBalancedTraversalTree raw).atoms = raw
    · simp [balancedCanonicalityOutput, hcode]
    · simp [balancedCanonicalityOutput, hcode] at hcanonical
  have hisSome : (decodeBalancedList raw).isSome :=
    (balancedCanonicalityOutput_eq_one_iff raw).1 hcanonicalOne
  cases hdecode : decodeBalancedList raw with
  | none =>
      simp [hdecode] at hisSome
  | some rawNodes =>
      have hraw : encodeBalancedList rawNodes = raw :=
        encodeBalancedList_of_decode hdecode
      have hatoms :
          booleanNodeListAtoms raw = rawNodes := by
        rw [← hraw]
        exact booleanNodeListAtoms_encodeBalancedList rawNodes
      let descriptors := booleanNodeListDescriptors raw
      have hdescriptorLength :
          descriptors.length = rawNodes.length := by
        simp [descriptors, booleanNodeListDescriptors,
          booleanNodeOutputs, hatoms]
      have hcountEquality :
          booleanNodeListTopologyCount inputLength raw =
            booleanNodeListNodeCount raw := by
        simpa [booleanNodeListTopologyEqualityOutput,
          nativeNatEqOutput] using hequality
      have hsupportCount :
          nonzeroSupportCount
              (fixedBooleanRangeValues inputLength descriptors.length
                (booleanNodeTopologyRangeContext descriptors)
                (booleanNodeTopologyRangeValue inputLength descriptors)) =
            descriptors.length := by
        simpa [booleanNodeListTopologyCount,
          booleanNodeListTopologyOutput,
          booleanNodeTopologyRangeOutput,
          fixedBooleanRangeAggregationOutput,
          booleanNodeListNodeCount, booleanNodeListRangeContext,
          booleanNodeListPreparationOutput,
          booleanCircuitPreparationOutput, descriptors,
          booleanNodeListDescriptors, booleanNodeOutputs, hatoms] using
          hcountEquality
      have hallTrue :
          ∀ value ∈
              fixedBooleanRangeValues inputLength descriptors.length
                (booleanNodeTopologyRangeContext descriptors)
                (booleanNodeTopologyRangeValue inputLength descriptors),
            value = true :=
        all_true_of_nonzeroSupportCount_eq_length (by
          simpa [fixedBooleanRangeValues, fixedBooleanRangeRequests] using
            hsupportCount)
      have hnodeAt :
          ∀ index : Fin rawNodes.length,
            ∃ node : BooleanNode inputLength,
              decodeBooleanNode inputLength (rawNodes.get index) =
                  some node ∧
                node.WellFormedAt index.val := by
        intro index
        have hrequestMember :
            booleanNodeTopologyRangeValue inputLength descriptors
                (balancedRangeRequestAtom inputLength index.val
                  (booleanNodeTopologyRangeContext descriptors)) ∈
              fixedBooleanRangeValues inputLength descriptors.length
                (booleanNodeTopologyRangeContext descriptors)
                (booleanNodeTopologyRangeValue inputLength descriptors) := by
          unfold fixedBooleanRangeValues
          apply List.mem_map.mpr
          refine
            ⟨balancedRangeRequestAtom inputLength index.val
                (booleanNodeTopologyRangeContext descriptors), ?_, rfl⟩
          unfold fixedBooleanRangeRequests
          rw [balancedRangeRequestAtoms_eq_map_range]
          apply List.mem_map.mpr
          refine ⟨index.val, ?_, ?_⟩
          · apply List.mem_range.mpr
            rw [hdescriptorLength]
            exact index.isLt
          · simp
        have hvalueTrue :=
          hallTrue _ hrequestMember
        have htopology :
            booleanNodeTopologyOutput inputLength
                descriptors[index.val]! index.val ≠ 0 := by
          simpa [booleanNodeTopologyRangeValue,
            booleanNodeTopologyRangeIndex,
            balancedRangeRequestAtom] using hvalueTrue
        have hdescriptor :
            descriptors[index.val]! =
              booleanNodeStructuralOutput (rawNodes.get index) := by
          have hindex : index.val < descriptors.length := by
            rw [hdescriptorLength]
            exact index.isLt
          rw [getElem!_pos descriptors index.val hindex]
          simp [descriptors, booleanNodeListDescriptors,
            booleanNodeOutputs, hatoms]
        rw [hdescriptor] at htopology
        exact
          (booleanNodeTopologyOutput_ne_zero_iff_decode
            inputLength (rawNodes.get index) index.val).1 htopology
      classical
      let nodeAt : Fin rawNodes.length → BooleanNode inputLength :=
        fun index => (hnodeAt index).choose
      let nodes : List (BooleanNode inputLength) :=
        List.ofFn nodeAt
      have hnodesLength : nodes.length = rawNodes.length := by
        simp [nodes]
      have hcodes :
          nodes.map encodeBooleanNode = rawNodes := by
        apply List.ext_get
        · simp [nodes]
        · intro index hleft hright
          let rawIndex : Fin rawNodes.length :=
            ⟨index, hright⟩
          have hchosen := (hnodeAt rawIndex).choose_spec
          have hencoded :
              encodeBooleanNode (nodeAt rawIndex) =
                rawNodes.get rawIndex :=
            encodeBooleanNode_of_decode hchosen.1
          simpa [nodes, nodeAt, rawIndex] using hencoded
      refine ⟨nodes, ?_, ?_⟩
      · rw [hcodes, hraw]
      · intro index
        let rawIndex : Fin rawNodes.length :=
          ⟨index.val, by simpa [hnodesLength] using index.isLt⟩
        have hchosen := (hnodeAt rawIndex).choose_spec
        simpa [nodes, nodeAt, rawIndex] using hchosen.2

theorem booleanNodeListValidationOutput_encodeNodes
    {inputLength : ℕ} (nodes : List (BooleanNode inputLength))
    (hwellFormed :
      ∀ index : Fin nodes.length,
        (nodes.get index).WellFormedAt index.val) :
    booleanNodeListValidationOutput inputLength
        (encodeBalancedList
          (nodes.map encodeBooleanNode)) =
      Nat.pair 1 nodes.length := by
  let raw :=
    encodeBalancedList (nodes.map encodeBooleanNode)
  have hatoms :
      booleanNodeListAtoms raw =
        nodes.map encodeBooleanNode := by
    simp [raw]
  have hdescriptors :
      booleanNodeListDescriptors raw =
        encodedBooleanNodeDescriptors nodes := by
    simp [booleanNodeListDescriptors, booleanNodeOutputs,
      encodedBooleanNodeDescriptors, hatoms]
  have hcanonical :
      balancedCanonicalityOutput raw = 1 := by
    apply (balancedCanonicalityOutput_eq_one_iff raw).2
    simp [raw]
  have houtputs :
      booleanNodeOutputs (nodes.map encodeBooleanNode) =
        encodedBooleanNodeDescriptors nodes := by
    simp [booleanNodeOutputs, encodedBooleanNodeDescriptors]
  have hpreparation :
      booleanNodeListPreparationOutput raw =
        Nat.pair nodes.length
          (encodeBalancedList
            (encodedBooleanNodeDescriptors nodes)) := by
    simp [booleanNodeListPreparationOutput,
      booleanCircuitPreparationOutput, hatoms, houtputs]
  have hcontext :
      booleanNodeListRangeContext raw =
        Nat.pair nodes.length 1 := by
    simp [booleanNodeListRangeContext, hpreparation, hcanonical]
  have hnodeCount :
      booleanNodeListNodeCount raw = nodes.length := by
    simp [booleanNodeListNodeCount, hcontext]
  have htopology :
      booleanNodeListTopologyOutput inputLength raw =
        Nat.pair nodes.length
          (booleanNodeTopologyRangeContext
            (encodedBooleanNodeDescriptors nodes)) := by
    unfold booleanNodeListTopologyOutput
    rw [hdescriptors]
    exact
      booleanNodeTopologyRangeOutput_encodeNodes nodes hwellFormed
  have htopologyCount :
      booleanNodeListTopologyCount inputLength raw =
        nodes.length := by
    simp [booleanNodeListTopologyCount, htopology]
  have hequality :
      booleanNodeListTopologyEqualityOutput inputLength raw = 1 := by
    simp [booleanNodeListTopologyEqualityOutput,
      nativeNatEqOutput, htopologyCount, hnodeCount]
  simp [booleanNodeListValidationOutput, raw, hequality,
    hcanonical, hnodeCount]

@[simp] theorem booleanNodeListValidationOutput_encodeBooleanCircuit
    {inputLength : ℕ} (circuit : BooleanCircuit inputLength) :
    booleanNodeListValidationOutput inputLength
        (encodeBalancedList
          (circuit.nodes.map encodeBooleanNode)) =
      Nat.pair 1 circuit.nodes.length :=
  booleanNodeListValidationOutput_encodeNodes
    circuit.nodes circuit.wellFormed

end NearCubicWires.CanonicalBooleanNodeListValidationProgram
