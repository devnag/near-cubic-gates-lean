import Proof.MachineModel.CanonicalBooleanNodeListValidationProgram
import Proof.MachineModel.CanonicalNatValidationProgram
import Proof.MachineModel.CanonicalTaggedTupleProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.VerifiedLinker

/-!
# Canonical Boolean-circuit validation

The public circuit word is consumed by one fixed pipeline.  A fixed-arity
tuple parser exposes the node tree and output-index code, the total node-list
validator derives the exact node count, the shared Nat validator derives the
output index, and the sole native less-than path checks that the output names
an existing node.  No decoded circuit, node count, topology witness, or runtime
callback is accepted from the caller.
-/

namespace NearCubicWires.CanonicalBooleanCircuitValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

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

private theorem bitLength_le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    natBitLength value ≤
      (values.map natBitLength).foldr max 1 := by
  apply value_le_foldr_max_of_mem
  exact List.mem_map.mpr ⟨value, hmem, rfl⟩

/-! ## Fixed outer tuple and field projection -/

def booleanCircuitTupleOutput (raw : ℕ) : ℕ :=
  taggedTupleOutput 2 raw

def booleanCircuitTupleProgram : NPOracleProgram :=
  taggedTupleProgram 2

@[simp] theorem booleanCircuitTupleProgram_oracleFree :
    OracleFree booleanCircuitTupleProgram := by
  exact taggedTupleProgram_oracleFree 2

def booleanCircuitTupleFuel : ℕ :=
  taggedTupleFuel 2

def booleanCircuitTupleBits (inputLength raw : ℕ) : ℕ :=
  taggedTupleBits inputLength 2 raw

theorem run_booleanCircuitTupleProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitTupleProgram
        (booleanCircuitTupleBits inputLength raw)
        booleanCircuitTupleFuel
        (initialNPOracleState inputLength raw) =
      some (booleanCircuitTupleOutput raw) := by
  exact run_taggedTupleProgram inputLength 2 raw

def booleanCircuitTupleFlag (raw : ℕ) : ℕ :=
  (Nat.unpair (booleanCircuitTupleOutput raw)).1

def booleanCircuitTupleFields (raw : ℕ) : ℕ :=
  (Nat.unpair (booleanCircuitTupleOutput raw)).2

def booleanCircuitNodesCode (raw : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair (booleanCircuitTupleFields raw)).1).2

def booleanCircuitOutputCode (raw : ℕ) : ℕ :=
  (Nat.unpair (booleanCircuitTupleFields raw)).2

def booleanCircuitFieldProjectionOutput (raw : ℕ) : ℕ :=
  Nat.pair (booleanCircuitNodesCode raw)
    (Nat.pair (booleanCircuitOutputCode raw)
      (booleanCircuitTupleFlag raw))

def booleanCircuitFieldProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 4 5 4
  , .unpairRight 3 6 5
  , .pair 6 2 7 6
  , .pair 5 7 0 7
  , .halt 0
  ]

@[simp] theorem booleanCircuitFieldProjectionProgram_oracleFree :
    OracleFree booleanCircuitFieldProjectionProgram := by
  rfl

def booleanCircuitFieldProjectionFuel : ℕ := 8

private def booleanCircuitFieldProjectionValues
    (inputLength raw : ℕ) : List ℕ :=
  let tuple := booleanCircuitTupleOutput raw
  let flag := booleanCircuitTupleFlag raw
  let fields := booleanCircuitTupleFields raw
  let prefixCode := (Nat.unpair fields).1
  let nodes := booleanCircuitNodesCode raw
  let output := booleanCircuitOutputCode raw
  [ inputLength
  , tuple
  , flag
  , fields
  , prefixCode
  , nodes
  , output
  , Nat.pair output flag
  , booleanCircuitFieldProjectionOutput raw
  ]

def booleanCircuitFieldProjectionBits
    (inputLength raw : ℕ) : ℕ :=
  (booleanCircuitFieldProjectionValues inputLength raw).map
    natBitLength |>.foldr max 1

private theorem booleanCircuitFieldProjectionValue_bits
    (inputLength raw value : ℕ)
    (hvalue :
      value ∈ booleanCircuitFieldProjectionValues inputLength raw) :
    natBitLength value ≤
      booleanCircuitFieldProjectionBits inputLength raw := by
  exact bitLength_le_foldr_max_of_mem hvalue

theorem run_booleanCircuitFieldProjectionProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitFieldProjectionProgram
        (booleanCircuitFieldProjectionBits inputLength raw)
        booleanCircuitFieldProjectionFuel
        (initialNPOracleState inputLength
          (booleanCircuitTupleOutput raw)) =
      some (booleanCircuitFieldProjectionOutput raw) := by
  let flag := booleanCircuitTupleFlag raw
  let fields := booleanCircuitTupleFields raw
  let prefixCode := (Nat.unpair fields).1
  let nodes := booleanCircuitNodesCode raw
  let output := booleanCircuitOutputCode raw
  have hflag :
      natBitLength flag ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    apply booleanCircuitFieldProjectionValue_bits
    simp [booleanCircuitFieldProjectionValues, flag]
  have hfields :
      natBitLength fields ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    apply booleanCircuitFieldProjectionValue_bits
    simp [booleanCircuitFieldProjectionValues, fields]
  have hprefix :
      natBitLength prefixCode ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    apply booleanCircuitFieldProjectionValue_bits
    simp [booleanCircuitFieldProjectionValues, prefixCode, fields]
  have hnodes :
      natBitLength nodes ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    apply booleanCircuitFieldProjectionValue_bits
    simp [booleanCircuitFieldProjectionValues, nodes]
  have houtput :
      natBitLength output ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    apply booleanCircuitFieldProjectionValue_bits
    simp [booleanCircuitFieldProjectionValues, output]
  have houtputFlag :
      natBitLength (Nat.pair output flag) ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    apply booleanCircuitFieldProjectionValue_bits
    simp [booleanCircuitFieldProjectionValues, output, flag]
  have hresult :
      natBitLength (booleanCircuitFieldProjectionOutput raw) ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    apply booleanCircuitFieldProjectionValue_bits
    simp [booleanCircuitFieldProjectionValues]
  have hflag' :
      natBitLength
          (Nat.unpair (booleanCircuitTupleOutput raw)).1 ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    simpa [flag, booleanCircuitTupleFlag] using hflag
  have hfields' :
      natBitLength
          (Nat.unpair (booleanCircuitTupleOutput raw)).2 ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    simpa [fields, booleanCircuitTupleFields] using hfields
  have hprefix' :
      natBitLength
          (Nat.unpair
            (Nat.unpair (booleanCircuitTupleOutput raw)).2).1 ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    simpa [prefixCode, fields, booleanCircuitTupleFields] using hprefix
  have hnodes' :
      natBitLength
          (Nat.unpair
            (Nat.unpair
              (Nat.unpair (booleanCircuitTupleOutput raw)).2).1).2 ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    simpa [nodes, booleanCircuitNodesCode, booleanCircuitTupleFields]
      using hnodes
  have houtput' :
      natBitLength
          (Nat.unpair
            (Nat.unpair (booleanCircuitTupleOutput raw)).2).2 ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    simpa [output, booleanCircuitOutputCode, booleanCircuitTupleFields]
      using houtput
  have houtputFlag' :
      natBitLength
          (Nat.pair
            (Nat.unpair
              (Nat.unpair (booleanCircuitTupleOutput raw)).2).2
            (Nat.unpair (booleanCircuitTupleOutput raw)).1) ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    simpa [output, flag, booleanCircuitOutputCode,
      booleanCircuitTupleFlag, booleanCircuitTupleFields] using
      houtputFlag
  have hresult' :
      natBitLength
          (Nat.pair
            (Nat.unpair
              (Nat.unpair
                (Nat.unpair (booleanCircuitTupleOutput raw)).2).1).2
            (Nat.pair
              (Nat.unpair
                (Nat.unpair (booleanCircuitTupleOutput raw)).2).2
              (Nat.unpair (booleanCircuitTupleOutput raw)).1)) ≤
        booleanCircuitFieldProjectionBits inputLength raw := by
    simpa [booleanCircuitFieldProjectionOutput,
      booleanCircuitNodesCode, booleanCircuitOutputCode,
      booleanCircuitTupleFlag, booleanCircuitTupleFields] using hresult
  simp [booleanCircuitFieldProjectionProgram,
    booleanCircuitFieldProjectionFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    booleanCircuitTupleFlag, booleanCircuitTupleFields,
    booleanCircuitNodesCode, booleanCircuitOutputCode,
    booleanCircuitFieldProjectionOutput,
    hflag', hfields', hprefix', hnodes', houtput',
    houtputFlag', hresult']

/-! ## Total node-list validation while preserving the output field -/

def booleanCircuitNodeStageOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair
    (booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw))
    (Nat.pair (booleanCircuitOutputCode raw)
      (booleanCircuitTupleFlag raw))

def booleanCircuitNodeStageProgram : NPOracleProgram :=
  preserveRightProgram booleanNodeListValidationProgram

@[simp] theorem booleanCircuitNodeStageProgram_oracleFree :
    OracleFree booleanCircuitNodeStageProgram := by
  exact preserveRightProgram_oracleFree booleanNodeListValidationProgram
    booleanNodeListValidationProgram_oracleFree

def booleanCircuitNodeStageFuel
    (inputLength raw : ℕ) : ℕ :=
  preserveRightFuel <|
    booleanNodeListValidationFuel inputLength
      (booleanCircuitNodesCode raw)

def booleanCircuitNodeStageBits
    (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (booleanNodeListValidationBits inputLength
      (booleanCircuitNodesCode raw))
    (booleanCircuitNodesCode raw)
    (Nat.pair (booleanCircuitOutputCode raw)
      (booleanCircuitTupleFlag raw))
    (booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw))

theorem run_booleanCircuitNodeStageProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitNodeStageProgram
        (booleanCircuitNodeStageBits inputLength raw)
        (booleanCircuitNodeStageFuel inputLength raw)
        (initialNPOracleState inputLength
          (booleanCircuitFieldProjectionOutput raw)) =
      some (booleanCircuitNodeStageOutput inputLength raw) := by
  exact run_preserveRightProgram booleanNodeListValidationProgram
    inputLength
    (booleanNodeListValidationBits inputLength
      (booleanCircuitNodesCode raw))
    (booleanNodeListValidationFuel inputLength
      (booleanCircuitNodesCode raw))
    (booleanCircuitNodesCode raw)
    (Nat.pair (booleanCircuitOutputCode raw)
      (booleanCircuitTupleFlag raw))
    (booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw))
    (run_booleanNodeListValidationProgram inputLength
      (booleanCircuitNodesCode raw))

/-! ## Shared Nat validation on the machine-projected output field -/

def booleanCircuitNatLoweringOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (booleanCircuitOutputCode raw) <|
    Nat.pair
      (booleanNodeListValidationOutput inputLength
        (booleanCircuitNodesCode raw))
      (booleanCircuitTupleFlag raw)

def booleanCircuitNatLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 5 6 5
  , .pair 4 6 0 6
  , .halt 0
  ]

@[simp] theorem booleanCircuitNatLoweringProgram_oracleFree :
    OracleFree booleanCircuitNatLoweringProgram := by
  rfl

def booleanCircuitNatLoweringFuel : ℕ := 7

private def booleanCircuitNatLoweringValues
    (inputLength raw : ℕ) : List ℕ :=
  let nodeOutput :=
    booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw)
  let outputCode := booleanCircuitOutputCode raw
  let tupleFlag := booleanCircuitTupleFlag raw
  let context := Nat.pair outputCode tupleFlag
  [ inputLength
  , Nat.pair nodeOutput context
  , nodeOutput
  , context
  , outputCode
  , tupleFlag
  , Nat.pair nodeOutput tupleFlag
  , booleanCircuitNatLoweringOutput inputLength raw
  ]

def booleanCircuitNatLoweringBits
    (inputLength raw : ℕ) : ℕ :=
  (booleanCircuitNatLoweringValues inputLength raw).map
    natBitLength |>.foldr max 1

private theorem booleanCircuitNatLoweringValue_bits
    (inputLength raw value : ℕ)
    (hvalue :
      value ∈ booleanCircuitNatLoweringValues inputLength raw) :
    natBitLength value ≤
      booleanCircuitNatLoweringBits inputLength raw := by
  exact bitLength_le_foldr_max_of_mem hvalue

theorem run_booleanCircuitNatLoweringProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitNatLoweringProgram
        (booleanCircuitNatLoweringBits inputLength raw)
        booleanCircuitNatLoweringFuel
        (initialNPOracleState inputLength
          (booleanCircuitNodeStageOutput inputLength raw)) =
      some (booleanCircuitNatLoweringOutput inputLength raw) := by
  let nodeOutput :=
    booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw)
  let outputCode := booleanCircuitOutputCode raw
  let tupleFlag := booleanCircuitTupleFlag raw
  let context := Nat.pair outputCode tupleFlag
  have hnode :
      natBitLength nodeOutput ≤
        booleanCircuitNatLoweringBits inputLength raw := by
    apply booleanCircuitNatLoweringValue_bits
    simp [booleanCircuitNatLoweringValues, nodeOutput]
  have hcontext :
      natBitLength context ≤
        booleanCircuitNatLoweringBits inputLength raw := by
    apply booleanCircuitNatLoweringValue_bits
    simp [booleanCircuitNatLoweringValues, context, outputCode,
      tupleFlag]
  have houtput :
      natBitLength outputCode ≤
        booleanCircuitNatLoweringBits inputLength raw := by
    apply booleanCircuitNatLoweringValue_bits
    simp [booleanCircuitNatLoweringValues, outputCode]
  have hflag :
      natBitLength tupleFlag ≤
        booleanCircuitNatLoweringBits inputLength raw := by
    apply booleanCircuitNatLoweringValue_bits
    simp [booleanCircuitNatLoweringValues, tupleFlag]
  have hnodeFlag :
      natBitLength (Nat.pair nodeOutput tupleFlag) ≤
        booleanCircuitNatLoweringBits inputLength raw := by
    apply booleanCircuitNatLoweringValue_bits
    simp [booleanCircuitNatLoweringValues, nodeOutput, tupleFlag]
  have hresult :
      natBitLength
          (booleanCircuitNatLoweringOutput inputLength raw) ≤
        booleanCircuitNatLoweringBits inputLength raw := by
    apply booleanCircuitNatLoweringValue_bits
    simp [booleanCircuitNatLoweringValues]
  have hresult' :
      natBitLength
          (Nat.pair (booleanCircuitOutputCode raw)
            (Nat.pair
              (booleanNodeListValidationOutput inputLength
                (booleanCircuitNodesCode raw))
              (booleanCircuitTupleFlag raw))) ≤
        booleanCircuitNatLoweringBits inputLength raw := by
    simpa [booleanCircuitNatLoweringOutput] using hresult
  simp [booleanCircuitNatLoweringProgram,
    booleanCircuitNatLoweringFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    booleanCircuitNodeStageOutput,
    booleanCircuitNatLoweringOutput,
    nodeOutput, outputCode, tupleFlag, context,
    hnode, hcontext, houtput, hflag, hnodeFlag, hresult']

def booleanCircuitNatStageOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair
    (canonicalNatValidationOutput
      (booleanCircuitOutputCode raw)) <|
    Nat.pair
      (booleanNodeListValidationOutput inputLength
        (booleanCircuitNodesCode raw))
      (booleanCircuitTupleFlag raw)

def booleanCircuitNatStageProgram : NPOracleProgram :=
  preserveRightProgram canonicalNatValidationProgram

@[simp] theorem booleanCircuitNatStageProgram_oracleFree :
    OracleFree booleanCircuitNatStageProgram := by
  exact preserveRightProgram_oracleFree canonicalNatValidationProgram
    canonicalNatValidationProgram_oracleFree

def booleanCircuitNatStageFuel (raw : ℕ) : ℕ :=
  preserveRightFuel <|
    canonicalNatValidationFuel (booleanCircuitOutputCode raw)

def booleanCircuitNatStageBits
    (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (canonicalNatValidationBits inputLength
      (booleanCircuitOutputCode raw))
    (booleanCircuitOutputCode raw)
    (Nat.pair
      (booleanNodeListValidationOutput inputLength
        (booleanCircuitNodesCode raw))
      (booleanCircuitTupleFlag raw))
    (canonicalNatValidationOutput
      (booleanCircuitOutputCode raw))

theorem run_booleanCircuitNatStageProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitNatStageProgram
        (booleanCircuitNatStageBits inputLength raw)
        (booleanCircuitNatStageFuel raw)
        (initialNPOracleState inputLength
          (booleanCircuitNatLoweringOutput inputLength raw)) =
      some (booleanCircuitNatStageOutput inputLength raw) := by
  exact run_preserveRightProgram canonicalNatValidationProgram
    inputLength
    (canonicalNatValidationBits inputLength
      (booleanCircuitOutputCode raw))
    (canonicalNatValidationFuel (booleanCircuitOutputCode raw))
    (booleanCircuitOutputCode raw)
    (Nat.pair
      (booleanNodeListValidationOutput inputLength
        (booleanCircuitNodesCode raw))
      (booleanCircuitTupleFlag raw))
    (canonicalNatValidationOutput
      (booleanCircuitOutputCode raw))
    (run_canonicalNatValidationProgram inputLength
      (booleanCircuitOutputCode raw))

/-! ## Machine-derived output-range request -/

def booleanCircuitNatValue (raw : ℕ) : ℕ :=
  (Nat.unpair
    (canonicalNatValidationOutput
      (booleanCircuitOutputCode raw))).2

def booleanCircuitNodeCount
    (inputLength raw : ℕ) : ℕ :=
  (Nat.unpair
    (booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw))).2

def booleanCircuitLtRequest
    (inputLength raw : ℕ) : ℕ :=
  nativeLtRequest (booleanCircuitNatValue raw)
    (booleanCircuitNodeCount inputLength raw)

def booleanCircuitLtLoweringOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (booleanCircuitLtRequest inputLength raw)
    (booleanCircuitNatStageOutput inputLength raw)

def booleanCircuitLtLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 2 4 3
  , .unpairLeft 3 5 4
  , .unpairRight 5 6 5
  , .pair 6 4 7 6
  , .pair 7 0 0 7
  , .halt 0
  ]

@[simp] theorem booleanCircuitLtLoweringProgram_oracleFree :
    OracleFree booleanCircuitLtLoweringProgram := by
  rfl

def booleanCircuitLtLoweringFuel : ℕ := 8

private def booleanCircuitLtLoweringValues
    (inputLength raw : ℕ) : List ℕ :=
  let natOutput :=
    canonicalNatValidationOutput (booleanCircuitOutputCode raw)
  let nodeOutput :=
    booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw)
  let tupleFlag := booleanCircuitTupleFlag raw
  let rest := Nat.pair nodeOutput tupleFlag
  let natValue := booleanCircuitNatValue raw
  let nodeCount := booleanCircuitNodeCount inputLength raw
  let request := booleanCircuitLtRequest inputLength raw
  [ inputLength
  , Nat.pair natOutput rest
  , natOutput
  , rest
  , natValue
  , nodeOutput
  , nodeCount
  , request
  , booleanCircuitLtLoweringOutput inputLength raw
  ]

def booleanCircuitLtLoweringBits
    (inputLength raw : ℕ) : ℕ :=
  (booleanCircuitLtLoweringValues inputLength raw).map
    natBitLength |>.foldr max 1

private theorem booleanCircuitLtLoweringValue_bits
    (inputLength raw value : ℕ)
    (hvalue :
      value ∈ booleanCircuitLtLoweringValues inputLength raw) :
    natBitLength value ≤
      booleanCircuitLtLoweringBits inputLength raw := by
  exact bitLength_le_foldr_max_of_mem hvalue

theorem run_booleanCircuitLtLoweringProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitLtLoweringProgram
        (booleanCircuitLtLoweringBits inputLength raw)
        booleanCircuitLtLoweringFuel
        (initialNPOracleState inputLength
          (booleanCircuitNatStageOutput inputLength raw)) =
      some (booleanCircuitLtLoweringOutput inputLength raw) := by
  let natOutput :=
    canonicalNatValidationOutput (booleanCircuitOutputCode raw)
  let nodeOutput :=
    booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw)
  let tupleFlag := booleanCircuitTupleFlag raw
  let rest := Nat.pair nodeOutput tupleFlag
  let natValue := booleanCircuitNatValue raw
  let nodeCount := booleanCircuitNodeCount inputLength raw
  let request := booleanCircuitLtRequest inputLength raw
  have hnatOutput :
      natBitLength natOutput ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    apply booleanCircuitLtLoweringValue_bits
    simp [booleanCircuitLtLoweringValues, natOutput]
  have hrest :
      natBitLength rest ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    apply booleanCircuitLtLoweringValue_bits
    simp [booleanCircuitLtLoweringValues, rest, nodeOutput, tupleFlag]
  have hnatValue :
      natBitLength natValue ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    apply booleanCircuitLtLoweringValue_bits
    simp [booleanCircuitLtLoweringValues, natValue]
  have hnodeOutput :
      natBitLength nodeOutput ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    apply booleanCircuitLtLoweringValue_bits
    simp [booleanCircuitLtLoweringValues, nodeOutput]
  have hnodeCount :
      natBitLength nodeCount ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    apply booleanCircuitLtLoweringValue_bits
    simp [booleanCircuitLtLoweringValues, nodeCount]
  have hrequest :
      natBitLength request ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    apply booleanCircuitLtLoweringValue_bits
    simp [booleanCircuitLtLoweringValues, request]
  have hresult :
      natBitLength
          (booleanCircuitLtLoweringOutput inputLength raw) ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    apply booleanCircuitLtLoweringValue_bits
    simp [booleanCircuitLtLoweringValues]
  have hnatOutput' :
      natBitLength
          (canonicalNatValidationOutput
            (booleanCircuitOutputCode raw)) ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    simpa [natOutput] using hnatOutput
  have hrest' :
      natBitLength
          (Nat.pair
            (booleanNodeListValidationOutput inputLength
              (booleanCircuitNodesCode raw))
            (booleanCircuitTupleFlag raw)) ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    simpa [rest, nodeOutput, tupleFlag] using hrest
  have hnatValue' :
      natBitLength
          (Nat.unpair
            (canonicalNatValidationOutput
              (booleanCircuitOutputCode raw))).2 ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    simpa [natValue, booleanCircuitNatValue] using hnatValue
  have hnodeOutput' :
      natBitLength
          (booleanNodeListValidationOutput inputLength
            (booleanCircuitNodesCode raw)) ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    simpa [nodeOutput] using hnodeOutput
  have hnodeCount' :
      natBitLength
          (Nat.unpair
            (booleanNodeListValidationOutput inputLength
              (booleanCircuitNodesCode raw))).2 ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    simpa [nodeCount, booleanCircuitNodeCount] using hnodeCount
  have hrequest' :
      natBitLength
          (Nat.pair
            (Nat.unpair
              (booleanNodeListValidationOutput inputLength
                (booleanCircuitNodesCode raw))).2
            (Nat.unpair
              (canonicalNatValidationOutput
                (booleanCircuitOutputCode raw))).2) ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    simpa [request, booleanCircuitLtRequest, nativeLtRequest,
      nativeInputRequest, booleanCircuitNatValue,
      booleanCircuitNodeCount] using hrequest
  have hresult' :
      natBitLength
          (Nat.pair
            (Nat.pair
              (Nat.unpair
                (booleanNodeListValidationOutput inputLength
                  (booleanCircuitNodesCode raw))).2
              (Nat.unpair
                (canonicalNatValidationOutput
                  (booleanCircuitOutputCode raw))).2)
            (booleanCircuitNatStageOutput inputLength raw)) ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    simpa [booleanCircuitLtLoweringOutput, booleanCircuitLtRequest,
      nativeLtRequest, nativeInputRequest, booleanCircuitNatValue,
      booleanCircuitNodeCount] using hresult
  have hresult'' :
      natBitLength
          (Nat.pair
            (Nat.pair
              (Nat.unpair
                (booleanNodeListValidationOutput inputLength
                  (booleanCircuitNodesCode raw))).2
              (Nat.unpair
                (canonicalNatValidationOutput
                  (booleanCircuitOutputCode raw))).2)
            (Nat.pair
              (canonicalNatValidationOutput
                (booleanCircuitOutputCode raw))
              (Nat.pair
                (booleanNodeListValidationOutput inputLength
                  (booleanCircuitNodesCode raw))
                (booleanCircuitTupleFlag raw)))) ≤
        booleanCircuitLtLoweringBits inputLength raw := by
    simpa [booleanCircuitNatStageOutput] using hresult'
  simp [booleanCircuitLtLoweringProgram,
    booleanCircuitLtLoweringFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    booleanCircuitNatStageOutput, booleanCircuitLtLoweringOutput,
    booleanCircuitLtRequest, nativeLtRequest, nativeInputRequest,
    booleanCircuitNatValue, booleanCircuitNodeCount,
    hnatOutput', hrest', hnatValue', hnodeOutput', hnodeCount',
    hrequest', hresult'']

def booleanCircuitLtFlag
    (inputLength raw : ℕ) : ℕ :=
  nativeLtRequestOutput
    (booleanCircuitLtRequest inputLength raw)

def booleanCircuitLtStageOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (booleanCircuitLtFlag inputLength raw)
    (booleanCircuitNatStageOutput inputLength raw)

def booleanCircuitLtStageProgram : NPOracleProgram :=
  preserveRightProgram nativeLtRequestProgram

@[simp] theorem booleanCircuitLtStageProgram_oracleFree :
    OracleFree booleanCircuitLtStageProgram := by
  exact preserveRightProgram_oracleFree nativeLtRequestProgram
    nativeLtRequestProgram_oracleFree

def booleanCircuitLtStageFuel
    (inputLength raw : ℕ) : ℕ :=
  preserveRightFuel <|
    nativeLtRequestFuel (booleanCircuitLtRequest inputLength raw)

def booleanCircuitLtStageBits
    (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (nativeLtRequestBits inputLength
      (booleanCircuitLtRequest inputLength raw))
    (booleanCircuitLtRequest inputLength raw)
    (booleanCircuitNatStageOutput inputLength raw)
    (booleanCircuitLtFlag inputLength raw)

theorem run_booleanCircuitLtStageProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitLtStageProgram
        (booleanCircuitLtStageBits inputLength raw)
        (booleanCircuitLtStageFuel inputLength raw)
        (initialNPOracleState inputLength
          (booleanCircuitLtLoweringOutput inputLength raw)) =
      some (booleanCircuitLtStageOutput inputLength raw) := by
  exact run_preserveRightProgram nativeLtRequestProgram
    inputLength
    (nativeLtRequestBits inputLength
      (booleanCircuitLtRequest inputLength raw))
    (nativeLtRequestFuel (booleanCircuitLtRequest inputLength raw))
    (booleanCircuitLtRequest inputLength raw)
    (booleanCircuitNatStageOutput inputLength raw)
    (booleanCircuitLtFlag inputLength raw)
    (by
      simpa [booleanCircuitLtFlag] using
        run_nativeLtRequestProgram inputLength
          (booleanCircuitLtRequest inputLength raw))

/-! ## One fail-closed acceptance gate -/

def booleanCircuitValidationOutput
    (inputLength raw : ℕ) : ℕ :=
  if booleanCircuitLtFlag inputLength raw = 0 then
    0
  else if
      canonicalNatValidationOutput
        (booleanCircuitOutputCode raw) = 0 then
    0
  else if
      booleanNodeListValidationOutput inputLength
        (booleanCircuitNodesCode raw) = 0 then
    0
  else if booleanCircuitTupleFlag raw = 0 then
    0
  else
    Nat.pair 1 (booleanCircuitNodeCount inputLength raw)

def booleanCircuitValidationGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 13 2
  , .unpairRight 0 3 3
  , .unpairLeft 3 4 4
  , .branchZero 4 13 5
  , .unpairRight 3 5 6
  , .unpairLeft 5 6 7
  , .branchZero 6 13 8
  , .unpairRight 5 7 9
  , .branchZero 7 13 10
  , .unpairRight 6 8 11
  , .set 9 1 12
  , .pair 9 8 0 14
  , .set 0 0 14
  , .halt 0
  ]

@[simp] theorem booleanCircuitValidationGateProgram_oracleFree :
    OracleFree booleanCircuitValidationGateProgram := by
  rfl

def booleanCircuitValidationGateFuel : ℕ := 15

private def booleanCircuitValidationGateValues
    (inputLength raw : ℕ) : List ℕ :=
  let ltFlag := booleanCircuitLtFlag inputLength raw
  let natOutput :=
    canonicalNatValidationOutput (booleanCircuitOutputCode raw)
  let nodeOutput :=
    booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw)
  let tupleFlag := booleanCircuitTupleFlag raw
  let rest := Nat.pair nodeOutput tupleFlag
  let context := Nat.pair natOutput rest
  let count := booleanCircuitNodeCount inputLength raw
  [ inputLength
  , Nat.pair ltFlag context
  , ltFlag
  , context
  , natOutput
  , rest
  , nodeOutput
  , tupleFlag
  , count
  , 1
  , Nat.pair 1 count
  , 0
  ]

def booleanCircuitValidationGateBits
    (inputLength raw : ℕ) : ℕ :=
  (booleanCircuitValidationGateValues inputLength raw).map
    natBitLength |>.foldr max 1

private theorem booleanCircuitValidationGateValue_bits
    (inputLength raw value : ℕ)
    (hvalue :
      value ∈ booleanCircuitValidationGateValues inputLength raw) :
    natBitLength value ≤
      booleanCircuitValidationGateBits inputLength raw := by
  exact bitLength_le_foldr_max_of_mem hvalue

set_option maxHeartbeats 800000 in
-- Five explicit fail-closed traces share the same nested register context.
theorem run_booleanCircuitValidationGateProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitValidationGateProgram
        (booleanCircuitValidationGateBits inputLength raw)
        booleanCircuitValidationGateFuel
        (initialNPOracleState inputLength
          (booleanCircuitLtStageOutput inputLength raw)) =
      some (booleanCircuitValidationOutput inputLength raw) := by
  let ltFlag := booleanCircuitLtFlag inputLength raw
  let natOutput :=
    canonicalNatValidationOutput (booleanCircuitOutputCode raw)
  let nodeOutput :=
    booleanNodeListValidationOutput inputLength
      (booleanCircuitNodesCode raw)
  let tupleFlag := booleanCircuitTupleFlag raw
  let rest := Nat.pair nodeOutput tupleFlag
  let context := Nat.pair natOutput rest
  let count := booleanCircuitNodeCount inputLength raw
  have hlt :
      natBitLength ltFlag ≤
        booleanCircuitValidationGateBits inputLength raw := by
    apply booleanCircuitValidationGateValue_bits
    simp [booleanCircuitValidationGateValues, ltFlag]
  have hcontext :
      natBitLength context ≤
        booleanCircuitValidationGateBits inputLength raw := by
    apply booleanCircuitValidationGateValue_bits
    simp [booleanCircuitValidationGateValues, context, natOutput,
      rest, nodeOutput, tupleFlag]
  have hnat :
      natBitLength natOutput ≤
        booleanCircuitValidationGateBits inputLength raw := by
    apply booleanCircuitValidationGateValue_bits
    simp [booleanCircuitValidationGateValues, natOutput]
  have hrest :
      natBitLength rest ≤
        booleanCircuitValidationGateBits inputLength raw := by
    apply booleanCircuitValidationGateValue_bits
    simp [booleanCircuitValidationGateValues, rest, nodeOutput, tupleFlag]
  have hnode :
      natBitLength nodeOutput ≤
        booleanCircuitValidationGateBits inputLength raw := by
    apply booleanCircuitValidationGateValue_bits
    simp [booleanCircuitValidationGateValues, nodeOutput]
  have htuple :
      natBitLength tupleFlag ≤
        booleanCircuitValidationGateBits inputLength raw := by
    apply booleanCircuitValidationGateValue_bits
    simp [booleanCircuitValidationGateValues, tupleFlag]
  have hcount :
      natBitLength count ≤
        booleanCircuitValidationGateBits inputLength raw := by
    apply booleanCircuitValidationGateValue_bits
    simp [booleanCircuitValidationGateValues, count]
  have hone :
      natBitLength 1 ≤
        booleanCircuitValidationGateBits inputLength raw := by
    apply booleanCircuitValidationGateValue_bits
    simp [booleanCircuitValidationGateValues]
  have haccept :
      natBitLength (Nat.pair 1 count) ≤
        booleanCircuitValidationGateBits inputLength raw := by
    apply booleanCircuitValidationGateValue_bits
    simp [booleanCircuitValidationGateValues, count]
  have hzero :
      natBitLength 0 ≤
        booleanCircuitValidationGateBits inputLength raw := by
    apply booleanCircuitValidationGateValue_bits
    simp [booleanCircuitValidationGateValues]
  rw [show booleanCircuitLtStageOutput inputLength raw =
      Nat.pair ltFlag context by
    simp [booleanCircuitLtStageOutput, booleanCircuitNatStageOutput,
      ltFlag, context, natOutput, rest, nodeOutput, tupleFlag]]
  by_cases hltZero : ltFlag = 0
  · rw [show booleanCircuitValidationOutput inputLength raw = 0 by
      simp [booleanCircuitValidationOutput, ltFlag, hltZero]]
    rw [show booleanCircuitValidationGateFuel = 14 + 1 by rfl]
    rw [run_unpairLeft_instruction
      (program := booleanCircuitValidationGateProgram)
      (maximumBits :=
        booleanCircuitValidationGateBits inputLength raw)
      (fuel := 14) (pc := 0) (source := 0) (destination := 2)
      (next := 1) (value := ltFlag)
      (by rfl) (by rfl)
      (by simp [initialNPOracleState]) hlt]
    rw [show (14 : ℕ) = 13 + 1 by omega]
    rw [run_branchZero_instruction
      (program := booleanCircuitValidationGateProgram)
      (maximumBits :=
        booleanCircuitValidationGateBits inputLength raw)
      (fuel := 13) (pc := 1) (register := 2)
      (zeroTarget := 13) (nonzeroTarget := 2)
      (by rfl) (by rfl)]
    rw [if_pos (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, hltZero])]
    rw [show (13 : ℕ) = 12 + 1 by omega]
    rw [run_set_instruction
      (program := booleanCircuitValidationGateProgram)
      (maximumBits :=
        booleanCircuitValidationGateBits inputLength raw)
      (fuel := 12) (pc := 13) (register := 0) (value := 0)
      (next := 14) (by rfl) (by rfl) hzero]
    exact run_halt_instruction
      (program := booleanCircuitValidationGateProgram)
      (maximumBits :=
        booleanCircuitValidationGateBits inputLength raw)
      (fuel := 11) (pc := 14) (outputRegister := 0) (value := 0)
      (by rfl) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump]) hzero
  · by_cases hnatZero : natOutput = 0
    · rw [show booleanCircuitValidationOutput inputLength raw = 0 by
        simp [booleanCircuitValidationOutput, ltFlag, natOutput,
          hltZero, hnatZero]]
      rw [show booleanCircuitValidationGateFuel = 14 + 1 by rfl]
      rw [run_unpairLeft_instruction
        (program := booleanCircuitValidationGateProgram)
        (maximumBits :=
          booleanCircuitValidationGateBits inputLength raw)
        (fuel := 14) (pc := 0) (source := 0) (destination := 2)
        (next := 1) (value := ltFlag)
        (by rfl) (by rfl)
        (by simp [initialNPOracleState]) hlt]
      rw [show (14 : ℕ) = 13 + 1 by omega]
      rw [run_branchZero_instruction
        (program := booleanCircuitValidationGateProgram)
        (maximumBits :=
          booleanCircuitValidationGateBits inputLength raw)
        (fuel := 13) (pc := 1) (register := 2)
        (zeroTarget := 13) (nonzeroTarget := 2)
        (by rfl) (by rfl)]
      rw [if_neg (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, hltZero])]
      rw [show (13 : ℕ) = 12 + 1 by omega]
      rw [run_unpairRight_instruction
        (program := booleanCircuitValidationGateProgram)
        (maximumBits :=
          booleanCircuitValidationGateBits inputLength raw)
        (fuel := 12) (pc := 2) (source := 0) (destination := 3)
        (next := 3) (value := context)
        (by rfl) (by rfl)
        (by simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump]) hcontext]
      rw [show (12 : ℕ) = 11 + 1 by omega]
      rw [run_unpairLeft_instruction
        (program := booleanCircuitValidationGateProgram)
        (maximumBits :=
          booleanCircuitValidationGateBits inputLength raw)
        (fuel := 11) (pc := 3) (source := 3) (destination := 4)
        (next := 4) (value := natOutput)
        (by rfl) (by rfl)
        (by simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, context]) hnat]
      rw [show (11 : ℕ) = 10 + 1 by omega]
      rw [run_branchZero_instruction
        (program := booleanCircuitValidationGateProgram)
        (maximumBits :=
          booleanCircuitValidationGateBits inputLength raw)
        (fuel := 10) (pc := 4) (register := 4)
        (zeroTarget := 13) (nonzeroTarget := 5)
        (by rfl) (by rfl)]
      rw [if_pos (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, hnatZero])]
      rw [show (10 : ℕ) = 9 + 1 by omega]
      rw [run_set_instruction
        (program := booleanCircuitValidationGateProgram)
        (maximumBits :=
          booleanCircuitValidationGateBits inputLength raw)
        (fuel := 9) (pc := 13) (register := 0) (value := 0)
        (next := 14) (by rfl) (by rfl) hzero]
      exact run_halt_instruction
        (program := booleanCircuitValidationGateProgram)
        (maximumBits :=
          booleanCircuitValidationGateBits inputLength raw)
        (fuel := 8) (pc := 14) (outputRegister := 0) (value := 0)
        (by rfl) (by rfl)
        (by simp [NPOracleState.write, NPOracleState.jump]) hzero
    · by_cases hnodeZero : nodeOutput = 0
      · rw [show booleanCircuitValidationOutput inputLength raw = 0 by
          simp [booleanCircuitValidationOutput, ltFlag, natOutput,
            nodeOutput, hltZero, hnatZero, hnodeZero]]
        rw [show booleanCircuitValidationGateFuel = 14 + 1 by rfl]
        rw [run_unpairLeft_instruction
          (program := booleanCircuitValidationGateProgram)
          (maximumBits :=
            booleanCircuitValidationGateBits inputLength raw)
          (fuel := 14) (pc := 0) (source := 0) (destination := 2)
          (next := 1) (value := ltFlag)
          (by rfl) (by rfl)
          (by simp [initialNPOracleState]) hlt]
        rw [show (14 : ℕ) = 13 + 1 by omega]
        rw [run_branchZero_instruction
          (program := booleanCircuitValidationGateProgram)
          (maximumBits :=
            booleanCircuitValidationGateBits inputLength raw)
          (fuel := 13) (pc := 1) (register := 2)
          (zeroTarget := 13) (nonzeroTarget := 2)
          (by rfl) (by rfl)]
        rw [if_neg (by
          simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, hltZero])]
        rw [show (13 : ℕ) = 12 + 1 by omega]
        rw [run_unpairRight_instruction
          (program := booleanCircuitValidationGateProgram)
          (maximumBits :=
            booleanCircuitValidationGateBits inputLength raw)
          (fuel := 12) (pc := 2) (source := 0) (destination := 3)
          (next := 3) (value := context)
          (by rfl) (by rfl)
          (by simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump]) hcontext]
        rw [show (12 : ℕ) = 11 + 1 by omega]
        rw [run_unpairLeft_instruction
          (program := booleanCircuitValidationGateProgram)
          (maximumBits :=
            booleanCircuitValidationGateBits inputLength raw)
          (fuel := 11) (pc := 3) (source := 3) (destination := 4)
          (next := 4) (value := natOutput)
          (by rfl) (by rfl)
          (by simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, context]) hnat]
        rw [show (11 : ℕ) = 10 + 1 by omega]
        rw [run_branchZero_instruction
          (program := booleanCircuitValidationGateProgram)
          (maximumBits :=
            booleanCircuitValidationGateBits inputLength raw)
          (fuel := 10) (pc := 4) (register := 4)
          (zeroTarget := 13) (nonzeroTarget := 5)
          (by rfl) (by rfl)]
        rw [if_neg (by
          simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, hnatZero])]
        rw [show (10 : ℕ) = 9 + 1 by omega]
        rw [run_unpairRight_instruction
          (program := booleanCircuitValidationGateProgram)
          (maximumBits :=
            booleanCircuitValidationGateBits inputLength raw)
          (fuel := 9) (pc := 5) (source := 3) (destination := 5)
          (next := 6) (value := rest)
          (by rfl) (by rfl)
          (by simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, context]) hrest]
        rw [show (9 : ℕ) = 8 + 1 by omega]
        rw [run_unpairLeft_instruction
          (program := booleanCircuitValidationGateProgram)
          (maximumBits :=
            booleanCircuitValidationGateBits inputLength raw)
          (fuel := 8) (pc := 6) (source := 5) (destination := 6)
          (next := 7) (value := nodeOutput)
          (by rfl) (by rfl)
          (by simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, rest]) hnode]
        rw [show (8 : ℕ) = 7 + 1 by omega]
        rw [run_branchZero_instruction
          (program := booleanCircuitValidationGateProgram)
          (maximumBits :=
            booleanCircuitValidationGateBits inputLength raw)
          (fuel := 7) (pc := 7) (register := 6)
          (zeroTarget := 13) (nonzeroTarget := 8)
          (by rfl) (by rfl)]
        rw [if_pos (by
          simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, hnodeZero])]
        rw [show (7 : ℕ) = 6 + 1 by omega]
        rw [run_set_instruction
          (program := booleanCircuitValidationGateProgram)
          (maximumBits :=
            booleanCircuitValidationGateBits inputLength raw)
          (fuel := 6) (pc := 13) (register := 0) (value := 0)
          (next := 14) (by rfl) (by rfl) hzero]
        exact run_halt_instruction
          (program := booleanCircuitValidationGateProgram)
          (maximumBits :=
            booleanCircuitValidationGateBits inputLength raw)
          (fuel := 5) (pc := 14) (outputRegister := 0) (value := 0)
          (by rfl) (by rfl)
          (by simp [NPOracleState.write, NPOracleState.jump]) hzero
      · by_cases htupleZero : tupleFlag = 0
        · rw [show booleanCircuitValidationOutput inputLength raw = 0 by
            simp [booleanCircuitValidationOutput, ltFlag, natOutput,
              nodeOutput, tupleFlag, hltZero, hnatZero, hnodeZero,
              htupleZero]]
          rw [show booleanCircuitValidationGateFuel = 14 + 1 by rfl]
          rw [run_unpairLeft_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 14) (pc := 0) (source := 0) (destination := 2)
            (next := 1) (value := ltFlag)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState]) hlt]
          rw [show (14 : ℕ) = 13 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 13) (pc := 1) (register := 2)
            (zeroTarget := 13) (nonzeroTarget := 2)
            (by rfl) (by rfl)]
          rw [if_neg (by
            simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, hltZero])]
          rw [show (13 : ℕ) = 12 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 12) (pc := 2) (source := 0) (destination := 3)
            (next := 3) (value := context)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump]) hcontext]
          rw [show (12 : ℕ) = 11 + 1 by omega]
          rw [run_unpairLeft_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 11) (pc := 3) (source := 3) (destination := 4)
            (next := 4) (value := natOutput)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, context]) hnat]
          rw [show (11 : ℕ) = 10 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 10) (pc := 4) (register := 4)
            (zeroTarget := 13) (nonzeroTarget := 5)
            (by rfl) (by rfl)]
          rw [if_neg (by
            simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, hnatZero])]
          rw [show (10 : ℕ) = 9 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 9) (pc := 5) (source := 3) (destination := 5)
            (next := 6) (value := rest)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, context]) hrest]
          rw [show (9 : ℕ) = 8 + 1 by omega]
          rw [run_unpairLeft_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 8) (pc := 6) (source := 5) (destination := 6)
            (next := 7) (value := nodeOutput)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, rest]) hnode]
          rw [show (8 : ℕ) = 7 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 7) (pc := 7) (register := 6)
            (zeroTarget := 13) (nonzeroTarget := 8)
            (by rfl) (by rfl)]
          rw [if_neg (by
            simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, hnodeZero])]
          rw [show (7 : ℕ) = 6 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 6) (pc := 8) (source := 5) (destination := 7)
            (next := 9) (value := tupleFlag)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, rest]) htuple]
          rw [show (6 : ℕ) = 5 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 5) (pc := 9) (register := 7)
            (zeroTarget := 13) (nonzeroTarget := 10)
            (by rfl) (by rfl)]
          rw [if_pos (by
            simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, htupleZero])]
          rw [show (5 : ℕ) = 4 + 1 by omega]
          rw [run_set_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 4) (pc := 13) (register := 0) (value := 0)
            (next := 14) (by rfl) (by rfl) hzero]
          exact run_halt_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 3) (pc := 14) (outputRegister := 0) (value := 0)
            (by rfl) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump]) hzero
        · rw [show booleanCircuitValidationOutput inputLength raw =
              Nat.pair 1 count by
            simp [booleanCircuitValidationOutput,
              booleanCircuitNodeCount, ltFlag, natOutput, nodeOutput,
              tupleFlag, count, hltZero, hnatZero, hnodeZero,
              htupleZero]]
          rw [show booleanCircuitValidationGateFuel = 14 + 1 by rfl]
          rw [run_unpairLeft_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 14) (pc := 0) (source := 0) (destination := 2)
            (next := 1) (value := ltFlag)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState]) hlt]
          rw [show (14 : ℕ) = 13 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 13) (pc := 1) (register := 2)
            (zeroTarget := 13) (nonzeroTarget := 2)
            (by rfl) (by rfl)]
          rw [if_neg (by
            simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, hltZero])]
          rw [show (13 : ℕ) = 12 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 12) (pc := 2) (source := 0) (destination := 3)
            (next := 3) (value := context)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump]) hcontext]
          rw [show (12 : ℕ) = 11 + 1 by omega]
          rw [run_unpairLeft_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 11) (pc := 3) (source := 3) (destination := 4)
            (next := 4) (value := natOutput)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, context]) hnat]
          rw [show (11 : ℕ) = 10 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 10) (pc := 4) (register := 4)
            (zeroTarget := 13) (nonzeroTarget := 5)
            (by rfl) (by rfl)]
          rw [if_neg (by
            simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, hnatZero])]
          rw [show (10 : ℕ) = 9 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 9) (pc := 5) (source := 3) (destination := 5)
            (next := 6) (value := rest)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, context]) hrest]
          rw [show (9 : ℕ) = 8 + 1 by omega]
          rw [run_unpairLeft_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 8) (pc := 6) (source := 5) (destination := 6)
            (next := 7) (value := nodeOutput)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, rest]) hnode]
          rw [show (8 : ℕ) = 7 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 7) (pc := 7) (register := 6)
            (zeroTarget := 13) (nonzeroTarget := 8)
            (by rfl) (by rfl)]
          rw [if_neg (by
            simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, hnodeZero])]
          rw [show (7 : ℕ) = 6 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 6) (pc := 8) (source := 5) (destination := 7)
            (next := 9) (value := tupleFlag)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, rest]) htuple]
          rw [show (6 : ℕ) = 5 + 1 by omega]
          rw [run_branchZero_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 5) (pc := 9) (register := 7)
            (zeroTarget := 13) (nonzeroTarget := 10)
            (by rfl) (by rfl)]
          rw [if_neg (by
            simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, htupleZero])]
          rw [show (5 : ℕ) = 4 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 4) (pc := 10) (source := 6) (destination := 8)
            (next := 11) (value := count)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, count, nodeOutput,
              booleanCircuitNodeCount]) hcount]
          rw [show (4 : ℕ) = 3 + 1 by omega]
          rw [run_set_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 3) (pc := 11) (register := 9) (value := 1)
            (next := 12) (by rfl) (by rfl) hone]
          rw [show (3 : ℕ) = 2 + 1 by omega]
          rw [run_pair_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 2) (pc := 12) (left := 9) (right := 8)
            (destination := 0) (next := 14)
            (value := Nat.pair 1 count)
            (by rfl) (by rfl)
            (by simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump]) haccept]
          exact run_halt_instruction
            (program := booleanCircuitValidationGateProgram)
            (maximumBits :=
              booleanCircuitValidationGateBits inputLength raw)
            (fuel := 1) (pc := 14) (outputRegister := 0)
            (value := Nat.pair 1 count)
            (by rfl) (by rfl)
            (by simp [NPOracleState.write, NPOracleState.jump])
            haccept

/-! ## Unique total circuit validator -/

def booleanCircuitValidationProgram : NPOracleProgram :=
  linkPrograms booleanCircuitTupleProgram <|
    linkPrograms booleanCircuitFieldProjectionProgram <|
      linkPrograms booleanCircuitNodeStageProgram <|
        linkPrograms booleanCircuitNatLoweringProgram <|
          linkPrograms booleanCircuitNatStageProgram <|
            linkPrograms booleanCircuitLtLoweringProgram <|
              linkPrograms booleanCircuitLtStageProgram
                booleanCircuitValidationGateProgram

@[simp] theorem booleanCircuitValidationProgram_oracleFree :
    OracleFree booleanCircuitValidationProgram := by
  exact oracleFree_linkPrograms booleanCircuitTupleProgram_oracleFree <|
    oracleFree_linkPrograms
      booleanCircuitFieldProjectionProgram_oracleFree <|
      oracleFree_linkPrograms booleanCircuitNodeStageProgram_oracleFree <|
        oracleFree_linkPrograms
          booleanCircuitNatLoweringProgram_oracleFree <|
          oracleFree_linkPrograms booleanCircuitNatStageProgram_oracleFree <|
            oracleFree_linkPrograms
              booleanCircuitLtLoweringProgram_oracleFree <|
              oracleFree_linkPrograms
                booleanCircuitLtStageProgram_oracleFree
                booleanCircuitValidationGateProgram_oracleFree

def booleanCircuitValidationFuel
    (inputLength raw : ℕ) : ℕ :=
  linkFuel
      (linkPrograms booleanCircuitFieldProjectionProgram <|
        linkPrograms booleanCircuitNodeStageProgram <|
          linkPrograms booleanCircuitNatLoweringProgram <|
            linkPrograms booleanCircuitNatStageProgram <|
              linkPrograms booleanCircuitLtLoweringProgram <|
                linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
      booleanCircuitTupleFuel <|
    linkFuel
        (linkPrograms booleanCircuitNodeStageProgram <|
          linkPrograms booleanCircuitNatLoweringProgram <|
            linkPrograms booleanCircuitNatStageProgram <|
              linkPrograms booleanCircuitLtLoweringProgram <|
                linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
        booleanCircuitFieldProjectionFuel <|
      linkFuel
          (linkPrograms booleanCircuitNatLoweringProgram <|
            linkPrograms booleanCircuitNatStageProgram <|
              linkPrograms booleanCircuitLtLoweringProgram <|
                linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
          (booleanCircuitNodeStageFuel inputLength raw) <|
        linkFuel
            (linkPrograms booleanCircuitNatStageProgram <|
              linkPrograms booleanCircuitLtLoweringProgram <|
                linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
            booleanCircuitNatLoweringFuel <|
          linkFuel
              (linkPrograms booleanCircuitLtLoweringProgram <|
                linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
              (booleanCircuitNatStageFuel raw) <|
            linkFuel
                (linkPrograms booleanCircuitLtStageProgram
                  booleanCircuitValidationGateProgram)
                booleanCircuitLtLoweringFuel <|
              linkFuel booleanCircuitValidationGateProgram
                (booleanCircuitLtStageFuel inputLength raw)
                booleanCircuitValidationGateFuel

def booleanCircuitValidationBits
    (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (booleanCircuitTupleBits inputLength raw) <|
      max (booleanCircuitFieldProjectionBits inputLength raw) <|
        max (booleanCircuitNodeStageBits inputLength raw) <|
          max (booleanCircuitNatLoweringBits inputLength raw) <|
            max (booleanCircuitNatStageBits inputLength raw) <|
              max (booleanCircuitLtLoweringBits inputLength raw) <|
                max (booleanCircuitLtStageBits inputLength raw)
                  (booleanCircuitValidationGateBits inputLength raw)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- The exact runner links eight independently bounded validation stages.
theorem run_booleanCircuitValidationProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram booleanCircuitValidationProgram
        (booleanCircuitValidationBits inputLength raw)
        (booleanCircuitValidationFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (booleanCircuitValidationOutput inputLength raw) := by
  let maximumBits := booleanCircuitValidationBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationBits]
  have htupleBits :
      booleanCircuitTupleBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationBits]
  have hprojectionBits :
      booleanCircuitFieldProjectionBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationBits]
  have hnodeBits :
      booleanCircuitNodeStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationBits]
  have hnatLoweringBits :
      booleanCircuitNatLoweringBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationBits]
  have hnatBits :
      booleanCircuitNatStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationBits]
  have hltLoweringBits :
      booleanCircuitLtLoweringBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationBits]
  have hltBits :
      booleanCircuitLtStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationBits]
  have hgateBits :
      booleanCircuitValidationGateBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, booleanCircuitValidationBits]
  have htuple :=
    run_bits_mono (run_booleanCircuitTupleProgram inputLength raw)
      htupleBits
  have hprojection :=
    run_bits_mono
      (run_booleanCircuitFieldProjectionProgram inputLength raw)
      hprojectionBits
  have hnode :=
    run_bits_mono
      (run_booleanCircuitNodeStageProgram inputLength raw) hnodeBits
  have hnatLowering :=
    run_bits_mono
      (run_booleanCircuitNatLoweringProgram inputLength raw)
      hnatLoweringBits
  have hnat :=
    run_bits_mono
      (run_booleanCircuitNatStageProgram inputLength raw) hnatBits
  have hltLowering :=
    run_bits_mono
      (run_booleanCircuitLtLoweringProgram inputLength raw)
      hltLoweringBits
  have hlt :=
    run_bits_mono
      (run_booleanCircuitLtStageProgram inputLength raw) hltBits
  have hgate :=
    run_bits_mono
      (run_booleanCircuitValidationGateProgram inputLength raw)
      hgateBits
  have hltTail := run_linkPrograms hpositive hlength hlt hgate
  have hltLoweringTail :=
    run_linkPrograms hpositive hlength hltLowering hltTail
  have hnatTail :=
    run_linkPrograms hpositive hlength hnat hltLoweringTail
  have hnatLoweringTail :=
    run_linkPrograms hpositive hlength hnatLowering hnatTail
  have hnodeTail :=
    run_linkPrograms hpositive hlength hnode hnatLoweringTail
  have hprojectionTail :=
    run_linkPrograms hpositive hlength hprojection hnodeTail
  have hrun :=
    run_linkPrograms hpositive hlength htuple hprojectionTail
  simpa [booleanCircuitValidationProgram,
    booleanCircuitValidationFuel] using hrun

/-! ## Semantic soundness -/

@[simp] private theorem booleanCircuitTupleOutput_encodeFields
    (nodesCode outputCode : ℕ) :
    booleanCircuitTupleOutput
        (encodeTaggedList [nodesCode, outputCode]) =
      Nat.pair 1 (Nat.pair (Nat.pair 0 nodesCode) outputCode) := by
  unfold booleanCircuitTupleOutput taggedTupleOutput
  rw [show (2 : ℕ) = [nodesCode, outputCode].length by rfl]
  rw [decodeTaggedTuple_encode]
  rfl

set_option maxHeartbeats 800000 in
-- Reconstructing the dependent circuit packages the machine-proved range facts.
/-- Every nonzero validator result decodes through the sole public Boolean
circuit codec.  The proof consumes only fields and counts produced by the fixed
machine pipeline. -/
theorem booleanCircuitValidationOutput_sound
    (inputLength raw : ℕ)
    (haccept :
      booleanCircuitValidationOutput inputLength raw ≠ 0) :
    ∃ circuit : BooleanCircuit inputLength,
      decodeBooleanCircuit inputLength raw = some circuit := by
  have hlt :
      booleanCircuitLtFlag inputLength raw ≠ 0 := by
    intro hzero
    simp [booleanCircuitValidationOutput, hzero] at haccept
  have hnat :
      canonicalNatValidationOutput
          (booleanCircuitOutputCode raw) ≠ 0 := by
    intro hzero
    simp [booleanCircuitValidationOutput, hlt, hzero] at haccept
  have hnodes :
      booleanNodeListValidationOutput inputLength
          (booleanCircuitNodesCode raw) ≠ 0 := by
    intro hzero
    simp [booleanCircuitValidationOutput, hlt, hnat, hzero] at haccept
  have htupleFlag :
      booleanCircuitTupleFlag raw ≠ 0 := by
    intro hzero
    simp [booleanCircuitValidationOutput, hlt, hnat, hnodes,
      hzero] at haccept
  have htuple :
      booleanCircuitTupleOutput raw ≠ 0 := by
    intro hzero
    apply htupleFlag
    simp [booleanCircuitTupleFlag, hzero]
  obtain ⟨fields, hfieldCount, hraw⟩ :=
    (taggedTupleOutput_ne_zero_iff 2 raw).1 htuple
  cases fields with
  | nil =>
      simp at hfieldCount
  | cons nodesCode rest =>
      cases rest with
      | nil =>
          simp at hfieldCount
      | cons outputCode rest =>
          cases rest with
          | cons extra rest =>
              simp at hfieldCount
          | nil =>
              have hnodesProjection :
                  booleanCircuitNodesCode raw = nodesCode := by
                rw [← hraw]
                simp [booleanCircuitNodesCode,
                  booleanCircuitTupleFields]
              have houtputProjection :
                  booleanCircuitOutputCode raw = outputCode := by
                rw [← hraw]
                simp [booleanCircuitOutputCode,
                  booleanCircuitTupleFields]
              obtain ⟨nodes, hnodesCode, hwellFormed⟩ :=
                booleanNodeListValidationOutput_sound
                  inputLength (booleanCircuitNodesCode raw) hnodes
              obtain ⟨output, houtputDecode⟩ :=
                (canonicalNatValidationOutput_ne_zero_iff
                  (booleanCircuitOutputCode raw)).1 hnat
              have hnodeValidation :
                  booleanNodeListValidationOutput inputLength
                      (booleanCircuitNodesCode raw) =
                    Nat.pair 1 nodes.length := by
                rw [hnodesCode]
                exact
                  booleanNodeListValidationOutput_encodeNodes
                    nodes hwellFormed
              have hnodeCount :
                  booleanCircuitNodeCount inputLength raw =
                    nodes.length := by
                simp [booleanCircuitNodeCount, hnodeValidation]
              have hnatValidation :
                  canonicalNatValidationOutput
                      (booleanCircuitOutputCode raw) =
                    Nat.pair 1 output :=
                canonicalNatValidationOutput_of_decode houtputDecode
              have hnatValue :
                  booleanCircuitNatValue raw = output := by
                simp [booleanCircuitNatValue, hnatValidation]
              have houtputLt :
                  output < nodes.length := by
                have hmachineLt :
                    booleanCircuitNatValue raw <
                      booleanCircuitNodeCount inputLength raw := by
                  simpa [booleanCircuitLtFlag,
                    booleanCircuitLtRequest] using hlt
                rw [hnatValue, hnodeCount] at hmachineLt
                exact hmachineLt
              let circuit : BooleanCircuit inputLength := {
                nodes := nodes
                output := ⟨output, houtputLt⟩
                wellFormed := hwellFormed
              }
              have hnodesCode' :
                  nodesCode =
                    encodeBalancedList
                      (nodes.map encodeBooleanNode) :=
                hnodesProjection.symm.trans hnodesCode
              have houtputCode :
                  outputCode = encodeNat output :=
                houtputProjection.symm.trans
                  (encodeNat_of_decode houtputDecode).symm
              have hcanonicalRaw :
                  raw = encodeBooleanCircuit circuit := by
                calc
                  raw =
                      encodeTaggedList [nodesCode, outputCode] :=
                    hraw.symm
                  _ =
                      encodeTaggedList
                        [encodeBalancedList
                            (nodes.map encodeBooleanNode),
                          encodeNat output] := by
                    rw [hnodesCode', houtputCode]
                  _ = encodeBooleanCircuit circuit := by
                    rfl
              refine ⟨circuit, ?_⟩
              rw [hcanonicalRaw]
              exact decodeBooleanCircuit_encode circuit

/-! ## Typed-code refinement -/

@[simp] theorem booleanCircuitTupleOutput_encodeBooleanCircuit
    {inputLength : ℕ} (circuit : BooleanCircuit inputLength) :
    booleanCircuitTupleOutput (encodeBooleanCircuit circuit) =
      Nat.pair 1
        (Nat.pair
          (Nat.pair 0
            (encodeBalancedList
              (circuit.nodes.map encodeBooleanNode)))
          (encodeNat circuit.output.val)) := by
  unfold booleanCircuitTupleOutput taggedTupleOutput encodeBooleanCircuit
  rw [show (2 : ℕ) =
      [encodeBalancedList (circuit.nodes.map encodeBooleanNode),
        encodeNat circuit.output.val].length by rfl]
  rw [decodeTaggedTuple_encode]
  rfl

@[simp] theorem booleanCircuitTupleFlag_encodeBooleanCircuit
    {inputLength : ℕ} (circuit : BooleanCircuit inputLength) :
    booleanCircuitTupleFlag (encodeBooleanCircuit circuit) = 1 := by
  simp [booleanCircuitTupleFlag]

@[simp] theorem booleanCircuitNodesCode_encodeBooleanCircuit
    {inputLength : ℕ} (circuit : BooleanCircuit inputLength) :
    booleanCircuitNodesCode (encodeBooleanCircuit circuit) =
      encodeBalancedList (circuit.nodes.map encodeBooleanNode) := by
  simp [booleanCircuitNodesCode, booleanCircuitTupleFields]

@[simp] theorem booleanCircuitOutputCode_encodeBooleanCircuit
    {inputLength : ℕ} (circuit : BooleanCircuit inputLength) :
    booleanCircuitOutputCode (encodeBooleanCircuit circuit) =
      encodeNat circuit.output.val := by
  simp [booleanCircuitOutputCode, booleanCircuitTupleFields]

@[simp] theorem booleanCircuitNodeCount_encodeBooleanCircuit
    {inputLength : ℕ} (circuit : BooleanCircuit inputLength) :
    booleanCircuitNodeCount inputLength (encodeBooleanCircuit circuit) =
      circuit.nodes.length := by
  simp [booleanCircuitNodeCount]

@[simp] theorem booleanCircuitNatValue_encodeBooleanCircuit
    {inputLength : ℕ} (circuit : BooleanCircuit inputLength) :
    booleanCircuitNatValue (encodeBooleanCircuit circuit) =
      circuit.output.val := by
  simp [booleanCircuitNatValue]

@[simp] theorem booleanCircuitLtFlag_encodeBooleanCircuit
    {inputLength : ℕ} (circuit : BooleanCircuit inputLength) :
    booleanCircuitLtFlag inputLength (encodeBooleanCircuit circuit) = 1 := by
  simp [booleanCircuitLtFlag, booleanCircuitLtRequest,
    circuit.output.isLt]

@[simp] theorem booleanCircuitValidationOutput_encodeBooleanCircuit
    {inputLength : ℕ} (circuit : BooleanCircuit inputLength) :
    booleanCircuitValidationOutput inputLength
        (encodeBooleanCircuit circuit) =
      Nat.pair 1 circuit.nodes.length := by
  simp [booleanCircuitValidationOutput]

theorem booleanCircuitValidationOutput_ne_zero_iff_decodeBooleanCircuit
    (inputLength raw : ℕ) :
    booleanCircuitValidationOutput inputLength raw ≠ 0 ↔
      ∃ circuit : BooleanCircuit inputLength,
        decodeBooleanCircuit inputLength raw = some circuit := by
  constructor
  · exact booleanCircuitValidationOutput_sound inputLength raw
  · rintro ⟨circuit, hdecode⟩
    have hcode := encodeBooleanCircuit_of_decode hdecode
    rw [← hcode]
    simp

theorem booleanCircuitValidationOutput_eq_pair_iff
    (inputLength raw count : ℕ) :
    booleanCircuitValidationOutput inputLength raw =
        Nat.pair 1 count ↔
      ∃ circuit : BooleanCircuit inputLength,
        decodeBooleanCircuit inputLength raw = some circuit ∧
          circuit.size = count := by
  constructor
  · intro houtput
    have hnonzero :
        booleanCircuitValidationOutput inputLength raw ≠ 0 := by
      rw [houtput]
      have hleft := Nat.left_le_pair 1 count
      omega
    obtain ⟨circuit, hdecode⟩ :=
      booleanCircuitValidationOutput_sound inputLength raw hnonzero
    have hcode := encodeBooleanCircuit_of_decode hdecode
    have hcircuitOutput :
        booleanCircuitValidationOutput inputLength raw =
          Nat.pair 1 circuit.nodes.length := by
      rw [← hcode]
      exact booleanCircuitValidationOutput_encodeBooleanCircuit circuit
    have hpairs :
        Nat.pair 1 circuit.nodes.length = Nat.pair 1 count :=
      hcircuitOutput.symm.trans houtput
    have hcount :
        circuit.nodes.length = count := by
      simpa using
        congrArg (fun code => (Nat.unpair code).2) hpairs
    exact ⟨circuit, hdecode, by
      simpa [BooleanCircuit.size] using hcount⟩
  · rintro ⟨circuit, hdecode, hsize⟩
    have hcode := encodeBooleanCircuit_of_decode hdecode
    rw [← hcode]
    rw [booleanCircuitValidationOutput_encodeBooleanCircuit]
    simpa [BooleanCircuit.size] using hsize

end NearCubicWires.CanonicalBooleanCircuitValidationProgram
