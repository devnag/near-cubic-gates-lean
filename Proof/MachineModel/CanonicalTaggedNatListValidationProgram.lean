import Proof.MachineModel.BalancedClauseStreamFlattenProgram
import Proof.Circuits.CanonicalBalancedBuilder
import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalNatValidationProgram
import Proof.MachineModel.CanonicalTaggedListValidationProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Canonical natural validation over one tagged field list

Fixed witness records repeatedly contain canonical naturals.  This module
provides their single list-level execution path: validate the tagged spine,
convert it to the sole balanced ABI, attach register-one to every call, run the
total canonical-natural validator, and flatten the results back to a tagged
stream.  Invalid spines become the empty stream; malformed fields remain zero
atoms, so the record-specific continuation can reject them without reparsing
the public bytes.
-/

namespace NearCubicWires.CanonicalTaggedNatListValidationProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedListValidationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

def taggedNatFieldCodes (raw : ℕ) : List ℕ :=
  (decodeTaggedList raw).getD []

def taggedNatFieldOutputs (raw : ℕ) : List ℕ :=
  (taggedNatFieldCodes raw).map canonicalNatValidationOutput

def taggedNatListValidationOutput (raw : ℕ) : ℕ :=
  encodeTaggedList (taggedNatFieldOutputs raw)

/-! ## Retain exactly one validated tagged spine -/

private def duplicateTaggedRawProgram : NPOracleProgram :=
  [.pair 0 0 0 1, .halt 0]

private def duplicateTaggedRawBits (raw : ℕ) : ℕ :=
  max (natBitLength raw) (natBitLength (Nat.pair raw raw))

private theorem duplicateTaggedRawProgram_oracleFree :
    OracleFree duplicateTaggedRawProgram := by
  rfl

private theorem run_duplicateTaggedRawProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram duplicateTaggedRawProgram
        (duplicateTaggedRawBits raw) 2
        (initialNPOracleState inputLength raw) =
      some (Nat.pair raw raw) := by
  have houtput :
      natBitLength (Nat.pair raw raw) ≤ duplicateTaggedRawBits raw :=
    Nat.le_max_right _ _
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := duplicateTaggedRawProgram)
    (maximumBits := duplicateTaggedRawBits raw)
    (fuel := 1) (pc := 0) (left := 0) (right := 0)
    (destination := 0) (next := 1)
    (value := Nat.pair raw raw)
    (by rfl) (by rfl)
    (by simp [initialNPOracleState]) houtput]
  exact run_halt_instruction
    (program := duplicateTaggedRawProgram)
    (maximumBits := duplicateTaggedRawBits raw)
    (fuel := 0) (pc := 1) (outputRegister := 0)
    (value := Nat.pair raw raw)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

private def taggedListRetainGateOutput
    (flag raw : ℕ) : ℕ :=
  if flag = 0 then 0 else raw

private def taggedListRetainGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 3 2
  , .unpairRight 0 0 4
  , .set 0 0 4
  , .halt 0
  ]

private theorem taggedListRetainGateProgram_oracleFree :
    OracleFree taggedListRetainGateProgram := by
  rfl

private def taggedListRetainGateBits
    (flag raw : ℕ) : ℕ :=
  natBitLength (Nat.pair flag raw)

private theorem run_taggedListRetainGateProgram
    (inputLength flag raw : ℕ) :
    runNPOracleProgram taggedListRetainGateProgram
        (taggedListRetainGateBits flag raw) 4
        (initialNPOracleState inputLength (Nat.pair flag raw)) =
      some (taggedListRetainGateOutput flag raw) := by
  let maximumBits := taggedListRetainGateBits flag raw
  have hflag : natBitLength flag ≤ maximumBits :=
    natBitLength_mono (Nat.left_le_pair flag raw)
  have hraw : natBitLength raw ≤ maximumBits :=
    natBitLength_mono (Nat.right_le_pair flag raw)
  have hzero : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le raw)).trans hraw
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := taggedListRetainGateProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := flag) (by rfl) (by rfl)
    (by simp [initialNPOracleState]) hflag]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_branchZero_instruction
    (program := taggedListRetainGateProgram)
    (maximumBits := maximumBits) (fuel := 2)
    (pc := 1) (register := 2) (zeroTarget := 3)
    (nonzeroTarget := 2) (by rfl) (by rfl)]
  by_cases hflagZero : flag = 0
  · rw [if_pos (by simp [hflagZero])]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_set_instruction
      (program := taggedListRetainGateProgram)
      (maximumBits := maximumBits) (fuel := 1)
      (pc := 3) (register := 0) (value := 0) (next := 4)
      (by rfl) (by rfl) hzero]
    rw [show taggedListRetainGateOutput flag raw = 0 by
      simp [taggedListRetainGateOutput, hflagZero]]
    exact run_halt_instruction
      (program := taggedListRetainGateProgram)
      (maximumBits := maximumBits) (fuel := 0)
      (pc := 4) (outputRegister := 0) (value := 0)
      (by rfl) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump]) hzero
  · rw [if_neg (by simp [hflagZero])]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := taggedListRetainGateProgram)
      (maximumBits := maximumBits) (fuel := 1)
      (pc := 2) (source := 0) (destination := 0) (next := 4)
      (value := raw) (by rfl) (by rfl)
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump])
      hraw]
    rw [show taggedListRetainGateOutput flag raw = raw by
      simp [taggedListRetainGateOutput, hflagZero]]
    exact run_halt_instruction
      (program := taggedListRetainGateProgram)
      (maximumBits := maximumBits) (fuel := 0)
      (pc := 4) (outputRegister := 0) (value := raw)
      (by rfl) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump]) hraw

private def taggedListRetainProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms duplicateTaggedRawProgram <|
      preserveRightProgram taggedListValidationProgram)
    taggedListRetainGateProgram

private theorem taggedListRetainProgram_oracleFree :
    OracleFree taggedListRetainProgram := by
  exact oracleFree_linkPrograms
    (oracleFree_linkPrograms duplicateTaggedRawProgram_oracleFree <|
      preserveRightProgram_oracleFree taggedListValidationProgram
        taggedListValidationProgram_oracleFree)
    taggedListRetainGateProgram_oracleFree

private def taggedListRetainFuel (raw : ℕ) : ℕ :=
  linkFuel taggedListRetainGateProgram
    (linkFuel (preserveRightProgram taggedListValidationProgram)
      2 (preserveRightFuel (taggedListValidationFuel raw)))
    4

private def taggedListRetainBits
    (inputLength raw : ℕ) : ℕ :=
  let flag := (taggedListValid raw).toNat
  max 1 <| max (natBitLength inputLength) <|
    max (duplicateTaggedRawBits raw) <|
      max
        (preserveRightBits
          (taggedListValidationBits raw)
          raw raw flag)
        (taggedListRetainGateBits flag raw)

private theorem taggedListRetainGateOutput_eq
    (raw : ℕ) :
    taggedListRetainGateOutput
        (taggedListValid raw).toNat raw =
      encodeTaggedList (taggedNatFieldCodes raw) := by
  cases hdecode : decodeTaggedList raw with
  | none =>
      have hvalid : taggedListValid raw = false := by
        cases hresult : taggedListValid raw with
        | false => rfl
        | true =>
            have :=
              (taggedListValid_eq_true_iff_decode raw).mp hresult
            simp [hdecode] at this
      simp [taggedListRetainGateOutput, taggedNatFieldCodes,
        hdecode, hvalid, encodeTaggedList]
  | some values =>
      have hvalid : taggedListValid raw = true :=
        (taggedListValid_eq_true_iff_decode raw).mpr
          (by simp [hdecode])
      have hcode : encodeTaggedList values = raw :=
        encodeTaggedList_of_decode hdecode
      simp [taggedListRetainGateOutput, taggedNatFieldCodes,
        hdecode, hvalid, hcode]

private theorem run_taggedListRetainProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram taggedListRetainProgram
        (taggedListRetainBits inputLength raw)
        (taggedListRetainFuel raw)
        (initialNPOracleState inputLength raw) =
      some (encodeTaggedList (taggedNatFieldCodes raw)) := by
  let flag := (taggedListValid raw).toNat
  let maximumBits := taggedListRetainBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, taggedListRetainBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, taggedListRetainBits]
  have hduplicate : duplicateTaggedRawBits raw ≤ maximumBits := by
    simp [maximumBits, taggedListRetainBits]
  have hvalidation :
      preserveRightBits (taggedListValidationBits raw)
          raw raw flag ≤ maximumBits := by
    simp [maximumBits, taggedListRetainBits, flag]
  have hgate :
      taggedListRetainGateBits flag raw ≤ maximumBits := by
    simp [maximumBits, taggedListRetainBits, flag]
  have hfirst :
      runNPOracleProgram duplicateTaggedRawProgram maximumBits 2
          (initialNPOracleState inputLength raw) =
        some (Nat.pair raw raw) :=
    run_bits_mono
      (run_duplicateTaggedRawProgram inputLength raw) hduplicate
  have hsecond :
      runNPOracleProgram
          (preserveRightProgram taggedListValidationProgram)
          maximumBits
          (preserveRightFuel (taggedListValidationFuel raw))
          (initialNPOracleState inputLength (Nat.pair raw raw)) =
        some (Nat.pair flag raw) := by
    exact run_bits_mono
      (run_preserveRightProgram taggedListValidationProgram
        inputLength (taggedListValidationBits raw)
        (taggedListValidationFuel raw) raw raw flag
        (run_taggedListValidationProgram inputLength raw))
      hvalidation
  have hfirstSecond :
      runNPOracleProgram
          (linkPrograms duplicateTaggedRawProgram <|
            preserveRightProgram taggedListValidationProgram)
          maximumBits
          (linkFuel (preserveRightProgram taggedListValidationProgram)
            2 (preserveRightFuel (taggedListValidationFuel raw)))
          (initialNPOracleState inputLength raw) =
        some (Nat.pair flag raw) :=
    run_linkPrograms hpositive hlength hfirst hsecond
  have hthird :
      runNPOracleProgram taggedListRetainGateProgram maximumBits 4
          (initialNPOracleState inputLength (Nat.pair flag raw)) =
        some (encodeTaggedList (taggedNatFieldCodes raw)) := by
    rw [← taggedListRetainGateOutput_eq raw]
    exact run_bits_mono
      (run_taggedListRetainGateProgram inputLength flag raw) hgate
  exact run_linkPrograms hpositive hlength hfirstSecond hthird

/-! ## One shared field-validation pipeline -/

private def taggedNatRequestOutput (request : ℕ) : ℕ :=
  canonicalNatValidationOutput (Nat.unpair request).2

private def taggedNatRequestFuel (request : ℕ) : ℕ :=
  canonicalNatValidationFuel (Nat.unpair request).2

def taggedNatListValidationProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms
      (linkPrograms
        (linkPrograms
          (linkPrograms taggedListRetainProgram
            taggedToBalancedProgram)
          nativeInputRequestTreeProgram)
        (balancedCallProgram canonicalNatValidationProgram))
      balancedBitSingletonProgram)
    balancedClauseStreamFlattenProgram

@[simp] theorem taggedNatListValidationProgram_oracleFree :
    OracleFree taggedNatListValidationProgram := by
  exact oracleFree_linkPrograms
    (oracleFree_linkPrograms
      (oracleFree_linkPrograms
        (oracleFree_linkPrograms
          (oracleFree_linkPrograms
            taggedListRetainProgram_oracleFree
            taggedToBalancedProgram_oracleFree)
          nativeInputRequestTreeProgram_oracleFree)
        (balancedCallProgram_oracleFree
          canonicalNatValidationProgram_oracleFree))
      balancedBitSingletonProgram_oracleFree)
    balancedClauseStreamFlattenProgram_oracleFree

private def taggedNatRequests
    (inputLength raw : ℕ) : List ℕ :=
  (taggedNatFieldCodes raw).map
    (nativeInputRequest inputLength)

private def taggedNatOutputTree (raw : ℕ) :
    BalancedTraversalTree :=
  balancedTraversalTree (taggedNatFieldOutputs raw)

private def taggedNatSingletonTree (raw : ℕ) :
    BalancedTraversalTree :=
  (taggedNatOutputTree raw).map singletonTaggedBit

def taggedNatListValidationFuel
    (inputLength raw : ℕ) : ℕ :=
  let fields := taggedNatFieldCodes raw
  let requests := taggedNatRequests inputLength raw
  let outputTree := taggedNatOutputTree raw
  let singletonTree := taggedNatSingletonTree raw
  linkFuel balancedClauseStreamFlattenProgram
    (linkFuel balancedBitSingletonProgram
      (linkFuel (balancedCallProgram canonicalNatValidationProgram)
        (linkFuel nativeInputRequestTreeProgram
          (linkFuel taggedToBalancedProgram
            (taggedListRetainFuel raw)
            (taggedToBalancedFuel fields))
          (nativeInputRequestTreeFuel fields))
        (balancedCallFuel canonicalNatValidationProgram
          taggedNatRequestFuel requests))
      (balancedBitSingletonTreeFuel outputTree))
    (balancedTreeStreamFlattenFuel singletonTree)

private def taggedNatCalleeBits
    (inputLength raw : ℕ) : ℕ :=
  ((taggedNatFieldCodes raw).map fun field =>
      canonicalNatValidationBits inputLength field).foldr max 0

private theorem member_le_foldr_max
    {value : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact le_max_left _ _
      · exact (inductionHypothesis htail).trans (le_max_right _ _)

def taggedNatListValidationBits
    (inputLength raw : ℕ) : ℕ :=
  let fields := taggedNatFieldCodes raw
  let requests := taggedNatRequests inputLength raw
  let outputTree := taggedNatOutputTree raw
  let singletonTree := taggedNatSingletonTree raw
  max 1 <| max (natBitLength inputLength) <|
    max (taggedListRetainBits inputLength raw) <|
      max (taggedToBalancedRegisterBitsFor inputLength fields) <|
        max (nativeInputRequestTreeBits inputLength fields) <|
          max (taggedNatCalleeBits inputLength raw) <|
            max (balancedCallRequiredBits taggedNatRequestOutput requests) <|
              max (balancedBitSingletonTreeBits outputTree)
                (balancedTreeStreamFlattenMaximumBits singletonTree)

private theorem taggedNatRequests_outputs
    (inputLength raw : ℕ) :
    (taggedNatRequests inputLength raw).map
        taggedNatRequestOutput =
      taggedNatFieldOutputs raw := by
  simp [taggedNatRequests, taggedNatRequestOutput,
    taggedNatFieldOutputs, nativeInputRequest,
    Function.comp_def]

private theorem taggedNatSingletonTree_values
    (raw : ℕ) :
    treeStreamValues (taggedNatSingletonTree raw) =
      taggedNatFieldOutputs raw := by
  have hsingleton :
      ∀ values : List ℕ,
        List.flatMap streamOfCode
            (values.map singletonTaggedBit) =
          values := by
    intro values
    induction values with
    | nil => rfl
    | cons value values inductionHypothesis =>
        simp [singletonTaggedBit, streamOfCode,
          inductionHypothesis]
  simpa [taggedNatSingletonTree, taggedNatOutputTree,
    treeStreamValues, balancedTraversalTree_atoms] using
    hsingleton (taggedNatFieldOutputs raw)

theorem run_taggedNatListValidationProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram taggedNatListValidationProgram
        (taggedNatListValidationBits inputLength raw)
        (taggedNatListValidationFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (taggedNatListValidationOutput raw) := by
  let fields := taggedNatFieldCodes raw
  let requests := taggedNatRequests inputLength raw
  let outputs := taggedNatFieldOutputs raw
  let outputTree := taggedNatOutputTree raw
  let singletonTree := taggedNatSingletonTree raw
  let maximumBits := taggedNatListValidationBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, taggedNatListValidationBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, taggedNatListValidationBits]
  have hretain :
      taggedListRetainBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, taggedNatListValidationBits]
  have hbalance :
      taggedToBalancedRegisterBitsFor inputLength fields ≤
        maximumBits := by
    simp [maximumBits, taggedNatListValidationBits, fields]
  have hrequests :
      nativeInputRequestTreeBits inputLength fields ≤ maximumBits := by
    simp [maximumBits, taggedNatListValidationBits, fields]
  have hcallee :
      taggedNatCalleeBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, taggedNatListValidationBits]
  have hcall :
      balancedCallRequiredBits taggedNatRequestOutput requests ≤
        maximumBits := by
    simp [maximumBits, taggedNatListValidationBits, requests]
  have hsingleton :
      balancedBitSingletonTreeBits outputTree ≤ maximumBits := by
    simp [maximumBits, taggedNatListValidationBits, outputTree]
  have hflatten :
      balancedTreeStreamFlattenMaximumBits singletonTree ≤
        maximumBits := by
    simp [maximumBits, taggedNatListValidationBits, singletonTree]
  have hrunRetain :
      runNPOracleProgram taggedListRetainProgram maximumBits
          (taggedListRetainFuel raw)
          (initialNPOracleState inputLength raw) =
        some (encodeTaggedList fields) := by
    simpa [fields] using
      run_bits_mono
        (run_taggedListRetainProgram inputLength raw) hretain
  have hrunBalance :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (taggedToBalancedFuel fields)
          (initialNPOracleState inputLength
            (encodeTaggedList fields)) =
        some (encodeBalancedList fields) :=
    run_bits_mono
      (run_taggedToBalancedProgram_from inputLength fields) hbalance
  have hrunRetainBalance :
      runNPOracleProgram
          (linkPrograms taggedListRetainProgram
            taggedToBalancedProgram)
          maximumBits
          (linkFuel taggedToBalancedProgram
            (taggedListRetainFuel raw)
            (taggedToBalancedFuel fields))
          (initialNPOracleState inputLength raw) =
        some (encodeBalancedList fields) :=
    run_linkPrograms hpositive hlength hrunRetain hrunBalance
  have hrunRequests :
      runNPOracleProgram nativeInputRequestTreeProgram maximumBits
          (nativeInputRequestTreeFuel fields)
          (initialNPOracleState inputLength
            (encodeBalancedList fields)) =
        some (encodeBalancedList requests) := by
    simpa [requests, taggedNatRequests, fields] using
      run_bits_mono
        (run_nativeInputRequestTreeProgram inputLength fields)
        hrequests
  have hrunThroughRequests :
      runNPOracleProgram
          (linkPrograms
            (linkPrograms taggedListRetainProgram
              taggedToBalancedProgram)
            nativeInputRequestTreeProgram)
          maximumBits
          (linkFuel nativeInputRequestTreeProgram
            (linkFuel taggedToBalancedProgram
              (taggedListRetainFuel raw)
              (taggedToBalancedFuel fields))
            (nativeInputRequestTreeFuel fields))
          (initialNPOracleState inputLength raw) =
        some (encodeBalancedList requests) :=
    run_linkPrograms hpositive hlength
      hrunRetainBalance hrunRequests
  have hrunCall :
      runNPOracleProgram
          (balancedCallProgram canonicalNatValidationProgram)
          maximumBits
          (balancedCallFuel canonicalNatValidationProgram
            taggedNatRequestFuel requests)
          (initialNPOracleState inputLength
            (encodeBalancedList requests)) =
        some (encodeBalancedList outputs) := by
    change
      runNPOracleProgram
          (balancedCallProgram canonicalNatValidationProgram)
          maximumBits
          (balancedCallFuel canonicalNatValidationProgram
            taggedNatRequestFuel requests)
          (initialNPOracleState inputLength
            (encodeBalancedList requests)) =
        some (encodeBalancedList (taggedNatFieldOutputs raw))
    rw [← taggedNatRequests_outputs inputLength raw]
    apply run_balancedCallProgram_from inputLength requests
      taggedNatRequestFuel taggedNatRequestOutput hcall
    intro request hrequest
    rcases List.mem_map.mp hrequest with
      ⟨field, hfield, rfl⟩
    have hfieldBits :
        canonicalNatValidationBits inputLength field ≤
          maximumBits := by
      apply le_trans ?_ hcallee
      unfold taggedNatCalleeBits
      exact member_le_foldr_max <|
        List.mem_map.mpr ⟨field, hfield, rfl⟩
    simpa [taggedNatRequestFuel, taggedNatRequestOutput,
      nativeInputRequest] using
      run_bits_mono
        (run_canonicalNatValidationProgram inputLength field)
        hfieldBits
  have hrunThroughCall :
      runNPOracleProgram
          (linkPrograms
            (linkPrograms
              (linkPrograms taggedListRetainProgram
                taggedToBalancedProgram)
              nativeInputRequestTreeProgram)
            (balancedCallProgram canonicalNatValidationProgram))
          maximumBits
          (linkFuel
            (balancedCallProgram canonicalNatValidationProgram)
            (linkFuel nativeInputRequestTreeProgram
              (linkFuel taggedToBalancedProgram
                (taggedListRetainFuel raw)
                (taggedToBalancedFuel fields))
              (nativeInputRequestTreeFuel fields))
            (balancedCallFuel canonicalNatValidationProgram
              taggedNatRequestFuel requests))
          (initialNPOracleState inputLength raw) =
        some (encodeBalancedList outputs) :=
    run_linkPrograms hpositive hlength hrunThroughRequests hrunCall
  have hrunSingleton :
      runNPOracleProgram balancedBitSingletonProgram maximumBits
          (balancedBitSingletonTreeFuel outputTree)
          (initialNPOracleState inputLength outputTree.code) =
        some singletonTree.code := by
    simpa [singletonTree, taggedNatSingletonTree] using
      run_bits_mono
        (run_balancedBitSingletonTreeProgram inputLength outputTree)
        hsingleton
  have houtputCode :
      outputTree.code = encodeBalancedList outputs := by
    simpa [outputTree, taggedNatOutputTree, outputs] using
      balancedTraversalTree_code outputs
  have hrunThroughSingleton :
      runNPOracleProgram
          (linkPrograms
            (linkPrograms
              (linkPrograms
                (linkPrograms taggedListRetainProgram
                  taggedToBalancedProgram)
                nativeInputRequestTreeProgram)
              (balancedCallProgram canonicalNatValidationProgram))
            balancedBitSingletonProgram)
          maximumBits
          (linkFuel balancedBitSingletonProgram
            (linkFuel
              (balancedCallProgram canonicalNatValidationProgram)
              (linkFuel nativeInputRequestTreeProgram
                (linkFuel taggedToBalancedProgram
                  (taggedListRetainFuel raw)
                  (taggedToBalancedFuel fields))
                (nativeInputRequestTreeFuel fields))
              (balancedCallFuel canonicalNatValidationProgram
                taggedNatRequestFuel requests))
            (balancedBitSingletonTreeFuel outputTree))
          (initialNPOracleState inputLength raw) =
        some singletonTree.code := by
    apply run_linkPrograms hpositive hlength hrunThroughCall
    simpa [houtputCode] using hrunSingleton
  have hsingletonValid :
      ∀ atom ∈ singletonTree.atoms,
        encodeTaggedList (streamOfCode atom) = atom := by
    intro atom hatom
    have hatomMapped :
        atom ∈ outputs.map singletonTaggedBit := by
      simpa [singletonTree, taggedNatSingletonTree,
        outputTree, taggedNatOutputTree,
        balancedTraversalTree_atoms] using hatom
    rcases List.mem_map.mp hatomMapped with
      ⟨output, _houtput, rfl⟩
    simp [singletonTaggedBit, streamOfCode]
  have hrunFlatten :
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits
          (balancedTreeStreamFlattenFuel singletonTree)
          (initialNPOracleState inputLength singletonTree.code) =
        some (encodeTaggedList outputs) := by
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits
          (balancedTreeStreamFlattenFuel singletonTree)
          (initialNPOracleState inputLength singletonTree.code) =
        some (encodeTaggedList (taggedNatFieldOutputs raw))
    rw [← taggedNatSingletonTree_values raw]
    exact run_bits_mono
      (run_balancedClauseStreamFlattenTree singletonTree
        inputLength hsingletonValid)
      hflatten
  have hrun :=
    run_linkPrograms hpositive hlength
      hrunThroughSingleton hrunFlatten
  simpa [taggedNatListValidationProgram,
    taggedNatListValidationFuel, taggedNatListValidationOutput,
    fields, requests, outputs, outputTree, singletonTree]
    using hrun

theorem taggedNatFieldOutputs_eq_zero_iff
    (raw : ℕ) (index : Fin (taggedNatFieldOutputs raw).length) :
    (taggedNatFieldOutputs raw).get index = 0 ↔
      decodeNat
        ((taggedNatFieldCodes raw).get
          ⟨index.val, by
            simpa [taggedNatFieldOutputs] using index.isLt⟩) =
        none := by
  rw [show
    (taggedNatFieldOutputs raw).get index =
      canonicalNatValidationOutput
        ((taggedNatFieldCodes raw).get
          ⟨index.val, by
            simpa [taggedNatFieldOutputs] using index.isLt⟩) by
      simp [taggedNatFieldOutputs]]
  exact canonicalNatValidationOutput_eq_zero_iff _

end NearCubicWires.CanonicalTaggedNatListValidationProgram
