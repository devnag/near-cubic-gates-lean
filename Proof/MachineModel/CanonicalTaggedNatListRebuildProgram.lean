import Batteries.Tactic.OpenPrivate
import Proof.MachineModel.CanonicalTaggedSpineIndexProgram
import Proof.Circuits.ValidatorCanonicalizerRebuildLedger

namespace NearCubicWires.CanonicalTaggedNatListRebuildProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedAtomIndexProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedMidpointRebuildProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalGateAtomHeadListProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalSignedAtomRequestProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.CanonicalTaggedSpineIndexProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.ValidatorCanonicalizerRebuildLedger
open NearCubicWires.VerifiedLinker

open private taggedListRetainProgram taggedListRetainProgram_oracleFree
  taggedListRetainFuel taggedListRetainBits run_taggedListRetainProgram
  taggedNatOutputTree taggedNatSingletonTree taggedNatSingletonTree_values from
  Proof.MachineModel.CanonicalTaggedNatListValidationProgram

private theorem le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 1 := by
  induction values with
  | nil => simp at hmem
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmem).trans (Nat.le_max_right _ _)

def taggedNatFieldValidateProgram : NPOracleProgram :=
  linkPrograms taggedSpineSelectProgram canonicalNatValidationRebuildProgram

@[simp] theorem taggedNatFieldValidateProgram_oracleFree :
    OracleFree taggedNatFieldValidateProgram :=
  oracleFree_linkPrograms taggedSpineSelectProgram_oracleFree
    canonicalNatValidationRebuildProgram_oracleFree

def taggedNatFieldValidateFuel (index : ℕ) (fields : List ℕ) : ℕ :=
  linkFuel canonicalNatValidationRebuildProgram (taggedSpineSelectFuel index)
    (canonicalNatValidationRebuildFuel index (fields.getD index 0))

def taggedNatFieldValidateBits (index : ℕ) (fields : List ℕ) : ℕ :=
  max 1 <| max (natBitLength index) <|
    max (taggedSpineSelectBits index fields)
      (canonicalNatValidationRebuildBits index (fields.getD index 0))

theorem run_taggedNatFieldValidateProgram (index : ℕ) (fields : List ℕ) :
    runNPOracleProgram taggedNatFieldValidateProgram
        (taggedNatFieldValidateBits index fields)
        (taggedNatFieldValidateFuel index fields)
        (initialNPOracleState index (encodeTaggedList fields)) =
      some (canonicalNatValidationOutput (fields.getD index 0)) := by
  let maximumBits := taggedNatFieldValidateBits index fields
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, taggedNatFieldValidateBits]
  have hlength : natBitLength index ≤ maximumBits := by
    simp [maximumBits, taggedNatFieldValidateBits]
  have hselect : taggedSpineSelectBits index fields ≤ maximumBits := by
    simp [maximumBits, taggedNatFieldValidateBits]
  have hvalidate :
      canonicalNatValidationRebuildBits index (fields.getD index 0) ≤
        maximumBits := by
    simp [maximumBits, taggedNatFieldValidateBits]
  exact run_linkPrograms hpositive hlength
    (run_bits_mono (run_taggedSpineSelectProgram index fields) hselect)
    (run_bits_mono
      (run_canonicalNatValidationRebuildProgram index (fields.getD index 0))
      hvalidate)

/-! ## §2 The indexed request family -/

/-- One request per field index, all against the same tagged code. -/
def taggedNatIndexRequests (raw : ℕ) : List ℕ :=
  (List.range (taggedNatFieldCodes raw).length).map fun index =>
    Nat.pair index (encodeTaggedList (taggedNatFieldCodes raw))

/-- The validated field a request selects. -/
def taggedNatIndexOutput (raw request : ℕ) : ℕ :=
  canonicalNatValidationOutput
    ((taggedNatFieldCodes raw).getD (Nat.unpair request).1 0)

/-- **Reading every index rebuilds the validated field list.** -/
theorem map_taggedNatIndexOutput (raw : ℕ) :
    (taggedNatIndexRequests raw).map (taggedNatIndexOutput raw) =
      taggedNatFieldOutputs raw := by
  have hmap :
      (taggedNatIndexRequests raw).map (taggedNatIndexOutput raw) =
        ((List.range (taggedNatFieldCodes raw).length).map
          fun index => (taggedNatFieldCodes raw).getD index 0).map
          canonicalNatValidationOutput := by
    simp only [taggedNatIndexRequests, List.map_map]
    refine List.map_congr_left ?_
    intro index _hindex
    simp [taggedNatIndexOutput]
  rw [hmap, map_range_getD, taggedNatFieldOutputs]

theorem mem_taggedNatIndexRequests {raw index : ℕ}
    (hindex : index < (taggedNatFieldCodes raw).length) :
    Nat.pair index (encodeTaggedList (taggedNatFieldCodes raw)) ∈
      taggedNatIndexRequests raw :=
  List.mem_map.mpr ⟨index, List.mem_range.mpr hindex, rfl⟩

/-- Width of every emitted request. -/
def taggedNatIndexRequestBits (raw : ℕ) : ℕ :=
  ((taggedNatIndexRequests raw).map natBitLength).foldr max 1

def taggedNatFieldValidateMaximumBits (raw : ℕ) : ℕ :=
  ((List.range (taggedNatFieldCodes raw).length).map fun index =>
    taggedNatFieldValidateBits index (taggedNatFieldCodes raw)).foldr max 1

theorem taggedNatIndexRequestBits_of_mem {raw index : ℕ}
    (hindex : index < (taggedNatFieldCodes raw).length) :
    natBitLength (Nat.pair index (encodeTaggedList (taggedNatFieldCodes raw))) ≤
      taggedNatIndexRequestBits raw :=
  le_foldr_max_of_mem
    (List.mem_map.mpr ⟨_, mem_taggedNatIndexRequests hindex, rfl⟩)

theorem taggedNatFieldValidateMaximumBits_of_mem {raw index : ℕ}
    (hindex : index < (taggedNatFieldCodes raw).length) :
    taggedNatFieldValidateBits index (taggedNatFieldCodes raw) ≤
      taggedNatFieldValidateMaximumBits raw :=
  le_foldr_max_of_mem
    (List.mem_map.mpr ⟨index, List.mem_range.mpr hindex, rfl⟩)

/-! ## §3 The rebuilt tagged-nat list validator -/

/-- **The tagged-nat list validator, over the indexed spine.**  The builder and
the frozen natural validator are both gone; the retained spine, the generated
request list, the singleton tagging and the stream flattener are the frozen
stages, unchanged. -/
def taggedNatListValidationRebuildProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms
      (linkPrograms
        (linkPrograms
          (linkPrograms taggedListRetainProgram taggedSpineLengthProgram)
          (atomRequestListProgram identityStageProgram))
        (balancedCallProgram taggedNatFieldValidateProgram))
      balancedBitSingletonProgram)
    balancedClauseStreamFlattenProgram

@[simp] theorem taggedNatListValidationRebuildProgram_oracleFree :
    OracleFree taggedNatListValidationRebuildProgram :=
  oracleFree_linkPrograms
    (oracleFree_linkPrograms
      (oracleFree_linkPrograms
        (oracleFree_linkPrograms
          (oracleFree_linkPrograms taggedListRetainProgram_oracleFree
            taggedSpineLengthProgram_oracleFree)
          (atomRequestListProgram_oracleFree identityStageProgram
            identityStageProgram_oracleFree))
        (balancedCallProgram_oracleFree taggedNatFieldValidateProgram_oracleFree))
      balancedBitSingletonProgram_oracleFree)
    balancedClauseStreamFlattenProgram_oracleFree

def taggedNatListValidationRebuildFuel (inputLength raw : ℕ) : ℕ :=
  let fields := taggedNatFieldCodes raw
  let code := encodeTaggedList fields
  linkFuel balancedClauseStreamFlattenProgram
    (linkFuel balancedBitSingletonProgram
      (linkFuel (balancedCallProgram taggedNatFieldValidateProgram)
        (linkFuel (atomRequestListProgram identityStageProgram)
          (linkFuel taggedSpineLengthProgram (taggedListRetainFuel raw)
            (taggedSpineLengthFuel code))
          (indexedAtomListFuel identityStageProgram inputLength fields.length
            code (fun _index => 1)))
        (balancedCallFuel taggedNatFieldValidateProgram
          (fun request =>
            taggedNatFieldValidateFuel (Nat.unpair request).1 fields)
          (taggedNatIndexRequests raw)))
      (balancedBitSingletonTreeFuel (taggedNatOutputTree raw)))
    (balancedTreeStreamFlattenFuel (taggedNatSingletonTree raw))

/-- The rebuilt charge, stage by stage.  Compare
`CanonicalTaggedNatListValidationProgram.taggedNatListValidationBits`: the
builder's clock entry is replaced by the counter's returned pair and the
generated request list, and the callee entry names the rebuilt validator. -/
def taggedNatListValidationRebuildStageBits (inputLength raw : ℕ) : List ℕ :=
  let fields := taggedNatFieldCodes raw
  let code := encodeTaggedList fields
  [ 1
  , natBitLength inputLength
  , taggedListRetainBits inputLength raw
  , taggedSpineLengthBits code
  , indexedAtomListBits inputLength fields.length code
      fun index => Nat.pair index code
  , taggedNatIndexRequestBits raw
  , balancedCallRequiredBits (taggedNatIndexOutput raw)
      (taggedNatIndexRequests raw)
  , taggedNatFieldValidateMaximumBits raw
  , balancedBitSingletonTreeBits (taggedNatOutputTree raw)
  , balancedTreeStreamFlattenMaximumBits (taggedNatSingletonTree raw)
  ]

def taggedNatListValidationRebuildBits (inputLength raw : ℕ) : ℕ :=
  (taggedNatListValidationRebuildStageBits inputLength raw).foldr max 1

theorem taggedNatListValidationRebuildBits_of_mem
    {inputLength raw value : ℕ}
    (hmem : value ∈ taggedNatListValidationRebuildStageBits inputLength raw) :
    value ≤ taggedNatListValidationRebuildBits inputLength raw :=
  le_foldr_max_of_mem hmem

set_option maxHeartbeats 800000 in
-- Six links over the frozen flattening tail; the counter and the indexed
-- request list replace the builder at the same intermediate value.
/-- **The rebuilt tagged-nat list validator returns the published verdict.**
Output contract unchanged from `run_taggedNatListValidationProgram`. -/
theorem run_taggedNatListValidationRebuildProgram (inputLength raw : ℕ) :
    runNPOracleProgram taggedNatListValidationRebuildProgram
        (taggedNatListValidationRebuildBits inputLength raw)
        (taggedNatListValidationRebuildFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (taggedNatListValidationOutput raw) := by
  let fields := taggedNatFieldCodes raw
  let code := encodeTaggedList fields
  let outputs := taggedNatFieldOutputs raw
  let outputTree := taggedNatOutputTree raw
  let singletonTree := taggedNatSingletonTree raw
  let maximumBits := taggedNatListValidationRebuildBits inputLength raw
  have bits_of_member {value : ℕ}
      (hmem : value ∈ taggedNatListValidationRebuildStageBits inputLength raw) :
      value ≤ maximumBits :=
    taggedNatListValidationRebuildBits_of_mem hmem
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [taggedNatListValidationRebuildStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [taggedNatListValidationRebuildStageBits]
  have hretain :
      runNPOracleProgram taggedListRetainProgram maximumBits
          (taggedListRetainFuel raw)
          (initialNPOracleState inputLength raw) =
        some code := by
    refine run_bits_mono (run_taggedListRetainProgram inputLength raw) ?_
    apply bits_of_member
    simp [taggedNatListValidationRebuildStageBits]
  have hcount :
      runNPOracleProgram taggedSpineLengthProgram maximumBits
          (taggedSpineLengthFuel code)
          (initialNPOracleState inputLength code) =
        some (generatedBalancedRangeInput fields.length code) := by
    refine run_bits_mono (run_taggedSpineLengthProgram inputLength fields) ?_
    apply bits_of_member
    simp [taggedNatListValidationRebuildStageBits, fields]
  have hrequestBits : taggedNatIndexRequestBits raw ≤ maximumBits := by
    apply bits_of_member
    simp [taggedNatListValidationRebuildStageBits]
  have hlist :
      runNPOracleProgram (atomRequestListProgram identityStageProgram)
          maximumBits
          (indexedAtomListFuel identityStageProgram inputLength fields.length
            code (fun _index => 1))
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput fields.length code)) =
        some (encodeBalancedList (taggedNatIndexRequests raw)) := by
    have hrun :=
      run_indexedAtomRequestListProgram identityStageProgram inputLength
        fields.length code maximumBits (fun _index => 1)
        (fun index => Nat.pair index code)
        (by
          apply bits_of_member
          simp [taggedNatListValidationRebuildStageBits, code, fields])
        (by
          intro index hindex
          exact run_identityStageProgram inputLength (Nat.pair index code)
            maximumBits
            ((taggedNatIndexRequestBits_of_mem hindex).trans hrequestBits))
    simpa [taggedNatIndexRequests, fields, code] using hrun
  have hcall :
      runNPOracleProgram (balancedCallProgram taggedNatFieldValidateProgram)
          maximumBits
          (balancedCallFuel taggedNatFieldValidateProgram
            (fun request =>
              taggedNatFieldValidateFuel (Nat.unpair request).1 fields)
            (taggedNatIndexRequests raw))
          (initialNPOracleState inputLength
            (encodeBalancedList (taggedNatIndexRequests raw))) =
        some (encodeBalancedList outputs) := by
    have hrequired :
        balancedCallRequiredBits (taggedNatIndexOutput raw)
            (taggedNatIndexRequests raw) ≤ maximumBits := by
      apply bits_of_member
      simp [taggedNatListValidationRebuildStageBits]
    have hleafBits : taggedNatFieldValidateMaximumBits raw ≤ maximumBits := by
      apply bits_of_member
      simp [taggedNatListValidationRebuildStageBits]
    have hexec :
        ∀ request, request ∈ taggedNatIndexRequests raw →
          runNPOracleProgram taggedNatFieldValidateProgram maximumBits
              (taggedNatFieldValidateFuel (Nat.unpair request).1 fields)
              (initialNPOracleState (Nat.unpair request).1
                (Nat.unpair request).2) =
            some (taggedNatIndexOutput raw request) := by
      intro request hrequest
      rcases List.mem_map.mp hrequest with ⟨index, hindexMem, hrequestEq⟩
      have hindex : index < fields.length := List.mem_range.mp hindexMem
      subst hrequestEq
      have hrun :=
        run_bits_mono (run_taggedNatFieldValidateProgram index fields)
          ((taggedNatFieldValidateMaximumBits_of_mem hindex).trans hleafBits)
      simpa [taggedNatIndexOutput, fields, code] using hrun
    have hfrom :=
      run_balancedCallProgram_from (callee := taggedNatFieldValidateProgram)
        (maximumBits := maximumBits) inputLength (taggedNatIndexRequests raw)
        (fun request =>
          taggedNatFieldValidateFuel (Nat.unpair request).1 fields)
        (taggedNatIndexOutput raw) hrequired hexec
    rwa [map_taggedNatIndexOutput] at hfrom
  have houtputCode : outputTree.code = encodeBalancedList outputs := by
    simpa [outputTree, taggedNatOutputTree, outputs] using
      balancedTraversalTree_code outputs
  have hsingleton :
      runNPOracleProgram balancedBitSingletonProgram maximumBits
          (balancedBitSingletonTreeFuel outputTree)
          (initialNPOracleState inputLength (encodeBalancedList outputs)) =
        some singletonTree.code := by
    have hrun :=
      run_bits_mono (run_balancedBitSingletonTreeProgram inputLength outputTree)
        (by
          apply bits_of_member
          simp [taggedNatListValidationRebuildStageBits, outputTree])
    rw [houtputCode] at hrun
    simpa [singletonTree, taggedNatSingletonTree] using hrun
  have hsingletonValid :
      ∀ atom ∈ singletonTree.atoms,
        encodeTaggedList (streamOfCode atom) = atom := by
    intro atom hatom
    have hatomMapped : atom ∈ outputs.map singletonTaggedBit := by
      simpa [singletonTree, taggedNatSingletonTree, outputTree,
        taggedNatOutputTree, balancedTraversalTree_atoms, outputs] using hatom
    rcases List.mem_map.mp hatomMapped with ⟨output, _houtput, rfl⟩
    simp [singletonTaggedBit, streamOfCode]
  have hflatten :
      runNPOracleProgram balancedClauseStreamFlattenProgram maximumBits
          (balancedTreeStreamFlattenFuel singletonTree)
          (initialNPOracleState inputLength singletonTree.code) =
        some (encodeTaggedList outputs) := by
    have hrun :=
      run_bits_mono
        (run_balancedClauseStreamFlattenTree singletonTree inputLength
          hsingletonValid)
        (by
          apply bits_of_member
          simp [taggedNatListValidationRebuildStageBits, singletonTree])
    rwa [taggedNatSingletonTree_values raw] at hrun
  have hthroughList :=
    run_linkPrograms hpositive hlength
      (run_linkPrograms hpositive hlength hretain hcount) hlist
  have hthroughCall :=
    run_linkPrograms hpositive hlength hthroughList hcall
  have hthroughSingleton :=
    run_linkPrograms hpositive hlength hthroughCall hsingleton
  have hrun := run_linkPrograms hpositive hlength hthroughSingleton hflatten
  simpa [taggedNatListValidationRebuildProgram,
    taggedNatListValidationRebuildFuel, taggedNatListValidationOutput,
    fields, code, outputs, outputTree, singletonTree] using hrun

end NearCubicWires.CanonicalTaggedNatListRebuildProgram
