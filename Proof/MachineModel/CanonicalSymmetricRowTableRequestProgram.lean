import Proof.MachineModel.CanonicalOccurrenceRequestProgram
import Proof.MachineModel.CanonicalSymmetricLiveMaskProgram
import Proof.MachineModel.CanonicalSymmetricSupportMaskProgram

namespace NearCubicWires.CanonicalSymmetricRowTableRequestProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalFourfoldRowCountFormula
open NearCubicWires.CanonicalFourfoldRowEvaluationProgram
open NearCubicWires.CanonicalFourfoldRowProducerDispatchProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalFourfoldRowTailProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalOccurrenceRequestProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalSignedAtomRequestProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.CanonicalSymmetricLiveMaskProgram
open NearCubicWires.CanonicalSymmetricRowTableProgram
open NearCubicWires.CanonicalStructuralGF2EvaluationProgram
open NearCubicWires.CanonicalSymmetricSupportMaskProgram
open NearCubicWires.CanonicalTouchingSweepRoundProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

private theorem le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

/-! ## §1 The pool's balanced gate tree

The circuit's bottom fan is already a balanced list of encoded gates — the
third field of its canonical tagged encoding — so one circuit's contribution to
the pool needs no decoding at all, only the canonical balanced-to-tagged
conversion that makes it concatenable.  Concatenating and rebalancing once is
then the same three-program tail
`CanonicalSymmetricSupportMaskProgram` uses. -/

/-- One circuit's bottom fan as a canonical tagged stream of gate codes. -/
def encodedCircuitGateStream (code : ℕ) : ℕ :=
  encodeTaggedList (encodedCircuitGateCodes code)

/-- **The per-circuit gate-stream producer.**  Repair the balanced-call atom,
read the bottom-fan field, and hand it on as a canonical tagged stream. -/
def circuitGateStreamProgram : NPOracleProgram :=
  linkPrograms repairAtomProgram
    (linkPrograms taggedFieldTwoProgram balancedBitsToTaggedProgram)

theorem circuitGateStreamProgram_oracleFree :
    OracleFree circuitGateStreamProgram :=
  oracleFree_linkPrograms repairAtomProgram_oracleFree
    (oracleFree_linkPrograms taggedFieldTwoProgram_oracleFree
      balancedBitsToTaggedProgram_oracleFree)

def circuitGateStreamFuel (code : ℕ) : ℕ :=
  linkFuel (linkPrograms taggedFieldTwoProgram balancedBitsToTaggedProgram) 2
    (linkFuel balancedBitsToTaggedProgram 7
      (balancedBitsToTaggedFuel (encodedCircuitGateCodes code)))

def circuitGateStreamBits (code : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength code)
      (balancedBitsToTaggedBits (Nat.unpair code).1
        (encodedCircuitGateCodes code))

theorem run_circuitGateStreamProgram {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) (maximumBits : ℕ)
    (hbits :
      circuitGateStreamBits
          (encodeNormalizedSymmetricThresholdCircuit circuit) ≤
        maximumBits) :
    runNPOracleProgram circuitGateStreamProgram maximumBits
        (circuitGateStreamFuel
          (encodeNormalizedSymmetricThresholdCircuit circuit))
        (initialNPOracleState
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).2) =
      some
        (encodedCircuitGateStream
          (encodeNormalizedSymmetricThresholdCircuit circuit)) := by
  have hpositive : 1 ≤ maximumBits := (Nat.le_max_left _ _).trans hbits
  have hcodeBits :
      natBitLength (encodeNormalizedSymmetricThresholdCircuit circuit) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have hconvertBits :
      balancedBitsToTaggedBits
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
          (encodedCircuitGateCodes
            (encodeNormalizedSymmetricThresholdCircuit circuit)) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have hlength :
      natBitLength
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1 ≤
        maximumBits :=
    bits_of_le (Nat.unpair_left_le _) hcodeBits
  have hpair :
      Nat.pair
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).2 =
        encodeNormalizedSymmetricThresholdCircuit circuit :=
    Nat.pair_unpair _
  have hstageOne :
      runNPOracleProgram repairAtomProgram maximumBits 2
          (initialNPOracleState
            (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
            (Nat.unpair
              (encodeNormalizedSymmetricThresholdCircuit circuit)).2) =
        some (encodeNormalizedSymmetricThresholdCircuit circuit) := by
    have hatomBits :
        repairAtomBits
            (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
            (Nat.unpair
              (encodeNormalizedSymmetricThresholdCircuit circuit)).2 ≤
          maximumBits := by
      unfold repairAtomBits
      rw [hpair]
      exact hcodeBits
    have hrun :=
      run_repairAtomProgram
        (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
        (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).2
    rw [hpair] at hrun
    exact run_bits_mono hrun hatomBits
  have hstageTwo :
      runNPOracleProgram taggedFieldTwoProgram maximumBits 7
          (initialNPOracleState
            (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
            (encodeNormalizedSymmetricThresholdCircuit circuit)) =
        some
          (taggedFieldTwo
            (encodeNormalizedSymmetricThresholdCircuit circuit)) :=
    run_bits_mono
      (run_taggedFieldTwoProgram
        (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
        (encodeNormalizedSymmetricThresholdCircuit circuit))
      hcodeBits
  have hstageThree :
      runNPOracleProgram balancedBitsToTaggedProgram maximumBits
          (balancedBitsToTaggedFuel
            (encodedCircuitGateCodes
              (encodeNormalizedSymmetricThresholdCircuit circuit)))
          (initialNPOracleState
            (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
            (taggedFieldTwo
              (encodeNormalizedSymmetricThresholdCircuit circuit))) =
        some
          (encodedCircuitGateStream
            (encodeNormalizedSymmetricThresholdCircuit circuit)) := by
    have hrun :=
      run_balancedBitsToTaggedProgram
        (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
        (encodedCircuitGateCodes
          (encodeNormalizedSymmetricThresholdCircuit circuit))
    rw [encodeBalancedList_encodedCircuitGateCodes circuit] at hrun
    exact run_bits_mono hrun hconvertBits
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo hstageThree)

private theorem map_encodedCircuitGateStream (codes : List ℕ) :
    codes.map encodedCircuitGateStream =
      (codes.map encodedCircuitGateCodes).map encodeTaggedList := by
  induction codes with
  | nil => rfl
  | cons code rest inductionHypothesis =>
      simp only [List.map_cons, inductionHypothesis, encodedCircuitGateStream]

private theorem occurrencePoolCodes_flatMap {n : ℕ}
    (circuits : List (NormalizedSymmetricThresholdCircuit n)) :
    occurrencePoolCodes (circuits.flatMap symmetricCircuitOccurrences) =
      (circuits.map fun circuit =>
        occurrencePoolCodes (symmetricCircuitOccurrences circuit)).flatten := by
  induction circuits with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_cons, List.flatten_cons]
      rw [← inductionHypothesis]
      simp [occurrencePoolCodes]

private theorem encodedCircuitGateCodes_pool {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) :
    encodedCircuitGateCodes
        (encodeNormalizedSymmetricThresholdCircuit circuit) =
      occurrencePoolCodes (symmetricCircuitOccurrences circuit) := by
  unfold occurrencePoolCodes symmetricCircuitOccurrences
  rw [encodedCircuitGateCodes_encode, List.map_ofFn]
  rfl

/-- The per-circuit gate streams, before concatenation. -/
def symmetricPoolGateStreams
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List (List ℕ) :=
  (request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
    encodedCircuitGateCodes

theorem symmetricPoolGateStreams_flatten
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (symmetricPoolGateStreams request).flatten =
      occurrencePoolCodes (symmetricFourfoldOccurrences request) := by
  unfold symmetricPoolGateStreams
  rw [List.map_map]
  have hcodes :
      request.circuits.map
          (encodedCircuitGateCodes ∘
            encodeNormalizedSymmetricThresholdCircuit) =
        request.circuits.map fun circuit =>
          occurrencePoolCodes (symmetricCircuitOccurrences circuit) := by
    refine List.map_congr_left ?_
    intro circuit _
    simp only [Function.comp_apply]
    exact encodedCircuitGateCodes_pool circuit
  rw [hcodes]
  unfold symmetricFourfoldOccurrences
  exact (occurrencePoolCodes_flatMap request.circuits).symm

private def poolTreeTailThree : NPOracleProgram :=
  linkPrograms balancedClauseStreamFlattenProgram taggedToBalancedProgram

private def poolTreeTailTwo : NPOracleProgram :=
  linkPrograms (balancedCallProgram circuitGateStreamProgram) poolTreeTailThree

private def poolTreeTailOne : NPOracleProgram :=
  linkPrograms rightProjectionProgram poolTreeTailTwo

/-- **The symmetric occurrence pool's gate-tree program.**  Strip the family
tag, strip the arity, map the per-circuit stream producer across the balanced
circuit list, concatenate the streams, and rebalance once. -/
def symmetricOccurrencePoolTreeProgram : NPOracleProgram :=
  linkPrograms rightProjectionProgram poolTreeTailOne

theorem symmetricOccurrencePoolTreeProgram_oracleFree :
    OracleFree symmetricOccurrencePoolTreeProgram :=
  oracleFree_linkPrograms rightProjectionProgram_oracleFree
    (oracleFree_linkPrograms rightProjectionProgram_oracleFree
      (oracleFree_linkPrograms
        (balancedCallProgram_oracleFree circuitGateStreamProgram_oracleFree)
        (oracleFree_linkPrograms
          balancedClauseStreamFlattenProgram_oracleFree
          taggedToBalancedProgram_oracleFree)))

def symmetricOccurrencePoolTreeFuel
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  linkFuel poolTreeTailOne 2
    (linkFuel poolTreeTailTwo 2
      (linkFuel poolTreeTailThree
        (balancedCallFuel circuitGateStreamProgram circuitGateStreamFuel
          (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
        (linkFuel taggedToBalancedProgram
          (balancedClauseStreamFlattenFuel (symmetricPoolGateStreams request))
          (taggedToBalancedFuel
            (occurrencePoolCodes (symmetricFourfoldOccurrences request))))))

def symmetricOccurrencePoolTreeStageBits
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List ℕ :=
  [ 1
  , natBitLength request.q
  , rightProjectionBits (encodeNat symmetricCircuitFamilyTag)
      (Nat.pair request.q
        (encodeBalancedList
          (request.circuits.map encodeNormalizedSymmetricThresholdCircuit)))
  , rightProjectionBits request.q
      (encodeBalancedList
        (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
  , balancedCallRequiredBits encodedCircuitGateStream
      (request.circuits.map encodeNormalizedSymmetricThresholdCircuit)
  , ((request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
      circuitGateStreamBits).foldr max 1
  , balancedClauseStreamFlattenMaximumBits (symmetricPoolGateStreams request)
  , taggedToBalancedRegisterBitsFor request.q
      (occurrencePoolCodes (symmetricFourfoldOccurrences request))
  ]

def symmetricOccurrencePoolTreeBits
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  (symmetricOccurrencePoolTreeStageBits request).foldr max 1

set_option maxHeartbeats 800000 in
-- Five linked stages at one shared register width; every premise is a closed
-- `…Bits` name of this file.
/-- **The symmetric occurrence pool's gate tree, executed from the typed
envelope.**  This is the fourth input the pool traversal needs, and the one
`CanonicalOccurrenceRequestProgram` §5 left open. -/
theorem run_symmetricOccurrencePoolTreeProgram
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (maximumBits : ℕ)
    (hbits : symmetricOccurrencePoolTreeBits request ≤ maximumBits) :
    runNPOracleProgram symmetricOccurrencePoolTreeProgram maximumBits
        (symmetricOccurrencePoolTreeFuel request)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some (occurrencePoolTree (symmetricFourfoldOccurrences request)) := by
  have bits_of_member {value : ℕ}
      (hvalue : value ∈ symmetricOccurrencePoolTreeStageBits request) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrencePoolTreeStageBits]
  have hlength : natBitLength request.q ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrencePoolTreeStageBits]
  have hcallBits :
      balancedCallRequiredBits encodedCircuitGateStream
          (request.circuits.map encodeNormalizedSymmetricThresholdCircuit) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrencePoolTreeStageBits]
  have hcalleeBits :
      ((request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
        circuitGateStreamBits).foldr max 1 ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrencePoolTreeStageBits]
  have hflattenBits :
      balancedClauseStreamFlattenMaximumBits
          (symmetricPoolGateStreams request) ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrencePoolTreeStageBits]
  have hbuilderBits :
      taggedToBalancedRegisterBitsFor request.q
          (occurrencePoolCodes (symmetricFourfoldOccurrences request)) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrencePoolTreeStageBits]
  have houterProjectionBits :
      rightProjectionBits (encodeNat symmetricCircuitFamilyTag)
          (Nat.pair request.q
            (encodeBalancedList
              (request.circuits.map
                encodeNormalizedSymmetricThresholdCircuit))) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrencePoolTreeStageBits]
  have hinnerProjectionBits :
      rightProjectionBits request.q
          (encodeBalancedList
            (request.circuits.map
              encodeNormalizedSymmetricThresholdCircuit)) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrencePoolTreeStageBits]
  have hstageOne :
      runNPOracleProgram rightProjectionProgram maximumBits 2
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some
          (Nat.pair request.q
            (encodeBalancedList
              (request.circuits.map
                encodeNormalizedSymmetricThresholdCircuit))) :=
    run_bits_mono
      (run_rightProjectionProgram request.q
        (encodeNat symmetricCircuitFamilyTag)
        (Nat.pair request.q
          (encodeBalancedList
            (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))))
      houterProjectionBits
  have hstageTwo :
      runNPOracleProgram rightProjectionProgram maximumBits 2
          (initialNPOracleState request.q
            (Nat.pair request.q
              (encodeBalancedList
                (request.circuits.map
                  encodeNormalizedSymmetricThresholdCircuit)))) =
        some
          (encodeBalancedList
            (request.circuits.map
              encodeNormalizedSymmetricThresholdCircuit)) :=
    run_bits_mono
      (run_rightProjectionProgram request.q request.q
        (encodeBalancedList
          (request.circuits.map encodeNormalizedSymmetricThresholdCircuit)))
      hinnerProjectionBits
  have hexec : ∀ code : ℕ,
      code ∈
        request.circuits.map encodeNormalizedSymmetricThresholdCircuit →
      runNPOracleProgram circuitGateStreamProgram maximumBits
          (circuitGateStreamFuel code)
          (initialNPOracleState (Nat.unpair code).1 (Nat.unpair code).2) =
        some (encodedCircuitGateStream code) := by
    intro code hcode
    have hcircuitBits : circuitGateStreamBits code ≤ maximumBits := by
      refine le_trans ?_ hcalleeBits
      exact le_foldr_max_of_mem (List.mem_map_of_mem hcode)
    obtain ⟨circuit, _hcircuit, hencode⟩ := List.mem_map.mp hcode
    rw [← hencode] at hcircuitBits ⊢
    exact run_circuitGateStreamProgram circuit maximumBits hcircuitBits
  have hstageThree :
      runNPOracleProgram (balancedCallProgram circuitGateStreamProgram)
          maximumBits
          (balancedCallFuel circuitGateStreamProgram circuitGateStreamFuel
            (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
          (initialNPOracleState request.q
            (encodeBalancedList
              (request.circuits.map
                encodeNormalizedSymmetricThresholdCircuit))) =
        some
          (encodeBalancedList
            ((symmetricPoolGateStreams request).map encodeTaggedList)) := by
    have hrun :=
      run_balancedCallProgram_from (callee := circuitGateStreamProgram)
        (maximumBits := maximumBits) request.q
        (request.circuits.map encodeNormalizedSymmetricThresholdCircuit)
        circuitGateStreamFuel encodedCircuitGateStream hcallBits hexec
    have hstreams :
        (request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
            encodedCircuitGateStream =
          (symmetricPoolGateStreams request).map encodeTaggedList := by
      unfold symmetricPoolGateStreams
      exact map_encodedCircuitGateStream
        (request.circuits.map encodeNormalizedSymmetricThresholdCircuit)
    rw [hstreams] at hrun
    exact hrun
  have hstageFour :
      runNPOracleProgram balancedClauseStreamFlattenProgram maximumBits
          (balancedClauseStreamFlattenFuel (symmetricPoolGateStreams request))
          (initialNPOracleState request.q
            (encodeBalancedList
              ((symmetricPoolGateStreams request).map encodeTaggedList))) =
        some
          (encodeTaggedList
            (occurrencePoolCodes (symmetricFourfoldOccurrences request))) := by
    have hrun :=
      run_balancedClauseStreamFlattenProgram (symmetricPoolGateStreams request)
        request.q
    rw [symmetricPoolGateStreams_flatten request] at hrun
    exact run_bits_mono hrun hflattenBits
  have hstageFive :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (taggedToBalancedFuel
            (occurrencePoolCodes (symmetricFourfoldOccurrences request)))
          (initialNPOracleState request.q
            (encodeTaggedList
              (occurrencePoolCodes (symmetricFourfoldOccurrences request)))) =
        some (occurrencePoolTree (symmetricFourfoldOccurrences request)) :=
    run_bits_mono
      (run_taggedToBalancedProgram_from request.q
        (occurrencePoolCodes (symmetricFourfoldOccurrences request)))
      hbuilderBits
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo
      (run_linkPrograms hpositive hlength hstageThree
        (run_linkPrograms hpositive hlength hstageFour hstageFive)))

/-- The index a generated range atom carries, read structurally. -/
def rangeAtomIndex (raw : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair raw).2).1

@[simp] theorem rangeAtomIndex_atom (inputLength index context : ℕ) :
    rangeAtomIndex (balancedRangeRequestAtom inputLength index context) =
      index := by
  simp [rangeAtomIndex, balancedRangeRequestAtom]

def indexedPoolListProgram (leaf : NPOracleProgram) : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram
    (linkPrograms leftProjectionProgram (balancedCallProgram leaf))

theorem indexedPoolListProgram_oracleFree
    (leaf : NPOracleProgram) (hleaf : OracleFree leaf) :
    OracleFree (indexedPoolListProgram leaf) :=
  oracleFree_linkPrograms generatedBalancedRangeProgram_oracleFree
    (oracleFree_linkPrograms leftProjectionProgram_oracleFree
      (balancedCallProgram_oracleFree hleaf))

def indexedPoolListFuel
    (leaf : NPOracleProgram) (inputLength count context : ℕ)
    (leafFuel : ℕ → ℕ) : ℕ :=
  linkFuel (linkPrograms leftProjectionProgram (balancedCallProgram leaf))
    (generatedBalancedRangeFuel inputLength count context)
    (linkFuel (balancedCallProgram leaf) 2
      (balancedCallFuel leaf (fun raw => leafFuel (rangeAtomIndex raw))
        (balancedRangeRequestAtoms inputLength context 0 count)))

def indexedPoolListStageBits
    (inputLength count context : ℕ) (leafOutput : ℕ → ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , generatedBalancedRangeRequiredBits inputLength count context
  , leftProjectionBits
      (encodeBalancedList
        (balancedRangeRequestAtoms inputLength context 0 count))
      context
  , balancedCallRequiredBits (fun raw => leafOutput (rangeAtomIndex raw))
      (balancedRangeRequestAtoms inputLength context 0 count)
  ]

def indexedPoolListBits
    (inputLength count context : ℕ) (leafOutput : ℕ → ℕ) : ℕ :=
  (indexedPoolListStageBits inputLength count context leafOutput).foldr max 1

private theorem map_rangeAtomIndex
    (inputLength count context : ℕ) (leafOutput : ℕ → ℕ) :
    (balancedRangeRequestAtoms inputLength context 0 count).map
        (fun raw => leafOutput (rangeAtomIndex raw)) =
      (List.range count).map leafOutput := by
  rw [balancedRangeRequestAtoms_eq_map_range, List.map_map]
  refine List.map_congr_left ?_
  intro index _
  simp only [Function.comp_apply, Nat.zero_add, rangeAtomIndex_atom]

theorem run_indexedPoolListProgram
    (leaf : NPOracleProgram) (inputLength count context maximumBits : ℕ)
    (leafFuel leafOutput : ℕ → ℕ)
    (hbits :
      indexedPoolListBits inputLength count context leafOutput ≤ maximumBits)
    (hleaf : ∀ index : ℕ, index < count →
      runNPOracleProgram leaf maximumBits (leafFuel index)
          (initialNPOracleState inputLength (Nat.pair index context)) =
        some (leafOutput index)) :
    runNPOracleProgram (indexedPoolListProgram leaf) maximumBits
        (indexedPoolListFuel leaf inputLength count context leafFuel)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput count context)) =
      some (encodeBalancedList ((List.range count).map leafOutput)) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ indexedPoolListStageBits inputLength count context leafOutput) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [indexedPoolListStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [indexedPoolListStageBits]
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel inputLength count context)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput count context)) =
        some
          (Nat.pair
            (encodeBalancedList
              (balancedRangeRequestAtoms inputLength context 0 count))
            context) := by
    refine run_bits_mono
      (run_generatedBalancedRangeProgram inputLength count context) ?_
    apply bits_of_member
    simp [indexedPoolListStageBits]
  have hproject :
      runNPOracleProgram leftProjectionProgram maximumBits 2
          (initialNPOracleState inputLength
            (Nat.pair
              (encodeBalancedList
                (balancedRangeRequestAtoms inputLength context 0 count))
              context)) =
        some
          (encodeBalancedList
            (balancedRangeRequestAtoms inputLength context 0 count)) := by
    refine run_bits_mono
      (run_leftProjectionProgram inputLength
        (encodeBalancedList
          (balancedRangeRequestAtoms inputLength context 0 count))
        context) ?_
    apply bits_of_member
    simp [indexedPoolListStageBits]
  have hcallBits :
      balancedCallRequiredBits (fun raw => leafOutput (rangeAtomIndex raw))
          (balancedRangeRequestAtoms inputLength context 0 count) ≤
        maximumBits := by
    apply bits_of_member
    simp [indexedPoolListStageBits]
  have hexec : ∀ raw : ℕ,
      raw ∈ balancedRangeRequestAtoms inputLength context 0 count →
      runNPOracleProgram leaf maximumBits (leafFuel (rangeAtomIndex raw))
          (initialNPOracleState (Nat.unpair raw).1 (Nat.unpair raw).2) =
        some (leafOutput (rangeAtomIndex raw)) := by
    intro raw hraw
    rw [balancedRangeRequestAtoms_eq_map_range] at hraw
    obtain ⟨offset, hoffset, hatom⟩ := List.mem_map.mp hraw
    have hindex : offset < count := List.mem_range.mp hoffset
    have hraw_eq :
        raw = balancedRangeRequestAtom inputLength offset context := by
      rw [← hatom, Nat.zero_add]
    have hleft : (Nat.unpair raw).1 = inputLength := by
      rw [hraw_eq]
      simp [balancedRangeRequestAtom]
    have hright : (Nat.unpair raw).2 = Nat.pair offset context := by
      rw [hraw_eq]
      simp [balancedRangeRequestAtom]
    have hatomIndex : rangeAtomIndex raw = offset := by
      rw [hraw_eq, rangeAtomIndex_atom]
    rw [hleft, hright, hatomIndex]
    exact hleaf offset hindex
  have hcall :=
    run_balancedCallProgram_from (callee := leaf) (maximumBits := maximumBits)
      inputLength (balancedRangeRequestAtoms inputLength context 0 count)
      (fun raw => leafFuel (rangeAtomIndex raw))
      (fun raw => leafOutput (rangeAtomIndex raw)) hcallBits hexec
  rw [map_rangeAtomIndex] at hcall
  exact run_linkPrograms hpositive hlength hrange
    (run_linkPrograms hpositive hlength hproject hcall)

def occurrencePoolContext {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) : ℕ :=
  Nat.pair occurrences.length
    (Nat.pair (occurrencePoolTree occurrences)
      (signedAtomMaskPair inputMask liveMask))

def poolRequestAt {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask index : ℕ) : ℕ :=
  if hindex : index < occurrences.length then
    residualAssignmentRequest occurrences inputMask liveMask ⟨index, hindex⟩
  else 0

def poolRequestFuelAt {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask index : ℕ) : ℕ :=
  if hindex : index < occurrences.length then
    occurrencePoolLeafFuel occurrences ⟨index, hindex⟩ inputMask liveMask
  else 0

def poolRequestBitsAt {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask index : ℕ) : ℕ :=
  if hindex : index < occurrences.length then
    occurrencePoolLeafBits occurrences ⟨index, hindex⟩ inputMask liveMask
  else 1

@[simp] theorem poolRequestAt_val {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) (index : Fin occurrences.length) :
    poolRequestAt occurrences inputMask liveMask index.val =
      residualAssignmentRequest occurrences inputMask liveMask index := by
  unfold poolRequestAt
  rw [dif_pos index.isLt]

private theorem map_range_poolRequestAt {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) :
    (List.range occurrences.length).map
        (poolRequestAt occurrences inputMask liveMask) =
      residualAssignmentRequests occurrences inputMask liveMask := by
  unfold residualAssignmentRequests
  refine List.ext_getElem (by simp) ?_
  intro index hleft hright
  have hindex : index < occurrences.length := by
    simpa using hleft
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact poolRequestAt_val occurrences inputMask liveMask ⟨index, hindex⟩

/-- **The pool's request-list producer.** -/
def occurrencePoolRequestListProgram : NPOracleProgram :=
  indexedPoolListProgram occurrencePoolLeafProgram

theorem occurrencePoolRequestListProgram_oracleFree :
    OracleFree occurrencePoolRequestListProgram :=
  indexedPoolListProgram_oracleFree occurrencePoolLeafProgram
    occurrencePoolLeafProgram_oracleFree

def occurrencePoolRequestListFuel {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) : ℕ :=
  indexedPoolListFuel occurrencePoolLeafProgram q occurrences.length
    (occurrencePoolContext occurrences inputMask liveMask)
    (poolRequestFuelAt occurrences inputMask liveMask)

def occurrencePoolRequestListStageBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) : List ℕ :=
  [ indexedPoolListBits q occurrences.length
      (occurrencePoolContext occurrences inputMask liveMask)
      (poolRequestAt occurrences inputMask liveMask)
  , ((List.range occurrences.length).map
      (poolRequestBitsAt occurrences inputMask liveMask)).foldr max 1
  ]

def occurrencePoolRequestListBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) : ℕ :=
  (occurrencePoolRequestListStageBits occurrences inputMask liveMask).foldr
    max 1

/-- **The pool's request list, executed** from the population, the gate tree,
and the two masks. -/
theorem run_occurrencePoolRequestListProgram {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask maximumBits : ℕ)
    (hbits :
      occurrencePoolRequestListBits occurrences inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram occurrencePoolRequestListProgram maximumBits
        (occurrencePoolRequestListFuel occurrences inputMask liveMask)
        (initialNPOracleState q
          (generatedBalancedRangeInput occurrences.length
            (occurrencePoolContext occurrences inputMask liveMask))) =
      some
        (encodeBalancedList
          (residualAssignmentRequests occurrences inputMask liveMask)) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          occurrencePoolRequestListStageBits occurrences inputMask liveMask) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hlistBits :
      indexedPoolListBits q occurrences.length
          (occurrencePoolContext occurrences inputMask liveMask)
          (poolRequestAt occurrences inputMask liveMask) ≤
        maximumBits := by
    apply bits_of_member
    simp [occurrencePoolRequestListStageBits]
  have hleafBits :
      ((List.range occurrences.length).map
        (poolRequestBitsAt occurrences inputMask liveMask)).foldr max 1 ≤
        maximumBits := by
    apply bits_of_member
    simp [occurrencePoolRequestListStageBits]
  have hleaf : ∀ index : ℕ, index < occurrences.length →
      runNPOracleProgram occurrencePoolLeafProgram maximumBits
          (poolRequestFuelAt occurrences inputMask liveMask index)
          (initialNPOracleState q
            (Nat.pair index
              (occurrencePoolContext occurrences inputMask liveMask))) =
        some (poolRequestAt occurrences inputMask liveMask index) := by
    intro index hindex
    have hentryBits :
        occurrencePoolLeafBits occurrences ⟨index, hindex⟩ inputMask
            liveMask ≤
          maximumBits := by
      refine le_trans ?_ hleafBits
      have hmember :
          poolRequestBitsAt occurrences inputMask liveMask index ∈
            (List.range occurrences.length).map
              (poolRequestBitsAt occurrences inputMask liveMask) :=
        List.mem_map_of_mem (List.mem_range.mpr hindex)
      have hvalue :
          poolRequestBitsAt occurrences inputMask liveMask index =
            occurrencePoolLeafBits occurrences ⟨index, hindex⟩ inputMask
              liveMask := by
        unfold poolRequestBitsAt
        rw [dif_pos hindex]
      rw [← hvalue]
      exact le_foldr_max_of_mem hmember
    have hfuel :
        poolRequestFuelAt occurrences inputMask liveMask index =
          occurrencePoolLeafFuel occurrences ⟨index, hindex⟩ inputMask
            liveMask := by
      unfold poolRequestFuelAt
      rw [dif_pos hindex]
    have houtput :
        poolRequestAt occurrences inputMask liveMask index =
          residualAssignmentRequest occurrences inputMask liveMask
            ⟨index, hindex⟩ := by
      unfold poolRequestAt
      rw [dif_pos hindex]
    rw [hfuel, houtput]
    exact run_occurrencePoolLeafProgram occurrences ⟨index, hindex⟩ inputMask
      liveMask maximumBits hentryBits
  have hrun :=
    run_indexedPoolListProgram occurrencePoolLeafProgram q occurrences.length
      (occurrencePoolContext occurrences inputMask liveMask) maximumBits
      (poolRequestFuelAt occurrences inputMask liveMask)
      (poolRequestAt occurrences inputMask liveMask) hlistBits hleaf
  rw [map_range_poolRequestAt] at hrun
  exact hrun

/-! ## §4 The row-tail front end's four frames

Three of the pool's inputs are produced from the typed envelope and one is the
handoff's own fifth field, so the front end reads the envelope once, keeps a
copy for each envelope-driven producer, and rotates the accumulated results
into the traversal's request.  All four stages are straight-line pair surgery;
nothing below decodes a circuit. -/

/-- The envelope, kept once per envelope-driven producer, beside the row's
input code. -/
def envelopeInputFrame (envelopeCode inputCode : ℕ) : ℕ :=
  Nat.pair envelopeCode
    (Nat.pair envelopeCode (Nat.pair envelopeCode inputCode))

/-- Read the envelope and the input code off the row-tail handoff. -/
def rowHandoffEnvelopeInputProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 2 3 2
  , .unpairRight 3 4 3
  , .unpairLeft 4 5 4
  , .unpairRight 4 6 5
  , .unpairRight 6 7 6
  , .pair 5 7 8 7
  , .pair 5 8 9 8
  , .pair 5 9 0 9
  , .halt 0
  ]

@[simp] theorem rowHandoffEnvelopeInputProgram_oracleFree :
    OracleFree rowHandoffEnvelopeInputProgram := by
  rfl

def rowHandoffEnvelopeInputBits
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) : ℕ :=
  max
    (natBitLength
      (fourfoldRowTailHandoff bottomForest envelopeCode modeCode q rowIndex
        inputCode))
    (natBitLength (envelopeInputFrame envelopeCode inputCode))

theorem run_rowHandoffEnvelopeInputProgram
    (bottomForest envelopeCode modeCode q rowIndex inputCode maximumBits : ℕ)
    (hbits :
      rowHandoffEnvelopeInputBits bottomForest envelopeCode modeCode q rowIndex
          inputCode ≤
        maximumBits) :
    runNPOracleProgram rowHandoffEnvelopeInputProgram maximumBits 10
        (initialNPOracleState q
          (fourfoldRowTailHandoff bottomForest envelopeCode modeCode q rowIndex
            inputCode)) =
      some (envelopeInputFrame envelopeCode inputCode) := by
  have hinputBits :
      natBitLength
          (Nat.pair
            (Nat.pair modeCode
              (Nat.pair q
                (Nat.pair envelopeCode (Nat.pair rowIndex inputCode))))
            bottomForest) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength
          (Nat.pair envelopeCode
            (Nat.pair envelopeCode (Nat.pair envelopeCode inputCode))) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  have hfieldsBits :
      natBitLength
          (Nat.pair modeCode
            (Nat.pair q
              (Nat.pair envelopeCode (Nat.pair rowIndex inputCode)))) ≤
        maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have harityBits :
      natBitLength
          (Nat.pair q (Nat.pair envelopeCode (Nat.pair rowIndex inputCode))) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hfieldsBits
  have henvelopeTailBits :
      natBitLength (Nat.pair envelopeCode (Nat.pair rowIndex inputCode)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) harityBits
  have henvelopeBits : natBitLength envelopeCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) henvelopeTailBits
  have hrowInputBits :
      natBitLength (Nat.pair rowIndex inputCode) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) henvelopeTailBits
  have hinputCodeBits : natBitLength inputCode ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hrowInputBits
  have hinnerTwoBits :
      natBitLength
          (Nat.pair envelopeCode (Nat.pair envelopeCode inputCode)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputBits
  have hinnerOneBits :
      natBitLength (Nat.pair envelopeCode inputCode) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinnerTwoBits
  rw [show (10 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value :=
      Nat.pair modeCode
        (Nat.pair q (Nat.pair envelopeCode (Nat.pair rowIndex inputCode))))
    (by rfl) rfl
    (by simp [initialNPOracleState, fourfoldRowTailHandoff])
    hfieldsBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair q (Nat.pair envelopeCode (Nat.pair rowIndex inputCode)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    harityBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair envelopeCode (Nat.pair rowIndex inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    henvelopeTailBits]
  rw [run_unpairLeft_instruction
    (value := envelopeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    henvelopeBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair rowIndex inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrowInputBits]
  rw [run_unpairRight_instruction
    (value := inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinputCodeBits]
  rw [run_pair_instruction
    (value := Nat.pair envelopeCode inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinnerOneBits]
  rw [run_pair_instruction
    (value := Nat.pair envelopeCode (Nat.pair envelopeCode inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinnerTwoBits]
  rw [run_pair_instruction
    (value := envelopeInputFrame envelopeCode inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, envelopeInputFrame])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := envelopeInputFrame envelopeCode inputCode)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- The envelope, kept once per remaining producer, beside the two masks. -/
def envelopeMaskFrame (envelopeCode inputMask liveMask : ℕ) : ℕ :=
  Nat.pair envelopeCode
    (Nat.pair envelopeCode (signedAtomMaskPair inputMask liveMask))

/-- Fold the computed live mask into the frame. -/
def rowLiveMaskFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairRight 5 6 5
  , .pair 6 2 7 6
  , .pair 4 7 8 7
  , .pair 4 8 0 8
  , .halt 0
  ]

@[simp] theorem rowLiveMaskFrameProgram_oracleFree :
    OracleFree rowLiveMaskFrameProgram := by
  rfl

def rowLiveMaskFrameBits (envelopeCode inputMask liveMask : ℕ) : ℕ :=
  max
    (natBitLength
      (Nat.pair liveMask
        (Nat.pair envelopeCode (Nat.pair envelopeCode inputMask))))
    (natBitLength (envelopeMaskFrame envelopeCode inputMask liveMask))

theorem run_rowLiveMaskFrameProgram
    (arity envelopeCode inputMask liveMask maximumBits : ℕ)
    (hbits :
      rowLiveMaskFrameBits envelopeCode inputMask liveMask ≤ maximumBits) :
    runNPOracleProgram rowLiveMaskFrameProgram maximumBits 9
        (initialNPOracleState arity
          (Nat.pair liveMask
            (Nat.pair envelopeCode (Nat.pair envelopeCode inputMask)))) =
      some (envelopeMaskFrame envelopeCode inputMask liveMask) := by
  have hinputBits :
      natBitLength
          (Nat.pair liveMask
            (Nat.pair envelopeCode (Nat.pair envelopeCode inputMask))) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength
          (Nat.pair envelopeCode
            (Nat.pair envelopeCode (signedAtomMaskPair inputMask liveMask))) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  have hliveBits : natBitLength liveMask ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hcarriedBits :
      natBitLength (Nat.pair envelopeCode (Nat.pair envelopeCode inputMask)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have henvelopeBits : natBitLength envelopeCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hcarriedBits
  have hinnerBits :
      natBitLength (Nat.pair envelopeCode inputMask) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hcarriedBits
  have hinputMaskBits : natBitLength inputMask ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinnerBits
  have htailBits :
      natBitLength
          (Nat.pair envelopeCode (signedAtomMaskPair inputMask liveMask)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputBits
  have hmaskBits :
      natBitLength (signedAtomMaskPair inputMask liveMask) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) htailBits
  rw [show (9 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := liveMask)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hliveBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair envelopeCode (Nat.pair envelopeCode inputMask))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcarriedBits]
  rw [run_unpairLeft_instruction
    (value := envelopeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    henvelopeBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair envelopeCode inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinnerBits]
  rw [run_unpairRight_instruction
    (value := inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinputMaskBits]
  rw [run_pair_instruction
    (value := signedAtomMaskPair inputMask liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomMaskPair])
    hmaskBits]
  rw [run_pair_instruction
    (value := Nat.pair envelopeCode (signedAtomMaskPair inputMask liveMask))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [run_pair_instruction
    (value := envelopeMaskFrame envelopeCode inputMask liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, envelopeMaskFrame])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := envelopeMaskFrame envelopeCode inputMask liveMask)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- The last envelope copy, beside the executed population and the masks. -/
def envelopePopulationFrame (envelopeCode population maskPair : ℕ) : ℕ :=
  Nat.pair envelopeCode (Nat.pair population maskPair)

/-- Rotate the executed population under the retained envelope. -/
def rowPopulationFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 5 6 5
  , .pair 4 6 0 6
  , .halt 0
  ]

@[simp] theorem rowPopulationFrameProgram_oracleFree :
    OracleFree rowPopulationFrameProgram := by
  rfl

def rowPopulationFrameBits (envelopeCode population maskPair : ℕ) : ℕ :=
  max
    (natBitLength
      (Nat.pair population (Nat.pair envelopeCode maskPair)))
    (natBitLength (envelopePopulationFrame envelopeCode population maskPair))

theorem run_rowPopulationFrameProgram
    (arity envelopeCode population maskPair maximumBits : ℕ)
    (hbits :
      rowPopulationFrameBits envelopeCode population maskPair ≤ maximumBits) :
    runNPOracleProgram rowPopulationFrameProgram maximumBits 7
        (initialNPOracleState arity
          (Nat.pair population (Nat.pair envelopeCode maskPair))) =
      some (envelopePopulationFrame envelopeCode population maskPair) := by
  have hinputBits :
      natBitLength (Nat.pair population (Nat.pair envelopeCode maskPair)) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength (Nat.pair envelopeCode (Nat.pair population maskPair)) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  have hpopulationBits : natBitLength population ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hcarriedBits :
      natBitLength (Nat.pair envelopeCode maskPair) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have henvelopeBits : natBitLength envelopeCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hcarriedBits
  have hmaskBits : natBitLength maskPair ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hcarriedBits
  have htailBits :
      natBitLength (Nat.pair population maskPair) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputBits
  rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := population)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hpopulationBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair envelopeCode maskPair)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcarriedBits]
  rw [run_unpairLeft_instruction
    (value := envelopeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    henvelopeBits]
  rw [run_unpairRight_instruction
    (value := maskPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hmaskBits]
  rw [run_pair_instruction
    (value := Nat.pair population maskPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [run_pair_instruction
    (value := envelopePopulationFrame envelopeCode population maskPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, envelopePopulationFrame])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := envelopePopulationFrame envelopeCode population maskPair)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- The traversal's request beside the population it must be paired with. -/
def poolTraversalFrame (population poolTree maskPair : ℕ) : ℕ :=
  Nat.pair
    (generatedBalancedRangeInput population
      (Nat.pair population (Nat.pair poolTree maskPair)))
    population

/-- Assemble the generated range's request from the executed pool tree. -/
def rowTraversalFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 5 6 5
  , .pair 4 6 7 6
  , .pair 4 7 8 7
  , .pair 8 4 0 8
  , .halt 0
  ]

@[simp] theorem rowTraversalFrameProgram_oracleFree :
    OracleFree rowTraversalFrameProgram := by
  rfl

def rowTraversalFrameBits (population poolTree maskPair : ℕ) : ℕ :=
  max (natBitLength (Nat.pair poolTree (Nat.pair population maskPair)))
    (natBitLength (poolTraversalFrame population poolTree maskPair))

theorem run_rowTraversalFrameProgram
    (arity population poolTree maskPair maximumBits : ℕ)
    (hbits : rowTraversalFrameBits population poolTree maskPair ≤ maximumBits) :
    runNPOracleProgram rowTraversalFrameProgram maximumBits 9
        (initialNPOracleState arity
          (Nat.pair poolTree (Nat.pair population maskPair))) =
      some (poolTraversalFrame population poolTree maskPair) := by
  have hinputBits :
      natBitLength (Nat.pair poolTree (Nat.pair population maskPair)) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength
          (Nat.pair
            (Nat.pair population
              (Nat.pair population (Nat.pair poolTree maskPair)))
            population) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  have hpoolBits : natBitLength poolTree ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hcarriedBits :
      natBitLength (Nat.pair population maskPair) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hpopulationBits : natBitLength population ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hcarriedBits
  have hmaskBits : natBitLength maskPair ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hcarriedBits
  have hrangeBits :
      natBitLength
          (Nat.pair population
            (Nat.pair population (Nat.pair poolTree maskPair))) ≤
        maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputBits
  have hcontextBits :
      natBitLength (Nat.pair population (Nat.pair poolTree maskPair)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hrangeBits
  have hbodyBits :
      natBitLength (Nat.pair poolTree maskPair) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hcontextBits
  rw [show (9 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := poolTree)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hpoolBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair population maskPair)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcarriedBits]
  rw [run_unpairLeft_instruction
    (value := population)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpopulationBits]
  rw [run_unpairRight_instruction
    (value := maskPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hmaskBits]
  rw [run_pair_instruction
    (value := Nat.pair poolTree maskPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hbodyBits]
  rw [run_pair_instruction
    (value := Nat.pair population (Nat.pair poolTree maskPair))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [run_pair_instruction
    (value :=
      Nat.pair population
        (Nat.pair population (Nat.pair poolTree maskPair)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrangeBits]
  rw [run_pair_instruction
    (value := poolTraversalFrame population poolTree maskPair)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, poolTraversalFrame,
        generatedBalancedRangeInput])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := poolTraversalFrame population poolTree maskPair)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ## §5 The symmetric row's table request

Eight linked stages: the handoff frame, the three envelope-driven producers
with a rotation after each, and the pool traversal under one
`preserveRightProgram` that pairs the population back on.  The result is
exactly `CanonicalSignedGateEvaluationProgram` §10's input. -/

/-- The row's pool tree, named once. -/
def symmetricRowPoolTree
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  occurrencePoolTree (symmetricRowOccurrences request)

/-- The row's two masks, named once. -/
def symmetricRowMaskPair
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) (input : BitInput request.q) : ℕ :=
  signedAtomMaskPair (encodeBitInput input)
    (symmetricRowLiveMask request liveScale)

private theorem symmetricRowRequest_envelopeCode
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    (symmetricFourfoldRowRequest request rowIndex input).envelopeCode =
      symmetricEnvelopeCode request := by
  simp only [symmetricFourfoldRowRequest,
    CanonicalWitnessCodec.symmetricCircuitCodec, symmetricEnvelopeCode]

private def rowTableRequestTailSeven : NPOracleProgram :=
  preserveRightProgram occurrencePoolRequestListProgram

private def rowTableRequestTailSix : NPOracleProgram :=
  linkPrograms rowTraversalFrameProgram rowTableRequestTailSeven

private def rowTableRequestTailFive : NPOracleProgram :=
  linkPrograms (preserveRightProgram symmetricOccurrencePoolTreeProgram)
    rowTableRequestTailSix

private def rowTableRequestTailFour : NPOracleProgram :=
  linkPrograms rowPopulationFrameProgram rowTableRequestTailFive

private def rowTableRequestTailThree : NPOracleProgram :=
  linkPrograms (preserveRightProgram symmetricOccurrencePopulationProgram)
    rowTableRequestTailFour

private def rowTableRequestTailTwo : NPOracleProgram :=
  linkPrograms rowLiveMaskFrameProgram rowTableRequestTailThree

private def rowTableRequestTailOne (liveScale : ℕ) : NPOracleProgram :=
  linkPrograms (preserveRightProgram (symmetricLiveMaskProgram liveScale))
    rowTableRequestTailTwo

/-- **The symmetric row's request producer.** -/
def symmetricRowTableRequestProgram (liveScale : ℕ) : NPOracleProgram :=
  linkPrograms rowHandoffEnvelopeInputProgram (rowTableRequestTailOne liveScale)

theorem symmetricRowTableRequestProgram_oracleFree (liveScale : ℕ) :
    OracleFree (symmetricRowTableRequestProgram liveScale) :=
  oracleFree_linkPrograms rowHandoffEnvelopeInputProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree (symmetricLiveMaskProgram liveScale)
        (symmetricLiveMaskProgram_oracleFree liveScale))
      (oracleFree_linkPrograms rowLiveMaskFrameProgram_oracleFree
        (oracleFree_linkPrograms
          (preserveRightProgram_oracleFree
            symmetricOccurrencePopulationProgram
            symmetricOccurrencePopulationProgram_oracleFree)
          (oracleFree_linkPrograms rowPopulationFrameProgram_oracleFree
            (oracleFree_linkPrograms
              (preserveRightProgram_oracleFree
                symmetricOccurrencePoolTreeProgram
                symmetricOccurrencePoolTreeProgram_oracleFree)
              (oracleFree_linkPrograms rowTraversalFrameProgram_oracleFree
                (preserveRightProgram_oracleFree
                  occurrencePoolRequestListProgram
                  occurrencePoolRequestListProgram_oracleFree)))))))

def symmetricRowTableRequestFuel (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (input : BitInput request.q) : ℕ :=
  linkFuel (rowTableRequestTailOne liveScale) 10
    (linkFuel rowTableRequestTailTwo
        (preserveRightFuel (symmetricLiveMaskFuel liveScale request))
      (linkFuel rowTableRequestTailThree 9
        (linkFuel rowTableRequestTailFour
            (preserveRightFuel (symmetricOccurrencePopulationFuel request))
          (linkFuel rowTableRequestTailFive 7
            (linkFuel rowTableRequestTailSix
                (preserveRightFuel
                  (symmetricOccurrencePoolTreeFuel request))
              (linkFuel rowTableRequestTailSeven 9
                (preserveRightFuel
                  (occurrencePoolRequestListFuel
                    (symmetricRowOccurrences request) (encodeBitInput input)
                    (symmetricRowLiveMask request liveScale)))))))))

def symmetricRowTableRequestStageBits (liveScale : ℕ)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) : List ℕ :=
  [ 1
  , natBitLength request.q
  , rowHandoffEnvelopeInputBits
      (symmetricFourfoldRowBottomForest algorithm request)
      (symmetricEnvelopeCode request) symmetricCircuitFamilyTag request.q
      rowIndex (encodeBitInput input)
  , preserveRightBits (symmetricLiveMaskBits liveScale request)
      (symmetricEnvelopeCode request)
      (Nat.pair (symmetricEnvelopeCode request)
        (Nat.pair (symmetricEnvelopeCode request) (encodeBitInput input)))
      (symmetricRowLiveMask request liveScale)
  , rowLiveMaskFrameBits (symmetricEnvelopeCode request)
      (encodeBitInput input) (symmetricRowLiveMask request liveScale)
  , preserveRightBits (symmetricOccurrencePopulationBits request)
      (symmetricEnvelopeCode request)
      (Nat.pair (symmetricEnvelopeCode request)
        (symmetricRowMaskPair request liveScale input))
      (symmetricOccurrencePopulation request)
  , rowPopulationFrameBits (symmetricEnvelopeCode request)
      (symmetricOccurrencePopulation request)
      (symmetricRowMaskPair request liveScale input)
  , preserveRightBits (symmetricOccurrencePoolTreeBits request)
      (symmetricEnvelopeCode request)
      (Nat.pair (symmetricOccurrencePopulation request)
        (symmetricRowMaskPair request liveScale input))
      (symmetricRowPoolTree request)
  , rowTraversalFrameBits (symmetricOccurrencePopulation request)
      (symmetricRowPoolTree request)
      (symmetricRowMaskPair request liveScale input)
  , preserveRightBits
      (occurrencePoolRequestListBits (symmetricRowOccurrences request)
        (encodeBitInput input) (symmetricRowLiveMask request liveScale))
      (generatedBalancedRangeInput (symmetricOccurrencePopulation request)
        (occurrencePoolContext (symmetricRowOccurrences request)
          (encodeBitInput input) (symmetricRowLiveMask request liveScale)))
      (symmetricOccurrencePopulation request)
      (encodeBalancedList
        (residualAssignmentRequests (symmetricRowOccurrences request)
          (encodeBitInput input) (symmetricRowLiveMask request liveScale)))
  ]

def symmetricRowTableRequestBits (liveScale : ℕ)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) : ℕ :=
  (symmetricRowTableRequestStageBits liveScale algorithm request rowIndex
    input).foldr max 1

set_option maxHeartbeats 1600000 in
-- Eight linked stages at one shared register width; every premise is a closed
-- `…Bits` name of this file, and the sweep controller's own round width stays
-- quantified exactly as `run_symmetricLiveMaskProgram` states it.
/-- **The symmetric row's residual assignment request, executed from the
row-tail handoff.**  This is the second statement of
`CanonicalGateAtomHeadListProgram` §15. -/
theorem run_symmetricRowTableRequestProgram (liveScale : ℕ)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex maximumBits : ℕ) (input : BitInput request.q)
    (hbits :
      symmetricRowTableRequestBits liveScale algorithm request rowIndex
          input ≤
        maximumBits)
    (hroundBits : ∀ (selected : Finset (Fin request.q)) (stepCount counter : ℕ),
      counter + 1 ≤ request.q →
      stepCount ≤ normalizedLiveCount request.q liveScale →
      touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
          stepCount (request.q - (counter + 1)) counter ≤
        symmetricLiveMaskBits liveScale request) :
    runNPOracleProgram (symmetricRowTableRequestProgram liveScale) maximumBits
        (symmetricRowTableRequestFuel liveScale request input)
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
      some
        (residualAssignmentTableInput (symmetricRowOccurrences request)
          (encodeBitInput input) (symmetricRowLiveMask request liveScale)) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          symmetricRowTableRequestStageBits liveScale algorithm request rowIndex
            input) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricRowTableRequestStageBits]
  have hlength : natBitLength request.q ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricRowTableRequestStageBits]
  have hframeBits :
      rowHandoffEnvelopeInputBits
          (symmetricFourfoldRowBottomForest algorithm request)
          (symmetricEnvelopeCode request) symmetricCircuitFamilyTag request.q
          rowIndex (encodeBitInput input) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricRowTableRequestStageBits]
  have hliveBits :
      preserveRightBits (symmetricLiveMaskBits liveScale request)
          (symmetricEnvelopeCode request)
          (Nat.pair (symmetricEnvelopeCode request)
            (Nat.pair (symmetricEnvelopeCode request) (encodeBitInput input)))
          (symmetricRowLiveMask request liveScale) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricRowTableRequestStageBits]
  have hliveFrameBits :
      rowLiveMaskFrameBits (symmetricEnvelopeCode request)
          (encodeBitInput input) (symmetricRowLiveMask request liveScale) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricRowTableRequestStageBits]
  have hpopulationBits :
      preserveRightBits (symmetricOccurrencePopulationBits request)
          (symmetricEnvelopeCode request)
          (Nat.pair (symmetricEnvelopeCode request)
            (symmetricRowMaskPair request liveScale input))
          (symmetricOccurrencePopulation request) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricRowTableRequestStageBits]
  have hpopulationFrameBits :
      rowPopulationFrameBits (symmetricEnvelopeCode request)
          (symmetricOccurrencePopulation request)
          (symmetricRowMaskPair request liveScale input) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricRowTableRequestStageBits]
  have hpoolBits :
      preserveRightBits (symmetricOccurrencePoolTreeBits request)
          (symmetricEnvelopeCode request)
          (Nat.pair (symmetricOccurrencePopulation request)
            (symmetricRowMaskPair request liveScale input))
          (symmetricRowPoolTree request) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricRowTableRequestStageBits]
  have htraversalFrameBits :
      rowTraversalFrameBits (symmetricOccurrencePopulation request)
          (symmetricRowPoolTree request)
          (symmetricRowMaskPair request liveScale input) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricRowTableRequestStageBits]
  have hlistBits :
      preserveRightBits
          (occurrencePoolRequestListBits (symmetricRowOccurrences request)
            (encodeBitInput input) (symmetricRowLiveMask request liveScale))
          (generatedBalancedRangeInput (symmetricOccurrencePopulation request)
            (occurrencePoolContext (symmetricRowOccurrences request)
              (encodeBitInput input)
              (symmetricRowLiveMask request liveScale)))
          (symmetricOccurrencePopulation request)
          (encodeBalancedList
            (residualAssignmentRequests (symmetricRowOccurrences request)
              (encodeBitInput input)
              (symmetricRowLiveMask request liveScale))) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricRowTableRequestStageBits]
  have hhandoff :
      symmetricFourfoldRowTailHandoff algorithm request rowIndex input =
        fourfoldRowTailHandoff
          (symmetricFourfoldRowBottomForest algorithm request)
          (symmetricEnvelopeCode request) symmetricCircuitFamilyTag request.q
          rowIndex (encodeBitInput input) := by
    unfold symmetricFourfoldRowTailHandoff
    rw [symmetricRowRequest_envelopeCode]
  have hstageOne :
      runNPOracleProgram rowHandoffEnvelopeInputProgram maximumBits 10
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (envelopeInputFrame (symmetricEnvelopeCode request)
            (encodeBitInput input)) := by
    rw [hhandoff]
    exact run_rowHandoffEnvelopeInputProgram
      (symmetricFourfoldRowBottomForest algorithm request)
      (symmetricEnvelopeCode request) symmetricCircuitFamilyTag request.q
      rowIndex (encodeBitInput input) maximumBits hframeBits
  have hstageTwo :
      runNPOracleProgram (preserveRightProgram (symmetricLiveMaskProgram liveScale))
          maximumBits (preserveRightFuel (symmetricLiveMaskFuel liveScale request))
          (initialNPOracleState request.q
            (envelopeInputFrame (symmetricEnvelopeCode request)
              (encodeBitInput input))) =
        some
          (Nat.pair (symmetricRowLiveMask request liveScale)
            (Nat.pair (symmetricEnvelopeCode request)
              (Nat.pair (symmetricEnvelopeCode request)
                (encodeBitInput input)))) :=
    run_bits_mono
      (run_preserveRightProgram (symmetricLiveMaskProgram liveScale) request.q
        (symmetricLiveMaskBits liveScale request)
        (symmetricLiveMaskFuel liveScale request)
        (symmetricEnvelopeCode request)
        (Nat.pair (symmetricEnvelopeCode request)
          (Nat.pair (symmetricEnvelopeCode request) (encodeBitInput input)))
        (symmetricRowLiveMask request liveScale)
        (run_symmetricLiveMaskProgram_rowMask liveScale request
          (symmetricLiveMaskBits liveScale request) le_rfl hroundBits))
      hliveBits
  have hstageThree :
      runNPOracleProgram rowLiveMaskFrameProgram maximumBits 9
          (initialNPOracleState request.q
            (Nat.pair (symmetricRowLiveMask request liveScale)
              (Nat.pair (symmetricEnvelopeCode request)
                (Nat.pair (symmetricEnvelopeCode request)
                  (encodeBitInput input))))) =
        some
          (envelopeMaskFrame (symmetricEnvelopeCode request)
            (encodeBitInput input)
            (symmetricRowLiveMask request liveScale)) :=
    run_rowLiveMaskFrameProgram request.q (symmetricEnvelopeCode request)
      (encodeBitInput input) (symmetricRowLiveMask request liveScale)
      maximumBits hliveFrameBits
  have hstageFour :
      runNPOracleProgram
          (preserveRightProgram symmetricOccurrencePopulationProgram)
          maximumBits
          (preserveRightFuel (symmetricOccurrencePopulationFuel request))
          (initialNPOracleState request.q
            (envelopeMaskFrame (symmetricEnvelopeCode request)
              (encodeBitInput input)
              (symmetricRowLiveMask request liveScale))) =
        some
          (Nat.pair (symmetricOccurrencePopulation request)
            (Nat.pair (symmetricEnvelopeCode request)
              (symmetricRowMaskPair request liveScale input))) :=
    run_bits_mono
      (run_preserveRightProgram symmetricOccurrencePopulationProgram request.q
        (symmetricOccurrencePopulationBits request)
        (symmetricOccurrencePopulationFuel request)
        (symmetricEnvelopeCode request)
        (Nat.pair (symmetricEnvelopeCode request)
          (symmetricRowMaskPair request liveScale input))
        (symmetricOccurrencePopulation request)
        (run_symmetricOccurrencePopulationProgram request
          (symmetricOccurrencePopulationBits request) le_rfl))
      hpopulationBits
  have hstageFive :
      runNPOracleProgram rowPopulationFrameProgram maximumBits 7
          (initialNPOracleState request.q
            (Nat.pair (symmetricOccurrencePopulation request)
              (Nat.pair (symmetricEnvelopeCode request)
                (symmetricRowMaskPair request liveScale input)))) =
        some
          (envelopePopulationFrame (symmetricEnvelopeCode request)
            (symmetricOccurrencePopulation request)
            (symmetricRowMaskPair request liveScale input)) :=
    run_rowPopulationFrameProgram request.q (symmetricEnvelopeCode request)
      (symmetricOccurrencePopulation request)
      (symmetricRowMaskPair request liveScale input) maximumBits
      hpopulationFrameBits
  have hstageSix :
      runNPOracleProgram
          (preserveRightProgram symmetricOccurrencePoolTreeProgram) maximumBits
          (preserveRightFuel (symmetricOccurrencePoolTreeFuel request))
          (initialNPOracleState request.q
            (envelopePopulationFrame (symmetricEnvelopeCode request)
              (symmetricOccurrencePopulation request)
              (symmetricRowMaskPair request liveScale input))) =
        some
          (Nat.pair (symmetricRowPoolTree request)
            (Nat.pair (symmetricOccurrencePopulation request)
              (symmetricRowMaskPair request liveScale input))) :=
    run_bits_mono
      (run_preserveRightProgram symmetricOccurrencePoolTreeProgram request.q
        (symmetricOccurrencePoolTreeBits request)
        (symmetricOccurrencePoolTreeFuel request)
        (symmetricEnvelopeCode request)
        (Nat.pair (symmetricOccurrencePopulation request)
          (symmetricRowMaskPair request liveScale input))
        (symmetricRowPoolTree request)
        (run_symmetricOccurrencePoolTreeProgram request
          (symmetricOccurrencePoolTreeBits request) le_rfl))
      hpoolBits
  have hstageSeven :
      runNPOracleProgram rowTraversalFrameProgram maximumBits 9
          (initialNPOracleState request.q
            (Nat.pair (symmetricRowPoolTree request)
              (Nat.pair (symmetricOccurrencePopulation request)
                (symmetricRowMaskPair request liveScale input)))) =
        some
          (poolTraversalFrame (symmetricOccurrencePopulation request)
            (symmetricRowPoolTree request)
            (symmetricRowMaskPair request liveScale input)) :=
    run_rowTraversalFrameProgram request.q
      (symmetricOccurrencePopulation request) (symmetricRowPoolTree request)
      (symmetricRowMaskPair request liveScale input) maximumBits
      htraversalFrameBits
  have hstageEight :
      runNPOracleProgram
          (preserveRightProgram occurrencePoolRequestListProgram) maximumBits
          (preserveRightFuel
            (occurrencePoolRequestListFuel (symmetricRowOccurrences request)
              (encodeBitInput input)
              (symmetricRowLiveMask request liveScale)))
          (initialNPOracleState request.q
            (poolTraversalFrame (symmetricOccurrencePopulation request)
              (symmetricRowPoolTree request)
              (symmetricRowMaskPair request liveScale input))) =
        some
          (residualAssignmentTableInput (symmetricRowOccurrences request)
            (encodeBitInput input)
            (symmetricRowLiveMask request liveScale)) :=
    run_bits_mono
      (run_preserveRightProgram occurrencePoolRequestListProgram request.q
        (occurrencePoolRequestListBits (symmetricRowOccurrences request)
          (encodeBitInput input) (symmetricRowLiveMask request liveScale))
        (occurrencePoolRequestListFuel (symmetricRowOccurrences request)
          (encodeBitInput input) (symmetricRowLiveMask request liveScale))
        (generatedBalancedRangeInput (symmetricOccurrencePopulation request)
          (occurrencePoolContext (symmetricRowOccurrences request)
            (encodeBitInput input) (symmetricRowLiveMask request liveScale)))
        (symmetricOccurrencePopulation request)
        (encodeBalancedList
          (residualAssignmentRequests (symmetricRowOccurrences request)
            (encodeBitInput input) (symmetricRowLiveMask request liveScale)))
        (run_occurrencePoolRequestListProgram (symmetricRowOccurrences request)
          (encodeBitInput input) (symmetricRowLiveMask request liveScale)
          (occurrencePoolRequestListBits (symmetricRowOccurrences request)
            (encodeBitInput input) (symmetricRowLiveMask request liveScale))
          le_rfl))
      hlistBits
  have htailSix :
      runNPOracleProgram rowTableRequestTailSix maximumBits
          (linkFuel rowTableRequestTailSeven 9
            (preserveRightFuel
              (occurrencePoolRequestListFuel (symmetricRowOccurrences request)
                (encodeBitInput input)
                (symmetricRowLiveMask request liveScale))))
          (initialNPOracleState request.q
            (Nat.pair (symmetricRowPoolTree request)
              (Nat.pair (symmetricOccurrencePopulation request)
                (symmetricRowMaskPair request liveScale input)))) =
        some
          (residualAssignmentTableInput (symmetricRowOccurrences request)
            (encodeBitInput input)
            (symmetricRowLiveMask request liveScale)) :=
    run_linkPrograms hpositive hlength hstageSeven hstageEight
  have htailFive :
      runNPOracleProgram rowTableRequestTailFive maximumBits
          (linkFuel rowTableRequestTailSix
            (preserveRightFuel (symmetricOccurrencePoolTreeFuel request))
            (linkFuel rowTableRequestTailSeven 9
              (preserveRightFuel
                (occurrencePoolRequestListFuel
                  (symmetricRowOccurrences request) (encodeBitInput input)
                  (symmetricRowLiveMask request liveScale)))))
          (initialNPOracleState request.q
            (envelopePopulationFrame (symmetricEnvelopeCode request)
              (symmetricOccurrencePopulation request)
              (symmetricRowMaskPair request liveScale input))) =
        some
          (residualAssignmentTableInput (symmetricRowOccurrences request)
            (encodeBitInput input)
            (symmetricRowLiveMask request liveScale)) :=
    run_linkPrograms hpositive hlength hstageSix htailSix
  have htailFour :
      runNPOracleProgram rowTableRequestTailFour maximumBits
          (linkFuel rowTableRequestTailFive 7
            (linkFuel rowTableRequestTailSix
              (preserveRightFuel (symmetricOccurrencePoolTreeFuel request))
              (linkFuel rowTableRequestTailSeven 9
                (preserveRightFuel
                  (occurrencePoolRequestListFuel
                    (symmetricRowOccurrences request) (encodeBitInput input)
                    (symmetricRowLiveMask request liveScale))))))
          (initialNPOracleState request.q
            (Nat.pair (symmetricOccurrencePopulation request)
              (Nat.pair (symmetricEnvelopeCode request)
                (symmetricRowMaskPair request liveScale input)))) =
        some
          (residualAssignmentTableInput (symmetricRowOccurrences request)
            (encodeBitInput input)
            (symmetricRowLiveMask request liveScale)) :=
    run_linkPrograms hpositive hlength hstageFive htailFive
  have htailThree :
      runNPOracleProgram rowTableRequestTailThree maximumBits
          (linkFuel rowTableRequestTailFour
            (preserveRightFuel (symmetricOccurrencePopulationFuel request))
            (linkFuel rowTableRequestTailFive 7
              (linkFuel rowTableRequestTailSix
                (preserveRightFuel (symmetricOccurrencePoolTreeFuel request))
                (linkFuel rowTableRequestTailSeven 9
                  (preserveRightFuel
                    (occurrencePoolRequestListFuel
                      (symmetricRowOccurrences request) (encodeBitInput input)
                      (symmetricRowLiveMask request liveScale)))))))
          (initialNPOracleState request.q
            (envelopeMaskFrame (symmetricEnvelopeCode request)
              (encodeBitInput input)
              (symmetricRowLiveMask request liveScale))) =
        some
          (residualAssignmentTableInput (symmetricRowOccurrences request)
            (encodeBitInput input)
            (symmetricRowLiveMask request liveScale)) :=
    run_linkPrograms hpositive hlength hstageFour htailFour
  have htailTwo :
      runNPOracleProgram rowTableRequestTailTwo maximumBits
          (linkFuel rowTableRequestTailThree 9
            (linkFuel rowTableRequestTailFour
              (preserveRightFuel (symmetricOccurrencePopulationFuel request))
              (linkFuel rowTableRequestTailFive 7
                (linkFuel rowTableRequestTailSix
                  (preserveRightFuel (symmetricOccurrencePoolTreeFuel request))
                  (linkFuel rowTableRequestTailSeven 9
                    (preserveRightFuel
                      (occurrencePoolRequestListFuel
                        (symmetricRowOccurrences request)
                        (encodeBitInput input)
                        (symmetricRowLiveMask request liveScale))))))))
          (initialNPOracleState request.q
            (Nat.pair (symmetricRowLiveMask request liveScale)
              (Nat.pair (symmetricEnvelopeCode request)
                (Nat.pair (symmetricEnvelopeCode request)
                  (encodeBitInput input))))) =
        some
          (residualAssignmentTableInput (symmetricRowOccurrences request)
            (encodeBitInput input)
            (symmetricRowLiveMask request liveScale)) :=
    run_linkPrograms hpositive hlength hstageThree htailThree
  have htailOne :
      runNPOracleProgram (rowTableRequestTailOne liveScale) maximumBits
          (linkFuel rowTableRequestTailTwo
            (preserveRightFuel (symmetricLiveMaskFuel liveScale request))
            (linkFuel rowTableRequestTailThree 9
              (linkFuel rowTableRequestTailFour
                (preserveRightFuel (symmetricOccurrencePopulationFuel request))
                (linkFuel rowTableRequestTailFive 7
                  (linkFuel rowTableRequestTailSix
                    (preserveRightFuel
                      (symmetricOccurrencePoolTreeFuel request))
                    (linkFuel rowTableRequestTailSeven 9
                      (preserveRightFuel
                        (occurrencePoolRequestListFuel
                          (symmetricRowOccurrences request)
                          (encodeBitInput input)
                          (symmetricRowLiveMask request liveScale)))))))))
          (initialNPOracleState request.q
            (envelopeInputFrame (symmetricEnvelopeCode request)
              (encodeBitInput input))) =
        some
          (residualAssignmentTableInput (symmetricRowOccurrences request)
            (encodeBitInput input)
            (symmetricRowLiveMask request liveScale)) :=
    run_linkPrograms hpositive hlength hstageTwo htailTwo
  exact run_linkPrograms hpositive hlength hstageOne htailOne

/-! ## §6 The symmetric row evaluator over its compiled front end

§5 is exactly the `hrequest` premise both consumers carry, so instantiating
them at `symmetricRowTableRequestProgram` leaves the symmetric row evaluator
with the polynomial producer as its only interpreter premise. -/

/-- **The symmetric row table producer, front end included.** -/
def symmetricRowTableProgramCompiled (liveScale : ℕ) : NPOracleProgram :=
  symmetricRowTableProgram (symmetricRowTableRequestProgram liveScale)

theorem symmetricRowTableProgramCompiled_oracleFree (liveScale : ℕ) :
    OracleFree (symmetricRowTableProgramCompiled liveScale) :=
  symmetricRowTableProgram_oracleFree (symmetricRowTableRequestProgram liveScale)
    (symmetricRowTableRequestProgram_oracleFree liveScale)

def symmetricRowTableCompiledBits (liveScale : ℕ)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) : ℕ :=
  max
    (symmetricRowTableStageBits request liveScale input (encodeBitInput input)
      (symmetricRowLiveMask request liveScale))
    (symmetricRowTableRequestBits liveScale algorithm request rowIndex input)

/-- **The symmetric row's residual assignment context, executed from the
handoff with no link-time producer left.**  This is
`CanonicalSymmetricRowTableProgram.run_symmetricRowTableProgram` with both
`hlive` and `hrequest` discharged. -/
theorem run_symmetricRowTableProgramCompiled (liveScale : ℕ)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex maximumBits : ℕ) (input : BitInput request.q)
    (hbits :
      symmetricRowTableCompiledBits liveScale algorithm request rowIndex
          input ≤
        maximumBits)
    (hroundBits : ∀ (selected : Finset (Fin request.q)) (stepCount counter : ℕ),
      counter + 1 ≤ request.q →
      stepCount ≤ normalizedLiveCount request.q liveScale →
      touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
          stepCount (request.q - (counter + 1)) counter ≤
        symmetricLiveMaskBits liveScale request) :
    runNPOracleProgram (symmetricRowTableProgramCompiled liveScale) maximumBits
        (symmetricRowTableFuel request
          (symmetricRowTableRequestFuel liveScale request input)
          (encodeBitInput input) (symmetricRowLiveMask request liveScale))
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
      some
        (finiteAssignmentContext
          (symmetricRowResidualAssignment request liveScale input)) :=
  run_symmetricRowTableProgram (symmetricRowTableRequestProgram liveScale)
    algorithm request liveScale rowIndex input
    (symmetricRowLiveMask request liveScale) maximumBits
    (symmetricRowTableRequestFuel liveScale request input) rfl
    ((Nat.le_max_left _ _).trans hbits)
    (run_symmetricRowTableRequestProgram liveScale algorithm request rowIndex
      maximumBits input ((Nat.le_max_right _ _).trans hbits) hroundBits)

/-- **The symmetric fork row evaluator, table side compiled.** -/
def symmetricRowForkEvaluatorProgramCompiled
    (liveScale : ℕ) (polynomialProgram : NPOracleProgram) : NPOracleProgram :=
  symmetricRowForkEvaluatorProgram (symmetricRowTableRequestProgram liveScale)
    polynomialProgram

theorem symmetricRowForkEvaluatorProgramCompiled_oracleFree
    (liveScale : ℕ) (polynomialProgram : NPOracleProgram)
    (hpolynomial : OracleFree polynomialProgram) :
    OracleFree
      (symmetricRowForkEvaluatorProgramCompiled liveScale polynomialProgram) :=
  symmetricRowForkEvaluatorProgram_oracleFree
    (symmetricRowTableRequestProgram liveScale) polynomialProgram
    (symmetricRowTableRequestProgram_oracleFree liveScale) hpolynomial

/-- **The symmetric fork row evaluator at the computed live mask over its
compiled front end.**  Every premise about the table side is now a width bound;
the only interpreter premise left on the symmetric row evaluator is
`hpolynomial`. -/
theorem run_symmetricRowForkEvaluatorProgramCompiled (liveScale : ℕ)
    (polynomialProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (maximumBits tableBits polynomialBits polynomialFuel : ℕ)
    (htableBits :
      symmetricRowTableStageBits request liveScale input
          (encodeBitInput input) (symmetricRowLiveMask request liveScale) ≤
        tableBits)
    (hrequestBits :
      symmetricRowTableRequestBits liveScale algorithm request rowIndex
          input ≤
        tableBits)
    (hroundBits : ∀ (selected : Finset (Fin request.q)) (stepCount counter : ℕ),
      counter + 1 ≤ request.q →
      stepCount ≤ normalizedLiveCount request.q liveScale →
      touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
          stepCount (request.q - (counter + 1)) counter ≤
        symmetricLiveMaskBits liveScale request)
    (hbits :
      structuralForkRowEvaluatorBits request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
          tableBits polynomialBits
          (symmetricRowResidualAssignment request liveScale input)
          (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
            input) ≤
        maximumBits)
    (hpolynomial :
      runNPOracleProgram polynomialProgram polynomialBits polynomialFuel
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (encodedStructuralGF2
            (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
              input))) :
    runNPOracleProgram
        (symmetricRowForkEvaluatorProgramCompiled liveScale polynomialProgram)
        maximumBits
        (symmetricRowForkEvaluatorFuel
          (symmetricRowTableRequestProgram liveScale) polynomialProgram request
          liveScale accuracyExponent rowIndex input
          (symmetricRowTableRequestFuel liveScale request input) polynomialFuel
          (symmetricRowLiveMask request liveScale))
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) :=
  run_symmetricRowForkEvaluatorProgram_computedMask
    (symmetricRowTableRequestProgram liveScale) polynomialProgram algorithm
    request liveScale accuracyExponent rowIndex input maximumBits tableBits
    polynomialBits (symmetricRowTableRequestFuel liveScale request input)
    polynomialFuel htableBits hbits
    (run_symmetricRowTableRequestProgram liveScale algorithm request rowIndex
      tableBits input hrequestBits hroundBits)
    hpolynomial

end NearCubicWires.CanonicalSymmetricRowTableRequestProgram
