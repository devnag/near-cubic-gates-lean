import Proof.Circuits.CanonicalBalancedBuilder
import Proof.MachineModel.CanonicalTouchingSweepRoundProgram

/-!
# The symmetric occurrence pool's support masks, executed from the envelope

`CanonicalTouchingSweepRoundProgram` runs the whole greedy sweep on the pool's
`coordinateMask` list, but it receives that list as data.  This module produces
it from the typed request envelope, so the symmetric counting path no longer
assumes any preprocessed input.

Three structural facts make the stage a straight composition of already
compiled pieces.

* The symmetric family's occurrence pool is the concatenation of the circuits'
  bottom fans: `symmetricCircuitOccurrences circuit = List.ofFn circuit.bottom`.
  No retained-index selection happens on this side.
* The bottom fan is the *third* field of the circuit's canonical tagged-list
  encoding, and it is already a balanced list of gate codes.
* One gate's support is the *third* field of its own tagged-list encoding, as a
  canonical `encodeBoolList`.  Since `encodeBoolList` is a balanced list of bit
  codes and `coordinateMask` is the little-endian numeral of the same bits, the
  existing `canonicalNatDecodeProgram` — a balanced-to-tagged flattener followed
  by the tagged little-endian fold — computes the mask exactly.  No counted
  coordinate loop and no power-of-two table are needed.

The remaining work is shape: the outer balanced map produces one balanced mask
list per circuit, while the pool wants a single flat one.  Both directions of
the canonical list conversion are already verified
(`balancedBitsToTaggedProgram`, `taggedToBalancedProgram`), so the flattening is
`BalancedClauseStreamFlattenProgram` between them.
-/

namespace NearCubicWires.CanonicalSymmetricSupportMaskProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalTouchingSweepRoundProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
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

/-! ## §1 The third tagged field -/

/-- Third field of a canonical tagged list, read structurally. -/
def taggedFieldTwo (code : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair
      (Nat.unpair
        (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2).2).2).1

/-- Read the third field of a canonical tagged list. -/
def taggedFieldTwoProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .unpairRight 0 0 2
  , .unpairRight 0 0 3
  , .unpairRight 0 0 4
  , .unpairRight 0 0 5
  , .unpairLeft 0 0 6
  , .halt 0
  ]

@[simp] theorem taggedFieldTwoProgram_oracleFree :
    OracleFree taggedFieldTwoProgram := by
  rfl

def taggedFieldTwoBits (code : ℕ) : ℕ := natBitLength code

theorem run_taggedFieldTwoProgram (inputLength code : ℕ) :
    runNPOracleProgram taggedFieldTwoProgram (taggedFieldTwoBits code) 7
        (initialNPOracleState inputLength code) =
      some (taggedFieldTwo code) := by
  have hcode : natBitLength code ≤ taggedFieldTwoBits code := Nat.le_refl _
  have hfirst : natBitLength (Nat.unpair code).2 ≤ taggedFieldTwoBits code :=
    bits_of_le (Nat.unpair_right_le code) hcode
  have hsecond :
      natBitLength (Nat.unpair (Nat.unpair code).2).2 ≤
        taggedFieldTwoBits code :=
    bits_of_le (Nat.unpair_right_le _) hfirst
  have hthird :
      natBitLength (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2 ≤
        taggedFieldTwoBits code :=
    bits_of_le (Nat.unpair_right_le _) hsecond
  have hfourth :
      natBitLength
          (Nat.unpair
            (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2).2 ≤
        taggedFieldTwoBits code :=
    bits_of_le (Nat.unpair_right_le _) hthird
  have hfifth :
      natBitLength
          (Nat.unpair
            (Nat.unpair
              (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2).2).2 ≤
        taggedFieldTwoBits code :=
    bits_of_le (Nat.unpair_right_le _) hfourth
  have hsixth : natBitLength (taggedFieldTwo code) ≤ taggedFieldTwoBits code :=
    bits_of_le (Nat.unpair_left_le _) hfifth
  rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair code).2) (by rfl) rfl
    (by simp [initialNPOracleState]) hfirst]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair code).2).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsecond]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthird]
  rw [run_unpairRight_instruction
    (value :=
      (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2).2)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfourth]
  rw [run_unpairRight_instruction
    (value :=
      (Nat.unpair
        (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2).2).2)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfifth]
  rw [run_unpairLeft_instruction (value := taggedFieldTwo code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, taggedFieldTwo])
    hsixth]
  exact run_halt_instruction (fuel := 0) (value := taggedFieldTwo code)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hsixth

theorem taggedFieldTwo_encodeSupportedNormalizedGate {n : ℕ}
    (gate : SupportedNormalizedGate n) :
    taggedFieldTwo (encodeSupportedNormalizedGate gate) =
      encodeBoolList (List.ofFn fun index => decide (index ∈ gate.support)) := by
  simp [taggedFieldTwo, encodeSupportedNormalizedGate, encodeTaggedList]

theorem taggedFieldTwo_encodeNormalizedSymmetricThresholdCircuit {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) :
    taggedFieldTwo (encodeNormalizedSymmetricThresholdCircuit circuit) =
      encodeBalancedList
        (List.ofFn fun index =>
          encodeSupportedNormalizedGate (circuit.bottom index)) := by
  simp [taggedFieldTwo, encodeNormalizedSymmetricThresholdCircuit,
    encodeTaggedList]

/-! ## §2 A canonical bit list is its own coordinate mask -/

private theorem bitsValue_ofFn :
    ∀ {q : ℕ} (values : Fin q → Bool),
      bitsValue (List.ofFn values) = Nat.ofBits values := by
  intro q
  induction q with
  | zero =>
      intro values
      simp [bitsValue]
  | succ count inductionHypothesis =>
      intro values
      rw [List.ofFn_succ]
      change (values 0).toNat +
          2 * bitsValue (List.ofFn fun index : Fin count => values index.succ) =
        Nat.ofBits values
      rw [inductionHypothesis fun index : Fin count => values index.succ]
      rw [Nat.ofBits_succ values]
      change (values 0).toNat + 2 * Nat.ofBits (values ∘ Fin.succ) =
        2 * Nat.ofBits (values ∘ Fin.succ) + (values 0).toNat
      omega

/-- The canonical `encodeBoolList` support field and the sweep's
`coordinateMask` numeral carry the same bits in the same order. -/
theorem bitsValue_support_eq_coordinateMask {q : ℕ} (values : Finset (Fin q)) :
    bitsValue (List.ofFn fun index : Fin q => decide (index ∈ values)) =
      coordinateMask values :=
  bitsValue_ofFn fun index : Fin q => decide (index ∈ values)

private theorem taggedBitFoldValue_boolCodes (values : List Bool) :
    taggedBitFoldValue (values.map boolCode) 0 1 = bitsValue values :=
  taggedBitFoldValue_boolBits values

/-! ## §3 One gate's support mask -/

/-- Raw balanced payload of a gate code's support field. -/
def encodedGateSupportRawBits (code : ℕ) : List ℕ :=
  (decodeBalancedList (taggedFieldTwo code)).getD []

/-- Support mask of one encoded gate, read structurally from its canonical
tagged-list encoding. -/
def encodedGateSupportMask (code : ℕ) : ℕ :=
  taggedBitFoldValue (encodedGateSupportRawBits code) 0 1

theorem encodedGateSupportRawBits_encode {n : ℕ}
    (gate : SupportedNormalizedGate n) :
    encodedGateSupportRawBits (encodeSupportedNormalizedGate gate) =
      (List.ofFn fun index : Fin n => decide (index ∈ gate.support)).map
        boolCode := by
  unfold encodedGateSupportRawBits
  rw [taggedFieldTwo_encodeSupportedNormalizedGate]
  unfold encodeBoolList
  rw [decodeBalancedList_encode]
  rfl

theorem encodeBalancedList_encodedGateSupportRawBits {n : ℕ}
    (gate : SupportedNormalizedGate n) :
    encodeBalancedList
        (encodedGateSupportRawBits (encodeSupportedNormalizedGate gate)) =
      taggedFieldTwo (encodeSupportedNormalizedGate gate) := by
  rw [encodedGateSupportRawBits_encode,
    taggedFieldTwo_encodeSupportedNormalizedGate]
  rfl

theorem encodedGateSupportMask_encode {n : ℕ}
    (gate : SupportedNormalizedGate n) :
    encodedGateSupportMask (encodeSupportedNormalizedGate gate) =
      coordinateMask gate.support := by
  unfold encodedGateSupportMask
  rw [encodedGateSupportRawBits_encode, taggedBitFoldValue_boolCodes]
  exact bitsValue_support_eq_coordinateMask gate.support

/-- **The per-gate support-mask reader.**  Repair the balanced-call atom, read
the tagged support field, and fold its canonical bit list into the little-endian
`coordinateMask` numeral. -/
def gateSupportMaskProgram : NPOracleProgram :=
  linkPrograms repairAtomProgram
    (linkPrograms taggedFieldTwoProgram canonicalNatDecodeProgram)

theorem gateSupportMaskProgram_oracleFree : OracleFree gateSupportMaskProgram :=
  oracleFree_linkPrograms repairAtomProgram_oracleFree
    (oracleFree_linkPrograms taggedFieldTwoProgram_oracleFree
      canonicalNatDecodeProgram_oracleFree)

def gateSupportMaskFuel (code : ℕ) : ℕ :=
  linkFuel (linkPrograms taggedFieldTwoProgram canonicalNatDecodeProgram) 2
    (linkFuel canonicalNatDecodeProgram 7
      (canonicalNatDecodeListFuel (encodedGateSupportRawBits code)))

def gateSupportMaskBits (code : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength code)
      (canonicalNatDecodeListBits (Nat.unpair code).1
        (encodedGateSupportRawBits code))

theorem run_gateSupportMaskProgram {n : ℕ} (gate : SupportedNormalizedGate n)
    (maximumBits : ℕ)
    (hbits :
      gateSupportMaskBits (encodeSupportedNormalizedGate gate) ≤ maximumBits) :
    runNPOracleProgram gateSupportMaskProgram maximumBits
        (gateSupportMaskFuel (encodeSupportedNormalizedGate gate))
        (initialNPOracleState
          (Nat.unpair (encodeSupportedNormalizedGate gate)).1
          (Nat.unpair (encodeSupportedNormalizedGate gate)).2) =
      some (encodedGateSupportMask (encodeSupportedNormalizedGate gate)) := by
  have hpositive : 1 ≤ maximumBits := (Nat.le_max_left _ _).trans hbits
  have hcodeBits :
      natBitLength (encodeSupportedNormalizedGate gate) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have hdecodeBits :
      canonicalNatDecodeListBits
          (Nat.unpair (encodeSupportedNormalizedGate gate)).1
          (encodedGateSupportRawBits (encodeSupportedNormalizedGate gate)) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have hlength :
      natBitLength (Nat.unpair (encodeSupportedNormalizedGate gate)).1 ≤
        maximumBits :=
    bits_of_le (Nat.unpair_left_le _) hcodeBits
  have hpair :
      Nat.pair (Nat.unpair (encodeSupportedNormalizedGate gate)).1
          (Nat.unpair (encodeSupportedNormalizedGate gate)).2 =
        encodeSupportedNormalizedGate gate :=
    Nat.pair_unpair _
  have hstageOne :
      runNPOracleProgram repairAtomProgram maximumBits 2
          (initialNPOracleState
            (Nat.unpair (encodeSupportedNormalizedGate gate)).1
            (Nat.unpair (encodeSupportedNormalizedGate gate)).2) =
        some (encodeSupportedNormalizedGate gate) := by
    have hatomBits :
        repairAtomBits (Nat.unpair (encodeSupportedNormalizedGate gate)).1
            (Nat.unpair (encodeSupportedNormalizedGate gate)).2 ≤
          maximumBits := by
      unfold repairAtomBits
      rw [hpair]
      exact hcodeBits
    have hrun :=
      run_repairAtomProgram (Nat.unpair (encodeSupportedNormalizedGate gate)).1
        (Nat.unpair (encodeSupportedNormalizedGate gate)).2
    rw [hpair] at hrun
    exact run_bits_mono hrun hatomBits
  have hstageTwo :
      runNPOracleProgram taggedFieldTwoProgram maximumBits 7
          (initialNPOracleState
            (Nat.unpair (encodeSupportedNormalizedGate gate)).1
            (encodeSupportedNormalizedGate gate)) =
        some (taggedFieldTwo (encodeSupportedNormalizedGate gate)) :=
    run_bits_mono
      (run_taggedFieldTwoProgram
        (Nat.unpair (encodeSupportedNormalizedGate gate)).1
        (encodeSupportedNormalizedGate gate))
      hcodeBits
  have hstageThree :
      runNPOracleProgram canonicalNatDecodeProgram maximumBits
          (canonicalNatDecodeListFuel
            (encodedGateSupportRawBits (encodeSupportedNormalizedGate gate)))
          (initialNPOracleState
            (Nat.unpair (encodeSupportedNormalizedGate gate)).1
            (taggedFieldTwo (encodeSupportedNormalizedGate gate))) =
        some
          (encodedGateSupportMask (encodeSupportedNormalizedGate gate)) := by
    have hrun :=
      run_canonicalNatDecodeProgram_fromList
        (Nat.unpair (encodeSupportedNormalizedGate gate)).1
        (encodedGateSupportRawBits (encodeSupportedNormalizedGate gate))
    rw [encodeBalancedList_encodedGateSupportRawBits gate] at hrun
    exact run_bits_mono hrun hdecodeBits
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo hstageThree)

/-! ## §4 One circuit's support-mask stream -/

/-- Raw balanced payload of a circuit code's bottom-fan field. -/
def encodedCircuitGateCodes (code : ℕ) : List ℕ :=
  (decodeBalancedList (taggedFieldTwo code)).getD []

/-- Support masks of one encoded circuit's bottom fan, in canonical gate
order. -/
def encodedCircuitSupportMasks (code : ℕ) : List ℕ :=
  (encodedCircuitGateCodes code).map encodedGateSupportMask

/-- The same masks as a canonical tagged stream, ready for concatenation. -/
def encodedCircuitSupportStream (code : ℕ) : ℕ :=
  encodeTaggedList (encodedCircuitSupportMasks code)

theorem encodedCircuitGateCodes_encode {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) :
    encodedCircuitGateCodes
        (encodeNormalizedSymmetricThresholdCircuit circuit) =
      List.ofFn fun index =>
        encodeSupportedNormalizedGate (circuit.bottom index) := by
  unfold encodedCircuitGateCodes
  rw [taggedFieldTwo_encodeNormalizedSymmetricThresholdCircuit,
    decodeBalancedList_encode]
  rfl

theorem encodeBalancedList_encodedCircuitGateCodes {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) :
    encodeBalancedList
        (encodedCircuitGateCodes
          (encodeNormalizedSymmetricThresholdCircuit circuit)) =
      taggedFieldTwo (encodeNormalizedSymmetricThresholdCircuit circuit) := by
  rw [encodedCircuitGateCodes_encode,
    taggedFieldTwo_encodeNormalizedSymmetricThresholdCircuit]

theorem encodedCircuitSupportMasks_encode {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) :
    encodedCircuitSupportMasks
        (encodeNormalizedSymmetricThresholdCircuit circuit) =
      occurrenceSupportMasks (symmetricCircuitOccurrences circuit) := by
  unfold encodedCircuitSupportMasks occurrenceSupportMasks
    symmetricCircuitOccurrences
  rw [encodedCircuitGateCodes_encode, List.map_ofFn, List.map_ofFn]
  have hfunction :
      (encodedGateSupportMask ∘ fun index : Fin circuit.bottomCount =>
          encodeSupportedNormalizedGate (circuit.bottom index)) =
        ((fun gate : SupportedNormalizedGate n =>
          coordinateMask gate.support) ∘ circuit.bottom) := by
    funext index
    simp only [Function.comp_apply]
    exact encodedGateSupportMask_encode (circuit.bottom index)
  rw [hfunction]

private def circuitSupportMaskInner : NPOracleProgram :=
  linkPrograms (balancedCallProgram gateSupportMaskProgram)
    balancedBitsToTaggedProgram

private def circuitSupportMaskTail : NPOracleProgram :=
  linkPrograms taggedFieldTwoProgram circuitSupportMaskInner

/-- **The per-circuit support-mask stream producer.**  Repair the atom, read the
bottom fan, map the per-gate reader across it, and hand the result on as a
canonical tagged stream so the outer stage can concatenate. -/
def circuitSupportMaskProgram : NPOracleProgram :=
  linkPrograms repairAtomProgram circuitSupportMaskTail

theorem circuitSupportMaskProgram_oracleFree :
    OracleFree circuitSupportMaskProgram :=
  oracleFree_linkPrograms repairAtomProgram_oracleFree
    (oracleFree_linkPrograms taggedFieldTwoProgram_oracleFree
      (oracleFree_linkPrograms
        (balancedCallProgram_oracleFree gateSupportMaskProgram_oracleFree)
        balancedBitsToTaggedProgram_oracleFree))

def circuitSupportMaskFuel (code : ℕ) : ℕ :=
  linkFuel circuitSupportMaskTail 2
    (linkFuel circuitSupportMaskInner 7
      (linkFuel balancedBitsToTaggedProgram
        (balancedCallFuel gateSupportMaskProgram gateSupportMaskFuel
          (encodedCircuitGateCodes code))
        (balancedBitsToTaggedFuel (encodedCircuitSupportMasks code))))

def circuitSupportMaskStageBits (code : ℕ) : List ℕ :=
  [ 1
  , natBitLength code
  , balancedCallRequiredBits encodedGateSupportMask
      (encodedCircuitGateCodes code)
  , ((encodedCircuitGateCodes code).map gateSupportMaskBits).foldr max 1
  , balancedBitsToTaggedBits (Nat.unpair code).1
      (encodedCircuitSupportMasks code)
  ]

def circuitSupportMaskBits (code : ℕ) : ℕ :=
  (circuitSupportMaskStageBits code).foldr max 1

set_option maxHeartbeats 1200000 in
-- Four linked stages, each widened to the shared register bound first; the

theorem run_circuitSupportMaskProgram {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) (maximumBits : ℕ)
    (hbits :
      circuitSupportMaskBits
          (encodeNormalizedSymmetricThresholdCircuit circuit) ≤
        maximumBits) :
    runNPOracleProgram circuitSupportMaskProgram maximumBits
        (circuitSupportMaskFuel
          (encodeNormalizedSymmetricThresholdCircuit circuit))
        (initialNPOracleState
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).2) =
      some
        (encodedCircuitSupportStream
          (encodeNormalizedSymmetricThresholdCircuit circuit)) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          circuitSupportMaskStageBits
            (encodeNormalizedSymmetricThresholdCircuit circuit)) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [circuitSupportMaskStageBits]
  have hcodeBits :
      natBitLength (encodeNormalizedSymmetricThresholdCircuit circuit) ≤
        maximumBits := by
    apply bits_of_member
    simp [circuitSupportMaskStageBits]
  have hcallBits :
      balancedCallRequiredBits encodedGateSupportMask
          (encodedCircuitGateCodes
            (encodeNormalizedSymmetricThresholdCircuit circuit)) ≤
        maximumBits := by
    apply bits_of_member
    simp [circuitSupportMaskStageBits]
  have hcalleeBits :
      ((encodedCircuitGateCodes
          (encodeNormalizedSymmetricThresholdCircuit circuit)).map
        gateSupportMaskBits).foldr max 1 ≤ maximumBits := by
    apply bits_of_member
    simp [circuitSupportMaskStageBits]
  have htaggedBits :
      balancedBitsToTaggedBits
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
          (encodedCircuitSupportMasks
            (encodeNormalizedSymmetricThresholdCircuit circuit)) ≤
        maximumBits := by
    apply bits_of_member
    simp [circuitSupportMaskStageBits]
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
  have hexec : ∀ code : ℕ,
      code ∈
        encodedCircuitGateCodes
          (encodeNormalizedSymmetricThresholdCircuit circuit) →
      runNPOracleProgram gateSupportMaskProgram maximumBits
          (gateSupportMaskFuel code)
          (initialNPOracleState (Nat.unpair code).1 (Nat.unpair code).2) =
        some (encodedGateSupportMask code) := by
    intro code hcode
    have hgateBits : gateSupportMaskBits code ≤ maximumBits := by
      refine le_trans ?_ hcalleeBits
      exact le_foldr_max_of_mem (List.mem_map_of_mem hcode)
    rw [encodedCircuitGateCodes_encode] at hcode
    obtain ⟨index, hindex⟩ := List.mem_ofFn.mp hcode
    rw [← hindex] at hgateBits ⊢
    exact run_gateSupportMaskProgram (circuit.bottom index) maximumBits
      hgateBits
  have hstageThree :
      runNPOracleProgram (balancedCallProgram gateSupportMaskProgram)
          maximumBits
          (balancedCallFuel gateSupportMaskProgram gateSupportMaskFuel
            (encodedCircuitGateCodes
              (encodeNormalizedSymmetricThresholdCircuit circuit)))
          (initialNPOracleState
            (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
            (taggedFieldTwo
              (encodeNormalizedSymmetricThresholdCircuit circuit))) =
        some
          (encodeBalancedList
            (encodedCircuitSupportMasks
              (encodeNormalizedSymmetricThresholdCircuit circuit))) := by
    have hrun :=
      run_balancedCallProgram_from (callee := gateSupportMaskProgram)
        (maximumBits := maximumBits)
        (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
        (encodedCircuitGateCodes
          (encodeNormalizedSymmetricThresholdCircuit circuit))
        gateSupportMaskFuel encodedGateSupportMask hcallBits hexec
    rw [encodeBalancedList_encodedCircuitGateCodes circuit] at hrun
    exact hrun
  have hstageFour :
      runNPOracleProgram balancedBitsToTaggedProgram maximumBits
          (balancedBitsToTaggedFuel
            (encodedCircuitSupportMasks
              (encodeNormalizedSymmetricThresholdCircuit circuit)))
          (initialNPOracleState
            (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
            (encodeBalancedList
              (encodedCircuitSupportMasks
                (encodeNormalizedSymmetricThresholdCircuit circuit)))) =
        some
          (encodedCircuitSupportStream
            (encodeNormalizedSymmetricThresholdCircuit circuit)) :=
    run_bits_mono
      (run_balancedBitsToTaggedProgram
        (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
        (encodedCircuitSupportMasks
          (encodeNormalizedSymmetricThresholdCircuit circuit)))
      htaggedBits
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo
      (run_linkPrograms hpositive hlength hstageThree hstageFour))

/-! ## §5 The pool's support-mask list -/

private theorem map_encodedCircuitSupportStream (codes : List ℕ) :
    codes.map encodedCircuitSupportStream =
      (codes.map encodedCircuitSupportMasks).map encodeTaggedList := by
  induction codes with
  | nil => rfl
  | cons code rest inductionHypothesis =>
      simp only [List.map_cons, inductionHypothesis,
        encodedCircuitSupportStream]

private theorem map_flatMap_symmetricCircuitOccurrences {n : ℕ}
    (circuits : List (NormalizedSymmetricThresholdCircuit n)) :
    occurrenceSupportMasks (circuits.flatMap symmetricCircuitOccurrences) =
      (circuits.map fun circuit =>
        occurrenceSupportMasks (symmetricCircuitOccurrences circuit)).flatten := by
  induction circuits with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_cons, List.flatten_cons]
      rw [← inductionHypothesis]
      simp [occurrenceSupportMasks]

/-- The per-circuit mask streams, before concatenation. -/
def symmetricSupportMaskStreams
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List (List ℕ) :=
  (request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
    encodedCircuitSupportMasks

theorem symmetricSupportMaskStreams_flatten
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (symmetricSupportMaskStreams request).flatten =
      occurrenceSupportMasks (symmetricFourfoldOccurrences request) := by
  unfold symmetricSupportMaskStreams
  rw [List.map_map]
  have hmasks :
      request.circuits.map
          (encodedCircuitSupportMasks ∘
            encodeNormalizedSymmetricThresholdCircuit) =
        request.circuits.map fun circuit =>
          occurrenceSupportMasks (symmetricCircuitOccurrences circuit) := by
    refine List.map_congr_left ?_
    intro circuit _
    simp only [Function.comp_apply]
    exact encodedCircuitSupportMasks_encode circuit
  rw [hmasks]
  unfold symmetricFourfoldOccurrences
  exact (map_flatMap_symmetricCircuitOccurrences request.circuits).symm

private def supportMaskTailThree : NPOracleProgram :=
  linkPrograms balancedClauseStreamFlattenProgram taggedToBalancedProgram

private def supportMaskTailTwo : NPOracleProgram :=
  linkPrograms (balancedCallProgram circuitSupportMaskProgram)
    supportMaskTailThree

private def supportMaskTailOne : NPOracleProgram :=
  linkPrograms rightProjectionProgram supportMaskTailTwo

/-- **The symmetric occurrence pool's support-mask program.**  Strip the family
tag, strip the arity, map the per-circuit stream producer across the balanced
circuit list, concatenate the streams, and rebalance once. -/
def symmetricOccurrenceSupportMaskProgram : NPOracleProgram :=
  linkPrograms rightProjectionProgram supportMaskTailOne

theorem symmetricOccurrenceSupportMaskProgram_oracleFree :
    OracleFree symmetricOccurrenceSupportMaskProgram :=
  oracleFree_linkPrograms rightProjectionProgram_oracleFree
    (oracleFree_linkPrograms rightProjectionProgram_oracleFree
      (oracleFree_linkPrograms
        (balancedCallProgram_oracleFree circuitSupportMaskProgram_oracleFree)
        (oracleFree_linkPrograms
          balancedClauseStreamFlattenProgram_oracleFree
          taggedToBalancedProgram_oracleFree)))

def symmetricOccurrenceSupportMaskFuel
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  linkFuel supportMaskTailOne 2
    (linkFuel supportMaskTailTwo 2
      (linkFuel supportMaskTailThree
        (balancedCallFuel circuitSupportMaskProgram circuitSupportMaskFuel
          (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
        (linkFuel taggedToBalancedProgram
          (balancedClauseStreamFlattenFuel
            (symmetricSupportMaskStreams request))
          (taggedToBalancedFuel
            (occurrenceSupportMasks
              (symmetricFourfoldOccurrences request))))))

def symmetricOccurrenceSupportMaskStageBits
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
  , balancedCallRequiredBits encodedCircuitSupportStream
      (request.circuits.map encodeNormalizedSymmetricThresholdCircuit)
  , ((request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
      circuitSupportMaskBits).foldr max 1
  , balancedClauseStreamFlattenMaximumBits (symmetricSupportMaskStreams request)
  , taggedToBalancedRegisterBitsFor request.q
      (occurrenceSupportMasks (symmetricFourfoldOccurrences request))
  ]

def symmetricOccurrenceSupportMaskBits
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  (symmetricOccurrenceSupportMaskStageBits request).foldr max 1

set_option maxHeartbeats 800000 in
-- Five linked stages at one shared register width; every premise is a closed
-- `…Bits` name of this file.
/-- **The symmetric occurrence pool's support masks, executed from the typed
envelope.**  This is the input the greedy touching sweep consumes. -/
theorem run_symmetricOccurrenceSupportMaskProgram
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (maximumBits : ℕ)
    (hbits : symmetricOccurrenceSupportMaskBits request ≤ maximumBits) :
    runNPOracleProgram symmetricOccurrenceSupportMaskProgram maximumBits
        (symmetricOccurrenceSupportMaskFuel request)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some
        (encodeBalancedList
          (occurrenceSupportMasks (symmetricFourfoldOccurrences request))) := by
  have bits_of_member {value : ℕ}
      (hvalue : value ∈ symmetricOccurrenceSupportMaskStageBits request) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceSupportMaskStageBits]
  have hlength : natBitLength request.q ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceSupportMaskStageBits]
  have hcallBits :
      balancedCallRequiredBits encodedCircuitSupportStream
          (request.circuits.map encodeNormalizedSymmetricThresholdCircuit) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceSupportMaskStageBits]
  have hcalleeBits :
      ((request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
        circuitSupportMaskBits).foldr max 1 ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceSupportMaskStageBits]
  have hflattenBits :
      balancedClauseStreamFlattenMaximumBits
          (symmetricSupportMaskStreams request) ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceSupportMaskStageBits]
  have hbuilderBits :
      taggedToBalancedRegisterBitsFor request.q
          (occurrenceSupportMasks (symmetricFourfoldOccurrences request)) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceSupportMaskStageBits]
  have houterProjectionBits :
      rightProjectionBits (encodeNat symmetricCircuitFamilyTag)
          (Nat.pair request.q
            (encodeBalancedList
              (request.circuits.map
                encodeNormalizedSymmetricThresholdCircuit))) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceSupportMaskStageBits]
  have hinnerProjectionBits :
      rightProjectionBits request.q
          (encodeBalancedList
            (request.circuits.map
              encodeNormalizedSymmetricThresholdCircuit)) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricOccurrenceSupportMaskStageBits]
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
      runNPOracleProgram circuitSupportMaskProgram maximumBits
          (circuitSupportMaskFuel code)
          (initialNPOracleState (Nat.unpair code).1 (Nat.unpair code).2) =
        some (encodedCircuitSupportStream code) := by
    intro code hcode
    have hcircuitBits : circuitSupportMaskBits code ≤ maximumBits := by
      refine le_trans ?_ hcalleeBits
      exact le_foldr_max_of_mem (List.mem_map_of_mem hcode)
    obtain ⟨circuit, _hcircuit, hencode⟩ := List.mem_map.mp hcode
    rw [← hencode] at hcircuitBits ⊢
    exact run_circuitSupportMaskProgram circuit maximumBits hcircuitBits
  have hstageThree :
      runNPOracleProgram (balancedCallProgram circuitSupportMaskProgram)
          maximumBits
          (balancedCallFuel circuitSupportMaskProgram circuitSupportMaskFuel
            (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
          (initialNPOracleState request.q
            (encodeBalancedList
              (request.circuits.map
                encodeNormalizedSymmetricThresholdCircuit))) =
        some
          (encodeBalancedList
            ((symmetricSupportMaskStreams request).map encodeTaggedList)) := by
    have hrun :=
      run_balancedCallProgram_from (callee := circuitSupportMaskProgram)
        (maximumBits := maximumBits) request.q
        (request.circuits.map encodeNormalizedSymmetricThresholdCircuit)
        circuitSupportMaskFuel encodedCircuitSupportStream hcallBits hexec
    have hstreams :
        (request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
            encodedCircuitSupportStream =
          (symmetricSupportMaskStreams request).map encodeTaggedList := by
      unfold symmetricSupportMaskStreams
      exact map_encodedCircuitSupportStream
        (request.circuits.map encodeNormalizedSymmetricThresholdCircuit)
    rw [hstreams] at hrun
    exact hrun
  have hstageFour :
      runNPOracleProgram balancedClauseStreamFlattenProgram maximumBits
          (balancedClauseStreamFlattenFuel
            (symmetricSupportMaskStreams request))
          (initialNPOracleState request.q
            (encodeBalancedList
              ((symmetricSupportMaskStreams request).map encodeTaggedList))) =
        some
          (encodeTaggedList
            (occurrenceSupportMasks
              (symmetricFourfoldOccurrences request))) := by
    have hrun :=
      run_balancedClauseStreamFlattenProgram
        (symmetricSupportMaskStreams request) request.q
    rw [symmetricSupportMaskStreams_flatten request] at hrun
    exact run_bits_mono hrun hflattenBits
  have hstageFive :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (taggedToBalancedFuel
            (occurrenceSupportMasks (symmetricFourfoldOccurrences request)))
          (initialNPOracleState request.q
            (encodeTaggedList
              (occurrenceSupportMasks
                (symmetricFourfoldOccurrences request)))) =
        some
          (encodeBalancedList
            (occurrenceSupportMasks
              (symmetricFourfoldOccurrences request))) :=
    run_bits_mono
      (run_taggedToBalancedProgram_from request.q
        (occurrenceSupportMasks (symmetricFourfoldOccurrences request)))
      hbuilderBits
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo
      (run_linkPrograms hpositive hlength hstageThree
        (run_linkPrograms hpositive hlength hstageFour hstageFive)))

end NearCubicWires.CanonicalSymmetricSupportMaskProgram
