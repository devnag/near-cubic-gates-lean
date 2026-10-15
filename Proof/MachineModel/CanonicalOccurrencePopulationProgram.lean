import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalNatDecodeProgram
import Proof.MachineModel.CanonicalRowCountExponentProgram

/-!
# The symmetric occurrence population, executed from the typed envelope

`CanonicalRowCountExponentProgram` leaves the symmetric counting side with two
link-time premises about the occurrence pool.  This module discharges the first
of them.

The symmetric occurrence pool is the concatenation of the bottom fans of the
request's circuits, so its population is the sum of the circuits' bottom counts.
Each bottom count is the *second* field of the circuit's canonical tagged-list
encoding, so the whole quantity is one balanced map followed by the existing
balanced natural-number sum: no circuit is decoded beyond its header, and no
semantic parser is introduced.

After this module the only counting residual left is the touching cost of the
pool.
-/

namespace NearCubicWires.CanonicalOccurrencePopulationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalFourfoldRowCountFormula
open NearCubicWires.CanonicalFourfoldRowCountProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalSymmetricRowCountReduction
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SharedNormalizedEstimatorProgram
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

/-! ## §1 Three fixed structural stages -/

/-- Keep the right component of a canonical pair. -/
def rightProjectionProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .halt 0
  ]

@[simp] theorem rightProjectionProgram_oracleFree :
    OracleFree rightProjectionProgram := by
  rfl

def rightProjectionBits (left right : ℕ) : ℕ :=
  natBitLength (Nat.pair left right)

theorem run_rightProjectionProgram (inputLength left right : ℕ) :
    runNPOracleProgram rightProjectionProgram (rightProjectionBits left right) 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some right := by
  have hinput :
      natBitLength (Nat.pair left right) ≤ rightProjectionBits left right :=
    Nat.le_refl _
  have hright : natBitLength right ≤ rightProjectionBits left right :=
    bits_of_le (Nat.right_le_pair left right) hinput
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState]) hright]
  exact run_halt_instruction (fuel := 0) (value := right) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hright

def repairAtomProgram : NPOracleProgram :=
  [ .pair 1 0 0 1
  , .halt 0
  ]

@[simp] theorem repairAtomProgram_oracleFree : OracleFree repairAtomProgram := by
  rfl

def repairAtomBits (inputLength requestCode : ℕ) : ℕ :=
  natBitLength (Nat.pair inputLength requestCode)

theorem run_repairAtomProgram (inputLength requestCode : ℕ) :
    runNPOracleProgram repairAtomProgram
        (repairAtomBits inputLength requestCode) 2
        (initialNPOracleState inputLength requestCode) =
      some (Nat.pair inputLength requestCode) := by
  have houtput :
      natBitLength (Nat.pair inputLength requestCode) ≤
        repairAtomBits inputLength requestCode :=
    Nat.le_refl _
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputLength requestCode)
    (by rfl) rfl (by simp [initialNPOracleState]) houtput]
  exact run_halt_instruction (fuel := 0)
    (value := Nat.pair inputLength requestCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Second field of a canonical tagged list, read structurally. -/
def taggedFieldOne (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2).1

/-- Read the second field of a canonical tagged list. -/
def taggedFieldOneProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .unpairRight 0 0 2
  , .unpairRight 0 0 3
  , .unpairLeft 0 0 4
  , .halt 0
  ]

@[simp] theorem taggedFieldOneProgram_oracleFree :
    OracleFree taggedFieldOneProgram := by
  rfl

def taggedFieldOneBits (code : ℕ) : ℕ := natBitLength code

theorem run_taggedFieldOneProgram (inputLength code : ℕ) :
    runNPOracleProgram taggedFieldOneProgram (taggedFieldOneBits code) 5
        (initialNPOracleState inputLength code) =
      some (taggedFieldOne code) := by
  have hcode : natBitLength code ≤ taggedFieldOneBits code := Nat.le_refl _
  have hfirst : natBitLength (Nat.unpair code).2 ≤ taggedFieldOneBits code :=
    bits_of_le (Nat.unpair_right_le code) hcode
  have hsecond :
      natBitLength (Nat.unpair (Nat.unpair code).2).2 ≤
        taggedFieldOneBits code :=
    bits_of_le (Nat.unpair_right_le _) hfirst
  have hthird :
      natBitLength (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2 ≤
        taggedFieldOneBits code :=
    bits_of_le (Nat.unpair_right_le _) hsecond
  have hfourth : natBitLength (taggedFieldOne code) ≤ taggedFieldOneBits code :=
    bits_of_le (Nat.unpair_left_le _) hthird
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair code).2) (by rfl) rfl
    (by simp [initialNPOracleState]) hfirst]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair code).2).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsecond]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthird]
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := taggedFieldOne code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, taggedFieldOne])
    hfourth]
  exact run_halt_instruction (fuel := 0) (value := taggedFieldOne code)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hfourth

/-! ## §2 The per-circuit bottom counter -/

/-- Bottom count of one encoded circuit, read structurally from its canonical
tagged-list header. -/
def encodedCircuitBottomCount (code : ℕ) : ℕ :=
  (decodeNat (taggedFieldOne code)).getD 0

theorem taggedFieldOne_encodeNormalizedSymmetricThresholdCircuit
    {n : ℕ} (circuit : NormalizedSymmetricThresholdCircuit n) :
    taggedFieldOne (encodeNormalizedSymmetricThresholdCircuit circuit) =
      encodeNat circuit.bottomCount := by
  simp [taggedFieldOne, encodeNormalizedSymmetricThresholdCircuit,
    encodeTaggedList]

theorem encodedCircuitBottomCount_encode
    {n : ℕ} (circuit : NormalizedSymmetricThresholdCircuit n) :
    encodedCircuitBottomCount
        (encodeNormalizedSymmetricThresholdCircuit circuit) =
      circuit.bottomCount := by
  unfold encodedCircuitBottomCount
  rw [taggedFieldOne_encodeNormalizedSymmetricThresholdCircuit, decodeNat_encode]
  rfl

/-- **The per-circuit bottom counter.**  Repair the balanced-call atom, read the
tagged header field, and decode the canonical natural. -/
def circuitBottomCountProgram : NPOracleProgram :=
  linkPrograms repairAtomProgram
    (linkPrograms taggedFieldOneProgram canonicalNatDecodeProgram)

@[simp] theorem circuitBottomCountProgram_oracleFree :
    OracleFree circuitBottomCountProgram :=
  oracleFree_linkPrograms repairAtomProgram_oracleFree
    (oracleFree_linkPrograms taggedFieldOneProgram_oracleFree
      canonicalNatDecodeProgram_oracleFree)

def encodedCircuitBottomCountFuel (code : ℕ) : ℕ :=
  linkFuel (linkPrograms taggedFieldOneProgram canonicalNatDecodeProgram) 2
    (linkFuel canonicalNatDecodeProgram 5
      (canonicalNatDecodeFuel (encodedCircuitBottomCount code)))

def encodedCircuitBottomCountBits (code : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength code)
      (canonicalNatDecodeBits (Nat.unpair code).1
        (encodedCircuitBottomCount code))

theorem run_circuitBottomCountProgram
    {n : ℕ} (circuit : NormalizedSymmetricThresholdCircuit n)
    (maximumBits : ℕ)
    (hbits :
      encodedCircuitBottomCountBits
          (encodeNormalizedSymmetricThresholdCircuit circuit) ≤
        maximumBits) :
    runNPOracleProgram circuitBottomCountProgram maximumBits
        (encodedCircuitBottomCountFuel
          (encodeNormalizedSymmetricThresholdCircuit circuit))
        (initialNPOracleState
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).2) =
      some
        (encodedCircuitBottomCount
          (encodeNormalizedSymmetricThresholdCircuit circuit)) := by
  have hpositive : 1 ≤ maximumBits := (Nat.le_max_left _ _).trans hbits
  have hcodeBits :
      natBitLength (encodeNormalizedSymmetricThresholdCircuit circuit) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have hdecodeBits :
      canonicalNatDecodeBits
          (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
          (encodedCircuitBottomCount
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
  have hstage1 :
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
  have hstage2 :
      runNPOracleProgram taggedFieldOneProgram maximumBits 5
          (initialNPOracleState
            (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
            (encodeNormalizedSymmetricThresholdCircuit circuit)) =
        some
          (taggedFieldOne
            (encodeNormalizedSymmetricThresholdCircuit circuit)) :=
    run_bits_mono
      (run_taggedFieldOneProgram
        (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
        (encodeNormalizedSymmetricThresholdCircuit circuit))
      hcodeBits
  have hstage3 :
      runNPOracleProgram canonicalNatDecodeProgram maximumBits
          (canonicalNatDecodeFuel
            (encodedCircuitBottomCount
              (encodeNormalizedSymmetricThresholdCircuit circuit)))
          (initialNPOracleState
            (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
            (taggedFieldOne
              (encodeNormalizedSymmetricThresholdCircuit circuit))) =
        some
          (encodedCircuitBottomCount
            (encodeNormalizedSymmetricThresholdCircuit circuit)) := by
    have hfield :
        taggedFieldOne (encodeNormalizedSymmetricThresholdCircuit circuit) =
          encodeNat
            (encodedCircuitBottomCount
              (encodeNormalizedSymmetricThresholdCircuit circuit)) := by
      rw [encodedCircuitBottomCount_encode,
        taggedFieldOne_encodeNormalizedSymmetricThresholdCircuit]
    rw [hfield]
    exact run_bits_mono
      (run_canonicalNatDecodeProgram
        (Nat.unpair (encodeNormalizedSymmetricThresholdCircuit circuit)).1
        (encodedCircuitBottomCount
          (encodeNormalizedSymmetricThresholdCircuit circuit)))
      hdecodeBits
  exact run_linkPrograms hpositive hlength hstage1
    (run_linkPrograms hpositive hlength hstage2 hstage3)

/-! ## §3 The balanced bottom-count map -/

/-- **The bottom-count list producer.**  Strip the family tag, strip the arity,
and map the fixed per-circuit counter across the balanced circuit list. -/
def occurrencePopulationListProgram : NPOracleProgram :=
  linkPrograms rightProjectionProgram
    (linkPrograms rightProjectionProgram
      (balancedCallProgram circuitBottomCountProgram))

theorem occurrencePopulationListProgram_oracleFree :
    OracleFree occurrencePopulationListProgram :=
  oracleFree_linkPrograms rightProjectionProgram_oracleFree
    (oracleFree_linkPrograms rightProjectionProgram_oracleFree
      (balancedCallProgram_oracleFree circuitBottomCountProgram_oracleFree))

def occurrencePopulationListFuel (values : List ℕ) : ℕ :=
  linkFuel
      (linkPrograms rightProjectionProgram
        (balancedCallProgram circuitBottomCountProgram)) 2
    (linkFuel (balancedCallProgram circuitBottomCountProgram) 2
      (balancedCallFuel circuitBottomCountProgram encodedCircuitBottomCountFuel
        values))

def occurrencePopulationCalleeBits (values : List ℕ) : ℕ :=
  (values.map encodedCircuitBottomCountBits).foldr max 1

def occurrencePopulationListStageBits
    (inputLength tagCode q : ℕ) (values : List ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , rightProjectionBits tagCode (Nat.pair q (encodeBalancedList values))
  , rightProjectionBits q (encodeBalancedList values)
  , balancedCallRequiredBits encodedCircuitBottomCount values
  , occurrencePopulationCalleeBits values
  ]

def occurrencePopulationListBits
    (inputLength tagCode q : ℕ) (values : List ℕ) : ℕ :=
  (occurrencePopulationListStageBits inputLength tagCode q values).foldr max 1

/-- **The bottom-count list producer, executed.** -/
theorem run_occurrencePopulationListProgram
    {n : ℕ} (inputLength tagCode q maximumBits : ℕ)
    (circuits : List (NormalizedSymmetricThresholdCircuit n))
    (hbits :
      occurrencePopulationListBits inputLength tagCode q
          (circuits.map encodeNormalizedSymmetricThresholdCircuit) ≤
        maximumBits) :
    runNPOracleProgram occurrencePopulationListProgram maximumBits
        (occurrencePopulationListFuel
          (circuits.map encodeNormalizedSymmetricThresholdCircuit))
        (initialNPOracleState inputLength
          (Nat.pair tagCode
            (Nat.pair q
              (encodeBalancedList
                (circuits.map
                  encodeNormalizedSymmetricThresholdCircuit))))) =
      some
        (encodeBalancedList
          ((circuits.map encodeNormalizedSymmetricThresholdCircuit).map
            encodedCircuitBottomCount)) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          occurrencePopulationListStageBits inputLength tagCode q
            (circuits.map encodeNormalizedSymmetricThresholdCircuit)) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [occurrencePopulationListStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [occurrencePopulationListStageBits]
  have hcalleeBits :
      occurrencePopulationCalleeBits
          (circuits.map encodeNormalizedSymmetricThresholdCircuit) ≤
        maximumBits := by
    apply bits_of_member
    simp [occurrencePopulationListStageBits]
  have hcallBits :
      balancedCallRequiredBits encodedCircuitBottomCount
          (circuits.map encodeNormalizedSymmetricThresholdCircuit) ≤
        maximumBits := by
    apply bits_of_member
    simp [occurrencePopulationListStageBits]
  have hstage1 :
      runNPOracleProgram rightProjectionProgram maximumBits 2
          (initialNPOracleState inputLength
            (Nat.pair tagCode
              (Nat.pair q
                (encodeBalancedList
                  (circuits.map
                    encodeNormalizedSymmetricThresholdCircuit))))) =
        some
          (Nat.pair q
            (encodeBalancedList
              (circuits.map encodeNormalizedSymmetricThresholdCircuit))) :=
    run_bits_mono
      (run_rightProjectionProgram inputLength tagCode
        (Nat.pair q
          (encodeBalancedList
            (circuits.map encodeNormalizedSymmetricThresholdCircuit))))
      (by
        apply bits_of_member
        simp [occurrencePopulationListStageBits])
  have hstage2 :
      runNPOracleProgram rightProjectionProgram maximumBits 2
          (initialNPOracleState inputLength
            (Nat.pair q
              (encodeBalancedList
                (circuits.map
                  encodeNormalizedSymmetricThresholdCircuit)))) =
        some
          (encodeBalancedList
            (circuits.map encodeNormalizedSymmetricThresholdCircuit)) :=
    run_bits_mono
      (run_rightProjectionProgram inputLength q
        (encodeBalancedList
          (circuits.map encodeNormalizedSymmetricThresholdCircuit)))
      (by
        apply bits_of_member
        simp [occurrencePopulationListStageBits])
  have hexec : ∀ code : ℕ,
      code ∈ circuits.map encodeNormalizedSymmetricThresholdCircuit →
      runNPOracleProgram circuitBottomCountProgram maximumBits
          (encodedCircuitBottomCountFuel code)
          (initialNPOracleState (Nat.unpair code).1 (Nat.unpair code).2) =
        some (encodedCircuitBottomCount code) := by
    intro code hcode
    obtain ⟨circuit, hcircuit, hencode⟩ := List.mem_map.mp hcode
    have hcircuitBits :
        encodedCircuitBottomCountBits code ≤ maximumBits := by
      refine le_trans ?_ hcalleeBits
      apply le_foldr_max_of_mem
      exact List.mem_map_of_mem hcode
    subst hencode
    exact run_circuitBottomCountProgram circuit maximumBits hcircuitBits
  have hstage3 :
      runNPOracleProgram (balancedCallProgram circuitBottomCountProgram)
          maximumBits
          (balancedCallFuel circuitBottomCountProgram
            encodedCircuitBottomCountFuel
            (circuits.map encodeNormalizedSymmetricThresholdCircuit))
          (initialNPOracleState inputLength
            (encodeBalancedList
              (circuits.map encodeNormalizedSymmetricThresholdCircuit))) =
        some
          (encodeBalancedList
            ((circuits.map encodeNormalizedSymmetricThresholdCircuit).map
              encodedCircuitBottomCount)) :=
    run_balancedCallProgram_from inputLength
      (circuits.map encodeNormalizedSymmetricThresholdCircuit)
      encodedCircuitBottomCountFuel encodedCircuitBottomCount hcallBits hexec
  exact run_linkPrograms hpositive hlength hstage1
    (run_linkPrograms hpositive hlength hstage2 hstage3)

/-! ## §4 The symmetric occurrence population -/

/-- **The occurrence-population program.** -/
def symmetricOccurrencePopulationProgram : NPOracleProgram :=
  balancedNatSumAfterProgram occurrencePopulationListProgram

theorem symmetricOccurrencePopulationProgram_oracleFree :
    OracleFree symmetricOccurrencePopulationProgram :=
  balancedNatSumAfterProgram_oracleFree occurrencePopulationListProgram
    occurrencePopulationListProgram_oracleFree

def symmetricOccurrencePopulationBits
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  balancedNatSumAfterBits request.q
    (occurrencePopulationListBits request.q
      (encodeNat symmetricCircuitFamilyTag) request.q
      (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
    ((request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
      encodedCircuitBottomCount)

def symmetricOccurrencePopulationFuel
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  balancedNatSumAfterFuel
    (occurrencePopulationListFuel
      (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
    ((request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
      encodedCircuitBottomCount)

private theorem length_flatMap_symmetricCircuitOccurrences
    {n : ℕ} (circuits : List (NormalizedSymmetricThresholdCircuit n)) :
    (circuits.flatMap symmetricCircuitOccurrences).length =
      (circuits.map fun circuit => circuit.bottomCount).sum := by
  induction circuits with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp [List.flatMap_cons, inductionHypothesis, symmetricCircuitOccurrences]

private theorem mapped_bottomCounts
    {n : ℕ} (circuits : List (NormalizedSymmetricThresholdCircuit n)) :
    (circuits.map encodeNormalizedSymmetricThresholdCircuit).map
        encodedCircuitBottomCount =
      circuits.map fun circuit => circuit.bottomCount := by
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro circuit _
  simp only [Function.comp_apply]
  exact encodedCircuitBottomCount_encode circuit

theorem symmetricOccurrencePopulation_eq
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    symmetricOccurrencePopulation request =
      ((request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
        encodedCircuitBottomCount).sum := by
  rw [mapped_bottomCounts]
  unfold symmetricOccurrencePopulation symmetricFourfoldOccurrences
  exact length_flatMap_symmetricCircuitOccurrences request.circuits

/-- **The symmetric occurrence population, executed from the typed envelope.**
This discharges the first of the two counting premises left by
`run_symmetricRowCountExponentProgram`. -/
theorem run_symmetricOccurrencePopulationProgram
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (maximumBits : ℕ)
    (hbits : symmetricOccurrencePopulationBits request ≤ maximumBits) :
    runNPOracleProgram symmetricOccurrencePopulationProgram maximumBits
        (symmetricOccurrencePopulationFuel request)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some (symmetricOccurrencePopulation request) := by
  have hproducer :
      runNPOracleProgram occurrencePopulationListProgram
          (occurrencePopulationListBits request.q
            (encodeNat symmetricCircuitFamilyTag) request.q
            (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
          (occurrencePopulationListFuel
            (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some
          (encodeBalancedList
            ((request.circuits.map
              encodeNormalizedSymmetricThresholdCircuit).map
              encodedCircuitBottomCount)) :=
    run_occurrencePopulationListProgram request.q
      (encodeNat symmetricCircuitFamilyTag) request.q
      (occurrencePopulationListBits request.q
        (encodeNat symmetricCircuitFamilyTag) request.q
        (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
      request.circuits (le_refl _)
  rw [symmetricOccurrencePopulation_eq]
  exact run_bits_mono
    (run_balancedNatSumAfterProgram occurrencePopulationListProgram request.q
      (symmetricEnvelopeCode request)
      (occurrencePopulationListBits request.q
        (encodeNat symmetricCircuitFamilyTag) request.q
        (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
      (occurrencePopulationListFuel
        (request.circuits.map encodeNormalizedSymmetricThresholdCircuit))
      ((request.circuits.map encodeNormalizedSymmetricThresholdCircuit).map
        encodedCircuitBottomCount)
      hproducer)
    hbits

/-! ## §5 The counting side, closed to the touching cost

Instantiating the population half of the row-count exponent leaves exactly one
open interpreter premise on the whole symmetric counting path. -/

/-- **The symmetric row-count exponent program**, with the occurrence pool's
population supplied. -/
def symmetricRowCountExponentProgramOfCost
    (costProgram : NPOracleProgram) (accuracyExponent : ℕ) : NPOracleProgram :=
  symmetricRowCountExponentProgram symmetricOccurrencePopulationProgram
    costProgram accuracyExponent

theorem symmetricRowCountExponentProgramOfCost_oracleFree
    (costProgram : NPOracleProgram) (accuracyExponent : ℕ)
    (hcost : OracleFree costProgram) :
    OracleFree
      (symmetricRowCountExponentProgramOfCost costProgram accuracyExponent) :=
  symmetricRowCountExponentProgram_oracleFree symmetricOccurrencePopulationProgram
    costProgram accuracyExponent symmetricOccurrencePopulationProgram_oracleFree
    hcost

def symmetricRowCountExponentOfCostBits
    (costBits liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  symmetricRowCountExponentBits (symmetricOccurrencePopulationBits request)
    costBits liveScale accuracyExponent request

def symmetricRowCountExponentOfCostFuel
    (costProgram : NPOracleProgram)
    (costFuel liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  symmetricRowCountExponentFuel symmetricOccurrencePopulationProgram costProgram
    (symmetricOccurrencePopulationFuel request) costFuel liveScale
    accuracyExponent request

/-- **The symmetric row-count exponent, executed, modulo the touching cost.**
This is the whole counting residual of the artifact's symmetric execution
field: one program returning `symmetricOccurrenceTouchingCost`. -/
theorem run_symmetricRowCountExponentProgram_of_cost
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (costProgram : NPOracleProgram) (costBits costFuel maximumBits : ℕ)
    (hbits :
      symmetricRowCountExponentOfCostBits costBits liveScale accuracyExponent
          request ≤
        maximumBits)
    (hcost :
      runNPOracleProgram costProgram costBits costFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrenceTouchingCost request liveScale)) :
    runNPOracleProgram
        (symmetricRowCountExponentProgramOfCost costProgram accuracyExponent)
        maximumBits
        (symmetricRowCountExponentOfCostFuel costProgram costFuel liveScale
          accuracyExponent request)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some (symmetricRowCountExponent liveScale accuracyExponent request) :=
  run_symmetricRowCountExponentProgram liveScale accuracyExponent request
    symmetricOccurrencePopulationProgram costProgram
    (symmetricOccurrencePopulationBits request)
    (symmetricOccurrencePopulationFuel request) costBits costFuel maximumBits
    hbits
    (run_symmetricOccurrencePopulationProgram request
      (symmetricOccurrencePopulationBits request) (le_refl _))
    hcost

/-- **The artifact's symmetric execution field, counting side closed to one
number.**  Every stage from the typed envelope to the published ratio component
is fixed except a single program returning the occurrence pool's touching
cost. -/
theorem run_sharedFourfoldAggregationProgram_symmetric_of_cost
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (costProgram rowEvaluator : NPOracleProgram)
    (maximumBits calleeBits atomCountBits rowCountBits exponentBits costBits
      costFuel : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hentryBits :
      CanonicalFourfoldRowTailProgram.symmetricFourfoldEntryBits contracts
          liveScale accuracyExponent request atomCountBits ≤
        maximumBits)
    (hcomponentBits :
      CanonicalFourfoldRowTailProgram.symmetricFourfoldRangeComponentBits
          contracts liveScale accuracyExponent request calleeBits ≤
        maximumBits)
    (hcalleePositive : 1 ≤ calleeBits)
    (hcalleeLength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        FourfoldRangeAggregationComposition.fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request →
      CanonicalFourfoldRowEvaluationProgram.symmetricFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (FourfoldRangeAggregationComposition.fourfoldRangeDenominatorTail
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (CanonicalFourfoldRowProgram.evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (CanonicalFourfoldRowProgram.symmetricFourfoldRowRequest request
                rowIndex input))))
    (hrowCountLength : natBitLength request.q ≤ rowCountBits)
    (hrowCountBits :
      symmetricRowCountBits exponentBits
          (symmetricRowCountExponent liveScale accuracyExponent request) ≤
        rowCountBits)
    (hatomCountBits :
      fourfoldRangeAtomCountBits rowCountBits request.q
          ((publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request) ≤
        atomCountBits)
    (hexponentBits :
      symmetricRowCountExponentOfCostBits costBits liveScale accuracyExponent
          request ≤
        exponentBits)
    (hcost :
      runNPOracleProgram costProgram costBits costFuel
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricOccurrenceTouchingCost request liveScale)) :
    runNPOracleProgram
        (CanonicalFourfoldRowTailProgram.sharedFourfoldAggregationProgram
          (selectedExactDecompositionAlgorithm contracts)
          (symmetricFourfoldAtomCountProgram
            (symmetricRowCountExponentProgramOfCost costProgram
              accuracyExponent))
          rowEvaluator)
        maximumBits
        (CanonicalFourfoldRowTailProgram.symmetricSharedFourfoldAggregationFuel
          contracts liveScale accuracyExponent request
          (symmetricFourfoldAtomCountProgram
            (symmetricRowCountExponentProgramOfCost costProgram
              accuracyExponent))
          rowEvaluator
          (fourfoldRangeAtomCountFuel request.q
            (symmetricRowCountFuel
              (symmetricRowCountExponentOfCostFuel costProgram costFuel
                liveScale accuracyExponent request)
              (symmetricRowCountExponent liveScale accuracyExponent request)))
          evaluatorFuel)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some
        (symmetricRatioComponentCode
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :=
  run_sharedFourfoldAggregationProgram_symmetric_of_pool contracts liveScale
    accuracyExponent request symmetricOccurrencePopulationProgram costProgram
    rowEvaluator maximumBits calleeBits atomCountBits rowCountBits exponentBits
    (symmetricOccurrencePopulationBits request)
    (symmetricOccurrencePopulationFuel request) costBits costFuel evaluatorFuel
    hpositive hlength hentryBits hcomponentBits hcalleePositive hcalleeLength
    hbottomBits hrepackBits hevaluator hrowCountLength hrowCountBits
    hatomCountBits hexponentBits
    (run_symmetricOccurrencePopulationProgram request
      (symmetricOccurrencePopulationBits request) (le_refl _))
    hcost

/-! ## §6 The single remaining counting obligation

Every theorem above is unconditional except for one interpreter premise.  The
exact statement an owning module must supply is

```text
theorem run_symmetricOccurrenceTouchingCostProgram
    (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (maximumBits : ℕ)
    (hbits : symmetricOccurrenceTouchingCostBits liveScale request ≤
      maximumBits) :
    runNPOracleProgram symmetricOccurrenceTouchingCostProgram maximumBits
        (symmetricOccurrenceTouchingCostFuel liveScale request)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some (symmetricOccurrenceTouchingCost request liveScale)
```

with `symmetricOccurrenceTouchingCostProgram` oracle-free.  Semantically that
number is

```text
touchingCost (occurrenceSupport occurrences)
  (touchingSelect (occurrenceSupport occurrences)
    (normalizedLiveCount request.q liveScale))
```

for `occurrences = symmetricFourfoldOccurrences request`, i.e. one greedy
conditional-expectation sweep over `List.finRange request.q` in which each step
compares two `conditionalTouchNumerator` scores after cross-multiplying by their
binomial fiber sizes.  Executing it needs an exact `Nat.choose` stage; nothing
else in this file's chain remains open. -/

end NearCubicWires.CanonicalOccurrencePopulationProgram
