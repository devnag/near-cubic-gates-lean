import Proof.Circuits.BoundedOracleStructuralCircuit
import Proof.MachineModel.CanonicalBalancedLookupProgram
import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalRowCountExponentProgram
import Proof.MachineModel.CanonicalSymmetricRowTableRequestProgram
import Proof.MachineModel.CaseTwoOccurrenceProgram

namespace NearCubicWires.CanonicalDescriptionFieldProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalSymmetricRowTableRequestProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## 1. The description as a list of naturals -/

/-- The canonical description, as the list of naturals the decoder receives. -/
def descriptionBits {n : ℕ} (bound : ℕ) (circuit : BooleanCircuit n) :
    List ℕ :=
  (canonicalBoundedCircuitDescription bound circuit).map Bool.toNat

theorem descriptionBits_length {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) :
    (descriptionBits bound circuit).length = descriptionWidth n bound := by
  simpa only [descriptionBits, List.length_map] using
    canonicalBoundedCircuitDescription_length circuit hsize

/-- One bit of the description at an absolute position. -/
def descriptionBitAt {n : ℕ} (bound : ℕ) (circuit : BooleanCircuit n)
    (position : ℕ) : ℕ :=
  (descriptionBits bound circuit).getD position 0

/-- One row of the description, read total. -/
def descriptionRowAt {n : ℕ} (bound : ℕ) (circuit : BooleanCircuit n)
    (row : ℕ) : List Bool :=
  (canonicalDescriptionRows bound circuit).getD row []

/-- The sum of one thermometer block of one row. -/
def descriptionField {n : ℕ} (bound : ℕ) (circuit : BooleanCircuit n)
    (row start len : ℕ) : ℕ :=
  ((List.range len).map fun offset =>
    descriptionBitAt bound circuit
      (row * rowWidth n bound + start + offset)).sum

/-! ## 2. Thermometer arithmetic -/

private theorem sum_range_decide (len value : ℕ) :
    ((List.range len).map fun index => (decide (index < value)).toNat).sum =
      min value len := by
  induction len with
  | zero => simp
  | succ len ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      by_cases hlen : len < value
      · simp only [hlen, decide_true, Bool.toNat_true]
        omega
      · simp only [hlen, decide_false, Bool.toNat_false]
        omega

private theorem orderedNatBits_getD (limit value offset : ℕ)
    (hoffset : offset < limit) :
    (orderedNatBits limit value).getD offset false =
      decide (offset < value) := by
  have hlength : offset < (orderedNatBits limit value).length := by
    simpa only [orderedNatBits_length] using hoffset
  rw [List.getD_eq_getElem _ _ hlength]
  simp only [orderedNatBits, List.getElem_map, List.getElem_range]

private theorem getD_append_left (left right : List Bool) (index : ℕ)
    (hindex : index < left.length) :
    (left ++ right).getD index false = left.getD index false := by
  have hlength : index < (left ++ right).length := by
    simp only [List.length_append]
    omega
  rw [List.getD_eq_getElem _ _ hlength, List.getD_eq_getElem _ _ hindex,
    List.getElem_append_left hindex]

private theorem getD_append_right (left right : List Bool) (index : ℕ)
    (hindex : left.length ≤ index)
    (hbound : index < left.length + right.length) :
    (left ++ right).getD index false =
      right.getD (index - left.length) false := by
  have hlength : index < (left ++ right).length := by
    simp only [List.length_append]
    omega
  have hright : index - left.length < right.length := by omega
  rw [List.getD_eq_getElem _ _ hlength, List.getD_eq_getElem _ _ hright,
    List.getElem_append_right hindex]

/-- Every offset of an encoded row reads the thermometer digit of its own
field. -/
theorem encodedDescriptionRow_getD (n bound tag first second offset : ℕ)
    (hoffset : offset < rowWidth n bound) :
    (encodedDescriptionRow n bound tag first second).getD offset false =
      if offset < 6 then decide (offset < tag)
      else if offset < 6 + boundedCircuitFieldLimit n bound then
        decide (offset - 6 < first)
      else decide (offset - 6 - boundedCircuitFieldLimit n bound < second) := by
  have hwidth : rowWidth n bound = 6 + 2 * boundedCircuitFieldLimit n bound :=
    rfl
  have hhead :
      (orderedNatBits 6 tag ++
        orderedNatBits (boundedCircuitFieldLimit n bound) first).length =
        6 + boundedCircuitFieldLimit n bound := by
    simp only [List.length_append, orderedNatBits_length]
  rw [encodedDescriptionRow]
  by_cases hmid : offset < 6 + boundedCircuitFieldLimit n bound
  · rw [getD_append_left _ _ _ (by rw [hhead]; exact hmid)]
    by_cases hlow : offset < 6
    · rw [getD_append_left _ _ _
        (by simpa only [orderedNatBits_length] using hlow)]
      rw [orderedNatBits_getD 6 tag offset hlow, if_pos hlow]
    · have hge : (orderedNatBits 6 tag).length ≤ offset := by
        simpa only [orderedNatBits_length] using Nat.le_of_not_lt hlow
      have hbound :
          offset <
            (orderedNatBits 6 tag).length +
              (orderedNatBits (boundedCircuitFieldLimit n bound) first).length := by
        simp only [orderedNatBits_length]
        omega
      rw [getD_append_right _ _ _ hge hbound]
      simp only [orderedNatBits_length]
      rw [orderedNatBits_getD _ first _ (by omega), if_neg hlow, if_pos hmid]
  · have hge : (orderedNatBits 6 tag ++
        orderedNatBits (boundedCircuitFieldLimit n bound) first).length ≤ offset := by
      simp only [List.length_append, orderedNatBits_length]
      omega
    have hbound :
        offset <
          (orderedNatBits 6 tag ++
            orderedNatBits (boundedCircuitFieldLimit n bound) first).length +
            (orderedNatBits (boundedCircuitFieldLimit n bound) second).length := by
      simp only [List.length_append, orderedNatBits_length]
      omega
    have harith :
        offset -
            (orderedNatBits 6 tag ++
              orderedNatBits (boundedCircuitFieldLimit n bound) first).length =
          offset - 6 - boundedCircuitFieldLimit n bound := by
      simp only [List.length_append, orderedNatBits_length]
      omega
    rw [getD_append_right _ _ _ hge hbound, harith]
    rw [orderedNatBits_getD _ second _ (by omega), if_neg (by omega), if_neg hmid]

/-! ## 3. Absolute positions are row offsets -/

private theorem descriptionBits_getElem {n bound : ℕ}
    (circuit : BooleanCircuit n) (position : ℕ)
    (hposition : position < (descriptionBits bound circuit).length) :
    (descriptionBits bound circuit)[position] =
      ((canonicalBoundedCircuitDescription bound circuit)[position]'(by
        simpa only [descriptionBits, List.length_map] using hposition)).toNat := by
  simp only [descriptionBits, List.getElem_map]

private theorem descriptionRowAt_getElem {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) (row : ℕ)
    (hrow : row < bound + 1) :
    descriptionRowAt bound circuit row =
      (canonicalDescriptionRows bound circuit)[row]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact hrow) := by
  rw [descriptionRowAt]
  exact List.getD_eq_getElem _ _ (by
    rw [canonicalDescriptionRows_length circuit hsize]
    exact hrow)

theorem descriptionRowAt_length {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) (row : ℕ) (hrow : row < bound + 1) :
    (descriptionRowAt bound circuit row).length = rowWidth n bound := by
  rw [descriptionRowAt_getElem circuit hsize row hrow]
  exact canonicalDescriptionRows_uniform circuit _
    (List.getElem_mem (by
      rw [canonicalDescriptionRows_length circuit hsize]
      exact hrow))

/-- **One absolute position is one row offset.** -/
theorem descriptionBitAt_row {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) (row offset : ℕ) (hrow : row < bound + 1)
    (hoffset : offset < rowWidth n bound) :
    descriptionBitAt bound circuit (row * rowWidth n bound + offset) =
      ((descriptionRowAt bound circuit row).getD offset false).toNat := by
  have hrows : row < (canonicalDescriptionRows bound circuit).length := by
    rw [canonicalDescriptionRows_length circuit hsize]
    exact hrow
  have hposition :
      row * rowWidth n bound + offset <
        (descriptionBits bound circuit).length := by
    rw [descriptionBits_length circuit hsize]
    exact (descriptionIndex (n := n) ⟨row, hrow⟩ ⟨offset, hoffset⟩).isLt
  have hrowLength :
      offset <
        ((canonicalDescriptionRows bound circuit)[row]'hrows).length := by
    rw [canonicalDescriptionRows_uniform circuit _ (List.getElem_mem hrows)]
    exact hoffset
  rw [descriptionRowAt_getElem circuit hsize row hrow]
  rw [descriptionBitAt, List.getD_eq_getElem _ _ hposition,
    List.getD_eq_getElem _ _ hrowLength]
  rw [descriptionBits_getElem circuit _ hposition]
  congr 1
  simpa only [canonicalDescriptionRows_flatten] using
    getElem_flatten_uniform (canonicalDescriptionRows bound circuit)
      (rowWidth n bound) row offset
      (canonicalDescriptionRows_uniform circuit) hrows hoffset

/-! ## 4. The three fields of an encoded row -/

private theorem descriptionField_of_row {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (row start len : ℕ) (hrow : row < bound + 1)
    (hblock : start + len ≤ rowWidth n bound) (value : ℕ)
    (hbits : ∀ offset : ℕ, offset < len →
      (descriptionRowAt bound circuit row).getD (start + offset) false =
        decide (offset < value)) :
    descriptionField bound circuit row start len = min value len := by
  rw [descriptionField, ← sum_range_decide len value]
  congr 1
  refine List.map_congr_left ?_
  intro offset hoffset
  have hlt : offset < len := List.mem_range.mp hoffset
  have hoffsetLt : start + offset < rowWidth n bound := by omega
  rw [show row * rowWidth n bound + start + offset =
      row * rowWidth n bound + (start + offset) by omega]
  rw [descriptionBitAt_row circuit hsize row (start + offset) hrow hoffsetLt,
    hbits offset hlt]

/-- **The three thermometer fields of one encoded row.** -/
theorem descriptionField_encodedRow {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (row : ℕ) (hrow : row < bound + 1) (tag first second : ℕ)
    (hrowEq :
      descriptionRowAt bound circuit row =
        encodedDescriptionRow n bound tag first second) :
    descriptionField bound circuit row 0 6 = min tag 6 ∧
      descriptionField bound circuit row 6
          (boundedCircuitFieldLimit n bound) =
        min first (boundedCircuitFieldLimit n bound) ∧
      descriptionField bound circuit row (6 + boundedCircuitFieldLimit n bound)
          (boundedCircuitFieldLimit n bound) =
        min second (boundedCircuitFieldLimit n bound) := by
  have hwidth : rowWidth n bound = 6 + 2 * boundedCircuitFieldLimit n bound :=
    rfl
  refine ⟨?_, ?_, ?_⟩
  · refine descriptionField_of_row circuit hsize row 0 6 hrow (by omega) tag ?_
    intro offset hoffset
    rw [hrowEq, encodedDescriptionRow_getD n bound tag first second _ (by omega)]
    rw [if_pos (by omega)]
    simp only [Nat.zero_add]
  · refine descriptionField_of_row circuit hsize row 6
      (boundedCircuitFieldLimit n bound) hrow (by omega) first ?_
    intro offset hoffset
    rw [hrowEq, encodedDescriptionRow_getD n bound tag first second _ (by omega)]
    rw [if_neg (by omega), if_pos (by omega),
      show 6 + offset - 6 = offset by omega]
  · refine descriptionField_of_row circuit hsize row
      (6 + boundedCircuitFieldLimit n bound)
      (boundedCircuitFieldLimit n bound) hrow (by omega) second ?_
    intro offset hoffset
    rw [hrowEq, encodedDescriptionRow_getD n bound tag first second _ (by omega)]
    rw [if_neg (by omega), if_neg (by omega),
      show 6 + boundedCircuitFieldLimit n bound + offset - 6 -
        boundedCircuitFieldLimit n bound = offset by omega]

/-- The tag block's fifth digit, read as a one-cell block sum: it is zero
exactly on the rows that carry a node. -/
theorem descriptionField_tagDigit {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (row : ℕ) (hrow : row < bound + 1) (tag first second : ℕ)
    (hrowEq :
      descriptionRowAt bound circuit row =
        encodedDescriptionRow n bound tag first second) :
    descriptionField bound circuit row 4 1 = (decide (4 < tag)).toNat := by
  have hwidth : rowWidth n bound = 6 + 2 * boundedCircuitFieldLimit n bound :=
    rfl
  have hlimit : 1 ≤ boundedCircuitFieldLimit n bound := by
    unfold boundedCircuitFieldLimit
    omega
  rw [descriptionField]
  simp only [List.range_one, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero]
  rw [descriptionBitAt_row circuit hsize row 4 hrow (by omega), hrowEq,
    encodedDescriptionRow_getD n bound tag first second 4 (by omega),
    if_pos (by omega)]

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbound : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbound

private theorem le_foldr_max_of_mem {value : ℕ} {values : List ℕ}
    (hmem : value ∈ values) : value ≤ values.foldr max 1 := by
  induction values with
  | nil => exact absurd hmem List.not_mem_nil
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · exact hhead ▸ Nat.le_max_left _ _
      · exact (ih htail).trans (Nat.le_max_right _ _)

/-- The shared context of one block: its base offset beside the table's
length and its balanced code. -/
def descriptionSlotContext (base len code : ℕ) : ℕ :=
  Nat.pair base (Nat.pair len code)

/-- Register ABI:

* `r0`: the pool's request body and then the lookup request;
* `r2`: the requested offset and then the absolute position;
* `r4`/`r6`/`r7`: the base offset, the table length and the balanced code. -/
def descriptionSlotRequestProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .add 4 2 2 7
  , .pair 2 7 2 8
  , .pair 6 2 0 9
  , .halt 0
  ]

@[simp] theorem descriptionSlotRequestProgram_oracleFree :
    OracleFree descriptionSlotRequestProgram := by
  rfl

def descriptionSlotRequestOutput (base len code index : ℕ) : ℕ :=
  Nat.pair len (Nat.pair (base + index) code)

def descriptionSlotRequestFuel : ℕ := 10

def descriptionSlotRequestBits (base len code index : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair index (descriptionSlotContext base len code))
      (descriptionSlotRequestOutput base len code index))

/-- **The slot request, executed.**  One pool request body becomes one
balanced-lookup request at `base + index`. -/
theorem run_descriptionSlotRequestProgram (inputLength base len code index : ℕ) :
    runNPOracleProgram descriptionSlotRequestProgram
        (descriptionSlotRequestBits base len code index)
        descriptionSlotRequestFuel
        (initialNPOracleState inputLength
          (Nat.pair index (descriptionSlotContext base len code))) =
      some (descriptionSlotRequestOutput base len code index) := by
  have hinput :
      natBitLength (Nat.pair index (descriptionSlotContext base len code)) ≤
        descriptionSlotRequestBits base len code index :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput :
      natBitLength (descriptionSlotRequestOutput base len code index) ≤
        descriptionSlotRequestBits base len code index :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hindex : natBitLength index ≤ descriptionSlotRequestBits base len code index :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hcontext :
      natBitLength (descriptionSlotContext base len code) ≤
        descriptionSlotRequestBits base len code index :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hbase : natBitLength base ≤ descriptionSlotRequestBits base len code index :=
    bits_of_le (Nat.left_le_pair _ _) hcontext
  have htail :
      natBitLength (Nat.pair len code) ≤
        descriptionSlotRequestBits base len code index :=
    bits_of_le (Nat.right_le_pair _ _) hcontext
  have hlen : natBitLength len ≤ descriptionSlotRequestBits base len code index :=
    bits_of_le (Nat.left_le_pair _ _) htail
  have hcode : natBitLength code ≤ descriptionSlotRequestBits base len code index :=
    bits_of_le (Nat.right_le_pair _ _) htail
  have hcell :
      natBitLength (Nat.pair (base + index) code) ≤
        descriptionSlotRequestBits base len code index :=
    bits_of_le (Nat.right_le_pair _ _) houtput
  have hposition :
      natBitLength (base + index) ≤
        descriptionSlotRequestBits base len code index :=
    bits_of_le (Nat.left_le_pair _ _) hcell
  rw [show descriptionSlotRequestFuel = 9 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [initialNPOracleState, descriptionSlotContext]) hindex]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := descriptionSlotContext base len code)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := base) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionSlotContext])
    hbase]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair len code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, descriptionSlotContext])
    htail]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := len) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlen]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcode]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_add_instruction (value := base + index) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hposition]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (base + index) code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcell]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := descriptionSlotRequestOutput base len code index) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      descriptionSlotRequestOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def descriptionSlotProgram : NPOracleProgram :=
  linkPrograms descriptionSlotRequestProgram canonicalBalancedLookupProgram

theorem descriptionSlotProgram_oracleFree :
    OracleFree descriptionSlotProgram :=
  oracleFree_linkPrograms descriptionSlotRequestProgram_oracleFree
    canonicalBalancedLookupProgram_oracleFree

def descriptionSlotFuel (values : List ℕ) (base index : ℕ) : ℕ :=
  linkFuel canonicalBalancedLookupProgram descriptionSlotRequestFuel
    (balancedLookupFuel values (base + index))

def descriptionSlotBits (inputLength : ℕ) (values : List ℕ)
    (base index : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (descriptionSlotRequestBits base values.length
      (encodeBalancedList values) index)
    (balancedLookupMaximumBits values (base + index))

theorem run_descriptionSlotProgram (inputLength : ℕ) (values : List ℕ)
    (base index : ℕ) (hposition : base + index < values.length) :
    runNPOracleProgram descriptionSlotProgram
        (descriptionSlotBits inputLength values base index)
        (descriptionSlotFuel values base index)
        (initialNPOracleState inputLength
          (Nat.pair index
            (descriptionSlotContext base values.length
              (encodeBalancedList values)))) =
      some (values.getD (base + index) 0) := by
  have hlookup :=
    run_canonicalBalancedLookupProgram values (base + index) inputLength hposition
  rw [List.getD_eq_getElem _ _ hposition]
  refine run_occurrenceStage
    (run_descriptionSlotRequestProgram inputLength base values.length
      (encodeBalancedList values) index) ?_
  simpa only [descriptionSlotRequestOutput, balancedLookupInput] using hlookup

/-! ## 6. The block sum -/

/-- **One thermometer block, summed.**  The indexed pool of §5 under the
published balanced sum: no tagged accumulator and no stream flattener. -/
def descriptionBlockSumProgram : NPOracleProgram :=
  balancedNatSumAfterProgram (indexedPoolListProgram descriptionSlotProgram)

theorem descriptionBlockSumProgram_oracleFree :
    OracleFree descriptionBlockSumProgram :=
  balancedNatSumAfterProgram_oracleFree _
    (indexedPoolListProgram_oracleFree _ descriptionSlotProgram_oracleFree)

/-- The values one block reads. -/
def descriptionBlockValues (values : List ℕ) (base len : ℕ) : List ℕ :=
  (List.range len).map fun index => values.getD (base + index) 0

def descriptionBlockPoolFuel (inputLength : ℕ) (values : List ℕ)
    (base len : ℕ) : ℕ :=
  indexedPoolListFuel descriptionSlotProgram inputLength len
    (descriptionSlotContext base values.length (encodeBalancedList values))
    (descriptionSlotFuel values base)

def descriptionBlockPoolBits (inputLength : ℕ) (values : List ℕ)
    (base len : ℕ) : ℕ :=
  max
    (indexedPoolListBits inputLength len
      (descriptionSlotContext base values.length (encodeBalancedList values))
      (fun index => values.getD (base + index) 0))
    (((List.range len).map (descriptionSlotBits inputLength values base)).foldr
      max 1)

def descriptionBlockSumFuel (inputLength : ℕ) (values : List ℕ)
    (base len : ℕ) : ℕ :=
  balancedNatSumAfterFuel (descriptionBlockPoolFuel inputLength values base len)
    (descriptionBlockValues values base len)

def descriptionBlockSumBits (inputLength : ℕ) (values : List ℕ)
    (base len : ℕ) : ℕ :=
  balancedNatSumAfterBits inputLength
    (descriptionBlockPoolBits inputLength values base len)
    (descriptionBlockValues values base len)

/-- **The block sum, executed.**  From the block's own request word the fixed
stream returns the sum of the `len` table entries starting at `base`. -/
theorem run_descriptionBlockSumProgram (inputLength : ℕ) (values : List ℕ)
    (base len : ℕ) (hfit : base + len ≤ values.length) :
    runNPOracleProgram descriptionBlockSumProgram
        (descriptionBlockSumBits inputLength values base len)
        (descriptionBlockSumFuel inputLength values base len)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput len
            (descriptionSlotContext base values.length
              (encodeBalancedList values)))) =
      some (descriptionBlockValues values base len).sum := by
  have hpool :
      runNPOracleProgram (indexedPoolListProgram descriptionSlotProgram)
          (descriptionBlockPoolBits inputLength values base len)
          (descriptionBlockPoolFuel inputLength values base len)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput len
              (descriptionSlotContext base values.length
                (encodeBalancedList values)))) =
        some (encodeBalancedList (descriptionBlockValues values base len)) := by
    refine run_indexedPoolListProgram descriptionSlotProgram inputLength len
      (descriptionSlotContext base values.length (encodeBalancedList values))
      (descriptionBlockPoolBits inputLength values base len)
      (descriptionSlotFuel values base)
      (fun index => values.getD (base + index) 0) (Nat.le_max_left _ _) ?_
    intro index hindex
    refine run_bits_mono
      (run_descriptionSlotProgram inputLength values base index (by omega)) ?_
    refine le_trans (le_foldr_max_of_mem ?_) (Nat.le_max_right _ _)
    exact List.mem_map_of_mem (List.mem_range.mpr hindex)
  exact run_balancedNatSumAfterProgram
    (indexedPoolListProgram descriptionSlotProgram) inputLength _
    (descriptionBlockPoolBits inputLength values base len)
    (descriptionBlockPoolFuel inputLength values base len)
    (descriptionBlockValues values base len) hpool

/-! ## 7. The block sum at a description -/

/-- The block sums of §6 are exactly the thermometer field sums of §1. -/
theorem descriptionBlockValues_sum {n bound : ℕ} (circuit : BooleanCircuit n)
    (row start len : ℕ) :
    (descriptionBlockValues (descriptionBits bound circuit)
        (row * rowWidth n bound + start) len).sum =
      descriptionField bound circuit row start len := by
  rw [descriptionBlockValues, descriptionField]
  simp only [descriptionBitAt]

end NearCubicWires.CanonicalDescriptionFieldProgram
