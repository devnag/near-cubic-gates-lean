import Proof.MachineModel.CanonicalBooleanCircuitValidationProgram
import Proof.MachineModel.CanonicalRowCountExponentProgram
import Proof.MachineModel.CaseTwoOccurrenceProgram
import Proof.CaseAnalysis.CaseTwoOccurrenceRunnerCalls
import Proof.Circuits.ValidatorCircuitPrepareRebuildLedger

/-!
# The oracle triple from the substituted circuit's encoding alone

The oracle half of `RuntimeCaseTwoBlockOccurrenceProgram.occurrencePacket` is
three numerals: the published factory's clause width at the Case-2 substituted
circuit, that circuit's size, and its encoding.  Only the third is recovered
from the accepting oracle; the other two are *functions of it*, and both
functions are already fixed programs.

* The clause width is one published-runner call.
  `CaseTwoOccurrenceRunnerCalls.run_shapeCallProgram` runs the factory's own
  shape runner on `Nat.pair arity (encodeBooleanCircuit circuit)` — exactly the
  arity the schedule quad already emits beside the encoding — and
  `CaseTwoOccurrenceEvaluation.clauseBits_eq_shapeCode` reads the width out of
  its output by two `unpair`s.
* The size is the encoded node count.
  `CanonicalBooleanCircuitValidationProgram.run_booleanCircuitValidationProgram`
  returns `Nat.pair 1 circuit.nodes.length` on a genuine encoding, and it is
  entered at the circuit's own arity through
  `CanonicalNativeCallProgram.nativeContextCallProgram`.

§1 adds the three straight-line frames, §2 the size stage, and §3 the assembled
stream: from `pair arity (encodeBooleanCircuit circuit)` it emits the whole
oracle triple.  Nothing here mentions the schedule, the recovered oracle, or
any target-derived immediate.
-/

namespace NearCubicWires.RuntimeCaseTwoOracleTripleProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceRunnerCalls
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorCircuitPrepareRebuildLedger
open NearCubicWires.VerifiedLinker

/-! ## 1. The straight-line frames -/

/-- `code ↦ (unpair (unpair code).2).2`: the factory's clause width inside the
single shape-runner output. -/
def shapeClauseBitsProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .unpairRight 0 0 2
  , .halt 0
  ]

@[simp] theorem shapeClauseBitsProgram_oracleFree :
    OracleFree shapeClauseBitsProgram := by
  rfl

def shapeClauseBitsBits (code : ℕ) : ℕ := natBitLength code

theorem run_shapeClauseBitsProgram (inputLength code : ℕ) :
    runNPOracleProgram shapeClauseBitsProgram (shapeClauseBitsBits code) 3
        (initialNPOracleState inputLength code) =
      some (Nat.unpair (Nat.unpair code).2).2 := by
  have hfirst : natBitLength (Nat.unpair code).2 ≤ shapeClauseBitsBits code :=
    natBitLength_mono (Nat.unpair_right_le code)
  have hsecond :
      natBitLength (Nat.unpair (Nat.unpair code).2).2 ≤
        shapeClauseBitsBits code :=
    (natBitLength_mono (Nat.unpair_right_le _)).trans hfirst
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair code).2) (by rfl) rfl
    (by simp [initialNPOracleState]) hfirst]
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair code).2).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsecond]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsecond

/-- `pair left right ↦ pair right (pair left right)`: the native-call frame of
the circuit validator, whose callee length is the pair's *left* component and
whose request and retained context are both its right. -/
def frameRightProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .pair 2 0 0 2
  , .halt 0
  ]

@[simp] theorem frameRightProgram_oracleFree :
    OracleFree frameRightProgram := by
  rfl

def frameRightBits (left right : ℕ) : ℕ :=
  natBitLength (Nat.pair right (Nat.pair left right))

theorem run_frameRightProgram (inputLength left right : ℕ) :
    runNPOracleProgram frameRightProgram (frameRightBits left right) 3
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (Nat.pair right (Nat.pair left right)) := by
  have houtput :
      natBitLength (Nat.pair right (Nat.pair left right)) ≤
        frameRightBits left right := le_refl _
  have hright : natBitLength right ≤ frameRightBits left right :=
    natBitLength_mono (Nat.left_le_pair _ _)
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState]) hright]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair right (Nat.pair left right))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- `pair (pair flag size) (pair arity encoded) ↦ pair size encoded`: the
validator's accepted node count beside the retained encoding. -/
def sizeExtractProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 2 3 2
  , .unpairRight 0 4 3
  , .unpairRight 4 5 4
  , .pair 3 5 0 5
  , .halt 0
  ]

@[simp] theorem sizeExtractProgram_oracleFree :
    OracleFree sizeExtractProgram := by
  rfl

def sizeExtractBits (flag size arity encoded : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair (Nat.pair flag size) (Nat.pair arity encoded))
      (Nat.pair size encoded))

theorem run_sizeExtractProgram (inputLength flag size arity encoded : ℕ) :
    runNPOracleProgram sizeExtractProgram
        (sizeExtractBits flag size arity encoded) 6
        (initialNPOracleState inputLength
          (Nat.pair (Nat.pair flag size) (Nat.pair arity encoded))) =
      some (Nat.pair size encoded) := by
  have hinput : ∀ value : ℕ,
      value ≤ Nat.pair (Nat.pair flag size) (Nat.pair arity encoded) →
      natBitLength value ≤ sizeExtractBits flag size arity encoded :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hflagSize := hinput (Nat.pair flag size) (Nat.left_le_pair _ _)
  have hsize :=
    hinput size ((Nat.right_le_pair _ _).trans (Nat.left_le_pair _ _))
  have hpair := hinput (Nat.pair arity encoded) (Nat.right_le_pair _ _)
  have hencoded :=
    hinput encoded ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _))
  have houtput :
      natBitLength (Nat.pair size encoded) ≤
        sizeExtractBits flag size arity encoded :=
    natBitLength_mono (Nat.le_max_right _ _)
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := Nat.pair flag size) (by rfl) rfl
    (by simp [initialNPOracleState]) hflagSize]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := size) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsize]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair arity encoded) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpair]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := encoded) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hencoded]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair size encoded) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 2. The encoded node count -/

/-- The circuit's size from its encoding: the total validator, entered at the
circuit's own arity, beside the retained encoding. -/
def circuitSizeProgram : NPOracleProgram :=
  linkPrograms frameRightProgram <|
    linkPrograms
      (nativeContextCallProgram booleanCircuitValidationPrepareRebuildProgram)
      sizeExtractProgram

@[simp] theorem circuitSizeProgram_oracleFree :
    OracleFree circuitSizeProgram :=
  oracleFree_linkPrograms frameRightProgram_oracleFree
    (oracleFree_linkPrograms
      (nativeContextCallProgram_oracleFree
        booleanCircuitValidationPrepareRebuildProgram_oracleFree)
      sizeExtractProgram_oracleFree)

def circuitSizeFuel (arity encoded : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (nativeContextCallProgram booleanCircuitValidationPrepareRebuildProgram)
      sizeExtractProgram)
    3 <|
    linkFuel sizeExtractProgram
      (nativeContextCallFuel booleanCircuitValidationPrepareRebuildProgram
        (booleanCircuitValidationPrepareRebuildFuel arity encoded)
        arity encoded) 6

def circuitSizeBits (inputLength arity encoded size : ℕ) : ℕ :=
  occurrenceStageBits inputLength (frameRightBits arity encoded) <|
    occurrenceStageBits inputLength
      (nativeContextCallBits inputLength arity encoded encoded
        (Nat.pair 1 size)
        (booleanCircuitValidationPrepareRebuildBits arity encoded))
      (sizeExtractBits 1 size arity encoded)

/-- **The size, executed.**  The only input is a genuine circuit encoding and
the arity it is stated at. -/
theorem run_circuitSizeProgram (inputLength : ℕ) {arity : ℕ}
    (circuit : BooleanCircuit arity) :
    runNPOracleProgram circuitSizeProgram
        (circuitSizeBits inputLength arity (encodeBooleanCircuit circuit)
          circuit.size)
        (circuitSizeFuel arity (encodeBooleanCircuit circuit))
        (initialNPOracleState inputLength
          (Nat.pair arity (encodeBooleanCircuit circuit))) =
      some (Nat.pair circuit.size (encodeBooleanCircuit circuit)) := by
  have hvalidation :
      runNPOracleProgram booleanCircuitValidationPrepareRebuildProgram
          (booleanCircuitValidationPrepareRebuildBits arity
            (encodeBooleanCircuit circuit))
          (booleanCircuitValidationPrepareRebuildFuel arity
            (encodeBooleanCircuit circuit))
          (initialNPOracleState arity (encodeBooleanCircuit circuit)) =
        some (Nat.pair 1 circuit.size) := by
    have hrun :=
      run_booleanCircuitValidationPrepareRebuildProgram arity
        (encodeBooleanCircuit circuit)
    rw [booleanCircuitValidationOutput_encodeBooleanCircuit circuit] at hrun
    exact hrun
  exact run_occurrenceStage
    (run_frameRightProgram inputLength arity (encodeBooleanCircuit circuit))
    (run_occurrenceStage
      (run_nativeContextCallProgram booleanCircuitValidationPrepareRebuildProgram
        inputLength arity (encodeBooleanCircuit circuit)
        (encodeBooleanCircuit circuit) (Nat.pair 1 circuit.size)
        (booleanCircuitValidationPrepareRebuildBits arity
          (encodeBooleanCircuit circuit))
        (booleanCircuitValidationPrepareRebuildFuel arity
          (encodeBooleanCircuit circuit)) hvalidation)
      (run_sizeExtractProgram inputLength 1 circuit.size arity
        (encodeBooleanCircuit circuit)))

/-! ## 3. The assembled oracle triple -/

/-- The oracle half of the occurrence packet, as a numeral. -/
def oracleTripleWord (nativeClauseBits circuitSize encoded : ℕ) : ℕ :=
  Nat.pair nativeClauseBits (Nat.pair circuitSize encoded)

/-- **The oracle triple as one fixed stream.**  From the substituted circuit's
arity and encoding it emits the published factory's clause width, the circuit's
size, and the encoding itself. -/
def oracleTripleProgram (factory : ExecutablePointwisePCPPFactory) :
    NPOracleProgram :=
  linkPrograms duplicateProgram <|
    linkPrograms (preserveRightProgram (shapeCallProgram factory)) <|
      linkPrograms (preserveRightProgram shapeClauseBitsProgram) <|
        linkPrograms swapPairProgram <|
          linkPrograms (preserveRightProgram circuitSizeProgram)
            swapPairProgram

theorem oracleTripleProgram_oracleFree
    (factory : ExecutablePointwisePCPPFactory) :
    OracleFree (oracleTripleProgram factory) :=
  oracleFree_linkPrograms duplicateProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree _ (shapeCallProgram_oracleFree factory))
      (oracleFree_linkPrograms
        (preserveRightProgram_oracleFree _ shapeClauseBitsProgram_oracleFree)
        (oracleFree_linkPrograms swapPairProgram_oracleFree
          (oracleFree_linkPrograms
            (preserveRightProgram_oracleFree _ circuitSizeProgram_oracleFree)
            swapPairProgram_oracleFree))))

def oracleTripleFuel (factory : ExecutablePointwisePCPPFactory) {arity : ℕ}
    (circuit : BooleanCircuit arity) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram (shapeCallProgram factory))
      (linkPrograms (preserveRightProgram shapeClauseBitsProgram)
        (linkPrograms swapPairProgram
          (linkPrograms (preserveRightProgram circuitSizeProgram)
            swapPairProgram))))
    2 <|
    linkFuel
      (linkPrograms (preserveRightProgram shapeClauseBitsProgram)
        (linkPrograms swapPairProgram
          (linkPrograms (preserveRightProgram circuitSizeProgram)
            swapPairProgram)))
      (preserveRightFuel (shapeCallFuel factory circuit)) <|
      linkFuel
        (linkPrograms swapPairProgram
          (linkPrograms (preserveRightProgram circuitSizeProgram)
            swapPairProgram))
        (preserveRightFuel 3) <|
        linkFuel
          (linkPrograms (preserveRightProgram circuitSizeProgram)
            swapPairProgram)
          4 <|
          linkFuel swapPairProgram
            (preserveRightFuel
              (circuitSizeFuel arity (encodeBooleanCircuit circuit))) 4

noncomputable def oracleTripleBits (factory : ExecutablePointwisePCPPFactory)
    (inputLength : ℕ) {arity : ℕ} (circuit : BooleanCircuit arity) : ℕ :=
  let request := Nat.pair arity (encodeBooleanCircuit circuit)
  let shapeCode := occurrenceShapeCode factory circuit
  let clauseBits := (factory.forCircuit circuit).clauseBits
  let sized := Nat.pair circuit.size (encodeBooleanCircuit circuit)
  occurrenceStageBits inputLength (duplicateBits request) <|
    occurrenceStageBits inputLength
      (preserveRightBits (shapeCallBits factory inputLength circuit) request
        request shapeCode) <|
      occurrenceStageBits inputLength
        (preserveRightBits (shapeClauseBitsBits shapeCode) shapeCode request
          clauseBits) <|
        occurrenceStageBits inputLength (swapPairBits clauseBits request) <|
          occurrenceStageBits inputLength
            (preserveRightBits
              (circuitSizeBits inputLength arity
                (encodeBooleanCircuit circuit) circuit.size)
              request clauseBits sized)
            (swapPairBits sized clauseBits)

set_option maxHeartbeats 800000 in
-- Five linked stages with three `preserveRight` frames over a dependent
-- circuit, so elaborating the statement alone exceeds the default budget.
/-- **The oracle triple, executed.**  Given the arity and the encoding of the
substituted circuit, the fixed stream emits the whole oracle half of the
occurrence packet.  No hypothesis remains: both derived numerals are published
runner calls on the encoding. -/
theorem run_oracleTripleProgram (factory : ExecutablePointwisePCPPFactory)
    (inputLength : ℕ) {arity : ℕ} (circuit : BooleanCircuit arity) :
    runNPOracleProgram (oracleTripleProgram factory)
        (oracleTripleBits factory inputLength circuit)
        (oracleTripleFuel factory circuit)
        (initialNPOracleState inputLength
          (Nat.pair arity (encodeBooleanCircuit circuit))) =
      some
        (oracleTripleWord (factory.forCircuit circuit).clauseBits circuit.size
          (encodeBooleanCircuit circuit)) := by
  have hclause :
      runNPOracleProgram shapeClauseBitsProgram
          (shapeClauseBitsBits (occurrenceShapeCode factory circuit)) 3
          (initialNPOracleState inputLength
            (occurrenceShapeCode factory circuit)) =
        some (factory.forCircuit circuit).clauseBits := by
    rw [clauseBits_eq_shapeCode factory circuit]
    exact run_shapeClauseBitsProgram inputLength
      (occurrenceShapeCode factory circuit)
  refine run_occurrenceStage
    (run_duplicateProgram inputLength
      (Nat.pair arity (encodeBooleanCircuit circuit))) ?_
  refine run_occurrenceStage
    (run_preserveRightProgram (shapeCallProgram factory) inputLength
      (shapeCallBits factory inputLength circuit) (shapeCallFuel factory circuit)
      (Nat.pair arity (encodeBooleanCircuit circuit))
      (Nat.pair arity (encodeBooleanCircuit circuit))
      (occurrenceShapeCode factory circuit)
      (run_shapeCallProgram factory inputLength circuit)) ?_
  refine run_occurrenceStage
    (run_preserveRightProgram shapeClauseBitsProgram inputLength
      (shapeClauseBitsBits (occurrenceShapeCode factory circuit)) 3
      (occurrenceShapeCode factory circuit)
      (Nat.pair arity (encodeBooleanCircuit circuit))
      (factory.forCircuit circuit).clauseBits hclause) ?_
  refine run_occurrenceStage
    (run_swapPairProgram inputLength (factory.forCircuit circuit).clauseBits
      (Nat.pair arity (encodeBooleanCircuit circuit))) ?_
  exact run_occurrenceStage
    (run_preserveRightProgram circuitSizeProgram inputLength
      (circuitSizeBits inputLength arity (encodeBooleanCircuit circuit)
        circuit.size)
      (circuitSizeFuel arity (encodeBooleanCircuit circuit))
      (Nat.pair arity (encodeBooleanCircuit circuit))
      (factory.forCircuit circuit).clauseBits
      (Nat.pair circuit.size (encodeBooleanCircuit circuit))
      (run_circuitSizeProgram inputLength circuit))
    (run_swapPairProgram inputLength
      (Nat.pair circuit.size (encodeBooleanCircuit circuit))
      (factory.forCircuit circuit).clauseBits)

end NearCubicWires.RuntimeCaseTwoOracleTripleProgram
