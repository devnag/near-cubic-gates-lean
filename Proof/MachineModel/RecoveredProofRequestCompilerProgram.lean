import Proof.MachineModel.GeneratedBalancedRangeProgram
import Proof.MachineModel.RecoveredProofEncodingProgram

/-!
# The recovered-proof request compiler

`RecoveredProofEncodingProgram.run_recoveredProofEncodingProgram` consumes one
public code, `recoveredProofEncodingInput`, that is `encodeBalancedList` of the
whole address schedule of the C.12-recovered outer proof.  That list is
exponentially long, so it may not be supplied as data: a fixed program has to
build it.  This module is that builder.

Only two ingredients are used, both already certified elsewhere.

* `GeneratedBalancedRangeProgram` emits the canonical balanced list of the
  consecutive request atoms `pair inputLength (pair address stream)` directly,
  without materializing a linked spine.
* One canonical balanced call reshapes every atom into the exact prefix-SAT
  request `pair inputLength (pair stream (encodeUnary (address + 1)))` demanded
  by `RecoveredProofEncodingProgram.recoveredProofRequest`.  The tiny fixed
  callee is the only new instruction stream here; it performs no oracle query.

The composed program is therefore oracle-free: every SAT query of Case 1 still
happens inside the already published `recoveredProofEncodingProgram`.

## What remains outside

The compiler needs the raw clause stream of `outerProofRecoveryFormula` and the
proof address count `2 ^ scheduledWidth` in its input register.  Producing that
seed pair from the raw refuter word is one further fixed program — the *only*
remaining seam of the Case-1 request path — so it enters the theorems below as
an explicit program together with its own exact run hypothesis, exactly as
`CanonicalNativeCallProgram.run_nativeCallProgram` takes its callee.
-/

namespace NearCubicWires.RecoveredProofRequestCompilerProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveredProofEncodingProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. Monotonicity of the unary loop bound -/

private theorem encodeUnary_succ (count : ℕ) :
    encodeUnary (count + 1) = Nat.pair 1 (encodeUnary count) := rfl

private theorem encodeUnary_mono {left right : ℕ} (hle : left ≤ right) :
    encodeUnary left ≤ encodeUnary right := by
  induction right with
  | zero =>
      rw [Nat.le_zero.mp hle]
  | succ right ih =>
      rcases Nat.lt_or_ge left (right + 1) with hlt | hge
      · refine (ih (Nat.lt_succ_iff.mp hlt)).trans ?_
        rw [encodeUnary_succ]
        exact Nat.right_le_pair 1 (encodeUnary right)
      · rw [Nat.le_antisymm hle hge]

private theorem le_foldr_max_of_mem {value : ℕ} {values : List ℕ}
    (hmem : value ∈ values) : value ≤ values.foldr max 0 := by
  induction values with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · exact hhead ▸ Nat.le_max_left _ _
      · exact (ih htail).trans (Nat.le_max_right _ _)

/-! ## 2. One request atom

The callee receives the range generator's atom body `pair address stream` in
register zero and the shared public length in register one.  It returns the
canonical prefix-SAT request of that address. -/

/-- Exact output of the fixed atom callee. -/
def recoveredProofRequestAtomOutput (inputLength address stream : ℕ) : ℕ :=
  Nat.pair inputLength (Nat.pair stream (encodeUnary (address + 1)))

/-- Register ABI:

* `r0`: request body and then the emitted request;
* `r1`: preserved public input length;
* `r2`: requested address and then the unary countdown;
* `r3`: preserved raw clause stream;
* `r4`: unary accumulator;
* `r5`: the constant one, also the unconditional back edge;
* `r6`: pairing scratch. -/
def recoveredProofRequestAtomProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 4 0 3
  , .set 5 1 4
  , .increment 2 5
  , .branchZero 2 9 6
  , .pair 5 4 4 7
  , .decrement 2 8
  , .branchZero 5 5 5
  , .pair 3 4 6 10
  , .pair 1 6 0 11
  , .halt 0
  ]

@[simp] theorem recoveredProofRequestAtomProgram_oracleFree :
    OracleFree recoveredProofRequestAtomProgram := by
  rfl

private def recoveredProofRequestAtomLoopFuel (counter : ℕ) : ℕ :=
  4 * counter + 4

/-- Five setup instructions, four instructions per unary cell, and four
instructions for the exit test and both pairings. -/
def recoveredProofRequestAtomFuel (address : ℕ) : ℕ :=
  4 * address + 13

def recoveredProofRequestAtomBits
    (inputLength address stream : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair address stream)
      (max (address + 1)
        (recoveredProofRequestAtomOutput inputLength address stream)))

private theorem run_recoveredProofRequestAtomLoop
    (inputLength stream maximumBits : ℕ) (counter accumulated : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 5)
    (hlength : state.registers 1 = inputLength)
    (hcounter : state.registers 2 = counter)
    (hstream : state.registers 3 = stream)
    (haccumulated : state.registers 4 = encodeUnary accumulated)
    (hone : state.registers 5 = 1)
    (hcounterBits : natBitLength counter ≤ maximumBits)
    (hunaryBits :
      natBitLength (encodeUnary (accumulated + counter)) ≤ maximumBits)
    (hbodyBits :
      natBitLength
          (Nat.pair stream (encodeUnary (accumulated + counter))) ≤
        maximumBits)
    (houtputBits :
      natBitLength
          (Nat.pair inputLength
            (Nat.pair stream (encodeUnary (accumulated + counter)))) ≤
        maximumBits) :
    runNPOracleProgram recoveredProofRequestAtomProgram maximumBits
        (recoveredProofRequestAtomLoopFuel counter) state =
      some
        (Nat.pair inputLength
          (Nat.pair stream (encodeUnary (accumulated + counter)))) := by
  induction counter generalizing accumulated state with
  | zero =>
      have hbody :
          natBitLength (Nat.pair stream (encodeUnary accumulated)) ≤
            maximumBits := by
        simpa using hbodyBits
      have houtput :
          natBitLength
              (Nat.pair inputLength
                (Nat.pair stream (encodeUnary accumulated))) ≤
            maximumBits := by
        simpa using houtputBits
      rw [recoveredProofRequestAtomLoopFuel]
      rw [show 4 * 0 + 4 = 3 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hcounter, if_pos rfl]
      rw [show 3 = 2 + 1 by omega]
      rw [run_pair_instruction
        (value := Nat.pair stream (encodeUnary accumulated))
        (by rfl) rfl
        (by simp [NPOracleState.jump, hstream, haccumulated])
        hbody]
      rw [show 2 = 1 + 1 by omega]
      rw [run_pair_instruction
        (value :=
          Nat.pair inputLength (Nat.pair stream (encodeUnary accumulated)))
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hlength])
        houtput]
      rw [run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        houtput]
      simp
  | succ counter ih =>
      have htotal :
          accumulated + (counter + 1) = accumulated + 1 + counter := by
        omega
      have hstepBits :
          natBitLength (encodeUnary (accumulated + 1)) ≤ maximumBits := by
        refine (natBitLength_mono (encodeUnary_mono ?_)).trans hunaryBits
        omega
      have hcounterStepBits : natBitLength counter ≤ maximumBits :=
        (natBitLength_mono (Nat.le_succ counter)).trans hcounterBits
      rw [htotal] at hunaryBits hbodyBits houtputBits ⊢
      rw [recoveredProofRequestAtomLoopFuel]
      rw [show 4 * (counter + 1) + 4 =
          (recoveredProofRequestAtomLoopFuel counter + 3) + 1 by
        unfold recoveredProofRequestAtomLoopFuel
        omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hcounter, if_neg (Nat.succ_ne_zero counter)]
      rw [show recoveredProofRequestAtomLoopFuel counter + 3 =
          (recoveredProofRequestAtomLoopFuel counter + 2) + 1 by omega]
      rw [run_pair_instruction (value := encodeUnary (accumulated + 1))
        (by rfl) rfl
        (by
          simp [NPOracleState.jump, hone, haccumulated, encodeUnary_succ])
        hstepBits]
      rw [show recoveredProofRequestAtomLoopFuel counter + 2 =
          (recoveredProofRequestAtomLoopFuel counter + 1) + 1 by omega]
      rw [run_decrement_instruction (value := counter)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hcounter])
        hcounterStepBits]
      rw [run_branchZero_instruction (by rfl) rfl, ite_self]
      exact ih (accumulated + 1) _ rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hlength])
        (by simp [NPOracleState.write, NPOracleState.jump])
        (by simp [NPOracleState.write, NPOracleState.jump, hstream])
        (by simp [NPOracleState.write, NPOracleState.jump])
        (by simp [NPOracleState.write, NPOracleState.jump, hone])
        hcounterStepBits hunaryBits hbodyBits houtputBits

/-- Exact reshaping of one range atom into one prefix-SAT request. -/
theorem run_recoveredProofRequestAtomProgram
    (inputLength address stream : ℕ) :
    runNPOracleProgram recoveredProofRequestAtomProgram
        (recoveredProofRequestAtomBits inputLength address stream)
        (recoveredProofRequestAtomFuel address)
        (initialNPOracleState inputLength (Nat.pair address stream)) =
      some (recoveredProofRequestAtomOutput inputLength address stream) := by
  have houtputBits :
      natBitLength
          (recoveredProofRequestAtomOutput inputLength address stream) ≤
        recoveredProofRequestAtomBits inputLength address stream :=
    natBitLength_mono ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hbodyBits :
      natBitLength (Nat.pair stream (encodeUnary (address + 1))) ≤
        recoveredProofRequestAtomBits inputLength address stream :=
    (natBitLength_mono
      (Nat.right_le_pair inputLength
        (Nat.pair stream (encodeUnary (address + 1))))).trans houtputBits
  have hunaryBits :
      natBitLength (encodeUnary (address + 1)) ≤
        recoveredProofRequestAtomBits inputLength address stream :=
    (natBitLength_mono
      (Nat.right_le_pair stream (encodeUnary (address + 1)))).trans hbodyBits
  have hlengthBits :
      natBitLength inputLength ≤
        recoveredProofRequestAtomBits inputLength address stream :=
    (natBitLength_mono
      (Nat.left_le_pair inputLength
        (Nat.pair stream (encodeUnary (address + 1))))).trans houtputBits
  have hrequestBits :
      natBitLength (Nat.pair address stream) ≤
        recoveredProofRequestAtomBits inputLength address stream :=
    natBitLength_mono (Nat.le_max_left _ _)
  have haddressBits :
      natBitLength address ≤
        recoveredProofRequestAtomBits inputLength address stream :=
    (natBitLength_mono (Nat.left_le_pair address stream)).trans hrequestBits
  have hstreamBits :
      natBitLength stream ≤
        recoveredProofRequestAtomBits inputLength address stream :=
    (natBitLength_mono (Nat.right_le_pair address stream)).trans hrequestBits
  have hsuccBits :
      natBitLength (address + 1) ≤
        recoveredProofRequestAtomBits inputLength address stream :=
    natBitLength_mono ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have hzeroBits :
      natBitLength 0 ≤
        recoveredProofRequestAtomBits inputLength address stream :=
    (natBitLength_mono (Nat.zero_le _)).trans haddressBits
  have honeBits :
      natBitLength 1 ≤
        recoveredProofRequestAtomBits inputLength address stream :=
    (natBitLength_mono (by omega)).trans hsuccBits
  rw [show recoveredProofRequestAtomFuel address =
      recoveredProofRequestAtomLoopFuel (address + 1) + 1 + 1 + 1 + 1 + 1 by
    unfold recoveredProofRequestAtomFuel recoveredProofRequestAtomLoopFuel
    omega]
  rw [run_unpairLeft_instruction (value := address)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    haddressBits]
  rw [run_unpairRight_instruction (value := stream)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hstreamBits]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
  rw [run_increment_instruction (value := address + 1)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hsuccBits]
  rw [show recoveredProofRequestAtomOutput inputLength address stream =
      Nat.pair inputLength
        (Nat.pair stream (encodeUnary (0 + (address + 1)))) by
    rw [Nat.zero_add]
    rfl]
  refine run_recoveredProofRequestAtomLoop inputLength stream
    (recoveredProofRequestAtomBits inputLength address stream)
    (address + 1) 0 _ ?_ ?_ ?_ ?_ ?_ ?_ hsuccBits ?_ ?_ ?_
  · rfl
  · simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump, encodeUnary]
  · simp [NPOracleState.write, NPOracleState.jump]
  · rw [Nat.zero_add]
    exact hunaryBits
  · rw [Nat.zero_add]
    exact hbodyBits
  · rw [Nat.zero_add]
    exact houtputBits

/-! ## 3. The atom-indexed call schedule -/

/-- Total reading of one range atom as a prefix-SAT request. -/
def recoveredProofRequestOfAtom (atom : ℕ) : ℕ :=
  recoveredProofRequestAtomOutput (Nat.unpair atom).1
    (Nat.unpair (Nat.unpair atom).2).1
    (Nat.unpair (Nat.unpair atom).2).2

def recoveredProofRequestAtomCallFuel (atom : ℕ) : ℕ :=
  recoveredProofRequestAtomFuel (Nat.unpair (Nat.unpair atom).2).1

def recoveredProofRequestAtomCallBits (atom : ℕ) : ℕ :=
  recoveredProofRequestAtomBits (Nat.unpair atom).1
    (Nat.unpair (Nat.unpair atom).2).1
    (Nat.unpair (Nat.unpair atom).2).2

@[simp] theorem recoveredProofRequestOfAtom_atom
    (inputLength address stream : ℕ) :
    recoveredProofRequestOfAtom
        (balancedRangeRequestAtom inputLength address stream) =
      recoveredProofRequestAtomOutput inputLength address stream := by
  simp [recoveredProofRequestOfAtom, balancedRangeRequestAtom]

@[simp] theorem recoveredProofRequestAtomCallFuel_atom
    (inputLength address stream : ℕ) :
    recoveredProofRequestAtomCallFuel
        (balancedRangeRequestAtom inputLength address stream) =
      recoveredProofRequestAtomFuel address := by
  simp [recoveredProofRequestAtomCallFuel, balancedRangeRequestAtom]

@[simp] theorem recoveredProofRequestAtomCallBits_atom
    (inputLength address stream : ℕ) :
    recoveredProofRequestAtomCallBits
        (balancedRangeRequestAtom inputLength address stream) =
      recoveredProofRequestAtomBits inputLength address stream := by
  simp [recoveredProofRequestAtomCallBits, balancedRangeRequestAtom]

/-! ## 4. Dropping the generator's retained context -/

private def recoveredProofRequestTakeLeftProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

@[simp] private theorem recoveredProofRequestTakeLeftProgram_oracleFree :
    OracleFree recoveredProofRequestTakeLeftProgram := by
  rfl

private theorem run_recoveredProofRequestTakeLeftProgram
    {maximumBits : ℕ} (inputLength left right : ℕ)
    (hleftBits : natBitLength left ≤ maximumBits) :
    runNPOracleProgram recoveredProofRequestTakeLeftProgram maximumBits 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some left := by
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hleftBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hleftBits

/-! ## 5. The whole request list from one count and one clause stream -/

/-- The exact atom schedule generated for one address count. -/
def recoveredProofRangeAtoms (inputLength stream count : ℕ) : List ℕ :=
  (List.range count).map fun address =>
    balancedRangeRequestAtom inputLength address stream

private theorem balancedRangeRequestAtoms_eq_recoveredProofRangeAtoms
    (inputLength stream count : ℕ) :
    balancedRangeRequestAtoms inputLength stream 0 count =
      recoveredProofRangeAtoms inputLength stream count := by
  rw [balancedRangeRequestAtoms_eq_map_range]
  simp [recoveredProofRangeAtoms]

private theorem recoveredProofRangeAtoms_map (inputLength stream count : ℕ) :
    (recoveredProofRangeAtoms inputLength stream count).map
        recoveredProofRequestOfAtom =
      (List.range count).map fun address =>
        recoveredProofRequestAtomOutput inputLength address stream := by
  simp [recoveredProofRangeAtoms, List.map_map, Function.comp_def]

private theorem run_recoveredProofRequestAtomCall
    {maximumBits : ℕ} (inputLength stream count : ℕ) {atom : ℕ}
    (hatom : atom ∈ recoveredProofRangeAtoms inputLength stream count)
    (hbits :
      ((recoveredProofRangeAtoms inputLength stream count).map
        recoveredProofRequestAtomCallBits).foldr max 0 ≤ maximumBits) :
    runNPOracleProgram recoveredProofRequestAtomProgram maximumBits
        (recoveredProofRequestAtomCallFuel atom)
        (initialNPOracleState (Nat.unpair atom).1 (Nat.unpair atom).2) =
      some (recoveredProofRequestOfAtom atom) := by
  have hatomBits : recoveredProofRequestAtomCallBits atom ≤ maximumBits :=
    (le_foldr_max_of_mem (List.mem_map_of_mem hatom)).trans hbits
  simp only [recoveredProofRangeAtoms, List.mem_map] at hatom
  obtain ⟨address, _haddress, hatomEq⟩ := hatom
  subst hatomEq
  rw [recoveredProofRequestAtomCallBits_atom] at hatomBits
  rw [recoveredProofRequestOfAtom_atom, recoveredProofRequestAtomCallFuel_atom]
  have hleft :
      (Nat.unpair (balancedRangeRequestAtom inputLength address stream)).1 =
        inputLength := by
    simp [balancedRangeRequestAtom]
  have hright :
      (Nat.unpair (balancedRangeRequestAtom inputLength address stream)).2 =
        Nat.pair address stream := by
    simp [balancedRangeRequestAtom]
  rw [hleft, hright]
  exact run_bits_mono
    (run_recoveredProofRequestAtomProgram inputLength address stream)
    hatomBits

/-- Fixed request-list builder: generate the canonical balanced range, drop the
generator's retained context, and reshape every atom through the single
balanced call. -/
def recoveredProofRequestListProgram : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram
    (linkPrograms recoveredProofRequestTakeLeftProgram
      (balancedCallProgram recoveredProofRequestAtomProgram))

theorem recoveredProofRequestListProgram_oracleFree :
    OracleFree recoveredProofRequestListProgram := by
  apply oracleFree_linkPrograms
  · exact generatedBalancedRangeProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact recoveredProofRequestTakeLeftProgram_oracleFree
    · exact balancedCallProgram_oracleFree
        recoveredProofRequestAtomProgram_oracleFree

def recoveredProofRequestListFuel (inputLength stream count : ℕ) : ℕ :=
  linkFuel
    (linkPrograms recoveredProofRequestTakeLeftProgram
      (balancedCallProgram recoveredProofRequestAtomProgram))
    (generatedBalancedRangeFuel inputLength count stream)
    (linkFuel (balancedCallProgram recoveredProofRequestAtomProgram) 2
      (balancedCallFuel recoveredProofRequestAtomProgram
        recoveredProofRequestAtomCallFuel
        (recoveredProofRangeAtoms inputLength stream count)))

def recoveredProofRequestListBits (inputLength stream count : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max (generatedBalancedRangeRequiredBits inputLength count stream) <|
        max
          (natBitLength
            (encodeBalancedList
              (recoveredProofRangeAtoms inputLength stream count))) <|
          max
            (balancedCallRequiredBits recoveredProofRequestOfAtom
              (recoveredProofRangeAtoms inputLength stream count))
            (((recoveredProofRangeAtoms inputLength stream count).map
              recoveredProofRequestAtomCallBits).foldr max 0)

/-- Exact request-list construction.  One fixed instruction stream turns the
pair `(address count, raw clause stream)` into the canonical balanced list of
every prefix-SAT request of the recovered proof. -/
theorem run_recoveredProofRequestListProgram
    (inputLength stream count : ℕ) :
    runNPOracleProgram recoveredProofRequestListProgram
        (recoveredProofRequestListBits inputLength stream count)
        (recoveredProofRequestListFuel inputLength stream count)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput count stream)) =
      some
        (encodeBalancedList
          ((List.range count).map fun address =>
            recoveredProofRequestAtomOutput inputLength address stream)) := by
  have hpositive : 1 ≤ recoveredProofRequestListBits inputLength stream count :=
    Nat.le_max_left _ _
  have hlengthBits :
      natBitLength inputLength ≤
        recoveredProofRequestListBits inputLength stream count :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hrangeBits :
      generatedBalancedRangeRequiredBits inputLength count stream ≤
        recoveredProofRequestListBits inputLength stream count :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlistBits :
      natBitLength
          (encodeBalancedList
            (recoveredProofRangeAtoms inputLength stream count)) ≤
        recoveredProofRequestListBits inputLength stream count :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      balancedCallRequiredBits recoveredProofRequestOfAtom
          (recoveredProofRangeAtoms inputLength stream count) ≤
        recoveredProofRequestListBits inputLength stream count :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hatomBits :
      ((recoveredProofRangeAtoms inputLength stream count).map
          recoveredProofRequestAtomCallBits).foldr max 0 ≤
        recoveredProofRequestListBits inputLength stream count :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram
          (recoveredProofRequestListBits inputLength stream count)
          (generatedBalancedRangeFuel inputLength count stream)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput count stream)) =
        some
          (Nat.pair
            (encodeBalancedList
              (recoveredProofRangeAtoms inputLength stream count))
            stream) := by
    rw [← balancedRangeRequestAtoms_eq_recoveredProofRangeAtoms]
    exact run_bits_mono
      (run_generatedBalancedRangeProgram inputLength count stream) hrangeBits
  have htake :
      runNPOracleProgram recoveredProofRequestTakeLeftProgram
          (recoveredProofRequestListBits inputLength stream count) 2
          (initialNPOracleState inputLength
            (Nat.pair
              (encodeBalancedList
                (recoveredProofRangeAtoms inputLength stream count))
              stream)) =
        some
          (encodeBalancedList
            (recoveredProofRangeAtoms inputLength stream count)) :=
    run_recoveredProofRequestTakeLeftProgram inputLength
      (encodeBalancedList (recoveredProofRangeAtoms inputLength stream count))
      stream hlistBits
  have hcall :
      runNPOracleProgram
          (balancedCallProgram recoveredProofRequestAtomProgram)
          (recoveredProofRequestListBits inputLength stream count)
          (balancedCallFuel recoveredProofRequestAtomProgram
            recoveredProofRequestAtomCallFuel
            (recoveredProofRangeAtoms inputLength stream count))
          (initialNPOracleState inputLength
            (encodeBalancedList
              (recoveredProofRangeAtoms inputLength stream count))) =
        some
          (encodeBalancedList
            ((recoveredProofRangeAtoms inputLength stream count).map
              recoveredProofRequestOfAtom)) :=
    run_balancedCallProgram_from inputLength
      (recoveredProofRangeAtoms inputLength stream count)
      recoveredProofRequestAtomCallFuel recoveredProofRequestOfAtom hcallBits
      (fun _atom hatom =>
        run_recoveredProofRequestAtomCall inputLength stream count hatom
          hatomBits)
  have hsecond :=
    run_linkPrograms hpositive hlengthBits htake hcall
  have hrun := run_linkPrograms hpositive hlengthBits hrange hsecond
  rw [← recoveredProofRangeAtoms_map inputLength stream count]
  simpa only [recoveredProofRequestListProgram, recoveredProofRequestListFuel]
    using hrun

/-! ## 6. The scheduled instance

At the published schedule the generated list is literally
`recoveredProofEncodingInput`, so `run_recoveredProofEncodingProgram` may be
invoked immediately afterwards. -/

theorem recoveredProofRequestList_eq_encodingInput
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength : ℕ) :
    encodeBalancedList
        ((List.range (2 ^ pcp.nativeWidth n)).map fun address =>
          recoveredProofRequestAtomOutput inputLength address
            (rawClauseStream (outerProofRecoveryFormula pcp input))) =
      recoveredProofEncodingInput pcp input inputLength :=
  rfl

theorem run_recoveredProofRequestListProgram_scheduled
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength : ℕ) :
    runNPOracleProgram recoveredProofRequestListProgram
        (recoveredProofRequestListBits inputLength
          (rawClauseStream (outerProofRecoveryFormula pcp input))
          (2 ^ pcp.nativeWidth n))
        (recoveredProofRequestListFuel inputLength
          (rawClauseStream (outerProofRecoveryFormula pcp input))
          (2 ^ pcp.nativeWidth n))
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput (2 ^ pcp.nativeWidth n)
            (rawClauseStream (outerProofRecoveryFormula pcp input)))) =
      some (recoveredProofEncodingInput pcp input inputLength) := by
  rw [← recoveredProofRequestList_eq_encodingInput pcp input inputLength]
  exact run_recoveredProofRequestListProgram inputLength
    (rawClauseStream (outerProofRecoveryFormula pcp input))
    (2 ^ pcp.nativeWidth n)

/-! ## 7. The request compiler

The compiler is the seed stage followed by the request-list builder run on the
seed's left component; the retained right component is the
`(calleeInputLength, context)` frame consumed by
`CanonicalNativeCallProgram.nativeContextCallProgram`, so the published
encoder can be called immediately afterwards without recomputing the schedule
parameters. -/

/-- The exact seed the compiler consumes: the proof address count paired with
the raw clause stream of the C.12 recovery formula, beside the retained call
frame. -/
def recoveredProofCompilerSeedOutput
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) : ℕ :=
  Nat.pair
    (generatedBalancedRangeInput (2 ^ scheduledWidth outer sourceIndex)
      (rawClauseStream
        (outerProofRecoveryFormula (paddedOuterPCP outer) input)))
    (Nat.pair (sourceLength sourceIndex)
      (Nat.pair (scheduledWidth outer sourceIndex) (encodeBitInput input)))

def recoveredProofRequestCompilerProgram (seed : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms seed (preserveRightProgram recoveredProofRequestListProgram)

theorem recoveredProofRequestCompilerProgram_oracleFree
    {seed : NPOracleProgram} (hseed : OracleFree seed) :
    OracleFree (recoveredProofRequestCompilerProgram seed) :=
  oracleFree_linkPrograms hseed
    (preserveRightProgram_oracleFree _
      recoveredProofRequestListProgram_oracleFree)

def recoveredProofRequestCompilerFuel
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) (seedFuel : ℕ) : ℕ :=
  linkFuel (preserveRightProgram recoveredProofRequestListProgram) seedFuel
    (preserveRightFuel
      (recoveredProofRequestListFuel (sourceLength sourceIndex)
        (rawClauseStream
          (outerProofRecoveryFormula (paddedOuterPCP outer) input))
        (2 ^ scheduledWidth outer sourceIndex)))

def recoveredProofRequestCompilerBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) (seedBits : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength (sourceLength sourceIndex)) <|
      max seedBits
        (preserveRightBits
          (recoveredProofRequestListBits (sourceLength sourceIndex)
            (rawClauseStream
              (outerProofRecoveryFormula (paddedOuterPCP outer) input))
            (2 ^ scheduledWidth outer sourceIndex))
          (generatedBalancedRangeInput (2 ^ scheduledWidth outer sourceIndex)
            (rawClauseStream
              (outerProofRecoveryFormula (paddedOuterPCP outer) input)))
          (Nat.pair (sourceLength sourceIndex)
            (Nat.pair (scheduledWidth outer sourceIndex)
              (encodeBitInput input)))
          (recoveredProofEncodingInput (paddedOuterPCP outer) input
            (sourceLength sourceIndex)))

/-- Exact request compilation.  From the raw refuter word alone — modulo the
single named seed stage — one fixed program emits the whole balanced request
list of `outerProofRecoveryFormula` beside the retained arity and point
context, in precisely the frame that
`CanonicalNativeCallProgram.nativeContextCallProgram` consumes. -/
theorem run_recoveredProofRequestCompilerProgram
    (seed : NPOracleProgram) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex))
    (seedBits seedFuel : ℕ)
    (hseed :
      runNPOracleProgram seed seedBits seedFuel
          (initialNPOracleState (sourceLength sourceIndex)
            (encodeBitInput input)) =
        some (recoveredProofCompilerSeedOutput outer sourceIndex input)) :
    runNPOracleProgram (recoveredProofRequestCompilerProgram seed)
        (recoveredProofRequestCompilerBits outer sourceIndex input seedBits)
        (recoveredProofRequestCompilerFuel outer sourceIndex input seedFuel)
        (initialNPOracleState (sourceLength sourceIndex)
          (encodeBitInput input)) =
      some
        (Nat.pair
          (recoveredProofEncodingInput (paddedOuterPCP outer) input
            (sourceLength sourceIndex))
          (Nat.pair (sourceLength sourceIndex)
            (Nat.pair (scheduledWidth outer sourceIndex)
              (encodeBitInput input)))) := by
  have hpositive :
      1 ≤ recoveredProofRequestCompilerBits outer sourceIndex input seedBits :=
    Nat.le_max_left _ _
  have hlengthBits :
      natBitLength (sourceLength sourceIndex) ≤
        recoveredProofRequestCompilerBits outer sourceIndex input seedBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hseedBits :
      seedBits ≤
        recoveredProofRequestCompilerBits outer sourceIndex input seedBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpreserveBits :
      preserveRightBits
          (recoveredProofRequestListBits (sourceLength sourceIndex)
            (rawClauseStream
              (outerProofRecoveryFormula (paddedOuterPCP outer) input))
            (2 ^ scheduledWidth outer sourceIndex))
          (generatedBalancedRangeInput (2 ^ scheduledWidth outer sourceIndex)
            (rawClauseStream
              (outerProofRecoveryFormula (paddedOuterPCP outer) input)))
          (Nat.pair (sourceLength sourceIndex)
            (Nat.pair (scheduledWidth outer sourceIndex)
              (encodeBitInput input)))
          (recoveredProofEncodingInput (paddedOuterPCP outer) input
            (sourceLength sourceIndex)) ≤
        recoveredProofRequestCompilerBits outer sourceIndex input seedBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpreserve :=
    run_bits_mono
      (run_preserveRightProgram recoveredProofRequestListProgram
        (sourceLength sourceIndex)
        (recoveredProofRequestListBits (sourceLength sourceIndex)
          (rawClauseStream
            (outerProofRecoveryFormula (paddedOuterPCP outer) input))
          (2 ^ scheduledWidth outer sourceIndex))
        (recoveredProofRequestListFuel (sourceLength sourceIndex)
          (rawClauseStream
            (outerProofRecoveryFormula (paddedOuterPCP outer) input))
          (2 ^ scheduledWidth outer sourceIndex))
        (generatedBalancedRangeInput (2 ^ scheduledWidth outer sourceIndex)
          (rawClauseStream
            (outerProofRecoveryFormula (paddedOuterPCP outer) input)))
        (Nat.pair (sourceLength sourceIndex)
          (Nat.pair (scheduledWidth outer sourceIndex)
            (encodeBitInput input)))
        (recoveredProofEncodingInput (paddedOuterPCP outer) input
          (sourceLength sourceIndex))
        (run_recoveredProofRequestListProgram_scheduled (paddedOuterPCP outer)
          input (sourceLength sourceIndex)))
      hpreserveBits
  have hrun :=
    run_linkPrograms hpositive hlengthBits
      (run_bits_mono hseed hseedBits) hpreserve
  simpa only [recoveredProofRequestCompilerProgram,
    recoveredProofRequestCompilerFuel, recoveredProofCompilerSeedOutput]
    using hrun

end NearCubicWires.RecoveredProofRequestCompilerProgram
