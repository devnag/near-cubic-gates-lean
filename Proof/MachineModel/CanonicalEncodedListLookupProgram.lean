import Proof.Foundations.CanonicalBinaryProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.VerifiedLinker

/-!
# Fixed lookup in Lean's canonical `Encodable` list spine

Projection decision runners return `Encodable` codes for lists of three-literal
clauses.  The list instance is the zero/successor pairing spine, so one small
fixed program suffices for both the outer clause lookup and each inner literal
lookup.  This module keeps that codec boundary executable instead of decoding
runner output in the host logic.
-/

namespace NearCubicWires.CanonicalEncodedListLookupProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

def encodedListLookupInput
    (code index fallback : ℕ) : ℕ :=
  Nat.pair code (Nat.pair index fallback)

/-- Total structural interpretation of the zero/successor list spine. -/
def encodedListGetD : ℕ → ℕ → ℕ → ℕ
  | code, 0, fallback =>
      if code = 0 then
        fallback
      else
        let cell := Nat.unpair code.pred
        cell.1
  | code, index + 1, fallback =>
      if code = 0 then
        fallback
      else
        let cell := Nat.unpair code.pred
        encodedListGetD cell.2 index fallback

@[simp] theorem encodedListGetD_encodeValues
    {α : Type*} [Encodable α]
    (values : List α) (index fallback : ℕ) :
    encodedListGetD (Encodable.encode values) index fallback =
      (values.map Encodable.encode).getD index fallback := by
  induction values generalizing index with
  | nil =>
      cases index <;> simp [encodedListGetD]
  | cons value rest inductionHypothesis =>
      cases index with
      | zero =>
          simp [encodedListGetD]
      | succ index =>
          simp [encodedListGetD, inductionHypothesis]

@[simp] theorem encodedListGetD_encode
    (values : List ℕ) (index fallback : ℕ) :
    encodedListGetD (Encodable.encode values) index fallback =
      values.getD index fallback := by
  have hmap : values.map Encodable.encode = values := by
    induction values with
    | nil => rfl
    | cons value rest inductionHypothesis =>
        simp [inductionHypothesis]
  rw [encodedListGetD_encodeValues]
  exact congrArg (fun list => list.getD index fallback) hmap

/-- The structural machine semantics agrees with Lean's total list decoder on
every runner output, including non-canonical external codes. -/
theorem encodedListGetD_eq_decode
    (code index fallback : ℕ) :
    encodedListGetD code index fallback =
      ((Encodable.decode code : Option (List ℕ)).getD []).getD
        index fallback := by
  induction index generalizing code with
  | zero =>
      cases code with
      | zero =>
          simp [encodedListGetD]
      | succ spine =>
          simp [encodedListGetD]
  | succ index inductionHypothesis =>
      cases code with
      | zero =>
          simp [encodedListGetD]
      | succ spine =>
          simp [encodedListGetD, inductionHypothesis]

/-- Register ABI:

* `r0`: request, then result;
* `r2`: current encoded-list cursor;
* `r4`: remaining index;
* `r5`: fallback;
* `r6`/`r7`: current head and tail.
-/
def encodedListLookupProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .branchZero 2 11 5
  , .decrement 2 6
  , .unpairLeft 2 6 7
  , .unpairRight 2 7 8
  , .branchZero 4 13 9
  , .decrement 4 10
  , .copy 7 2 4
  , .copy 5 0 12
  , .halt 0
  , .copy 6 0 12
  ]

@[simp] theorem encodedListLookupProgram_oracleFree :
    OracleFree encodedListLookupProgram := by
  rfl

def encodedListLookupLoopFuel : ℕ → ℕ → ℕ
  | code, 0 =>
      if code = 0 then
        3
      else
        7
  | code, index + 1 =>
      if code = 0 then
        3
      else
        7 + encodedListLookupLoopFuel
          (Nat.unpair code.pred).2 index

def encodedListLookupFuel (code index : ℕ) : ℕ :=
  4 + encodedListLookupLoopFuel code index

def encodedListLookupBits
    (code index fallback : ℕ) : ℕ :=
  natBitLength (encodedListLookupInput code index fallback)

theorem encodedListLookupLoopFuel_le (code index : ℕ) :
    encodedListLookupLoopFuel code index ≤ 7 * index + 7 := by
  induction index generalizing code with
  | zero =>
      simp [encodedListLookupLoopFuel]
      split <;> omega
  | succ index inductionHypothesis =>
      simp only [encodedListLookupLoopFuel]
      split
      · omega
      · have hbound :=
          inductionHypothesis (Nat.unpair code.pred).2
        omega

theorem encodedListLookupFuel_le (code index : ℕ) :
    encodedListLookupFuel code index ≤ 7 * index + 11 := by
  unfold encodedListLookupFuel
  have hbound := encodedListLookupLoopFuel_le code index
  omega

private theorem encodedListLookupLoopFuel_zero (index : ℕ) :
    encodedListLookupLoopFuel 0 index = 3 := by
  cases index <;> simp [encodedListLookupLoopFuel]

private theorem encodedListGetD_zero (index fallback : ℕ) :
    encodedListGetD 0 index fallback = fallback := by
  cases index <;> simp [encodedListGetD]

private theorem run_encodedListLookupLoop_zero
    (index fallback maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 4)
    (hcode : state.registers 2 = 0)
    (hfallback : state.registers 5 = fallback)
    (hfallbackBits : natBitLength fallback ≤ maximumBits) :
    runNPOracleProgram encodedListLookupProgram maximumBits
        (encodedListLookupLoopFuel 0 index) state =
      some (encodedListGetD 0 index fallback) := by
  rw [encodedListLookupLoopFuel_zero, encodedListGetD_zero]
  rw [show 3 = 2 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) hpc, hcode, if_pos rfl]
  rw [show 2 = 1 + 1 by omega]
  rw [run_copy_instruction (value := fallback)
    (by rfl) rfl (by simpa using hfallback) hfallbackBits]
  exact run_halt_instruction (by rfl) rfl (by simp) hfallbackBits

private theorem run_encodedListLookupLoop
    (code index fallback maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 4)
    (hcode : state.registers 2 = code)
    (hindex : state.registers 4 = index)
    (hfallback : state.registers 5 = fallback)
    (hcodeBits : natBitLength code ≤ maximumBits)
    (hindexBits : natBitLength index ≤ maximumBits)
    (hfallbackBits : natBitLength fallback ≤ maximumBits) :
    runNPOracleProgram encodedListLookupProgram maximumBits
        (encodedListLookupLoopFuel code index) state =
      some (encodedListGetD code index fallback) := by
  induction index generalizing code state with
  | zero =>
      by_cases hcodeZero : code = 0
      · rw [hcodeZero]
        exact run_encodedListLookupLoop_zero 0 fallback maximumBits state
          hpc (by simpa [hcodeZero] using hcode) hfallback hfallbackBits
      · let cellCode := code.pred
        let head := (Nat.unpair cellCode).1
        let tail := (Nat.unpair cellCode).2
        let state1 := (state.write 2 cellCode).jump 6
        let state2 := (state1.write 6 head).jump 7
        let state3 := (state2.write 7 tail).jump 8
        let resultState := (state3.write 0 head).jump 12
        have hcellBits :
            natBitLength cellCode ≤ maximumBits :=
          (decrement_bits_le code).trans hcodeBits
        have hheadBits :
            natBitLength head ≤ maximumBits :=
          (natBitLength_mono (Nat.unpair_left_le cellCode)).trans
            hcellBits
        have htailBits :
            natBitLength tail ≤ maximumBits :=
          (natBitLength_mono (Nat.unpair_right_le cellCode)).trans
            hcellBits
        rw [encodedListLookupLoopFuel, if_neg hcodeZero]
        rw [encodedListGetD, if_neg hcodeZero]
        rw [show 7 = 6 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hcode, if_neg hcodeZero]
        change
          runNPOracleProgram encodedListLookupProgram maximumBits 6
              (state.jump 5) =
            some head
        rw [show 6 = 5 + 1 by omega]
        rw [run_decrement_instruction (value := cellCode)
          (by rfl) rfl (by simp [hcode, cellCode]) hcellBits]
        change
          runNPOracleProgram encodedListLookupProgram maximumBits 5 state1 =
            some head
        rw [show 5 = 4 + 1 by omega]
        rw [run_unpairLeft_instruction (value := head)
          (by rfl) rfl (by simp [state1, cellCode, head]) hheadBits]
        change
          runNPOracleProgram encodedListLookupProgram maximumBits 4 state2 =
            some head
        rw [show 4 = 3 + 1 by omega]
        rw [run_unpairRight_instruction (value := tail)
          (by rfl) rfl
          (by simp [state2, state1, cellCode, tail]) htailBits]
        change
          runNPOracleProgram encodedListLookupProgram maximumBits 3 state3 =
            some head
        rw [show 3 = 2 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state3.registers 4 = 0 by
          simp [state3, state2, state1, hindex], if_pos rfl]
        rw [show 2 = 1 + 1 by omega]
        rw [run_copy_instruction (value := head)
          (by rfl) rfl (by simp [state3, state2, head]) hheadBits]
        change
          runNPOracleProgram encodedListLookupProgram maximumBits 1
              resultState =
            some head
        exact run_halt_instruction (by rfl) rfl
          (by simp [resultState]) hheadBits
  | succ index inductionHypothesis =>
      by_cases hcodeZero : code = 0
      · rw [hcodeZero]
        exact run_encodedListLookupLoop_zero (index + 1) fallback
          maximumBits state hpc (by simpa [hcodeZero] using hcode)
          hfallback hfallbackBits
      · let cellCode := code.pred
        let head := (Nat.unpair cellCode).1
        let tail := (Nat.unpair cellCode).2
        let state1 := (state.write 2 cellCode).jump 6
        let state2 := (state1.write 6 head).jump 7
        let state3 := (state2.write 7 tail).jump 8
        let state4 := (state3.write 4 index).jump 10
        let nextState := (state4.write 2 tail).jump 4
        have hcellBits :
            natBitLength cellCode ≤ maximumBits :=
          (decrement_bits_le code).trans hcodeBits
        have hheadBits :
            natBitLength head ≤ maximumBits :=
          (natBitLength_mono (Nat.unpair_left_le cellCode)).trans
            hcellBits
        have htailBits :
            natBitLength tail ≤ maximumBits :=
          (natBitLength_mono (Nat.unpair_right_le cellCode)).trans
            hcellBits
        have hindexPredBits :
            natBitLength index ≤ maximumBits :=
          (decrement_bits_le (index + 1)).trans <| by
            simpa only [Nat.succ_eq_add_one] using hindexBits
        rw [encodedListLookupLoopFuel, if_neg hcodeZero]
        rw [show
          7 + encodedListLookupLoopFuel tail index =
            (6 + encodedListLookupLoopFuel tail index) + 1 by omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hcode, if_neg hcodeZero]
        change
          runNPOracleProgram encodedListLookupProgram maximumBits
              (6 + encodedListLookupLoopFuel tail index)
              (state.jump 5) =
            some (encodedListGetD code (index + 1) fallback)
        rw [show
          6 + encodedListLookupLoopFuel tail index =
            (5 + encodedListLookupLoopFuel tail index) + 1 by omega]
        rw [run_decrement_instruction (value := cellCode)
          (by rfl) rfl (by simp [hcode, cellCode]) hcellBits]
        change
          runNPOracleProgram encodedListLookupProgram maximumBits
              (5 + encodedListLookupLoopFuel tail index) state1 =
            some (encodedListGetD code (index + 1) fallback)
        rw [show
          5 + encodedListLookupLoopFuel tail index =
            (4 + encodedListLookupLoopFuel tail index) + 1 by omega]
        rw [run_unpairLeft_instruction (value := head)
          (by rfl) rfl (by simp [state1, cellCode, head]) hheadBits]
        change
          runNPOracleProgram encodedListLookupProgram maximumBits
              (4 + encodedListLookupLoopFuel tail index) state2 =
            some (encodedListGetD code (index + 1) fallback)
        rw [show
          4 + encodedListLookupLoopFuel tail index =
            (3 + encodedListLookupLoopFuel tail index) + 1 by omega]
        rw [run_unpairRight_instruction (value := tail)
          (by rfl) rfl (by simp [state2, state1, cellCode, tail])
          htailBits]
        change
          runNPOracleProgram encodedListLookupProgram maximumBits
              (3 + encodedListLookupLoopFuel tail index) state3 =
            some (encodedListGetD code (index + 1) fallback)
        rw [show
          3 + encodedListLookupLoopFuel tail index =
            (2 + encodedListLookupLoopFuel tail index) + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state3.registers 4 = index + 1 by
          simp [state3, state2, state1, hindex], if_neg (by omega)]
        rw [show
          2 + encodedListLookupLoopFuel tail index =
            (1 + encodedListLookupLoopFuel tail index) + 1 by omega]
        rw [run_decrement_instruction (value := index)
          (by rfl) rfl
          (by simp [state3, state2, state1, hindex])
          hindexPredBits]
        change
          runNPOracleProgram encodedListLookupProgram maximumBits
              (1 + encodedListLookupLoopFuel tail index) state4 =
            some (encodedListGetD code (index + 1) fallback)
        rw [show
          1 + encodedListLookupLoopFuel tail index =
            encodedListLookupLoopFuel tail index + 1 by omega]
        rw [run_copy_instruction (value := tail)
          (by rfl) rfl (by simp [state4, state3]) htailBits]
        change
          runNPOracleProgram encodedListLookupProgram maximumBits
              (encodedListLookupLoopFuel tail index) nextState =
            some (encodedListGetD code (index + 1) fallback)
        rw [inductionHypothesis tail nextState rfl
          (by simp [nextState])
          (by simp [nextState, state4])
          (by simp [nextState, state4, state3, state2, state1,
            hfallback])
          htailBits hindexPredBits]
        rw [encodedListGetD, if_neg hcodeZero]

theorem run_encodedListLookupProgram
    (inputLength code index fallback : ℕ) :
    runNPOracleProgram encodedListLookupProgram
        (encodedListLookupBits code index fallback)
        (encodedListLookupFuel code index)
        (initialNPOracleState inputLength
          (encodedListLookupInput code index fallback)) =
      some (encodedListGetD code index fallback) := by
  let request := encodedListLookupInput code index fallback
  let fields := Nat.pair index fallback
  let maximumBits := encodedListLookupBits code index fallback
  have hrequestBits :
      natBitLength request ≤ maximumBits := by
    rfl
  have hcodeBits :
      natBitLength code ≤ maximumBits :=
    (natBitLength_mono <| by
      simpa only [request, encodedListLookupInput] using
        Nat.left_le_pair code fields).trans hrequestBits
  have hfieldsBits :
      natBitLength fields ≤ maximumBits :=
    (natBitLength_mono <| by
      simpa only [request, encodedListLookupInput] using
        Nat.right_le_pair code fields).trans hrequestBits
  have hindexBits :
      natBitLength index ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair index fallback)).trans
      hfieldsBits
  have hfallbackBits :
      natBitLength fallback ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair index fallback)).trans
      hfieldsBits
  rw [show encodedListLookupFuel code index =
      (3 + encodedListLookupLoopFuel code index) + 1 by
    unfold encodedListLookupFuel
    omega]
  rw [run_unpairLeft_instruction (value := code)
    (by rfl) rfl
    (by simp [initialNPOracleState, encodedListLookupInput])
    hcodeBits]
  rw [show
    3 + encodedListLookupLoopFuel code index =
      (2 + encodedListLookupLoopFuel code index) + 1 by omega]
  rw [run_unpairRight_instruction (value := fields)
    (by rfl) rfl
    (by simp [initialNPOracleState, encodedListLookupInput, fields])
    hfieldsBits]
  rw [show
    2 + encodedListLookupLoopFuel code index =
      (1 + encodedListLookupLoopFuel code index) + 1 by omega]
  rw [run_unpairLeft_instruction (value := index)
    (by rfl) rfl (by simp [fields]) hindexBits]
  rw [show
    1 + encodedListLookupLoopFuel code index =
      encodedListLookupLoopFuel code index + 1 by omega]
  rw [run_unpairRight_instruction (value := fallback)
    (by rfl) rfl (by simp [fields]) hfallbackBits]
  apply run_encodedListLookupLoop code index fallback maximumBits
  · rfl
  · simp
  · simp
  · simp
  · exact hcodeBits
  · exact hindexBits
  · exact hfallbackBits

@[simp] theorem run_encodedListLookupProgram_encode
    (inputLength : ℕ) (values : List ℕ) (index fallback : ℕ) :
    runNPOracleProgram encodedListLookupProgram
        (encodedListLookupBits (Encodable.encode values) index fallback)
        (encodedListLookupFuel (Encodable.encode values) index)
        (initialNPOracleState inputLength
          (encodedListLookupInput
            (Encodable.encode values) index fallback)) =
      some (values.getD index fallback) := by
  rw [run_encodedListLookupProgram, encodedListGetD_encode]

/-! ## Reused two-level lookup -/

/-- A nested lookup preserves the inner index and fallback through the first
lookup.  `preserveRightProgram` then hands the resulting request directly to
the same lookup program; no second traversal implementation is introduced. -/
def encodedNestedListLookupInput
    (code outerIndex innerIndex fallback : ℕ) : ℕ :=
  Nat.pair
    (encodedListLookupInput code outerIndex 0)
    (Nat.pair innerIndex fallback)

def encodedNestedListGetD
    (code outerIndex innerIndex fallback : ℕ) : ℕ :=
  encodedListGetD
    (encodedListGetD code outerIndex 0) innerIndex fallback

def encodedNestedListLookupProgram : NPOracleProgram :=
  linkPrograms
    (preserveRightProgram encodedListLookupProgram)
    encodedListLookupProgram

@[simp] theorem encodedNestedListLookupProgram_oracleFree :
    OracleFree encodedNestedListLookupProgram := by
  exact oracleFree_linkPrograms
    (preserveRightProgram_oracleFree encodedListLookupProgram
      encodedListLookupProgram_oracleFree)
    encodedListLookupProgram_oracleFree

def encodedNestedListLookupFuel
    (code outerIndex innerIndex : ℕ) : ℕ :=
  let innerCode := encodedListGetD code outerIndex 0
  linkFuel encodedListLookupProgram
    (preserveRightFuel (encodedListLookupFuel code outerIndex))
    (encodedListLookupFuel innerCode innerIndex)

theorem encodedNestedListLookupFuel_le
    (code outerIndex innerIndex : ℕ) :
    encodedNestedListLookupFuel code outerIndex innerIndex ≤
      7 * (outerIndex + innerIndex) + 50 := by
  rw [encodedNestedListLookupFuel, linkFuel_exact]
  have houter := encodedListLookupFuel_le code outerIndex
  have hinner := encodedListLookupFuel_le
    (encodedListGetD code outerIndex 0) innerIndex
  norm_num [PreserveRightProgram.preserveRightFuel,
    programRegisterSpan, instructionRegisterSpan,
    instructionRegisters, encodedListLookupProgram] at *
  omega

def encodedNestedListLookupBits
    (inputLength code outerIndex innerIndex fallback : ℕ) : ℕ :=
  let firstInput := encodedListLookupInput code outerIndex 0
  let context := Nat.pair innerIndex fallback
  let innerCode := encodedListGetD code outerIndex 0
  max (natBitLength inputLength) <|
    max
      (preserveRightBits
        (encodedListLookupBits code outerIndex 0)
        firstInput context innerCode)
      (encodedListLookupBits innerCode innerIndex fallback)

/-- Exact two-level lookup in the canonical `List (List ℕ)` code.  The linked
interpreter runs the single list cursor twice and transports only its typed
request context between the calls. -/
theorem run_encodedNestedListLookupProgram
    (inputLength code outerIndex innerIndex fallback : ℕ) :
    runNPOracleProgram encodedNestedListLookupProgram
        (encodedNestedListLookupBits inputLength code outerIndex
          innerIndex fallback)
        (encodedNestedListLookupFuel code outerIndex innerIndex)
        (initialNPOracleState inputLength
          (encodedNestedListLookupInput code outerIndex
            innerIndex fallback)) =
      some
        (encodedNestedListGetD code outerIndex innerIndex fallback) := by
  let firstInput := encodedListLookupInput code outerIndex 0
  let context := Nat.pair innerIndex fallback
  let innerCode := encodedListGetD code outerIndex 0
  let firstBits := encodedListLookupBits code outerIndex 0
  let firstWrappedBits :=
    preserveRightBits firstBits firstInput context innerCode
  let secondBits :=
    encodedListLookupBits innerCode innerIndex fallback
  let maximumBits :=
    encodedNestedListLookupBits inputLength code outerIndex
      innerIndex fallback
  have hlengthBits :
      natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hfirstBits : firstWrappedBits ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsecondBits : secondBits ≤ maximumBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength inputLength).trans hlengthBits
  have hfirstAtOwnBits :
      runNPOracleProgram
          (preserveRightProgram encodedListLookupProgram)
          firstWrappedBits
          (preserveRightFuel
            (encodedListLookupFuel code outerIndex))
          (initialNPOracleState inputLength
            (Nat.pair firstInput context)) =
        some (Nat.pair innerCode context) := by
    exact run_preserveRightProgram encodedListLookupProgram
      inputLength firstBits
      (encodedListLookupFuel code outerIndex)
      firstInput context innerCode <| by
        simpa only [firstBits, firstInput, innerCode] using
          run_encodedListLookupProgram
            inputLength code outerIndex 0
  have hfirst :
      runNPOracleProgram
          (preserveRightProgram encodedListLookupProgram)
          maximumBits
          (preserveRightFuel
            (encodedListLookupFuel code outerIndex))
          (initialNPOracleState inputLength
            (Nat.pair firstInput context)) =
        some (Nat.pair innerCode context) :=
    run_bits_mono hfirstAtOwnBits hfirstBits
  have hsecondAtOwnBits :
      runNPOracleProgram encodedListLookupProgram secondBits
          (encodedListLookupFuel innerCode innerIndex)
          (initialNPOracleState inputLength
            (encodedListLookupInput innerCode innerIndex fallback)) =
        some (encodedListGetD innerCode innerIndex fallback) := by
    simpa only [secondBits] using
      run_encodedListLookupProgram
        inputLength innerCode innerIndex fallback
  have hsecond :
      runNPOracleProgram encodedListLookupProgram maximumBits
          (encodedListLookupFuel innerCode innerIndex)
          (initialNPOracleState inputLength
            (Nat.pair innerCode context)) =
        some (encodedListGetD innerCode innerIndex fallback) := by
    have hrun := run_bits_mono hsecondAtOwnBits hsecondBits
    simpa only [context, encodedListLookupInput] using hrun
  change
    runNPOracleProgram
        (linkPrograms
          (preserveRightProgram encodedListLookupProgram)
          encodedListLookupProgram)
        maximumBits
        (linkFuel encodedListLookupProgram
          (preserveRightFuel
            (encodedListLookupFuel code outerIndex))
          (encodedListLookupFuel innerCode innerIndex))
        (initialNPOracleState inputLength
          (Nat.pair firstInput context)) =
      some (encodedListGetD innerCode innerIndex fallback)
  exact run_linkPrograms hpositive hlengthBits hfirst hsecond

@[simp] theorem encodedNestedListGetD_encode
    (values : List (List ℕ)) (outerIndex innerIndex fallback : ℕ) :
    encodedNestedListGetD (Encodable.encode values)
        outerIndex innerIndex fallback =
      (values.getD outerIndex []).getD innerIndex fallback := by
  unfold encodedNestedListGetD
  rw [encodedListGetD_encodeValues]
  change
    encodedListGetD
        ((values.map Encodable.encode).getD
          outerIndex (Encodable.encode ([] : List ℕ)))
        innerIndex fallback =
      (values.getD outerIndex []).getD innerIndex fallback
  rw [List.getD_map, encodedListGetD_encode]

/-- The same result characterizes arbitrary external runner codes through the
total denumerable decoder used by `decodeThreeCNF`. -/
theorem encodedNestedListGetD_eq_decode
    (code outerIndex innerIndex fallback : ℕ) :
    encodedNestedListGetD code outerIndex innerIndex fallback =
      (((Encodable.decode code : Option (List (List ℕ))).getD []).getD
        outerIndex []).getD innerIndex fallback := by
  let values := Denumerable.ofNat (List (List ℕ)) code
  calc
    encodedNestedListGetD code outerIndex innerIndex fallback =
        encodedNestedListGetD (Encodable.encode values)
          outerIndex innerIndex fallback := by
            rw [Denumerable.encode_ofNat]
    _ = (values.getD outerIndex []).getD innerIndex fallback :=
      encodedNestedListGetD_encode values outerIndex innerIndex fallback
    _ = (((Encodable.decode code :
          Option (List (List ℕ))).getD []).getD outerIndex []).getD
            innerIndex fallback := by
      rw [Denumerable.decode_eq_ofNat]
      rfl

/-- Total pointwise bridge from the two machine traversals to the exact
`decodeThreeCNF` clause/literal selected by the structural compiler. -/
theorem decodeLiteral_encodedNestedListGetD
    (arity code clauseIndex : ℕ) (position : Fin 3)
    (harity : 0 < arity) :
    decodeLiteral harity
        (encodedNestedListGetD code clauseIndex position.val 0) =
      ((decodeThreeCNF arity code).clauses.getD clauseIndex
        (fun _ => decodeLiteral harity 0)) position := by
  let raw :=
    (Encodable.decode code : Option (List (List ℕ))).getD []
  rw [encodedNestedListGetD_eq_decode]
  unfold decodeThreeCNF
  rw [dif_pos harity]
  change
    decodeLiteral harity
        ((raw.getD clauseIndex []).getD position.val 0) =
      ((raw.map fun clause index =>
        decodeLiteral harity (clause.getD index.val 0)).getD
          clauseIndex (fun _ => decodeLiteral harity 0)) position
  exact (congrFun
    (List.getD_map (l := raw) (d := [])
      (n := clauseIndex) (fun clause index =>
        decodeLiteral harity (clause.getD index.val 0)))
    position).symm

@[simp] theorem run_encodedNestedListLookupProgram_encode
    (inputLength : ℕ) (values : List (List ℕ))
    (outerIndex innerIndex fallback : ℕ) :
    runNPOracleProgram encodedNestedListLookupProgram
        (encodedNestedListLookupBits inputLength
          (Encodable.encode values) outerIndex innerIndex fallback)
        (encodedNestedListLookupFuel
          (Encodable.encode values) outerIndex innerIndex)
        (initialNPOracleState inputLength
          (encodedNestedListLookupInput
            (Encodable.encode values) outerIndex innerIndex fallback)) =
      some ((values.getD outerIndex []).getD innerIndex fallback) := by
  rw [run_encodedNestedListLookupProgram,
    encodedNestedListGetD_encode]

end NearCubicWires.CanonicalEncodedListLookupProgram
