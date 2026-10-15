import Proof.Foundations.CanonicalBinaryProgram

/-!
# Fixed native-natural remainder

External literal codes use `index % arity`.  This module implements that exact
positive-denominator operation with the existing bounded register machine.
The controller performs explicit chunked subtraction, retaining the current
chunk offset as the remainder; it adds no arithmetic opcode or host callback.
-/

namespace NearCubicWires.CanonicalNativeModProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

def nativeModInput (numerator denominator : ℕ) : ℕ :=
  Nat.pair numerator denominator

/-- Register ABI:

* `r0`: paired request, then result;
* `r2`: remaining positions in the current denominator-sized chunk;
* `r3`: positions consumed in that chunk;
* `r4`: remaining numerator;
* `r5`: positive denominator.

The cursor-zero branch resets `r2 + r3 = denominator` before testing whether
the numerator is exhausted.  This ordering makes exact multiples return zero.
-/
def nativeModProgram : NPOracleProgram :=
  [ .unpairLeft 0 4 1
  , .unpairRight 0 5 2
  , .set 3 0 3
  , .copy 5 2 4
  , .branchZero 2 5 7
  , .set 3 0 6
  , .copy 5 2 7
  , .branchZero 4 11 8
  , .decrement 4 9
  , .decrement 2 10
  , .increment 3 4
  , .copy 3 0 12
  , .halt 0
  ]

@[simp] theorem nativeModProgram_oracleFree :
    OracleFree nativeModProgram := by
  rfl

/-- Exact instruction count from the loop header.  Only recursive branches
consume one unit of numerator, so the definition is structurally terminating
even at the cursor-reset boundary. -/
def nativeModLoopFuel (denominator cursor : ℕ) : ℕ → ℕ
  | 0 =>
      if cursor = 0 then 6 else 4
  | numerator + 1 =>
      if cursor = 0 then
        7 + nativeModLoopFuel denominator denominator.pred numerator
      else
        5 + nativeModLoopFuel denominator cursor.pred numerator

def nativeModFuel (numerator denominator : ℕ) : ℕ :=
  4 + nativeModLoopFuel denominator denominator numerator

def nativeModBits (numerator denominator : ℕ) : ℕ :=
  natBitLength (nativeModInput numerator denominator)

/-- The explicit clock exposes the cost of the minimal instruction set: the
current implementation is linear in the native numerator, never a hidden
unit-cost remainder operation. -/
theorem nativeModLoopFuel_le
    (denominator cursor numerator : ℕ) :
    nativeModLoopFuel denominator cursor numerator ≤
      7 * numerator + 6 := by
  induction numerator generalizing cursor with
  | zero =>
      simp [nativeModLoopFuel]
      split <;> omega
  | succ numerator inductionHypothesis =>
      simp only [nativeModLoopFuel]
      split
      · have hbound := inductionHypothesis denominator.pred
        omega
      · have hbound := inductionHypothesis cursor.pred
        omega

theorem nativeModFuel_le (numerator denominator : ℕ) :
    nativeModFuel numerator denominator ≤ 7 * numerator + 10 := by
  unfold nativeModFuel
  have hbound :=
    Nat.add_le_add_left
      (nativeModLoopFuel_le denominator denominator numerator) 4
  omega

private theorem zero_bits_le_of_denominator
    (denominator maximumBits : ℕ)
    (hdenominatorBits : natBitLength denominator ≤ maximumBits) :
    natBitLength 0 ≤ maximumBits :=
  (natBitLength_mono (Nat.zero_le denominator)).trans hdenominatorBits

private theorem one_bits_le_of_denominator
    (denominator maximumBits : ℕ)
    (hpositive : 0 < denominator)
    (hdenominatorBits : natBitLength denominator ≤ maximumBits) :
    natBitLength 1 ≤ maximumBits :=
  (natBitLength_mono hpositive).trans hdenominatorBits

private theorem run_nativeModLoop
    (denominator numerator cursor accumulator maximumBits : ℕ)
    (state : NPOracleState)
    (hpositive : 0 < denominator)
    (hpc : state.pc = 4)
    (hnumerator : state.registers 4 = numerator)
    (hdenominator : state.registers 5 = denominator)
    (hcursor : state.registers 2 = cursor)
    (haccumulator : state.registers 3 = accumulator)
    (hchunk : cursor + accumulator = denominator)
    (hsumBits :
      natBitLength (numerator + accumulator) ≤ maximumBits)
    (hdenominatorBits :
      natBitLength denominator ≤ maximumBits) :
    runNPOracleProgram nativeModProgram maximumBits
        (nativeModLoopFuel denominator cursor numerator) state =
      some ((numerator + accumulator) % denominator) := by
  induction numerator generalizing cursor accumulator state with
  | zero =>
      by_cases hcursorZero : cursor = 0
      · have haccumulatorEq : accumulator = denominator := by
          omega
        have hzeroBits :=
          zero_bits_le_of_denominator denominator maximumBits
            hdenominatorBits
        rw [nativeModLoopFuel, if_pos hcursorZero]
        rw [show 6 = 5 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hcursor, if_pos hcursorZero]
        rw [show 5 = 4 + 1 by omega]
        rw [run_set_instruction (value := 0)
          (by rfl) rfl hzeroBits]
        rw [show 4 = 3 + 1 by omega]
        rw [run_copy_instruction (value := denominator)
          (by rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump,
            hdenominator])
          hdenominatorBits]
        rw [show 3 = 2 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show
          (((((state.jump 5).write 3 0).jump 6).write
            2 denominator).jump 7).registers 4 = 0 by
              simp [NPOracleState.write, NPOracleState.jump,
                hnumerator],
          if_pos rfl]
        rw [show 2 = 1 + 1 by omega]
        rw [run_copy_instruction (value := 0)
          (by rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump])
          hzeroBits]
        rw [run_halt_instruction (by rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump])
          hzeroBits]
        simp [haccumulatorEq, Nat.mod_self]
      · have hcursorPositive : 0 < cursor :=
          Nat.pos_of_ne_zero hcursorZero
        have haccumulatorLt : accumulator < denominator := by
          omega
        have haccumulatorBits :
            natBitLength accumulator ≤ maximumBits :=
          (natBitLength_mono (Nat.le_of_lt haccumulatorLt)).trans
            hdenominatorBits
        rw [nativeModLoopFuel, if_neg hcursorZero]
        rw [show 4 = 3 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hcursor, if_neg hcursorZero]
        rw [show 3 = 2 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show (state.jump 7).registers 4 = 0 by
          simpa [NPOracleState.jump] using hnumerator, if_pos rfl]
        rw [show 2 = 1 + 1 by omega]
        rw [run_copy_instruction (value := accumulator)
          (by rfl) rfl
          (by simp [NPOracleState.jump, haccumulator])
          haccumulatorBits]
        rw [run_halt_instruction (by rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump])
          haccumulatorBits]
        rw [Nat.zero_add, Nat.mod_eq_of_lt haccumulatorLt]
  | succ numerator inductionHypothesis =>
      have hnumeratorPredBits :
          natBitLength numerator ≤ maximumBits := by
        apply (natBitLength_mono ?_).trans hsumBits
        omega
      by_cases hcursorZero : cursor = 0
      · have haccumulatorEq : accumulator = denominator := by
          omega
        let state1 := (state.write 3 0).jump 6
        let state2 := (state1.write 2 denominator).jump 7
        let state3 := (state2.write 4 numerator).jump 9
        let state4 := (state3.write 2 denominator.pred).jump 10
        let nextState := (state4.write 3 1).jump 4
        have hzeroBits :=
          zero_bits_le_of_denominator denominator maximumBits
            hdenominatorBits
        have honeBits :=
          one_bits_le_of_denominator denominator maximumBits
            hpositive hdenominatorBits
        have hcursorPredBits :
            natBitLength denominator.pred ≤ maximumBits :=
          (decrement_bits_le denominator).trans hdenominatorBits
        have hnextChunk :
            denominator.pred + 1 = denominator := by
          simpa [Nat.succ_eq_add_one] using
            Nat.succ_pred_eq_of_pos hpositive
        have hnextSumBits :
            natBitLength (numerator + 1) ≤ maximumBits := by
          exact (natBitLength_mono (by omega)).trans hsumBits
        rw [nativeModLoopFuel, if_pos hcursorZero]
        rw [show
          7 + nativeModLoopFuel denominator denominator.pred numerator =
            (6 + nativeModLoopFuel denominator denominator.pred numerator) +
              1 by omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hcursor, if_pos hcursorZero]
        rw [show
          6 + nativeModLoopFuel denominator denominator.pred numerator =
            (5 + nativeModLoopFuel denominator denominator.pred numerator) +
              1 by omega]
        rw [run_set_instruction (value := 0)
          (by rfl) rfl hzeroBits]
        change
          runNPOracleProgram nativeModProgram maximumBits
              (5 + nativeModLoopFuel denominator denominator.pred numerator)
              state1 =
            some (((numerator + 1) + accumulator) % denominator)
        rw [show
          5 + nativeModLoopFuel denominator denominator.pred numerator =
            (4 + nativeModLoopFuel denominator denominator.pred numerator) +
              1 by omega]
        rw [run_copy_instruction (value := denominator)
          (by rfl) rfl
          (by simp [state1, hdenominator]) hdenominatorBits]
        change
          runNPOracleProgram nativeModProgram maximumBits
              (4 + nativeModLoopFuel denominator denominator.pred numerator)
              state2 =
            some (((numerator + 1) + accumulator) % denominator)
        rw [show
          4 + nativeModLoopFuel denominator denominator.pred numerator =
            (3 + nativeModLoopFuel denominator denominator.pred numerator) +
              1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state2.registers 4 = numerator + 1 by
          simp [state2, state1, hnumerator], if_neg (by omega)]
        rw [show
          3 + nativeModLoopFuel denominator denominator.pred numerator =
            (2 + nativeModLoopFuel denominator denominator.pred numerator) +
              1 by omega]
        rw [run_decrement_instruction (value := numerator)
          (by rfl) rfl
          (by simp [state2, state1, hnumerator])
          hnumeratorPredBits]
        change
          runNPOracleProgram nativeModProgram maximumBits
              (2 + nativeModLoopFuel denominator denominator.pred numerator)
              state3 =
            some (((numerator + 1) + accumulator) % denominator)
        rw [show
          2 + nativeModLoopFuel denominator denominator.pred numerator =
            (1 + nativeModLoopFuel denominator denominator.pred numerator) +
              1 by omega]
        rw [run_decrement_instruction (value := denominator.pred)
          (by rfl) rfl
          (by simp [state3, state2, state1])
          hcursorPredBits]
        change
          runNPOracleProgram nativeModProgram maximumBits
              (1 + nativeModLoopFuel denominator denominator.pred numerator)
              state4 =
            some (((numerator + 1) + accumulator) % denominator)
        rw [show
          1 + nativeModLoopFuel denominator denominator.pred numerator =
            nativeModLoopFuel denominator denominator.pred numerator + 1 by
              omega]
        rw [run_increment_instruction (value := 1)
          (by rfl) rfl
          (by simp [state4, state3, state2, state1])
          honeBits]
        change
          runNPOracleProgram nativeModProgram maximumBits
              (nativeModLoopFuel denominator denominator.pred numerator)
              nextState =
            some (((numerator + 1) + accumulator) % denominator)
        rw [inductionHypothesis denominator.pred 1 nextState
          rfl
          (by simp [nextState, state4, state3])
          (by simp [nextState, state4, state3, state2, state1,
            hdenominator])
          (by simp [nextState, state4])
          (by simp [nextState])
          hnextChunk hnextSumBits]
        rw [haccumulatorEq]
        simp [Nat.add_mod]
      · have hcursorPositive : 0 < cursor :=
          Nat.pos_of_ne_zero hcursorZero
        let state1 := (state.write 4 numerator).jump 9
        let state2 := (state1.write 2 cursor.pred).jump 10
        let nextState := (state2.write 3 (accumulator + 1)).jump 4
        have hcursorPredBits :
            natBitLength cursor.pred ≤ maximumBits := by
          apply (decrement_bits_le cursor).trans
          apply (natBitLength_mono ?_).trans hdenominatorBits
          omega
        have haccumulatorIncBits :
            natBitLength (accumulator + 1) ≤ maximumBits := by
          apply (natBitLength_mono ?_).trans hsumBits
          omega
        have hnextChunk :
            cursor.pred + (accumulator + 1) = denominator := by
          have hcursorPred :
              cursor.pred + 1 = cursor :=
            by
              simpa [Nat.succ_eq_add_one] using
                Nat.succ_pred_eq_of_pos hcursorPositive
          omega
        have hnextSum :
            numerator + (accumulator + 1) =
              (numerator + 1) + accumulator := by
          omega
        rw [nativeModLoopFuel, if_neg hcursorZero]
        rw [show
          5 + nativeModLoopFuel denominator cursor.pred numerator =
            (4 + nativeModLoopFuel denominator cursor.pred numerator) + 1 by
              omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hcursor, if_neg hcursorZero]
        rw [show
          4 + nativeModLoopFuel denominator cursor.pred numerator =
            (3 + nativeModLoopFuel denominator cursor.pred numerator) + 1 by
              omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show (state.jump 7).registers 4 = numerator + 1 by
          simpa [NPOracleState.jump] using hnumerator, if_neg (by omega)]
        rw [show
          3 + nativeModLoopFuel denominator cursor.pred numerator =
            (2 + nativeModLoopFuel denominator cursor.pred numerator) + 1 by
              omega]
        rw [run_decrement_instruction (value := numerator)
          (by rfl) rfl
          (by simp [NPOracleState.jump, hnumerator])
          hnumeratorPredBits]
        change
          runNPOracleProgram nativeModProgram maximumBits
              (2 + nativeModLoopFuel denominator cursor.pred numerator)
              state1 =
            some (((numerator + 1) + accumulator) % denominator)
        rw [show
          2 + nativeModLoopFuel denominator cursor.pred numerator =
            (1 + nativeModLoopFuel denominator cursor.pred numerator) + 1 by
              omega]
        rw [run_decrement_instruction (value := cursor.pred)
          (by rfl) rfl
          (by simp [state1, hcursor])
          hcursorPredBits]
        change
          runNPOracleProgram nativeModProgram maximumBits
              (1 + nativeModLoopFuel denominator cursor.pred numerator)
              state2 =
            some (((numerator + 1) + accumulator) % denominator)
        rw [show
          1 + nativeModLoopFuel denominator cursor.pred numerator =
            nativeModLoopFuel denominator cursor.pred numerator + 1 by omega]
        rw [run_increment_instruction (value := accumulator + 1)
          (by rfl) rfl
          (by simp [state2, state1, haccumulator])
          haccumulatorIncBits]
        change
          runNPOracleProgram nativeModProgram maximumBits
              (nativeModLoopFuel denominator cursor.pred numerator)
              nextState =
            some (((numerator + 1) + accumulator) % denominator)
        rw [inductionHypothesis cursor.pred (accumulator + 1) nextState
          rfl
          (by simp [nextState, state2, state1])
          (by simp [nextState, state2, state1, hdenominator])
          (by simp [nextState, state2])
          (by simp [nextState])
          hnextChunk
          (by rw [hnextSum]; exact hsumBits)]
        rw [hnextSum]

/-- Exact remainder execution for the positive denominator used by literal
decoding. -/
theorem run_nativeModProgram
    (inputLength numerator denominator : ℕ)
    (hpositive : 0 < denominator) :
    runNPOracleProgram nativeModProgram
        (nativeModBits numerator denominator)
        (nativeModFuel numerator denominator)
        (initialNPOracleState inputLength
          (nativeModInput numerator denominator)) =
      some (numerator % denominator) := by
  let request := nativeModInput numerator denominator
  let maximumBits := nativeModBits numerator denominator
  have hrequestBits :
      natBitLength request ≤ maximumBits := by
    rfl
  have hnumeratorBits :
      natBitLength numerator ≤ maximumBits :=
    (natBitLength_mono <| by
      simpa only [request, nativeModInput] using
        Nat.left_le_pair numerator denominator).trans hrequestBits
  have hdenominatorBits :
      natBitLength denominator ≤ maximumBits :=
    (natBitLength_mono <| by
      simpa only [request, nativeModInput] using
        Nat.right_le_pair numerator denominator).trans hrequestBits
  have hzeroBits :=
    zero_bits_le_of_denominator denominator maximumBits
      hdenominatorBits
  rw [show nativeModFuel numerator denominator =
      (3 + nativeModLoopFuel denominator denominator numerator) + 1 by
    unfold nativeModFuel
    omega]
  rw [run_unpairLeft_instruction (value := numerator)
    (by rfl) rfl
    (by simp [initialNPOracleState, nativeModInput])
    hnumeratorBits]
  rw [show
    3 + nativeModLoopFuel denominator denominator numerator =
      (2 + nativeModLoopFuel denominator denominator numerator) + 1 by omega]
  rw [run_unpairRight_instruction (value := denominator)
    (by rfl) rfl
    (by simp [initialNPOracleState, nativeModInput])
    hdenominatorBits]
  rw [show
    2 + nativeModLoopFuel denominator denominator numerator =
      (1 + nativeModLoopFuel denominator denominator numerator) + 1 by omega]
  rw [run_set_instruction (value := 0)
    (by rfl) rfl hzeroBits]
  rw [show
    1 + nativeModLoopFuel denominator denominator numerator =
      nativeModLoopFuel denominator denominator numerator + 1 by omega]
  rw [run_copy_instruction (value := denominator)
    (by rfl) rfl (by simp) hdenominatorBits]
  apply run_nativeModLoop denominator numerator denominator 0 maximumBits
  · exact hpositive
  · rfl
  · simp
  · simp
  · simp
  · simp
  · simp
  · simpa using hnumeratorBits
  · exact hdenominatorBits

end NearCubicWires.CanonicalNativeModProgram
