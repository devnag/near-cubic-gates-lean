import Proof.Foundations.CanonicalBinaryProgram

/-!
# Fixed length of Lean's canonical encoded list spine

Decision formulas arrive as arbitrary natural codes for `List (List ℕ)`.
Before a structural emitter can enumerate their clauses, it needs the exact
decoded outer-list length.  This fixed fold follows the same successor/pairing
spine as `Encodable.decode`; no decoded host list crosses the machine boundary.
-/

namespace NearCubicWires.CanonicalEncodedListLengthProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-- Total structural length of a zero/successor list code. -/
def encodedListLength : ℕ → ℕ
  | 0 => 0
  | code + 1 =>
      1 + encodedListLength (Nat.unpair code).2
termination_by code => code
decreasing_by
  exact Nat.lt_succ_of_le (Nat.unpair_right_le code)

theorem encodedListLength_eq_decode (code : ℕ) :
    encodedListLength code =
      ((Encodable.decode code : Option (List ℕ)).getD []).length := by
  induction code using encodedListLength.induct with
  | case1 =>
      simp [encodedListLength]
  | case2 spine inductionHypothesis =>
      simp [encodedListLength, inductionHypothesis, Nat.add_comm]

theorem encodedListLength_eq_decode_nested (code : ℕ) :
    encodedListLength code =
      ((Encodable.decode code : Option (List (List ℕ))).getD []).length := by
  induction code using encodedListLength.induct with
  | case1 =>
      simp [encodedListLength]
  | case2 spine inductionHypothesis =>
      simp [encodedListLength, inductionHypothesis, Nat.add_comm]

theorem encodedListLength_eq_decodeThreeCNF_clauses
    (arity code : ℕ) (harity : 0 < arity) :
    encodedListLength code = (decodeThreeCNF arity code).clauses.length := by
  unfold decodeThreeCNF
  rw [dif_pos harity]
  simp [encodedListLength_eq_decode_nested]

/-- Register ABI: `r0` is the current encoded cursor and then the result;
`r2` is the accumulated length, and `r3` is the next tail code. -/
def encodedListLengthProgram : NPOracleProgram :=
  [ .set 2 0 1
  , .branchZero 0 6 2
  , .decrement 0 3
  , .unpairRight 0 3 4
  , .copy 3 0 5
  , .increment 2 1
  , .copy 2 0 7
  , .halt 0
  ]

@[simp] theorem encodedListLengthProgram_oracleFree :
    OracleFree encodedListLengthProgram := by
  rfl

def encodedListLengthLoopFuel (code : ℕ) : ℕ :=
  5 * encodedListLength code + 3

def encodedListLengthFuel (code : ℕ) : ℕ :=
  encodedListLengthLoopFuel code + 1

def encodedListLengthBits (code : ℕ) : ℕ :=
  natBitLength (max code (encodedListLength code))

private theorem run_encodedListLengthLoop
    (code accumulator maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 1)
    (hcode : state.registers 0 = code)
    (haccumulator : state.registers 2 = accumulator)
    (hcodeBits : natBitLength code ≤ maximumBits)
    (hresultBits :
      natBitLength (accumulator + encodedListLength code) ≤
        maximumBits) :
    runNPOracleProgram encodedListLengthProgram maximumBits
        (encodedListLengthLoopFuel code) state =
      some (accumulator + encodedListLength code) := by
  induction code using encodedListLength.induct generalizing accumulator state with
  | case1 =>
      have haccumulatorBits :
          natBitLength accumulator ≤ maximumBits := by
        simpa [encodedListLength] using hresultBits
      rw [encodedListLengthLoopFuel, encodedListLength]
      rw [show 5 * 0 + 3 = 2 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hcode, if_pos rfl]
      rw [show 2 = 1 + 1 by omega]
      rw [run_copy_instruction (value := accumulator)
        (by rfl) rfl
        (by simp [NPOracleState.jump, haccumulator])
        haccumulatorBits]
      rw [run_halt_instruction (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        haccumulatorBits]
      simp
  | case2 spine inductionHypothesis =>
      let tail := (Nat.unpair spine).2
      let state1 := ((state.jump 2).write 0 spine).jump 3
      let state2 := (state1.write 3 tail).jump 4
      let state3 := (state2.write 0 tail).jump 5
      let nextState := (state3.write 2 (accumulator + 1)).jump 1
      have hspineBits :
          natBitLength spine ≤ maximumBits :=
        (decrement_bits_le (spine + 1)).trans <| by
          simpa only [Nat.succ_eq_add_one] using hcodeBits
      have htailBits :
          natBitLength tail ≤ maximumBits :=
        (natBitLength_mono (Nat.unpair_right_le spine)).trans
          hspineBits
      have hnextResult :
          accumulator + encodedListLength (spine + 1) =
            accumulator + 1 + encodedListLength tail := by
        simp [encodedListLength, tail]
        omega
      have haccumulatorIncBits :
          natBitLength (accumulator + 1) ≤ maximumBits := by
        apply (natBitLength_mono ?_).trans hresultBits
        rw [hnextResult]
        omega
      have hnextResultBits :
          natBitLength
              (accumulator + 1 + encodedListLength tail) ≤
            maximumBits := by
        rw [← hnextResult]
        exact hresultBits
      rw [encodedListLengthLoopFuel, encodedListLength]
      rw [show
        5 * (1 + encodedListLength tail) + 3 =
          (4 + encodedListLengthLoopFuel tail) + 1 by
            unfold encodedListLengthLoopFuel
            omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hcode, if_neg (Nat.succ_ne_zero spine)]
      rw [show
        4 + encodedListLengthLoopFuel tail =
          (3 + encodedListLengthLoopFuel tail) + 1 by omega]
      rw [run_decrement_instruction (value := spine)
        (by rfl) rfl
        (by simp [NPOracleState.jump, hcode])
        hspineBits]
      change
        runNPOracleProgram encodedListLengthProgram maximumBits
            (3 + encodedListLengthLoopFuel tail) state1 =
          some (accumulator + (1 + encodedListLength tail))
      rw [show
        3 + encodedListLengthLoopFuel tail =
          (2 + encodedListLengthLoopFuel tail) + 1 by omega]
      rw [run_unpairRight_instruction (value := tail)
        (by rfl) rfl
        (by simp [state1, tail])
        htailBits]
      change
        runNPOracleProgram encodedListLengthProgram maximumBits
            (2 + encodedListLengthLoopFuel tail) state2 =
          some (accumulator + (1 + encodedListLength tail))
      rw [show
        2 + encodedListLengthLoopFuel tail =
          (1 + encodedListLengthLoopFuel tail) + 1 by omega]
      rw [run_copy_instruction (value := tail)
        (by rfl) rfl
        (by simp [state2, state1, tail])
        htailBits]
      change
        runNPOracleProgram encodedListLengthProgram maximumBits
            (1 + encodedListLengthLoopFuel tail) state3 =
          some (accumulator + (1 + encodedListLength tail))
      rw [show
        1 + encodedListLengthLoopFuel tail =
          encodedListLengthLoopFuel tail + 1 by omega]
      rw [run_increment_instruction (value := accumulator + 1)
        (by rfl) rfl
        (by simp [state3, state2, state1, haccumulator])
        haccumulatorIncBits]
      change
        runNPOracleProgram encodedListLengthProgram maximumBits
            (encodedListLengthLoopFuel tail) nextState =
          some (accumulator + (1 + encodedListLength tail))
      rw [inductionHypothesis (accumulator + 1) nextState
        rfl
        (by simp [nextState, state3, tail])
        (by simp [nextState])
        htailBits hnextResultBits]
      simp [tail, Nat.add_assoc]

theorem run_encodedListLengthProgram
    (inputLength code : ℕ) :
    runNPOracleProgram encodedListLengthProgram
        (encodedListLengthBits code)
        (encodedListLengthFuel code)
        (initialNPOracleState inputLength code) =
      some (encodedListLength code) := by
  let maximumBits := encodedListLengthBits code
  have hcodeBits :
      natBitLength code ≤ maximumBits := by
    unfold maximumBits encodedListLengthBits
    exact natBitLength_mono (Nat.le_max_left _ _)
  have hlengthBits :
      natBitLength (encodedListLength code) ≤ maximumBits := by
    unfold maximumBits encodedListLengthBits
    exact natBitLength_mono (Nat.le_max_right _ _)
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le code)).trans hcodeBits
  rw [show encodedListLengthFuel code =
      encodedListLengthLoopFuel code + 1 by
    rfl]
  rw [run_set_instruction (value := 0)
    (by rfl) rfl hzeroBits]
  simpa only [Nat.zero_add] using
    run_encodedListLengthLoop code 0 maximumBits
      (((initialNPOracleState inputLength code).write 2 0).jump 1)
      rfl
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump])
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump])
      hcodeBits
      (by simpa using hlengthBits)

theorem run_encodedListLengthProgram_eq_decode
    (inputLength code : ℕ) :
    runNPOracleProgram encodedListLengthProgram
        (encodedListLengthBits code)
        (encodedListLengthFuel code)
        (initialNPOracleState inputLength code) =
      some (((Encodable.decode code : Option (List ℕ)).getD []).length) := by
  rw [run_encodedListLengthProgram, encodedListLength_eq_decode]

theorem run_encodedListLengthProgram_eq_decodeThreeCNF_clauses
    (inputLength arity code : ℕ) (harity : 0 < arity) :
    runNPOracleProgram encodedListLengthProgram
        (encodedListLengthBits code)
        (encodedListLengthFuel code)
        (initialNPOracleState inputLength code) =
      some (decodeThreeCNF arity code).clauses.length := by
  rw [run_encodedListLengthProgram,
    encodedListLength_eq_decodeThreeCNF_clauses arity code harity]

end NearCubicWires.CanonicalEncodedListLengthProgram
