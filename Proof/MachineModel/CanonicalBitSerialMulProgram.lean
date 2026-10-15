import Proof.Foundations.CanonicalBinaryProgram

/-!
# Bit-serial natural multiplication

This module provides the fixed multiplication primitive used by executable
resource accounting.  It scans the multiplier in binary, so charged fuel is
linear in the multiplier's bit width rather than its numeric value.
-/

namespace NearCubicWires.CanonicalBitSerialMulProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

def bitSerialMulInput (left right : ℕ) : ℕ :=
  Nat.pair left right

/-!
Register ABI:

* `r0`: paired request, then accumulator/output;
* `r2`: current shifted multiplicand;
* `r3`: remaining multiplier;
* `r4`: immutable zero bit index;
* `r5`: current low bit.

The loop preserves `accumulator + multiplicand * remaining = left * right`.
The final redundant copy is intentional: it gives the back edge a dedicated
instruction and keeps every jump target within the fixed program.
-/
def bitSerialMulProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 0 0 3
  , .branchZero 3 11 4
  , .testBit 3 4 5 5
  , .branchZero 5 7 6
  , .add 0 2 0 7
  , .shiftRight 3 1 3 8
  , .branchZero 3 11 9
  , .shiftLeft 2 1 2 10
  , .copy 2 2 3
  , .halt 0
  ]

@[simp] theorem bitSerialMulProgram_oracleFree :
    OracleFree bitSerialMulProgram := by
  rfl

private theorem shiftRight_one_lt
    {value : ℕ} (hpositive : 0 < value) :
    value >>> 1 < value := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self hpositive (by norm_num)

private theorem shiftRight_decompose (value : ℕ) :
    value =
      2 * (value >>> 1) + (value.testBit 0).toNat := by
  calc
    value =
        Nat.bit (value.testBit 0) (value >>> 1) := by
      exact (Nat.bit_testBit_zero_shiftRight_one _).symm
    _ = 2 * (value >>> 1) + (value.testBit 0).toNat := by
      cases value.testBit 0 <;> simp [Nat.bit]

private theorem shiftLeft_one (value : ℕ) :
    Nat.shiftLeft value 1 = 2 * value := by
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

private theorem bits_of_nonzero {value : ℕ} (hvalue : value ≠ 0) :
    value.bits =
      value.testBit 0 :: (value >>> 1).bits := by
  calc
    value.bits =
        (Nat.bit (value.testBit 0) (value >>> 1)).bits := by
      rw [Nat.bit_testBit_zero_shiftRight_one]
    _ = value.testBit 0 :: (value >>> 1).bits := by
      apply Nat.bits_append_bit
      intro hshift
      have hbit :
          Nat.bit (value.testBit 0) (value >>> 1) ≠ 0 := by
        simpa only [Nat.bit_testBit_zero_shiftRight_one] using hvalue
      exact (Nat.bit_ne_zero_iff.mp hbit) hshift

def bitSerialMulLoopFuel (remaining : ℕ) : ℕ :=
  if hzero : remaining = 0 then
    2
  else
    let tail := remaining >>> 1
    let bit := (remaining.testBit 0).toNat
    if tail = 0 then
      6 + bit
    else
      7 + bit + bitSerialMulLoopFuel tail
termination_by remaining
decreasing_by
  exact shiftRight_one_lt (Nat.pos_of_ne_zero hzero)

def bitSerialMulFuel (right : ℕ) : ℕ :=
  3 + bitSerialMulLoopFuel right

/-- The exact charge is linear in the multiplier's canonical binary width. -/
theorem bitSerialMulLoopFuel_le (remaining : ℕ) :
    bitSerialMulLoopFuel remaining ≤
      2 + 8 * remaining.bits.length := by
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      by_cases hzero : remaining = 0
      · subst remaining
        simp [bitSerialMulLoopFuel]
      · have hpositive : 0 < remaining :=
          Nat.pos_of_ne_zero hzero
        let tail := remaining >>> 1
        have htailLt : tail < remaining :=
          shiftRight_one_lt hpositive
        have hbits :
            remaining.bits.length = tail.bits.length + 1 := by
          rw [bits_of_nonzero hzero]
          simp [tail]
        rw [bitSerialMulLoopFuel, dif_neg hzero]
        dsimp only
        change
          (if tail = 0 then
            6 + (remaining.testBit 0).toNat
          else
            7 + (remaining.testBit 0).toNat +
              bitSerialMulLoopFuel tail) ≤
            2 + 8 * remaining.bits.length
        have hbit : (remaining.testBit 0).toNat ≤ 1 := by
          cases remaining.testBit 0 <;> simp
        by_cases htailZero : tail = 0
        · rw [if_pos htailZero]
          rw [hbits]
          omega
        · rw [if_neg htailZero]
          have htailFuel := ih tail htailLt
          rw [hbits]
          omega

/-- Public charge bound, including the three ABI-initialization steps. -/
theorem bitSerialMulFuel_le (right : ℕ) :
    bitSerialMulFuel right ≤
      5 + 8 * right.bits.length := by
  unfold bitSerialMulFuel
  have := bitSerialMulLoopFuel_le right
  omega

def bitSerialMulRegisterBound
    (inputLength left right : ℕ) : ℕ :=
  max 1
    (max inputLength
      (max (bitSerialMulInput left right) (left * (right + 1))))

def bitSerialMulBits
    (inputLength left right : ℕ) : ℕ :=
  natBitLength (bitSerialMulRegisterBound inputLength left right)

private theorem registerValue_bits
    (inputLength left right value : ℕ)
    (hvalue : value ≤ bitSerialMulRegisterBound inputLength left right) :
    natBitLength value ≤ bitSerialMulBits inputLength left right := by
  exact natBitLength_mono hvalue

private theorem one_le_registerBound
    (inputLength left right : ℕ) :
    1 ≤ bitSerialMulRegisterBound inputLength left right := by
  simp [bitSerialMulRegisterBound]

private theorem input_le_registerBound
    (inputLength left right : ℕ) :
    bitSerialMulInput left right ≤
      bitSerialMulRegisterBound inputLength left right := by
  simp [bitSerialMulRegisterBound]

private theorem left_le_registerBound
    (inputLength left right : ℕ) :
    left ≤ bitSerialMulRegisterBound inputLength left right := by
  exact
    (Nat.left_le_pair left right).trans
      (input_le_registerBound inputLength left right)

private theorem right_le_registerBound
    (inputLength left right : ℕ) :
    right ≤ bitSerialMulRegisterBound inputLength left right := by
  exact
    (Nat.right_le_pair left right).trans
      (input_le_registerBound inputLength left right)

private theorem product_le_registerBound
    (inputLength left right : ℕ) :
    left * right ≤ bitSerialMulRegisterBound inputLength left right := by
  have : left * right ≤ left * (right + 1) :=
    Nat.mul_le_mul_left left (Nat.le_succ right)
  exact this.trans <| by
    simp [bitSerialMulRegisterBound]

private theorem shifted_le_registerBound
    (inputLength left right accumulator multiplicand remaining : ℕ)
    (hinvariant :
      accumulator + multiplicand * remaining = left * right)
    (hremaining : 0 < remaining) :
    multiplicand ≤ bitSerialMulRegisterBound inputLength left right := by
  have hmultiplicand :
      multiplicand ≤ accumulator + multiplicand * remaining := by
    have : multiplicand ≤ multiplicand * remaining := by
      simpa [Nat.mul_comm] using
        Nat.mul_le_mul_left multiplicand
          (Nat.succ_le_iff.mp hremaining)
    omega
  rw [hinvariant] at hmultiplicand
  exact hmultiplicand.trans
    (product_le_registerBound inputLength left right)

private theorem run_bitSerialMulLoop
    (inputLength left right accumulator multiplicand remaining : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 3)
    (haccumulator : state.registers 0 = accumulator)
    (hmultiplicand : state.registers 2 = multiplicand)
    (hremaining : state.registers 3 = remaining)
    (hbitIndex : state.registers 4 = 0)
    (hinvariant :
      accumulator + multiplicand * remaining = left * right)
    (hremainingBound :
      remaining ≤ bitSerialMulRegisterBound inputLength left right) :
    runNPOracleProgram bitSerialMulProgram
        (bitSerialMulBits inputLength left right)
        (bitSerialMulLoopFuel remaining) state =
      some (left * right) := by
  induction remaining using Nat.strong_induction_on generalizing
      state accumulator multiplicand with
  | h remaining ih =>
      let maximumBits := bitSerialMulBits inputLength left right
      let registerBound :=
        bitSerialMulRegisterBound inputLength left right
      have hproductBound : left * right ≤ registerBound := by
        exact product_le_registerBound inputLength left right
      have hproductBits : natBitLength (left * right) ≤ maximumBits := by
        exact registerValue_bits inputLength left right _ hproductBound
      have hzeroBits : natBitLength 0 ≤ maximumBits := by
        apply registerValue_bits inputLength left right
        exact Nat.zero_le registerBound
      have honeBits : natBitLength 1 ≤ maximumBits := by
        apply registerValue_bits inputLength left right
        exact one_le_registerBound inputLength left right
      by_cases hzero : remaining = 0
      · rw [bitSerialMulLoopFuel, dif_pos hzero]
        rw [show 2 = 1 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hremaining, if_pos hzero]
        have hfinal : accumulator = left * right := by
          simpa [hzero] using hinvariant
        apply run_halt_instruction (value := left * right)
          (by rfl) rfl
        · simp [NPOracleState.jump, haccumulator, hfinal]
        · exact hproductBits
      · have hpositive : 0 < remaining :=
          Nat.pos_of_ne_zero hzero
        let tail := remaining >>> 1
        have htailLt : tail < remaining := by
          exact shiftRight_one_lt hpositive
        have htailBound : tail ≤ registerBound := by
          exact (Nat.le_of_lt htailLt).trans hremainingBound
        have hmultiplicandBound : multiplicand ≤ registerBound := by
          exact shifted_le_registerBound inputLength left right
            accumulator multiplicand remaining hinvariant hpositive
        have hmultiplicandBits :
            natBitLength multiplicand ≤ maximumBits := by
          exact registerValue_bits inputLength left right _
            hmultiplicandBound
        have htailBits : natBitLength tail ≤ maximumBits := by
          exact registerValue_bits inputLength left right _ htailBound
        have hdecompose :
            remaining =
              2 * tail + (remaining.testBit 0).toNat := by
          exact shiftRight_decompose remaining
        rw [bitSerialMulLoopFuel, dif_neg hzero]
        dsimp only
        change
          runNPOracleProgram bitSerialMulProgram maximumBits
              (if tail = 0 then
                6 + (remaining.testBit 0).toNat
              else
                7 + (remaining.testBit 0).toNat +
                  bitSerialMulLoopFuel tail) state =
            some (left * right)
        by_cases htailZero : tail = 0
        · rw [if_pos htailZero]
          cases hbit : remaining.testBit 0 with
          | false =>
              have : remaining = 0 := by
                simpa [tail, htailZero, hbit] using hdecompose
              exact (hzero this).elim
          | true =>
              have hremainingOne : remaining = 1 := by
                simpa [tail, htailZero, hbit] using hdecompose
              have haddBound :
                  accumulator + multiplicand ≤ registerBound := by
                have hsum :
                    accumulator + multiplicand = left * right := by
                  simpa [hremainingOne] using hinvariant
                rw [hsum]
                exact hproductBound
              have haddBits :
                  natBitLength (accumulator + multiplicand) ≤ maximumBits := by
                exact registerValue_bits inputLength left right _
                  haddBound
              simp only [Bool.toNat_true, Nat.add_comm 6 1]
              rw [show 1 + 6 = (((((1 + 1) + 1) + 1) + 1) + 1) + 1 by
                omega]
              rw [run_branchZero_instruction (by rfl) hpc]
              rw [hremaining, if_neg hzero]
              rw [run_testBit_instruction (value := 1)
                (by rfl) rfl
                (by simp [hremaining, hbit, hbitIndex])
                honeBits]
              rw [run_branchZero_instruction (by rfl) rfl]
              rw [if_neg (by simp [NPOracleState.write])]
              rw [run_add_instruction
                (value := accumulator + multiplicand)
                (by rfl) rfl
                (by simp [NPOracleState.write, haccumulator,
                  hmultiplicand])
                haddBits]
              rw [run_shiftRight_instruction (value := tail)
                (by rfl) rfl
                (by simp [NPOracleState.write, hremaining, tail])
                htailBits]
              rw [run_branchZero_instruction (by rfl) rfl]
              rw [if_pos (by simp [NPOracleState.write, htailZero])]
              apply run_halt_instruction (value := left * right)
                (by rfl) rfl
              · simp only [NPOracleState.jump]
                simp [NPOracleState.write]
                simpa [hremainingOne] using hinvariant
              · exact hproductBits
        · rw [if_neg htailZero]
          have htailPositive : 0 < tail :=
            Nat.pos_of_ne_zero htailZero
          have hdoubleBound : 2 * multiplicand ≤ registerBound := by
            have hremainingAtLeastTwo : 2 ≤ remaining := by
              rw [hdecompose]
              omega
            have hdoubleLeProduct :
                2 * multiplicand ≤ left * right := by
              rw [← hinvariant]
              have :
                  2 * multiplicand ≤ multiplicand * remaining := by
                nlinarith
              omega
            exact hdoubleLeProduct.trans hproductBound
          have hdoubleBits :
              natBitLength (Nat.shiftLeft multiplicand 1) ≤ maximumBits := by
            rw [shiftLeft_one]
            exact registerValue_bits inputLength left right _ hdoubleBound
          cases hbit : remaining.testBit 0 with
          | false =>
              have hinvariant' :
                  accumulator +
                      (Nat.shiftLeft multiplicand 1) * tail =
                    left * right := by
                rw [shiftLeft_one]
                rw [← hinvariant]
                rw [hdecompose, hbit]
                simp only [Bool.toNat_false, Nat.add_zero]
                ring
              simp only [Bool.toNat_false, Nat.add_zero]
              rw [show
                7 + bitSerialMulLoopFuel tail =
                  ((((((bitSerialMulLoopFuel tail + 1) + 1) + 1) + 1) + 1) +
                    1) + 1 by omega]
              rw [run_branchZero_instruction (by rfl) hpc]
              rw [hremaining, if_neg hzero]
              rw [run_testBit_instruction (value := 0)
                (by rfl) rfl
                (by simp [hremaining, hbit, hbitIndex])
                hzeroBits]
              rw [run_branchZero_instruction (by rfl) rfl]
              rw [if_pos (by simp [NPOracleState.write])]
              rw [run_shiftRight_instruction (value := tail)
                (by rfl) rfl
                (by simp [NPOracleState.write, hremaining, tail])
                htailBits]
              rw [run_branchZero_instruction (by rfl) rfl]
              rw [if_neg (by simp [NPOracleState.write, htailZero])]
              rw [run_shiftLeft_instruction
                (value := Nat.shiftLeft multiplicand 1)
                (by rfl) rfl
                (by simp [NPOracleState.write, hmultiplicand])
                hdoubleBits]
              rw [run_copy_instruction
                (value := Nat.shiftLeft multiplicand 1)
                (by rfl) rfl
                (by simp [NPOracleState.write])
                hdoubleBits]
              apply ih tail htailLt
                (accumulator := accumulator)
                (multiplicand := Nat.shiftLeft multiplicand 1)
              · rfl
              · simp [NPOracleState.write, haccumulator]
              · simp [NPOracleState.write]
              · simp [NPOracleState.write]
              · simp [NPOracleState.write, hbitIndex]
              · exact hinvariant'
              · exact htailBound
          | true =>
              have haddBound :
                  accumulator + multiplicand ≤ registerBound := by
                have hmulLe :
                    accumulator + multiplicand ≤
                      accumulator + multiplicand * remaining := by
                  have :
                      multiplicand ≤ multiplicand * remaining := by
                    simpa [Nat.mul_comm] using
                      Nat.mul_le_mul_left multiplicand
                        (Nat.succ_le_iff.mp hpositive)
                  omega
                rw [hinvariant] at hmulLe
                exact hmulLe.trans hproductBound
              have haddBits :
                  natBitLength (accumulator + multiplicand) ≤ maximumBits := by
                exact registerValue_bits inputLength left right _
                  haddBound
              have hinvariant' :
                  (accumulator + multiplicand) +
                      (Nat.shiftLeft multiplicand 1) * tail =
                    left * right := by
                rw [shiftLeft_one]
                rw [← hinvariant]
                rw [hdecompose, hbit]
                simp only [Bool.toNat_true]
                ring
              simp only [Bool.toNat_true]
              rw [show
                7 + 1 + bitSerialMulLoopFuel tail =
                  (((((((bitSerialMulLoopFuel tail + 1) + 1) + 1) + 1) + 1) +
                    1) + 1) + 1 by omega]
              rw [run_branchZero_instruction (by rfl) hpc]
              rw [hremaining, if_neg hzero]
              rw [run_testBit_instruction (value := 1)
                (by rfl) rfl
                (by simp [hremaining, hbit, hbitIndex])
                honeBits]
              rw [run_branchZero_instruction (by rfl) rfl]
              rw [if_neg (by simp [NPOracleState.write])]
              rw [run_add_instruction
                (value := accumulator + multiplicand)
                (by rfl) rfl
                (by simp [NPOracleState.write, haccumulator,
                  hmultiplicand])
                haddBits]
              rw [run_shiftRight_instruction (value := tail)
                (by rfl) rfl
                (by simp [NPOracleState.write, hremaining, tail])
                htailBits]
              rw [run_branchZero_instruction (by rfl) rfl]
              rw [if_neg (by simp [NPOracleState.write, htailZero])]
              rw [run_shiftLeft_instruction
                (value := Nat.shiftLeft multiplicand 1)
                (by rfl) rfl
                (by simp [NPOracleState.write, hmultiplicand])
                hdoubleBits]
              rw [run_copy_instruction
                (value := Nat.shiftLeft multiplicand 1)
                (by rfl) rfl
                (by simp [NPOracleState.write])
                hdoubleBits]
              apply ih tail htailLt
                (accumulator := accumulator + multiplicand)
                (multiplicand := Nat.shiftLeft multiplicand 1)
              · rfl
              · simp [NPOracleState.write]
              · simp [NPOracleState.write]
              · simp [NPOracleState.write]
              · simp [NPOracleState.write, hbitIndex]
              · exact hinvariant'
              · exact htailBound

/-- Exact total execution from the public paired-input ABI. -/
theorem run_bitSerialMulProgram
    (inputLength left right : ℕ) :
    runNPOracleProgram bitSerialMulProgram
        (bitSerialMulBits inputLength left right)
        (bitSerialMulFuel right)
        (initialNPOracleState inputLength
          (bitSerialMulInput left right)) =
      some (left * right) := by
  let maximumBits := bitSerialMulBits inputLength left right
  let initial :=
    initialNPOracleState inputLength (bitSerialMulInput left right)
  let leftState := (initial.write 2 left).jump 1
  let rightState := (leftState.write 3 right).jump 2
  let loopState := (rightState.write 0 0).jump 3
  have hleftBits : natBitLength left ≤ maximumBits := by
    exact registerValue_bits inputLength left right _
      (left_le_registerBound inputLength left right)
  have hrightBits : natBitLength right ≤ maximumBits := by
    exact registerValue_bits inputLength left right _
      (right_le_registerBound inputLength left right)
  have hzeroBits : natBitLength 0 ≤ maximumBits := by
    apply registerValue_bits inputLength left right
    exact Nat.zero_le _
  rw [bitSerialMulFuel]
  rw [show
    3 + bitSerialMulLoopFuel right =
      ((bitSerialMulLoopFuel right + 1) + 1) + 1 by omega]
  rw [run_unpairLeft_instruction (value := left)
    (by rfl) rfl
    (by simp [initialNPOracleState, bitSerialMulInput])
    hleftBits]
  change
    runNPOracleProgram bitSerialMulProgram maximumBits
        (bitSerialMulLoopFuel right + 1 + 1) leftState =
      some (left * right)
  rw [run_unpairRight_instruction (value := right)
    (by rfl) rfl
    (by simp [leftState, initial, initialNPOracleState,
      bitSerialMulInput])
    hrightBits]
  change
    runNPOracleProgram bitSerialMulProgram maximumBits
        (bitSerialMulLoopFuel right + 1) rightState =
      some (left * right)
  rw [run_set_instruction (value := 0)
    (by rfl) rfl hzeroBits]
  change
    runNPOracleProgram bitSerialMulProgram maximumBits
        (bitSerialMulLoopFuel right) loopState =
      some (left * right)
  apply run_bitSerialMulLoop inputLength left right 0 left right loopState
  · rfl
  · simp [loopState, NPOracleState.write]
  · simp [loopState, rightState, leftState, NPOracleState.write]
  · simp [loopState, rightState, NPOracleState.write]
  · simp [loopState, rightState, leftState, initial,
      initialNPOracleState, NPOracleState.write]
  · simp
  · exact right_le_registerBound inputLength left right

end NearCubicWires.CanonicalBitSerialMulProgram
