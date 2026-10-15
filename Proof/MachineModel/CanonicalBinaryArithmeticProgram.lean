import Proof.Foundations.CanonicalBinaryProgram

/-!
# Canonical binary arithmetic semantics

Arithmetic is stated over decoded little-endian bit streams, independently of
their balanced public tree representation.  Executable consumers traverse the
tree with the shared shape-preserving ABI in `CanonicalBinaryProgram`; this
module deliberately does not retain the obsolete linked-list comparator.
-/

namespace NearCubicWires.CanonicalBinaryArithmeticProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-! ## Pure comparison semantics -/

/-- Scan little-endian bits while retaining the ordering determined by the
highest bit seen so far.  Missing high bits are zero. -/
def bitListLeScan : List Bool → List Bool → Bool → Bool
  | [], [], tie => tie
  | [], right :: rights, tie =>
      bitListLeScan [] rights (if right then true else tie)
  | left :: lefts, [], tie =>
      bitListLeScan lefts [] (if left then false else tie)
  | left :: lefts, right :: rights, tie =>
      bitListLeScan lefts rights
        (if left = right then tie else !left)

private theorem zero_lt_or_zero_eq (value : ℕ) :
    0 < value ∨ 0 = value := by
  rcases Nat.eq_zero_or_pos value with hzero | hpositive
  · exact Or.inr hzero.symm
  · exact Or.inl hpositive

private theorem twice_lt_odd_iff (left right : ℕ) :
    2 * left < 1 + 2 * right ↔ left ≤ right := by
  omega

private theorem odd_lt_twice_iff (left right : ℕ) :
    1 + 2 * left < 2 * right ↔ left < right := by
  omega

theorem bitListLeScan_eq
    (left right : List Bool) (tie : Bool) :
    bitListLeScan left right tie =
      decide
        (bitsValue left < bitsValue right ∨
          (bitsValue left = bitsValue right ∧ tie = true)) := by
  induction left generalizing right tie with
  | nil =>
      induction right generalizing tie with
      | nil =>
          cases tie <;> simp [bitListLeScan, bitsValue]
      | cons right rights ih =>
          cases right <;> cases tie <;>
            simp only [bitListLeScan, Bool.false_eq_true, ↓reduceIte,
              ih, bitsValue, and_false, or_false, Bool.toNat_false,
              zero_add, Order.lt_two_iff, zero_le,
              mul_pos_iff_of_pos_left, zero_eq_mul,
              OfNat.ofNat_ne_zero, false_or, and_true,
              Bool.decide_or, Bool.toNat_true, add_pos_iff,
              Order.lt_one_iff, true_or, decide_true,
              Bool.or_eq_true, decide_eq_true_eq] <;>
            try {
              apply Bool.eq_iff_iff.mpr
              simp
              omega
            }
          all_goals exact zero_lt_or_zero_eq _
  | cons left lefts ih =>
      cases right with
      | nil =>
          cases left <;> cases tie <;>
            simp [bitListLeScan, bitsValue, ih]
      | cons right rights =>
          cases left <;> cases right <;> cases tie <;>
            simp only [bitListLeScan, ↓reduceIte, ih,
              Bool.false_eq_true, and_false, or_false, bitsValue,
              Bool.toNat_false, zero_add, Order.lt_two_iff, zero_le,
              mul_lt_mul_iff_right₀, mul_eq_mul_left_iff,
              OfNat.ofNat_ne_zero, and_true, Bool.decide_or,
              Bool.not_false, Bool.toNat_true, Bool.true_eq_false,
              Bool.not_true, decide_eq_decide, add_lt_add_iff_left,
              Nat.add_left_cancel_iff] <;>
            try {
              apply Bool.eq_iff_iff.mpr
              simp
              omega
            }
          all_goals
            first
            | exact odd_lt_twice_iff _ _
            | exact twice_lt_odd_iff _ _
            | exact (odd_lt_twice_iff _ _).symm

theorem bitListLeScan_true (left right : List Bool) :
    bitListLeScan left right true =
      decide (bitsValue left ≤ bitsValue right) := by
  rw [bitListLeScan_eq]
  apply Bool.eq_iff_iff.mpr
  simp
  omega

/-- The fixed comparator input remains a pair of canonical balanced bit trees.
No native decoded integer is admitted at this boundary. -/
def bitListLeInput (left right : List Bool) : ℕ :=
  Nat.pair (encodeBits left) (encodeBits right)

def bitListLeOutput (left right : List Bool) : ℕ :=
  (bitListLeScan left right true).toNat

theorem bitListLeOutput_eq (left right : List Bool) :
    bitListLeOutput left right =
      (decide (bitsValue left ≤ bitsValue right) : Bool).toNat := by
  simp [bitListLeOutput, bitListLeScan_true]

/-! ## Fixed native-natural comparison

Resource counters and trusted public limits are native register values.  This
loop compares them in time linear in their binary width: it shifts both
operands right, retaining the order selected by the highest unequal bit seen
so far.  It does not convert either operand to unary and uses no SAT call.
-/

private theorem shiftRight_one_le (value : ℕ) :
    value >>> 1 ≤ value := by
  exact Nat.shiftRight_le value 1

private theorem shiftRight_one_lt
    {value : ℕ} (hpositive : 0 < value) :
    value >>> 1 < value := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self hpositive (by norm_num)

/-- Native counterpart of `bitListLeScan`. -/
def nativeNatLeScan : ℕ → ℕ → Bool → Bool
  | left, right, tie =>
      if left = 0 ∧ right = 0 then
        tie
      else
        nativeNatLeScan (left >>> 1) (right >>> 1)
          (if left.testBit 0 = right.testBit 0 then
            tie
          else
            !left.testBit 0)
termination_by left right _tie => left + right
decreasing_by
  have _hleft := shiftRight_one_le left
  have hright := shiftRight_one_le right
  by_cases hleftZero : left = 0
  · have hrightPositive : 0 < right := by
      omega
    have hrightStrict := shiftRight_one_lt hrightPositive
    omega
  · have hleftPositive : 0 < left := Nat.pos_of_ne_zero hleftZero
    have hleftStrict := shiftRight_one_lt hleftPositive
    omega

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

theorem nativeNatLeScan_eq_bitListLeScan
    (left right : ℕ) (tie : Bool) :
    nativeNatLeScan left right tie =
      bitListLeScan left.bits right.bits tie := by
  induction left, right, tie using nativeNatLeScan.induct with
  | case1 left right tie hzero =>
      rcases hzero with ⟨rfl, rfl⟩
      simp [nativeNatLeScan, bitListLeScan]
  | case2 left right tie hnonzero inductionHypothesis =>
      rw [nativeNatLeScan, if_neg hnonzero]
      by_cases hleft : left = 0
      · subst left
        have hright : right ≠ 0 := by
          simpa using hnonzero
        rw [bits_of_nonzero hright]
        simp only [Nat.zero_bits, bitListLeScan]
        cases hbit : right.testBit 0 <;> cases tie <;>
          simpa [hbit] using inductionHypothesis
      · rw [bits_of_nonzero hleft]
        by_cases hright : right = 0
        · subst right
          simp only [Nat.zero_bits, bitListLeScan]
          cases hbit : left.testBit 0 <;> cases tie <;>
            simpa [hbit] using inductionHypothesis
        · rw [bits_of_nonzero hright]
          simp only [bitListLeScan]
          exact inductionHypothesis

theorem nativeNatLeScan_true (left right : ℕ) :
    nativeNatLeScan left right true = decide (left ≤ right) := by
  rw [nativeNatLeScan_eq_bitListLeScan, bitListLeScan_true]
  simp [bitsValue_natBits]

def nativeNatLeInput (left right : ℕ) : ℕ :=
  Nat.pair left right

def nativeNatLeOutput (left right : ℕ) : ℕ :=
  (nativeNatLeScan left right true).toNat

theorem nativeNatLeOutput_eq (left right : ℕ) :
    nativeNatLeOutput left right =
      (decide (left ≤ right) : Bool).toNat := by
  simp [nativeNatLeOutput, nativeNatLeScan_true]

/-- Register ABI: `r0 = pair(left,right)` on entry and the Boolean result in
`r7` on exit.  Registers `r4/r5` are shifting cursors, `r6` is the fixed zero
bit index, and `r8/r9` hold the current low bits. -/
def nativeNatLeProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .copy 2 4 3
  , .copy 3 5 4
  , .set 7 1 5
  , .branchZero 4 6 8
  , .branchZero 5 20 10
  , .branchZero 0 20 20
  , .branchZero 5 10 10
  , .branchZero 0 20 20
  , .testBit 4 6 8 11
  , .testBit 5 6 9 12
  , .branchZero 8 13 15
  , .branchZero 9 18 14
  , .set 7 1 18
  , .branchZero 9 16 18
  , .set 7 0 18
  , .branchZero 0 20 20
  , .shiftRight 4 1 4 19
  , .shiftRight 5 1 5 5
  , .halt 7
  ]

@[simp] theorem nativeNatLeProgram_oracleFree :
    OracleFree nativeNatLeProgram := by
  rfl

def nativeNatLeIterationCost (left right : ℕ) : ℕ :=
  8 + if left.testBit 0 = right.testBit 0 then 0 else 1

def nativeNatLeLoopFuel : ℕ → ℕ → ℕ
  | left, right =>
      if left = 0 ∧ right = 0 then
        3
      else
        nativeNatLeIterationCost left right +
          nativeNatLeLoopFuel (left >>> 1) (right >>> 1)
termination_by left right => left + right
decreasing_by
  have _hleft := shiftRight_one_le left
  have hright := shiftRight_one_le right
  by_cases hleftZero : left = 0
  · have hrightPositive : 0 < right := by
      omega
    have hrightStrict := shiftRight_one_lt hrightPositive
    omega
  · have hleftPositive : 0 < left := Nat.pos_of_ne_zero hleftZero
    have hleftStrict := shiftRight_one_lt hleftPositive
    omega

def nativeNatLeFuel (left right : ℕ) : ℕ :=
  5 + nativeNatLeLoopFuel left right

def nativeNatLeBits (left right : ℕ) : ℕ :=
  natBitLength (nativeNatLeInput left right)

private def nativeNatLeObservedState
    (state : NPOracleState) (left right : ℕ) : NPOracleState :=
  (state.write 8 (left.testBit 0).toNat).write
    9 (right.testBit 0).toNat

private def nativeNatLeResultState
    (state : NPOracleState) (left right : ℕ) : NPOracleState :=
  if left.testBit 0 = right.testBit 0 then
    nativeNatLeObservedState state left right
  else
    (nativeNatLeObservedState state left right).write
      7 (!left.testBit 0).toNat

private def nativeNatLeDecisionCost (left right : ℕ) : ℕ :=
  2 + if left.testBit 0 = right.testBit 0 then 0 else 1

private def nativeNatLeLoopState
    (state : NPOracleState) (left right : ℕ) : NPOracleState :=
  ((((nativeNatLeResultState state left right).write
      4 (left >>> 1)).jump 19).write
    5 (right >>> 1)).jump 5

private theorem run_nativeNatLeControl
    (left right maximumBits fuel : ℕ)
    (state : NPOracleState)
    (hnonzero : ¬(left = 0 ∧ right = 0))
    (hpc : state.pc = 5)
    (hleft : state.registers 4 = left)
    (hright : state.registers 5 = right) :
    runNPOracleProgram nativeNatLeProgram maximumBits
        (fuel + 2) state =
      runNPOracleProgram nativeNatLeProgram maximumBits fuel
        (state.jump 10) := by
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [run_branchZero_instruction (by rfl) hpc]
  by_cases hleftZero : left = 0
  · have hrightNonzero : right ≠ 0 := by
      simpa [hleftZero] using hnonzero
    rw [if_pos (by simp [hleft, hleftZero])]
    rw [run_branchZero_instruction
      (pc := 6) (register := 5) (zeroTarget := 20)
      (nonzeroTarget := 10) (by rfl) (by rfl)]
    simp [NPOracleState.jump, hright, hrightNonzero]
  · rw [if_neg (by simpa [hleft] using hleftZero)]
    rw [run_branchZero_instruction
      (pc := 8) (register := 5) (zeroTarget := 10)
      (nonzeroTarget := 10) (by rfl) (by rfl)]
    simp [NPOracleState.jump]

private theorem run_nativeNatLeObserve
    (left right maximumBits fuel : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 10)
    (hleft : state.registers 4 = left)
    (hright : state.registers 5 = right)
    (hindex : state.registers 6 = 0)
    (hpositive : 1 ≤ maximumBits) :
    runNPOracleProgram nativeNatLeProgram maximumBits
        (fuel + 2) state =
      runNPOracleProgram nativeNatLeProgram maximumBits fuel
        ((nativeNatLeObservedState state left right).jump 12) := by
  have hleftBit :
      natBitLength (left.testBit 0).toNat ≤ maximumBits := by
    cases left.testBit 0 <;> simp_all [natBitLength]
  have hrightBit :
      natBitLength (right.testBit 0).toNat ≤ maximumBits := by
    cases right.testBit 0 <;> simp_all [natBitLength]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [run_testBit_instruction (by rfl) hpc
    (by simp [hleft, hindex]) hleftBit]
  rw [run_testBit_instruction
    (pc := 11) (source := 5) (index := 6) (destination := 9)
    (next := 12) (value := (right.testBit 0).toNat)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump, hright, hindex])
    hrightBit]
  rfl

private theorem run_nativeNatLeDecide
    (left right maximumBits fuel : ℕ)
    (state : NPOracleState)
    (hpositive : 1 ≤ maximumBits) :
    runNPOracleProgram nativeNatLeProgram maximumBits
        (fuel + nativeNatLeDecisionCost left right)
        ((nativeNatLeObservedState state left right).jump 12) =
      runNPOracleProgram nativeNatLeProgram maximumBits fuel
        ((nativeNatLeResultState state left right).jump 18) := by
  have hzero : natBitLength 0 ≤ maximumBits := by
    simp [natBitLength]
    omega
  have hone : natBitLength 1 ≤ maximumBits := by
    simp [natBitLength]
    omega
  cases hleftBit : left.testBit 0 <;>
    cases hrightBit : right.testBit 0 <;>
    simp [nativeNatLeDecisionCost, nativeNatLeObservedState,
      nativeNatLeResultState, nativeNatLeProgram, runNPOracleProgram,
      hleftBit, hrightBit, NPOracleState.boundedWrite,
      hzero, hone, NPOracleState.write, NPOracleState.jump]

private theorem run_nativeNatLeShift
    (left right maximumBits fuel : ℕ)
    (state : NPOracleState)
    (hleft : state.registers 4 = left)
    (hright : state.registers 5 = right)
    (hleftBits : natBitLength left ≤ maximumBits)
    (hrightBits : natBitLength right ≤ maximumBits) :
    runNPOracleProgram nativeNatLeProgram maximumBits
        (fuel + 2)
        ((nativeNatLeResultState state left right).jump 18) =
      runNPOracleProgram nativeNatLeProgram maximumBits fuel
        (nativeNatLeLoopState state left right) := by
  have hresultLeft :
      (nativeNatLeResultState state left right).registers 4 = left := by
    unfold nativeNatLeResultState nativeNatLeObservedState
    split <;> simp [NPOracleState.write, hleft]
  have hresultRight :
      (nativeNatLeResultState state left right).registers 5 = right := by
    unfold nativeNatLeResultState nativeNatLeObservedState
    split <;> simp [NPOracleState.write, hright]
  have hleftShift :
      natBitLength (left >>> 1) ≤ maximumBits :=
    (shiftRight_bits_le left 1).trans hleftBits
  have hrightShift :
      natBitLength (right >>> 1) ≤ maximumBits :=
    (shiftRight_bits_le right 1).trans hrightBits
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [run_shiftRight_instruction
    (pc := 18) (source := 4) (amount := 1) (destination := 4)
    (next := 19) (value := left >>> 1)
    (by rfl) (by rfl)
    (by simp [NPOracleState.jump, hresultLeft]) hleftShift]
  rw [run_shiftRight_instruction
    (pc := 19) (source := 5) (amount := 1) (destination := 5)
    (next := 5) (value := right >>> 1)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump, hresultRight])
    hrightShift]
  rfl

private theorem run_nativeNatLeIteration
    (left right maximumBits extra : ℕ)
    (state : NPOracleState)
    (hnonzero : ¬(left = 0 ∧ right = 0))
    (hpc : state.pc = 5)
    (hleft : state.registers 4 = left)
    (hright : state.registers 5 = right)
    (hindex : state.registers 6 = 0)
    (hpositive : 1 ≤ maximumBits)
    (hleftBits : natBitLength left ≤ maximumBits)
    (hrightBits : natBitLength right ≤ maximumBits) :
    runNPOracleProgram nativeNatLeProgram maximumBits
        (nativeNatLeIterationCost left right + extra) state =
      runNPOracleProgram nativeNatLeProgram maximumBits extra
        (nativeNatLeLoopState state left right) := by
  rw [show nativeNatLeIterationCost left right + extra =
      (((extra + 2) + nativeNatLeDecisionCost left right) + 2) + 2 by
    unfold nativeNatLeIterationCost nativeNatLeDecisionCost
    split <;> omega]
  rw [run_nativeNatLeControl left right maximumBits
    (((extra + 2) + nativeNatLeDecisionCost left right) + 2)
    state hnonzero hpc hleft hright]
  rw [run_nativeNatLeObserve left right maximumBits
    ((extra + 2) + nativeNatLeDecisionCost left right)
    (state.jump 10)
    (by rfl)
    (by simpa [NPOracleState.jump] using hleft)
    (by simpa [NPOracleState.jump] using hright)
    (by simpa [NPOracleState.jump] using hindex)
    hpositive]
  rw [run_nativeNatLeDecide left right maximumBits
    (extra + 2) (state.jump 10) hpositive]
  rw [run_nativeNatLeShift left right maximumBits extra
    (state.jump 10)
    (by simpa [NPOracleState.jump] using hleft)
    (by simpa [NPOracleState.jump] using hright)
    hleftBits hrightBits]
  congr 1
  unfold nativeNatLeLoopState nativeNatLeResultState
    nativeNatLeObservedState
  split <;> rfl

private theorem run_nativeNatLeLoop
    (left right maximumBits : ℕ) (tie : Bool)
    (state : NPOracleState)
    (hpc : state.pc = 5)
    (hleft : state.registers 4 = left)
    (hright : state.registers 5 = right)
    (hindex : state.registers 6 = 0)
    (htie : state.registers 7 = tie.toNat)
    (hpositive : 1 ≤ maximumBits)
    (hleftBits : natBitLength left ≤ maximumBits)
    (hrightBits : natBitLength right ≤ maximumBits) :
    runNPOracleProgram nativeNatLeProgram maximumBits
        (nativeNatLeLoopFuel left right) state =
      some (nativeNatLeScan left right tie).toNat := by
  induction left, right, tie using nativeNatLeScan.induct
      generalizing maximumBits state with
  | case1 left right tie hzero =>
      rcases hzero with ⟨rfl, rfl⟩
      cases tie <;>
        simp [nativeNatLeLoopFuel, nativeNatLeScan, nativeNatLeProgram,
          runNPOracleProgram, hpc, hleft, hright, htie, natBitLength,
          hpositive, NPOracleState.jump]
  | case2 left right tie hnonzero inductionHypothesis =>
      let nextTie :=
        if left.testBit 0 = right.testBit 0 then
          tie
        else
          !left.testBit 0
      let nextState := nativeNatLeLoopState state left right
      have hnextPc : nextState.pc = 5 := by
        unfold nextState nativeNatLeLoopState nativeNatLeResultState
          nativeNatLeObservedState
        split <;> rfl
      have hnextLeft :
          nextState.registers 4 = left >>> 1 := by
        unfold nextState nativeNatLeLoopState nativeNatLeResultState
          nativeNatLeObservedState
        split <;>
          simp [NPOracleState.write, NPOracleState.jump]
      have hnextRight :
          nextState.registers 5 = right >>> 1 := by
        unfold nextState nativeNatLeLoopState nativeNatLeResultState
          nativeNatLeObservedState
        split <;>
          simp [NPOracleState.write, NPOracleState.jump]
      have hnextIndex : nextState.registers 6 = 0 := by
        unfold nextState nativeNatLeLoopState nativeNatLeResultState
          nativeNatLeObservedState
        split <;>
          simp [NPOracleState.write, NPOracleState.jump, hindex]
      have hnextTie : nextState.registers 7 = nextTie.toNat := by
        unfold nextState nextTie nativeNatLeLoopState
          nativeNatLeResultState nativeNatLeObservedState
        split <;>
          simp_all [NPOracleState.write, NPOracleState.jump]
      have hnextLeftBits :
          natBitLength (left >>> 1) ≤ maximumBits :=
        (shiftRight_bits_le left 1).trans hleftBits
      have hnextRightBits :
          natBitLength (right >>> 1) ≤ maximumBits :=
        (shiftRight_bits_le right 1).trans hrightBits
      rw [nativeNatLeLoopFuel, if_neg hnonzero]
      rw [run_nativeNatLeIteration left right maximumBits
        (nativeNatLeLoopFuel (left >>> 1) (right >>> 1))
        state hnonzero hpc hleft hright hindex hpositive
        hleftBits hrightBits]
      rw [inductionHypothesis maximumBits nextState
        hnextPc hnextLeft hnextRight hnextIndex hnextTie hpositive
        hnextLeftBits hnextRightBits]
      have hscan :
          nativeNatLeScan left right tie =
            nativeNatLeScan (left >>> 1) (right >>> 1) nextTie := by
        rw [nativeNatLeScan, if_neg hnonzero]
      rw [hscan]
      rfl

/-- Exact execution theorem for the fixed, oracle-free native comparator. -/
theorem run_nativeNatLeProgram
    (inputLength left right : ℕ) :
    runNPOracleProgram nativeNatLeProgram
        (nativeNatLeBits left right)
        (nativeNatLeFuel left right)
        (initialNPOracleState inputLength (nativeNatLeInput left right)) =
      some (nativeNatLeOutput left right) := by
  have hpositive : 1 ≤ nativeNatLeBits left right := by
    simp [nativeNatLeBits, natBitLength]
  have hleftBits :
      natBitLength left ≤ nativeNatLeBits left right := by
    unfold nativeNatLeBits nativeNatLeInput
    exact natBitLength_mono (Nat.left_le_pair left right)
  have hrightBits :
      natBitLength right ≤ nativeNatLeBits left right := by
    unfold nativeNatLeBits nativeNatLeInput
    exact natBitLength_mono (Nat.right_le_pair left right)
  rw [show nativeNatLeFuel left right =
      (((((nativeNatLeLoopFuel left right + 1) + 1) + 1) + 1) + 1) by
    unfold nativeNatLeFuel
    omega]
  rw [run_unpairLeft_instruction
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := left) (by rfl) (by rfl)
    (by simp [initialNPOracleState, nativeNatLeInput])
    hleftBits]
  rw [run_unpairRight_instruction
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := right) (by rfl) (by rfl)
    (by simp [initialNPOracleState, nativeNatLeInput,
      NPOracleState.write, NPOracleState.jump])
    hrightBits]
  rw [run_copy_instruction
    (pc := 2) (source := 2) (destination := 4) (next := 3)
    (value := left) (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump])
    hleftBits]
  rw [run_copy_instruction
    (pc := 3) (source := 3) (destination := 5) (next := 4)
    (value := right) (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrightBits]
  rw [run_set_instruction
    (pc := 4) (register := 7) (value := 1) (next := 5)
    (by rfl) (by rfl)
    (by simpa [natBitLength] using hpositive)]
  apply run_nativeNatLeLoop left right (nativeNatLeBits left right) true
  · rfl
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hpositive
  · exact hleftBits
  · exact hrightBits

private theorem nativeNatLeLoopFuel_le_bits (left right : ℕ) :
    nativeNatLeLoopFuel left right ≤
      9 * (left.bits.length + right.bits.length) + 3 := by
  induction left, right using nativeNatLeLoopFuel.induct with
  | case1 left right hzero =>
      rcases hzero with ⟨rfl, rfl⟩
      simp [nativeNatLeLoopFuel]
  | case2 left right hnonzero inductionHypothesis =>
      have hcost : nativeNatLeIterationCost left right ≤ 9 := by
        unfold nativeNatLeIterationCost
        split <;> omega
      have hleftLength :
          (left >>> 1).bits.length ≤ left.bits.length := by
        by_cases hleftZero : left = 0
        · subst left
          simp
        · rw [bits_of_nonzero hleftZero]
          simp
      have hrightLength :
          (right >>> 1).bits.length ≤ right.bits.length := by
        by_cases hrightZero : right = 0
        · subst right
          simp
        · rw [bits_of_nonzero hrightZero]
          simp
      have hstrict :
          (left >>> 1).bits.length + (right >>> 1).bits.length + 1 ≤
            left.bits.length + right.bits.length := by
        by_cases hleftZero : left = 0
        · have hrightNonzero : right ≠ 0 := by
            simpa [hleftZero] using hnonzero
          subst left
          rw [bits_of_nonzero hrightNonzero]
          simp
        · rw [bits_of_nonzero hleftZero]
          simp only [List.length_cons]
          omega
      rw [nativeNatLeLoopFuel, if_neg hnonzero]
      omega

private theorem bitsLength_le_natBitLength (value : ℕ) :
    value.bits.length ≤ natBitLength value := by
  rw [Nat.size_eq_bits_len]
  apply (Nat.size_le).2
  simpa [natBitLength, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (b := 2) (by omega) value)

/-- Fuel is linear in the binary input width, independently of operand
magnitude. -/
theorem nativeNatLeFuel_le (left right : ℕ) :
    nativeNatLeFuel left right ≤
      18 * nativeNatLeBits left right + 8 := by
  have hloop := nativeNatLeLoopFuel_le_bits left right
  have hleftLength := bitsLength_le_natBitLength left
  have hrightLength := bitsLength_le_natBitLength right
  have hleftBits :
      natBitLength left ≤ nativeNatLeBits left right := by
    unfold nativeNatLeBits nativeNatLeInput
    exact natBitLength_mono (Nat.left_le_pair left right)
  have hrightBits :
      natBitLength right ≤ nativeNatLeBits left right := by
    unfold nativeNatLeBits nativeNatLeInput
    exact natBitLength_mono (Nat.right_le_pair left right)
  unfold nativeNatLeFuel
  omega

end NearCubicWires.CanonicalBinaryArithmeticProgram
